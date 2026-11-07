-- Prove2me | solution 1 for ShockWear.WearProcess.lemma41b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:21:07.830249+00:00
-- url     : https://prove2.me/submissions/54aff404-b502-4d18-bfff-b59d1c279910

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace SW41b

/-- Probability of staying `≤ x` for `n` more steps, starting at time `m` at level `z`
(increments clamped at `0`). -/
noncomputable def fS (κ : ℕ → Kernel ℝ ℝ) (x : ℝ) : ℕ → ℕ → ℝ → ℝ≥0∞
  | 0, _, z => Set.indicator (Set.Iic x) (fun _ => (1 : ℝ≥0∞)) z
  | n + 1, m, z => ∫⁻ u, fS κ x n (m + 1) (z + max u 0) ∂(κ m z)

variable (κ : ℕ → Kernel ℝ ℝ) (x : ℝ)

lemma fS_zero (m : ℕ) (z : ℝ) :
    fS κ x 0 m z = Set.indicator (Set.Iic x) (fun _ => (1 : ℝ≥0∞)) z := rfl

lemma fS_succ (n m : ℕ) (z : ℝ) :
    fS κ x (n + 1) m z = ∫⁻ u, fS κ x n (m + 1) (z + max u 0) ∂(κ m z) := rfl

lemma fS_meas [hκ : ∀ k, IsMarkovKernel (κ k)] : ∀ n m, Measurable (fS κ x n m) := by
  intro n
  induction n with
  | zero => intro m; exact (measurable_const.indicator measurableSet_Iic)
  | succ n ih =>
    intro m
    have h : Measurable (Function.uncurry fun z u => fS κ x n (m + 1) (z + max u 0)) := by
      apply (ih (m + 1)).comp
      fun_prop
    exact h.lintegral_kernel_prod_right

lemma fS_le_one [hκ : ∀ k, IsMarkovKernel (κ k)] : ∀ n m z, fS κ x n m z ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro m z
    simp only [fS]
    exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
  | succ n ih =>
    intro m z
    rw [fS_succ]
    calc ∫⁻ u, fS κ x n (m + 1) (z + max u 0) ∂(κ m z) ≤ ∫⁻ _, 1 ∂(κ m z) :=
          lintegral_mono fun u => ih _ _
      _ = 1 := by simp

lemma fS_above : ∀ n m z, x < z → fS κ x n m z = 0 := by
  intro n
  induction n with
  | zero => intro m z hz; unfold fS; simp [Set.indicator, not_le.2 hz]
  | succ n ih =>
    intro m z hz
    rw [fS_succ]
    have : ∀ u, fS κ x n (m + 1) (z + max u 0) = 0 := fun u =>
      ih _ _ (lt_of_lt_of_le hz (le_add_of_nonneg_right (le_max_right _ _)))
    simp [this]

/-- Lower sets: stochastic dominance on `Iic` implies dominance on every lower set. -/
lemma lower_le (ν ν' : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ u, ν' (Set.Iic u) ≤ ν (Set.Iic u)) (S : Set ℝ) (hS : IsLowerSet S) :
    ν' S ≤ ν S := by
  by_cases hne : S.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
  by_cases hb : BddAbove S
  swap
  · have : S = Set.univ := by
      ext a
      simp only [Set.mem_univ, iff_true]
      rw [not_bddAbove_iff] at hb
      obtain ⟨s, hs, has⟩ := hb a
      exact hS has.le hs
    rw [this]; simp
  set c := sSup S
  by_cases hc : c ∈ S
  · have : S = Set.Iic c := by
      ext a
      constructor
      · intro ha; exact le_csSup hb ha
      · intro ha; exact hS ha hc
    rw [this]; exact h c
  · have hS' : S = Set.Iio c := by
      ext a
      constructor
      · intro ha
        exact lt_of_le_of_ne (le_csSup hb ha) (fun hac => hc (by change sSup S ∈ S; rw [← hac]; exact ha))
      · intro ha
        obtain ⟨s, hs, has⟩ := exists_lt_of_lt_csSup hne ha
        exact hS has.le hs
    have hU : Set.Iio c = ⋃ n : ℕ, Set.Iic (c - 1 / ((n : ℝ) + 1)) := by
      ext a
      simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
      constructor
      · intro ha
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmono : Monotone (fun n : ℕ => Set.Iic (c - 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      apply Set.Iic_subset_Iic.2
      have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hab 1
      linarith
    rw [hS', hU, hmono.measure_iUnion, hmono.measure_iUnion]
    exact iSup_mono fun n => h _

/-- Stochastic dominance: integrals of antitone functions bounded by 1. -/
lemma sd_lintegral (ν ν' : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ u, ν' (Set.Iic u) ≤ ν (Set.Iic u)) (g : ℝ → ℝ≥0∞) (hg : Antitone g)
    (hgm : Measurable g) (hg1 : ∀ u, g u ≤ 1) :
    ∫⁻ u, g u ∂ν' ≤ ∫⁻ u, g u ∂ν := by
  have hfin : ∀ u, g u ≠ ⊤ := fun u => ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 u)
  have e : ∀ u, g u = ENNReal.ofReal (g u).toReal := fun u => (ENNReal.ofReal_toReal (hfin u)).symm
  rw [lintegral_congr fun u => e u, lintegral_congr (μ := ν) fun u => e u]
  have hm : Measurable (fun u => (g u).toReal) := hgm.ennreal_toReal
  rw [lintegral_eq_lintegral_meas_lt ν' (Eventually.of_forall fun u => ENNReal.toReal_nonneg)
      hm.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall fun u => ENNReal.toReal_nonneg)
      hm.aemeasurable]
  apply lintegral_mono
  intro t
  apply lower_le ν ν' h
  intro a b hab ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  exact lt_of_lt_of_le ha (ENNReal.toReal_mono (hfin b) (hg hab))


section Mono
variable [hκ : ∀ k, IsMarkovKernel (κ k)]
  (hdz : ∀ k u, AntitoneOn (fun z => κ k z (Set.Iic u)) (Set.Ici 0))
  (hdk : ∀ k u z, 0 ≤ z → κ (k + 1) z (Set.Iic u) ≤ κ k z (Set.Iic u))
include hdz hdk

lemma kdom : ∀ m m' z z', m ≤ m' → 0 ≤ z → z ≤ z' → ∀ u,
    κ m' z' (Set.Iic u) ≤ κ m z (Set.Iic u) := by
  intro m m' z z' hm hz hzz u
  have h1 : κ m' z' (Set.Iic u) ≤ κ m' z (Set.Iic u) :=
    hdz m' u (Set.mem_Ici.2 hz) (Set.mem_Ici.2 (le_trans hz hzz)) hzz
  refine le_trans h1 ?_
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact le_trans (hdk k u z hz) (ih (le_trans (hdz k u (Set.mem_Ici.2 hz)
      (Set.mem_Ici.2 (le_trans hz hzz)) hzz) (le_refl _)))

lemma fS_mono : ∀ n m m' z z', m ≤ m' → 0 ≤ z → z ≤ z' → fS κ x n m' z' ≤ fS κ x n m z := by
  intro n
  induction n with
  | zero =>
    intro m m' z z' _ _ hzz
    simp only [fS]
    by_cases h : z' ≤ x
    · have : z ≤ x := le_trans hzz h
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]
  | succ n ih =>
    intro m m' z z' hm hz hzz
    rw [fS_succ, fS_succ]
    calc ∫⁻ u, fS κ x n (m' + 1) (z' + max u 0) ∂(κ m' z')
        ≤ ∫⁻ u, fS κ x n (m + 1) (z + max u 0) ∂(κ m' z') := by
          apply lintegral_mono
          intro u
          exact ih _ _ _ _ (by omega) (by positivity) (by linarith)
      _ ≤ ∫⁻ u, fS κ x n (m + 1) (z + max u 0) ∂(κ m z) := by
          apply sd_lintegral (κ m z) (κ m' z') (kdom κ hdz hdk m m' z z' hm hz hzz)
          · intro a b hab
            exact ih _ _ _ _ le_rfl (by positivity) (by
              have := max_le_max_right 0 hab; linarith)
          · exact (fS_meas κ x n (m + 1)).comp (by fun_prop)
          · intro u; exact fS_le_one κ x _ _ _

omit hdz hdk in
lemma alg (a b c : ℝ≥0∞) (n : ℕ) (h : a ^ (n + 1) ≤ b * c ^ (n + 1)) :
    a ≤ b ^ (((n + 1 : ℕ) : ℝ)⁻¹) * c := by
  have hn : (n + 1 : ℕ) ≠ 0 := by omega
  have hr : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have h2 := ENNReal.rpow_le_rpow h hr
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr] at h2
  have e1 : (a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) = a := ENNReal.pow_rpow_inv_natCast hn a
  have e2 : (c ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) = c := ENNReal.pow_rpow_inv_natCast hn c
  rw [e1, e2] at h2
  exact h2

lemma step_Q (n : ℕ)
    (hPE : ∀ m z w, 0 ≤ z → z ≤ w →
      fS κ x (n + 1) (m + 1) w ^ (n + 1) ≤ fS κ x (n + 1) m z * fS κ x n (m + 1) w ^ (n + 1)) :
    ∀ m z, 0 ≤ z → fS κ x (n + 2) m z ^ (n + 1) ≤ fS κ x (n + 1) m z ^ (n + 2) := by
  intro m z hz
  set B := fS κ x (n + 1) m z with hB
  set e : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  have hle : fS κ x (n + 2) m z ≤ B ^ e * B := by
    rw [fS_succ]
    calc ∫⁻ u, fS κ x (n + 1) (m + 1) (z + max u 0) ∂(κ m z)
        ≤ ∫⁻ u, B ^ e * fS κ x n (m + 1) (z + max u 0) ∂(κ m z) := by
          apply lintegral_mono
          intro u
          exact alg _ _ _ n (hPE m z _ hz (le_add_of_nonneg_right (le_max_right _ _)))
      _ = B ^ e * B := by
          have hmeas : Measurable (fun u : ℝ => fS κ x n (m + 1) (z + max u 0)) :=
            (fS_meas κ x n (m + 1)).comp (by fun_prop)
          rw [lintegral_const_mul _ hmeas, hB, fS_succ]
  have hn : (n + 1 : ℕ) ≠ 0 := by omega
  calc fS κ x (n + 2) m z ^ (n + 1) ≤ (B ^ e * B) ^ (n + 1) := pow_le_pow_left₀ (by positivity) hle _
    _ = B ^ (n + 2) := by
      rw [mul_pow, ENNReal.rpow_inv_natCast_pow hn, pow_succ B (n + 1), mul_comm]

lemma fS_Q : ∀ n m z, 0 ≤ z → fS κ x (n + 2) m z ^ (n + 1) ≤ fS κ x (n + 1) m z ^ (n + 2) := by
  intro n
  induction n with
  | zero =>
    apply step_Q κ x hdz hdk 0
    intro m z w hz hzw
    simp only [pow_one, zero_add]
    by_cases hw : w ≤ x
    · have : fS κ x 0 (m + 1) w = 1 := by simp [fS, Set.indicator, hw]
      rw [this, mul_one]
      exact fS_mono κ x hdz hdk 1 m (m + 1) z w (by omega) hz hzw
    · rw [fS_above κ x 1 (m + 1) w (not_le.1 hw)]; positivity
  | succ n ih =>
    apply step_Q κ x hdz hdk (n + 1)
    intro m z w hz hzw
    have ha := fS_mono κ x hdz hdk (n + 2) m (m + 1) z w (by omega) hz hzw
    have hq := ih (m + 1) w (le_trans hz hzw)
    calc fS κ x (n + 1 + 1) (m + 1) w ^ (n + 1 + 1)
        = fS κ x (n + 2) (m + 1) w * fS κ x (n + 2) (m + 1) w ^ (n + 1) := by
          rw [pow_succ', show n + 1 + 1 = n + 2 by omega]
      _ ≤ fS κ x (n + 2) m z * fS κ x (n + 1) (m + 1) w ^ (n + 2) := by
          gcongr
      _ = fS κ x (n + 1 + 1) m z * fS κ x (n + 1) (m + 1) w ^ (n + 1 + 1) := rfl

end Mono

section Link
open ShockWear.WearProcess

lemma psum_eq_fin {Ω : Type*} (X : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) :
    psum X j ω = ∑ i : Fin j, X i ω := by
  unfold psum; exact Finset.sum_range (fun i => X i ω)

lemma key_step {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (X : ℕ → Ω → ℝ) (κ : ℕ → Kernel ℝ ℝ) (hX : IsDamageSeq pr X κ) (j : ℕ)
    (h : ℝ → ℝ → ℝ≥0∞) (hh : Measurable (Function.uncurry h)) :
    ∫⁻ ω, h (psum X j ω) (X j ω) ∂pr =
      ∫⁻ ω, ∫⁻ u, h (psum X j ω) u ∂(κ j (psum X j ω)) ∂pr := by
  haveI := hX.markov
  set V : Ω → (Fin j → ℝ) := fun ω i => X i ω with hVdef
  have hV : Measurable V := measurable_pi_lambda _ (fun i => hX.meas i)
  set H : (Fin j → ℝ) × ℝ → ℝ≥0∞ := fun p => h (∑ i, p.1 i) p.2 with hHdef
  have hH : Measurable H := by
    have : Measurable (fun p : (Fin j → ℝ) × ℝ => ((∑ i, p.1 i), p.2)) := by fun_prop
    exact hh.comp this
  have e1 : ∀ ω, h (psum X j ω) (X j ω) = H (V ω, X j ω) := fun ω => by
    simp [hHdef, hVdef, psum_eq_fin]
  simp_rw [e1]
  rw [← lintegral_map hH (hV.prodMk (hX.meas j)),
    ← compProd_map_condDistrib (hX.meas j).aemeasurable, Measure.lintegral_compProd hH]
  have hG : Measurable (fun z : ℝ => ∫⁻ u, h z u ∂(κ j z)) := hh.lintegral_kernel_prod_right
  have hG' : Measurable (fun v : Fin j → ℝ => ∫⁻ u, h (∑ i, v i) u ∂(κ j (∑ i, v i))) :=
    hG.comp (by fun_prop)
  have e2 : ∫⁻ v, ∫⁻ u, H (v, u) ∂(condDistrib (X j) V pr v) ∂(pr.map V) =
      ∫⁻ v, ∫⁻ u, h (∑ i, v i) u ∂(κ j (∑ i, v i)) ∂(pr.map V) := by
    apply lintegral_congr_ae
    filter_upwards [hX.cond j] with v hv
    rw [hv]
  rw [e2, lintegral_map hG' hV]
  congr 1
  ext ω
  simp [hVdef, psum_eq_fin]

lemma link {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (X : ℕ → Ω → ℝ) (κ : ℕ → Kernel ℝ ℝ) (hX : IsDamageSeq pr X κ) (x : ℝ) :
    ∀ r j, ∫⁻ ω, fS κ x r j (psum X j ω) ∂pr = pr {ω | psum X (j + r) ω ≤ x} := by
  haveI := hX.markov
  have hps : ∀ j, Measurable (psum X j) := fun j => by
    unfold psum; exact Finset.measurable_sum _ (fun i _ => hX.meas i)
  intro r
  induction r with
  | zero =>
    intro j
    simp only [fS_zero, add_zero]
    have : ∀ ω, Set.indicator (Set.Iic x) (fun _ => (1 : ℝ≥0∞)) (psum X j ω) =
        Set.indicator {ω | psum X j ω ≤ x} (fun _ => (1 : ℝ≥0∞)) ω := fun ω => by
      simp [Set.indicator]
    simp_rw [this]
    rw [lintegral_indicator_const (measurableSet_le (hps j) measurable_const), one_mul]
  | succ r ih =>
    intro j
    simp only [fS_succ]
    have hh : Measurable (Function.uncurry fun (z u : ℝ) => fS κ x r (j + 1) (z + max u 0)) :=
      (fS_meas κ x r (j + 1)).comp (by fun_prop)
    rw [← key_step pr X κ hX j (fun z u => fS κ x r (j + 1) (z + max u 0)) hh]
    have e : (fun ω => fS κ x r (j + 1) (psum X j ω + max (X j ω) 0)) =ᵐ[pr]
        fun ω => fS κ x r (j + 1) (psum X (j + 1) ω) := by
      filter_upwards [hX.nonneg j] with ω hω
      rw [max_eq_left hω]
      unfold psum
      rw [Finset.sum_range_succ]
    rw [lintegral_congr_ae e, ih (j + 1), show j + 1 + r = j + (r + 1) by omega]

end Link

end SW41b

open ShockWear.WearProcess SW41b

theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (X : ℕ → Ω → ℝ) (κ : ℕ → Kernel ℝ ℝ) (hX : IsDamageSeq pr X κ) (x : ℝ) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    (pr {ω | psum X k ω ≤ x}).toReal ^ (1 / (k : ℝ)) ≤
      (pr {ω | psum X j ω ≤ x}).toReal ^ (1 / (j : ℝ)) := by
  haveI := hX.markov
  have hP : ∀ n, pr {ω | psum X n ω ≤ x} = fS κ x n 0 0 := by
    intro n
    have := link pr X κ hX x n 0
    rw [zero_add] at this
    rw [← this]
    have h0 : ∀ ω, psum X 0 ω = 0 := fun ω => by simp [psum]
    simp [h0]
  have hQ : ∀ n : ℕ, (pr {ω | psum X (n + 2) ω ≤ x}).toReal ^ (n + 1) ≤
      (pr {ω | psum X (n + 1) ω ≤ x}).toReal ^ (n + 2) := by
    intro n
    rw [hP, hP, ← ENNReal.toReal_pow, ← ENNReal.toReal_pow]
    apply ENNReal.toReal_mono
    · exact ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (fS_le_one κ x _ _ _))
    · exact fS_Q κ x hX.dec_z hX.dec_k n 0 0 le_rfl
  set a : ℕ → ℝ := fun n => (pr {ω | psum X n ω ≤ x}).toReal with ha
  have hnn : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hstep : ∀ m : ℕ, 1 ≤ m →
      a (m + 1) ^ (1 / ((m + 1 : ℕ) : ℝ)) ≤ a m ^ (1 / (m : ℝ)) := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hQn := hQ n
    set u := a (n + 2)
    set v := a (n + 1)
    have hu : 0 ≤ u := hnn _
    have hv : 0 ≤ v := hnn _
    have hr : (0 : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by positivity
    have h := Real.rpow_le_rpow (by positivity) hQn hr
    rw [← Real.rpow_natCast u, ← Real.rpow_natCast v, ← Real.rpow_mul hu,
      ← Real.rpow_mul hv] at h
    have e1 : ((n + 1 : ℕ) : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) =
        1 / ((n + 2 : ℕ) : ℝ) := by
      push_cast; field_simp
    have e2 : ((n + 2 : ℕ) : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) =
        1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [e1, e2] at h
    have e4 : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := rfl
    rw [e4]; exact h
  show a k ^ (1 / (k : ℝ)) ≤ a j ^ (1 / (j : ℝ))
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact le_trans (hstep k (le_trans hj hk)) ih
