-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.occupationLimitPoints_subset_invariantMeasures
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:22:48.873548+00:00
-- url     : https://prove2.me/submissions/725b0687-ea49-4559-9255-91761fd4642f

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral



namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

lemma mds_orth {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m0)
    (Y D : Ω → ℝ) (hY : StronglyMeasurable[G] Y) (cY : ℝ) (hYb : ∀ᵐ ω ∂P, |Y ω| ≤ cY)
    (hDi : Integrable D P) (hD0 : P[D | G] =ᵐ[P] 0) :
    ∫ ω, Y ω * D ω ∂P = 0 := by
  have h1 := condExp_stronglyMeasurable_mul_of_bound hG hY hDi cY
    (by simpa [Real.norm_eq_abs] using hYb)
  calc ∫ ω, Y ω * D ω ∂P = ∫ ω, (P[Y * D | G]) ω ∂P := (integral_condExp hG).symm
    _ = ∫ ω, (Y * P[D | G]) ω ∂P := integral_congr_ae h1
    _ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      · filter_upwards [hD0] with ω h
        simp [h]

lemma mds_alg4 (s d C : ℝ) (hd : |d| ≤ C) :
    (s + d) ^ 4 ≤ s ^ 4 + 4 * (s ^ 3 * d) + 8 * C ^ 2 * s ^ 2 + 3 * C ^ 4 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hd
  have hd2 : d ^ 2 ≤ C ^ 2 := by
    have := abs_le.1 hd; nlinarith
  have hd4 : d ^ 4 ≤ C ^ 4 := by
    have : (d ^ 2) ^ 2 ≤ (C ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg d) hd2 2
    nlinarith
  have h1 : s ^ 2 * d ^ 2 ≤ s ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg s)
  have h2 : 0 ≤ (s * d - d ^ 2) ^ 2 := sq_nonneg _
  nlinarith

lemma mds_alg2 (s d C : ℝ) (hd : |d| ≤ C) :
    (s + d) ^ 2 ≤ s ^ 2 + 2 * (s * d) + C ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hd
  have := abs_le.1 hd; nlinarith

theorem mds_slln {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ n, G n ≤ m0) (hmono : Monotone G) (D : ℕ → Ω → ℝ) (C : ℝ)
    (hDm : ∀ n, StronglyMeasurable[G (n+1)] (D n)) (hDb : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ C)
    (hD0 : ∀ n, P[D n | G n] =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (1 / (n:ℝ)) * ∑ i ∈ Finset.range n, D i ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, |D i ω| ≤ C := ae_all_iff.2 hDb
  have hC : 0 ≤ C := by
    obtain ⟨ω, hω⟩ := (hDb 0).exists
    exact (abs_nonneg _).trans hω
  set S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, D i ω with hSdef
  have hSm : ∀ n, StronglyMeasurable[G n] (S n) := by
    intro n
    exact Finset.stronglyMeasurable_fun_sum _ (fun i hi =>
      (hDm i).mono (hmono (by simp at hi; omega)))
  have hSb : ∀ n, ∀ᵐ ω ∂P, |S n ω| ≤ C * n := by
    intro n
    filter_upwards [hall] with ω hω
    calc |S n ω| ≤ ∑ i ∈ Finset.range n, |D i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, C := Finset.sum_le_sum (fun i _ => hω i)
      _ = C * n := by simp [mul_comm]
  have hSsucc : ∀ n ω, S (n+1) ω = S n ω + D n ω := fun n ω => Finset.sum_range_succ _ _
  have intg : ∀ (f : Ω → ℝ), StronglyMeasurable[m0] f → ∀ c : ℝ, (∀ᵐ ω ∂P, |f ω| ≤ c) →
      Integrable f P := fun f hf c hb =>
    Integrable.of_bound hf.aestronglyMeasurable c (by simpa [Real.norm_eq_abs] using hb)
  have hSm0 : ∀ n, StronglyMeasurable[m0] (S n) := fun n => (hSm n).mono (hG n)
  have hDm0 : ∀ n, StronglyMeasurable[m0] (D n) := fun n => (hDm n).mono (hG (n+1))
  have hDi : ∀ n, Integrable (D n) P := fun n => intg _ (hDm0 n) C (hDb n)
  -- second moment
  have m2 : ∀ n : ℕ, ∫ ω, S n ω ^ 2 ∂P ≤ C ^ 2 * n := by
    intro n
    induction n with
    | zero => simp [hSdef]
    | succ n ih =>
      have i1 : Integrable (fun ω => S n ω ^ 2) P :=
        intg _ ((hSm0 n).pow 2) ((C * n) ^ 2) (by
          filter_upwards [hSb n] with ω h
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)
      have i2 : Integrable (fun ω => 2 * (S n ω * D n ω)) P :=
        (intg _ ((hSm0 n).mul (hDm0 n)) (C * n * C) (by
          filter_upwards [hSb n, hall] with ω h1 h2
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_mul]; exact mul_le_mul h1 (h2 n) (abs_nonneg _) (by positivity))).const_mul 2
      have i12 : Integrable (fun ω => S n ω ^ 2 + 2 * (S n ω * D n ω)) P := i1.add i2
      have orth : ∫ ω, S n ω * D n ω ∂P = 0 :=
        mds_orth P (G n) (hG n) (S n) (D n) (hSm n) (C * n) (hSb n) (hDi n) (hD0 n)
      calc ∫ ω, S (n+1) ω ^ 2 ∂P ≤ ∫ ω, (S n ω ^ 2 + 2 * (S n ω * D n ω) + C ^ 2) ∂P := by
            apply integral_mono_ae
            · exact intg _ ((hSm0 (n+1)).pow 2) ((C * (n+1:ℕ)) ^ 2) (by
                filter_upwards [hSb (n+1)] with ω h
                try simp only [Pi.mul_apply, Pi.pow_apply]
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)
            · exact i12.add (integrable_const _)
            · filter_upwards [hall] with ω h
              rw [hSsucc]; exact mds_alg2 _ _ _ (h n)
        _ = ∫ ω, S n ω ^ 2 ∂P + 2 * ∫ ω, S n ω * D n ω ∂P + C ^ 2 := by
            rw [integral_add i12 (integrable_const _), integral_add i1 i2,
              integral_const_mul]
            simp
        _ ≤ C ^ 2 * (n + 1 : ℕ) := by
            rw [orth]; push_cast; nlinarith
  -- fourth moment
  have m4 : ∀ n : ℕ, ∫ ω, S n ω ^ 4 ∂P ≤ 11 * C ^ 4 * (n:ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp [hSdef]
    | succ n ih =>
      have i1 : Integrable (fun ω => S n ω ^ 4) P :=
        intg _ ((hSm0 n).pow 4) ((C * n) ^ 4) (by
          filter_upwards [hSb n] with ω h
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
      have i2 : Integrable (fun ω => 4 * (S n ω ^ 3 * D n ω)) P :=
        (intg _ (((hSm0 n).pow 3).mul (hDm0 n)) ((C * n) ^ 3 * C) (by
          filter_upwards [hSb n, hall] with ω h1 h2
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_mul, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 3) (h2 n) (abs_nonneg _)
            (by positivity))).const_mul 4
      have i3 : Integrable (fun ω => 8 * C ^ 2 * S n ω ^ 2) P :=
        (intg _ ((hSm0 n).pow 2) ((C * n) ^ 2) (by
          filter_upwards [hSb n] with ω h
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)).const_mul _
      have i12 : Integrable (fun ω => S n ω ^ 4 + 4 * (S n ω ^ 3 * D n ω)) P := i1.add i2
      have i123 : Integrable (fun ω => S n ω ^ 4 + 4 * (S n ω ^ 3 * D n ω) +
          8 * C ^ 2 * S n ω ^ 2) P := i12.add i3
      have orth : ∫ ω, S n ω ^ 3 * D n ω ∂P = 0 :=
        mds_orth P (G n) (hG n) (fun ω => S n ω ^ 3) (D n) ((hSm n).pow 3) ((C * n) ^ 3)
          (by
            filter_upwards [hSb n] with ω h
            try simp only [Pi.mul_apply, Pi.pow_apply]
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 3) (hDi n) (hD0 n)
      calc ∫ ω, S (n+1) ω ^ 4 ∂P ≤ ∫ ω, (S n ω ^ 4 + 4 * (S n ω ^ 3 * D n ω) +
            8 * C ^ 2 * S n ω ^ 2 + 3 * C ^ 4) ∂P := by
            apply integral_mono_ae
            · exact intg _ ((hSm0 (n+1)).pow 4) ((C * (n+1:ℕ)) ^ 4) (by
                filter_upwards [hSb (n+1)] with ω h
                try simp only [Pi.mul_apply, Pi.pow_apply]
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
            · exact i123.add (integrable_const _)
            · filter_upwards [hall] with ω h
              rw [hSsucc]; exact mds_alg4 _ _ _ (h n)
        _ = ∫ ω, S n ω ^ 4 ∂P + 4 * ∫ ω, S n ω ^ 3 * D n ω ∂P +
              8 * C ^ 2 * ∫ ω, S n ω ^ 2 ∂P + 3 * C ^ 4 := by
            rw [integral_add i123 (integrable_const _),
              integral_add i12 i3, integral_add i1 i2,
              integral_const_mul, integral_const_mul]
            simp
        _ ≤ 11 * C ^ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
            rw [orth]
            have h2 := m2 n
            have : 8 * C ^ 2 * ∫ ω, S n ω ^ 2 ∂P ≤ 8 * C ^ 2 * (C ^ 2 * n) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
            push_cast
            have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith [pow_nonneg hC 4]
  -- Markov + Borel-Cantelli
  have hK : ∀ (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |S (n+1) ω| < ε * ((n:ℝ)+1) := by
    intro ε hε
    set K : ℝ := 11 * C ^ 4 / ε ^ 4 with hKdef
    have hbound : ∀ n : ℕ, P {ω | ε * ((n:ℝ)+1) ≤ |S (n+1) ω|} ≤
        ENNReal.ofReal (K / ((n:ℝ)+1) ^ 2) := by
      intro n
      have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have hpos : 0 < (ε * ((n:ℝ)+1)) ^ 4 := by positivity
      have i4 : Integrable (fun ω => S (n+1) ω ^ 4) P :=
        intg _ ((hSm0 (n+1)).pow 4) ((C * (n+1:ℕ)) ^ 4) (by
          filter_upwards [hSb (n+1)] with ω h
          try simp only [Pi.mul_apply, Pi.pow_apply]
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
        (Eventually.of_forall (fun ω => by positivity : ∀ ω, (0:Ω→ℝ) ω ≤ S (n+1) ω ^ 4)) i4
        ((ε * ((n:ℝ)+1)) ^ 4)
      have hsub : {ω | ε * ((n:ℝ)+1) ≤ |S (n+1) ω|} ⊆
          {ω | (ε * ((n:ℝ)+1)) ^ 4 ≤ S (n+1) ω ^ 4} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        calc (ε * ((n:ℝ)+1)) ^ 4 ≤ |S (n+1) ω| ^ 4 := pow_le_pow_left₀ (by positivity) hω 4
          _ = S (n+1) ω ^ 4 := by
            rw [show |S (n+1) ω| ^ 4 = (|S (n+1) ω| ^ 2) ^ 2 by ring, sq_abs]; ring
      have hr : P.real {ω | (ε * ((n:ℝ)+1)) ^ 4 ≤ S (n+1) ω ^ 4} ≤ K / ((n:ℝ)+1) ^ 2 := by
        have h4 := m4 (n+1)
        push_cast at h4
        set r := P.real {ω | (ε * ((n:ℝ)+1)) ^ 4 ≤ S (n+1) ω ^ 4}
        have key : r * (ε * ((n:ℝ)+1)) ^ 4 ≤ 11 * C ^ 4 * ((n:ℝ)+1) ^ 2 := by
          rw [mul_comm]; linarith
        rw [hKdef, div_div, le_div_iff₀ (by positivity)]
        have hn2 : (0:ℝ) < ((n:ℝ)+1)^2 := by positivity
        have e : r * (ε ^ 4 * ((n:ℝ)+1) ^ 2) * ((n:ℝ)+1) ^ 2 = r * (ε * ((n:ℝ)+1)) ^ 4 := by
          ring
        exact le_of_mul_le_mul_right (by rw [e]; exact key) hn2
      calc P {ω | ε * ((n:ℝ)+1) ≤ |S (n+1) ω|}
          ≤ P {ω | (ε * ((n:ℝ)+1)) ^ 4 ≤ S (n+1) ω ^ 4} := measure_mono hsub
        _ = ENNReal.ofReal (P.real {ω | (ε * ((n:ℝ)+1)) ^ 4 ≤ S (n+1) ω ^ 4}) :=
          (ofReal_measureReal).symm
        _ ≤ ENNReal.ofReal (K / ((n:ℝ)+1) ^ 2) := ENNReal.ofReal_le_ofReal hr
    have hsum : Summable (fun n : ℕ => K / ((n:ℝ)+1) ^ 2) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      have h2 := this.mul_left K
      refine h2.congr (fun n => ?_)
      push_cast; ring
    have htsum : ∑' n : ℕ, P {ω | ε * ((n:ℝ)+1) ≤ |S (n+1) ω|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem (s := fun n : ℕ => {ω | ε * ((n:ℝ)+1) ≤ |S (n+1) ω|}) htsum] with ω hω
    filter_upwards [hω] with n hn
    simpa using hn
  have hall2 : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in atTop,
      |S (n+1) ω| < (1 / ((k:ℝ)+1)) * ((n:ℝ)+1) :=
    ae_all_iff.2 (fun k => hK _ (by positivity))
  filter_upwards [hall2] with ω hω
  rw [← tendsto_add_atTop_iff_nat 1, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := (hω k).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero, abs_mul]
  push_cast
  rw [abs_of_pos (by positivity : (0:ℝ) < 1 / ((n:ℝ)+1))]
  have e : |∑ i ∈ Finset.range (n+1), D i ω| = |S (n+1) ω| := rfl
  rw [e, one_div_mul_eq_div, div_lt_iff₀ hpos]
  calc |S (n+1) ω| < 1 / ((k:ℝ)+1) * ((n:ℝ)+1) := h
    _ ≤ ε * ((n:ℝ)+1) := mul_le_mul_of_nonneg_right hk.le hpos.le

lemma block_meas_aux {Ω M : Type*} [mΩ : MeasurableSpace Ω] [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] (X : ℝ≥0 → Ω → M) (t : ℝ≥0) (ht : 0 < t)
    (hY : Measurable[(inferInstance : MeasurableSpace (Set.Icc (0 : ℝ≥0) t)).prod mΩ]
      (fun p : Set.Icc (0 : ℝ≥0) t × Ω => X p.1 p.2))
    (f : M → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b) (hb : b ≤ t) :
    StronglyMeasurable (fun ω => ∫ s in a..b, f (X s.toNNReal ω)) := by
  have hp : Measurable (fun q : Ω × ℝ => ((Set.projIcc (0:ℝ≥0) t ht.le q.2.toNNReal), q.1)) :=
    (((continuous_projIcc (a := (0:ℝ≥0)) (b := t) (h := ht.le)).measurable.comp measurable_real_toNNReal).comp measurable_snd).prodMk
      measurable_fst
  have hh : StronglyMeasurable
      (fun q : Ω × ℝ => f (X (Set.projIcc (0:ℝ≥0) t ht.le q.2.toNNReal) q.1)) :=
    (hf.measurable.comp (hY.comp hp)).stronglyMeasurable
  have hI := hh.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))
  have e : (fun ω => ∫ s in a..b, f (X s.toNNReal ω)) = fun ω =>
      ∫ s, f (X (Set.projIcc (0:ℝ≥0) t ht.le s.toNNReal) ω) ∂(volume.restrict (Set.Ioc a b)) := by
    funext ω
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hmem : s.toNNReal ∈ Set.Icc (0:ℝ≥0) t :=
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hs.2.trans hb)⟩
    simp only [Set.projIcc_of_mem _ hmem]
  rw [e]; exact hI

lemma block_meas {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : Continuous f) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    StronglyMeasurable[ℱ (((n + 1 : ℕ) : ℝ≥0) * T)] (blockIntegral X f T (n + 1)) := by
  have ht : 0 < ((n + 1 : ℕ) : ℝ≥0) * T := by positivity
  have := @block_meas_aux Ω M (ℱ (((n + 1 : ℕ) : ℝ≥0) * T)) _ _ _ X _ ht (hX _ ht) f hf
    (((n + 1 - 1 : ℕ) : ℝ) * T) (((n + 1 : ℕ) : ℝ) * T)
    (by gcongr; omega) (by push_cast; rfl)
  exact this

lemma block_bound {Ω M : Type*} (X : ℝ≥0 → Ω → M) (f : M → ℝ)
    (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    |blockIntegral X f T (n + 1) ω| ≤ T := by
  unfold blockIntegral
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun s _ => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 (X s.toNNReal ω)).1,
      (hf01 (X s.toNNReal ω)).2]
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [show ((n:ℝ) + 1) * T - n * T = T by ring, abs_of_nonneg (NNReal.coe_nonneg T)]
    simp

lemma sum_Icc_shift (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g i = ∑ i ∈ Finset.range n, g (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem e47_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T i ω - (P[blockIntegral X f T i | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by
  set G : ℕ → MeasurableSpace Ω := fun k => ℱ ((k : ℝ≥0) * T) with hGdef
  have hG : ∀ k, G k ≤ m0 := fun k => ℱ.le _
  have hmono : Monotone G := fun a b hab => ℱ.mono (by gcongr)
  set U : ℕ → Ω → ℝ := fun k => blockIntegral X f T (k + 1) with hUdef
  have hUm : ∀ k, StronglyMeasurable[G (k+1)] (U k) := fun k => block_meas ℱ X hX f hf T hT k
  have hUb : ∀ k ω, |U k ω| ≤ T := fun k ω => block_bound X f hf01 T k ω
  have hUi : ∀ k, Integrable (U k) P := fun k =>
    Integrable.of_bound ((hUm k).mono (hG _)).aestronglyMeasurable T
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hUb k ω))
  set D : ℕ → Ω → ℝ := fun k => U k - P[U k | G k] with hDdef
  have hDm : ∀ k, StronglyMeasurable[G (k+1)] (D k) := fun k =>
    (hUm k).sub (stronglyMeasurable_condExp.mono (hmono (Nat.le_succ k)))
  have hDb : ∀ k, ∀ᵐ ω ∂P, |D k ω| ≤ 2 * T := by
    intro k
    filter_upwards [ae_bdd_condExp_of_ae_bdd (m := G k) (R := T)
      (ae_of_all _ (fun ω => hUb k ω))] with ω hω
    simp only [hDdef, Pi.sub_apply]
    have := hUb k ω
    rw [abs_le] at *
    constructor <;> linarith [this.1, this.2, hω.1, hω.2]
  have hD0 : ∀ k, P[D k | G k] =ᵐ[P] 0 := by
    intro k
    have hidem : P[P[U k | G k] | G k] = P[U k | G k] :=
      condExp_of_stronglyMeasurable (μ := P) (hG k) stronglyMeasurable_condExp integrable_condExp
    filter_upwards [condExp_sub (m := G k) (hUi k) (integrable_condExp (m := G k) (f := U k))]
      with ω h1
    show P[U k - P[U k | G k] | G k] ω = (0 : Ω → ℝ) ω
    rw [h1, Pi.sub_apply, hidem]; simp
  have hmain := mds_slln P G hG hmono D (2 * T) hDm hDb hD0
  filter_upwards [hmain] with ω hω
  refine hω.congr (fun n => ?_)
  rw [sum_Icc_shift]
  simp only [hDdef, hUdef, Nat.add_sub_cancel, Pi.sub_apply, hGdef]

theorem e50_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf' : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T (i + 1) ω -
          (P[blockIntegral X f T (i + 1) | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by
  have hf : Continuous f := hf'.continuous
  set G : ℕ → MeasurableSpace Ω := fun k => ℱ ((k : ℝ≥0) * T) with hGdef
  have hG : ∀ k, G k ≤ m0 := fun k => ℱ.le _
  have hmono : Monotone G := fun a b hab => ℱ.mono (by gcongr)
  set U : ℕ → Ω → ℝ := fun k => blockIntegral X f T (k + 1) with hUdef
  have hUm : ∀ k, StronglyMeasurable[G (k+1)] (U k) := fun k => block_meas ℱ X hX f hf T hT k
  have hUb : ∀ k ω, |U k ω| ≤ T := fun k ω => block_bound X f hf01 T k ω
  have hUi : ∀ k, Integrable (U k) P := fun k =>
    Integrable.of_bound ((hUm k).mono (hG _)).aestronglyMeasurable T
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hUb k ω))
  set D : ℕ → Ω → ℝ := fun k => U k - P[U k | G k] with hDdef
  have hDm : ∀ k, StronglyMeasurable[G (k+1)] (D k) := fun k =>
    (hUm k).sub (stronglyMeasurable_condExp.mono (hmono (Nat.le_succ k)))
  have hDb : ∀ k, ∀ᵐ ω ∂P, |D k ω| ≤ 2 * T := by
    intro k
    filter_upwards [ae_bdd_condExp_of_ae_bdd (m := G k) (R := T)
      (ae_of_all _ (fun ω => hUb k ω))] with ω hω
    simp only [hDdef, Pi.sub_apply]
    have := hUb k ω
    rw [abs_le] at *
    constructor <;> linarith [this.1, this.2, hω.1, hω.2]
  have hD0 : ∀ k, P[D k | G k] =ᵐ[P] 0 := by
    intro k
    have hidem : P[P[U k | G k] | G k] = P[U k | G k] :=
      condExp_of_stronglyMeasurable (μ := P) (hG k) stronglyMeasurable_condExp integrable_condExp
    filter_upwards [condExp_sub (m := G k) (hUi k) (integrable_condExp (m := G k) (f := U k))]
      with ω h1
    show P[U k - P[U k | G k] | G k] ω = (0 : Ω → ℝ) ω
    rw [h1, Pi.sub_apply, hidem]; simp
  set E : ℕ → Ω → ℝ := fun k => P[U (k+1) | G (k+1)] - P[U (k+1) | G k] with hEdef
  have hEm : ∀ k, StronglyMeasurable[G (k+1)] (E k) := fun k =>
    stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.mono (hmono (Nat.le_succ k)))
  have hEb : ∀ k, ∀ᵐ ω ∂P, |E k ω| ≤ 2 * T := by
    intro k
    filter_upwards [ae_bdd_condExp_of_ae_bdd (m := G k) (R := T)
      (ae_of_all _ (fun ω => hUb (k+1) ω)), ae_bdd_condExp_of_ae_bdd (m := G (k+1)) (R := T)
      (ae_of_all _ (fun ω => hUb (k+1) ω))] with ω hω hω'
    simp only [hEdef, Pi.sub_apply]
    rw [abs_le] at *
    constructor <;> linarith [hω.1, hω.2, hω'.1, hω'.2]
  have hE0 : ∀ k, P[E k | G k] =ᵐ[P] 0 := by
    intro k
    have hidem : P[P[U (k+1) | G k] | G k] = P[U (k+1) | G k] :=
      condExp_of_stronglyMeasurable (μ := P) (hG k) stronglyMeasurable_condExp integrable_condExp
    filter_upwards [condExp_sub (m := G k) (integrable_condExp (m := G (k+1)) (f := U (k+1)))
      (integrable_condExp (m := G k) (f := U (k+1))),
      condExp_condExp_of_le (μ := P) (f := U (k+1)) (hmono (Nat.le_succ k)) (hG (k+1))]
      with ω h1 h2
    show P[P[U (k+1) | G (k+1)] - P[U (k+1) | G k] | G k] ω = (0 : Ω → ℝ) ω
    rw [h1, Pi.sub_apply, hidem, h2]; simp
  have hmainE := mds_slln P G hG hmono E (2 * T) hEm hEb hE0
  have hmainD := mds_slln P (fun k => G (k+1)) (fun k => hG (k+1))
    (fun a b hab => hmono (by omega)) (fun k => D (k+1)) (2 * T) (fun k => hDm (k+1))
    (fun k => hDb (k+1)) (fun k => hD0 (k+1))
  filter_upwards [hmainE, hmainD] with ω hωE hωD
  have := hωD.add hωE
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  rw [sum_Icc_shift, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [hDdef, hEdef, hUdef, Nat.add_sub_cancel, Pi.sub_apply, hGdef]
  push_cast
  ring_nf



open scoped ENNReal

/-- essential supremum of a family, realized by a countable subfamily -/
lemma e51_exists_seq_ae_sup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    [Nonempty ι] (Y : ι → Ω → ℝ≥0∞) (hY : ∀ i, Measurable (Y i)) (hb : ∀ i ω, Y i ω ≤ 1) :
    ∃ σ : ℕ → ι, ∀ i, Y i ≤ᵐ[P] fun ω => ⨆ n, Y (σ n) ω := by
  classical
  let F : (ℕ → ι) → ℝ≥0∞ := fun σ => ∫⁻ ω, ⨆ n, Y (σ n) ω ∂P
  have hS : (Set.range F).Nonempty := Set.range_nonempty F
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hS (OrderTop.bddAbove _)
  choose τ hτ using huS
  let σ : ℕ → ι := fun n => τ (Nat.unpair n).1 (Nat.unpair n).2
  have hV : ∀ k ω, (⨆ n, Y (τ k n) ω) ≤ ⨆ n, Y (σ n) ω := fun k ω =>
    iSup_le fun n => le_iSup_of_le (Nat.pair k n) (by simp [σ, Nat.unpair_pair])
  have hFσ : sSup (Set.range F) ≤ F σ :=
    le_of_tendsto' hu (fun k => (hτ k) ▸ lintegral_mono (hV k))
  refine ⟨σ, fun i => ?_⟩
  let σ' : ℕ → ι := fun n => Nat.casesOn n i σ
  have hle : (fun ω => ⨆ n, Y (σ n) ω) ≤ᵐ[P] fun ω => ⨆ n, Y (σ' n) ω :=
    ae_of_all _ (fun ω => iSup_le fun n => le_iSup_of_le (n+1) le_rfl)
  have hF' : F σ' ≤ F σ := (le_sSup (Set.mem_range_self σ')).trans hFσ
  have hfin : ∫⁻ ω, ⨆ n, Y (σ n) ω ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂P) ?_ (lintegral_mono fun ω => iSup_le fun n => hb _ _)
    simp
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hfin
    (Measurable.iSup fun n => hY (σ' n)).aemeasurable hF'
  filter_upwards [heq] with ω hω
  rw [hω]; exact le_iSup_of_le 0 le_rfl

/-- joint measurability of a progressively measurable process -/
lemma e51_joint_meas {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (hX : IsProgressivelyMeasurable ℱ X) :
    Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2) := by
  let g : ℕ → ℝ≥0 × Ω → M := fun n p =>
    X (Set.projIcc (0:ℝ≥0) ((n:ℝ≥0) + 1) (by positivity) p.1) p.2
  have hg : ∀ n, Measurable (g n) := by
    intro n
    have h1 := hX ((n:ℝ≥0) + 1) (by positivity)
    have h2 : Measurable[_, (inferInstance : MeasurableSpace (Set.Icc (0 : ℝ≥0) ((n:ℝ≥0) + 1))).prod
        (ℱ ((n:ℝ≥0) + 1))] (fun p : ℝ≥0 × Ω =>
          ((Set.projIcc (0:ℝ≥0) ((n:ℝ≥0) + 1) (by positivity) p.1), p.2)) := by
      apply Measurable.prodMk
      · exact (continuous_projIcc).measurable.comp measurable_fst
      · exact (measurable_id.mono (ℱ.le _) le_rfl).comp measurable_snd
    exact h1.comp h2
  refine measurable_of_tendsto_metrizable hg ?_
  rw [tendsto_pi_nhds]
  intro p
  apply tendsto_nhds_of_eventually_eq
  obtain ⟨N, hN⟩ := exists_nat_ge p.1
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [g]
  rw [Set.projIcc_of_mem]
  exact ⟨zero_le, hN.trans (by exact_mod_cast (show (N:ℝ≥0) ≤ n + 1 by exact_mod_cast (by omega)))⟩

lemma e51_ii {h : ℝ → ℝ} (hm : Measurable h) (C : ℝ) (hb : ∀ s, |h s| ≤ C) (a b : ℝ) :
    IntervalIntegrable h volume a b :=
  ⟨Measure.integrableOn_of_bounded (s := Set.Ioc a b) (by simp) hm.aestronglyMeasurable
    (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact hb s)),
   Measure.integrableOn_of_bounded (s := Set.Ioc b a) (by simp) hm.aestronglyMeasurable
    (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact hb s))⟩

lemma e51_int_meas {Ω : Type*} [MeasurableSpace Ω] (H : ℝ × Ω → ℝ) (hH : Measurable H)
    (a b : ℝ) (hab : a ≤ b) :
    Measurable (fun ω => ∫ s in a..b, H (s, ω)) := by
  have h1 : StronglyMeasurable (fun q : Ω × ℝ => H (q.2, q.1)) :=
    (hH.comp measurable_swap).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))
  have e : (fun ω => ∫ s in a..b, H (s, ω)) =
      fun ω => ∫ s, H (s, ω) ∂(volume.restrict (Set.Ioc a b)) := by
    funext ω; rw [intervalIntegral.integral_of_le hab]
  rw [e]; exact h2.measurable

lemma e51_step {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hfε : ∀ a b, dist a b < δ → |f a - f b| ≤ ε)
    (v : Ω → ℝ) (hv : Measurable v) (hv1 : ∀ ω, |v ω| ≤ 1) (S : ℝ≥0)
    (hvS : ∀ s : ℝ≥0, S ≤ s →
      P[(deviationEvent Φ X s δ T).indicator (fun _ => (1:ℝ)) | ℱ s] ≤ᵐ[P] v)
    (a : ℝ≥0) (ha : S ≤ a) :
    ∀ᵐ ω ∂P, |(P[fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T,
        (f (X (s + T).toNNReal ω) - f (Φ T (X s.toNNReal ω))) | ℱ a]) ω|
      ≤ ε * T + T * (P[v | ℱ a]) ω := by
  have hm := ℱ.le a
  have hjm := e51_joint_meas ℱ X hX.progMeasurable
  have hX1 : Measurable (fun p : ℝ × Ω => X (p.1 + T).toNNReal p.2) :=
    hjm.comp ((measurable_real_toNNReal.comp (measurable_fst.add_const _)).prodMk measurable_snd)
  have hX0 : Measurable (fun p : ℝ × Ω => X p.1.toNNReal p.2) :=
    hjm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hΦm : Measurable (fun x => Φ T x) := (Φ.continuous continuous_const continuous_id).measurable
  set g : ℝ × Ω → ℝ := fun p => f (X (p.1 + T).toNNReal p.2) - f (Φ T (X p.1.toNNReal p.2))
    with hgdef
  have hgm : Measurable g := (hf.measurable.comp hX1).sub (hf.measurable.comp (hΦm.comp hX0))
  set C : Set (ℝ × Ω) := {p | ENNReal.ofReal δ ≤
    edist (X (p.1 + T).toNNReal p.2) (Φ T (X p.1.toNNReal p.2))} with hCdef
  have hCm : MeasurableSet C := measurableSet_le measurable_const (hX1.edist (hΦm.comp hX0))
  set k : ℝ × Ω → ℝ := C.indicator (fun _ => 1) with hkdef
  have hkm : Measurable k := measurable_const.indicator hCm
  have hk01 : ∀ p, 0 ≤ k p ∧ k p ≤ 1 := fun p => by
    simp only [hkdef, Set.indicator]; split_ifs <;> norm_num
  have hkb : ∀ p, |k p| ≤ 1 := fun p => by
    rw [abs_le]; constructor <;> linarith [hk01 p]
  have hgb : ∀ p, |g p| ≤ 1 := fun p => by
    have h1 := hf01 (X (p.1 + T).toNNReal p.2); have h2 := hf01 (Φ T (X p.1.toNNReal p.2))
    simp only [hgdef]; rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hgk : ∀ p, |g p| ≤ ε + k p := by
    intro p
    by_cases hp : p ∈ C
    · have : k p = 1 := by simp [hkdef, hp]
      rw [this]
      linarith [hgb p]
    · have : k p = 0 := by simp [hkdef, hp]
      rw [this, add_zero]
      apply hfε
      simp only [hCdef, Set.mem_setOf_eq, not_le] at hp
      exact (edist_lt_ofReal).1 hp
  set D : Ω → ℝ := fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T, g (s, ω) with hDdef
  set Z : Ω → ℝ := fun ω => ∫ s in (a:ℝ)..(a:ℝ) + T, k (s, ω) with hZdef
  have hab : (a:ℝ) ≤ a + T := le_add_of_nonneg_right T.2
  have hDm : Measurable D := e51_int_meas g hgm _ _ hab
  have hZm : Measurable Z := e51_int_meas k hkm _ _ hab
  have hTab : |((a:ℝ) + T) - a| = T := by rw [add_sub_cancel_left, NNReal.abs_eq]
  have hDb : ∀ ω, ‖D ω‖ ≤ T := fun ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a:ℝ)) (b := (a:ℝ) + T)
      (f := fun s => g (s, ω)) (C := 1) (fun s _ => by rw [Real.norm_eq_abs]; exact hgb _)
    rw [hTab, one_mul] at this; exact this
  have hZb : ∀ ω, ‖Z ω‖ ≤ T := fun ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a:ℝ)) (b := (a:ℝ) + T)
      (f := fun s => k (s, ω)) (C := 1) (fun s _ => by rw [Real.norm_eq_abs]; exact hkb _)
    rw [hTab, one_mul] at this; exact this
  have hDi : Integrable D P := Integrable.of_bound hDm.aestronglyMeasurable T (ae_of_all _ hDb)
  have hZi : Integrable Z P := Integrable.of_bound hZm.aestronglyMeasurable T (ae_of_all _ hZb)
  have hvi : Integrable v P := Integrable.of_bound hv.aestronglyMeasurable 1
    (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hv1 ω))
  have hkii : ∀ ω, IntervalIntegrable (fun s => k (s, ω)) volume (a:ℝ) (a + T) := fun ω =>
    e51_ii (hkm.comp (measurable_id.prodMk measurable_const)) 1 (fun s => hkb _) _ _
  have hDZ : ∀ ω, |D ω| ≤ ε * T + Z ω := by
    intro ω
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun s => g (s, ω)) (g := fun s => ε + k (s, ω)) hab
      (ae_of_all _ (fun s _ => by rw [Real.norm_eq_abs]; exact hgk (s, ω)))
      ((intervalIntegrable_const).add (hkii ω))
    rw [Real.norm_eq_abs, intervalIntegral.integral_add intervalIntegrable_const (hkii ω),
      intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] at h1
    simp only [hDdef, hZdef]
    linarith
  -- key set-integral inequality
  have key : ∀ B, MeasurableSet[ℱ a] B → ∫ ω in B, Z ω ∂P ≤ T * ∫ ω in B, v ω ∂P := by
    intro B hB
    have hBm : MeasurableSet B := hm _ hB
    have hint : Integrable (Function.uncurry fun ω s => k (s, ω))
        ((P.restrict B).prod (volume.restrict (Set.Ioc (a:ℝ) (a + T)))) :=
      Integrable.of_bound (hkm.comp measurable_swap).aestronglyMeasurable 1
        (ae_of_all _ (fun q => by rw [Real.norm_eq_abs]; exact hkb _))
    have e1 : ∫ ω in B, Z ω ∂P =
        ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P := by
      simp only [hZdef]
      simp_rw [intervalIntegral.integral_of_le hab]
      exact integral_integral_swap hint
    rw [e1]
    have hbd : ∀ s ∈ Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P ≤ ∫ ω in B, v ω ∂P := by
      intro s hs
      have hs0 : 0 ≤ s := (a.2).trans hs.1.le
      have has' : a ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).2 hs.1.le
      have hBs : MeasurableSet[ℱ s.toNNReal] B := ℱ.mono has' _ hB
      have hA := hX.measurableSet_deviation s.toNNReal δ T hδ hT
      have hind : Integrable ((deviationEvent Φ X s.toNNReal δ T).indicator
          (fun _ => (1:ℝ))) P := (integrable_const 1).indicator hA
      have hks : Integrable (fun ω => k (s, ω)) P :=
        Integrable.of_bound (hkm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hkb _))
      calc ∫ ω in B, k (s, ω) ∂P
          ≤ ∫ ω in B, (deviationEvent Φ X s.toNNReal δ T).indicator (fun _ => (1:ℝ)) ω ∂P := by
            apply setIntegral_mono hks.integrableOn hind.integrableOn
            intro ω
            by_cases hp : (s, ω) ∈ C
            · have hmem : ω ∈ deviationEvent Φ X s.toNNReal δ T := by
                simp only [deviationEvent, Set.mem_setOf_eq]
                refine le_trans ?_ (le_iSup₂_of_le T ⟨zero_le, le_rfl⟩ le_rfl)
                have e : (s + T).toNNReal = s.toNNReal + T := by
                  rw [Real.toNNReal_add hs0 T.coe_nonneg, Real.toNNReal_coe]
                simpa [hCdef, e] using hp
              simp [hkdef, hp, hmem]
            · simp only [hkdef, Set.indicator_of_notMem hp]
              exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
        _ = ∫ ω in B, (P[(deviationEvent Φ X s.toNNReal δ T).indicator (fun _ => (1:ℝ)) |
              ℱ s.toNNReal]) ω ∂P := (setIntegral_condExp (ℱ.le _) hind hBs).symm
        _ ≤ ∫ ω in B, v ω ∂P := setIntegral_mono_ae integrable_condExp.integrableOn
              hvi.integrableOn (hvS _ (ha.trans has'))
    have hsm : StronglyMeasurable (fun s : ℝ => ∫ ω in B, k (s, ω) ∂P) :=
      hkm.stronglyMeasurable.integral_prod_right' (ν := P.restrict B)
    have hsi : IntegrableOn (fun s : ℝ => ∫ ω in B, k (s, ω) ∂P) (Set.Ioc (a:ℝ) (a + T)) volume :=
      Measure.integrableOn_of_bounded (M := 1) (by simp) hsm.aestronglyMeasurable
        (ae_of_all _ (fun s => by
          rw [Real.norm_eq_abs]
          refine (abs_integral_le_integral_abs).trans ?_
          calc ∫ ω in B, |k (s, ω)| ∂P ≤ ∫ ω in B, (1:ℝ) ∂P :=
                setIntegral_mono (Integrable.of_bound
                  ((hkm.comp (measurable_const.prodMk measurable_id)).abs).aestronglyMeasurable 1
                  (ae_of_all _ (fun ω => by simp [hkb]))).integrableOn
                  (integrableOn_const (by simp)) (fun ω => hkb _)
            _ ≤ 1 := by
                rw [setIntegral_const, smul_eq_mul, mul_one]
                exact measureReal_le_one))
    calc ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, k (s, ω) ∂P
        ≤ ∫ s in Set.Ioc (a:ℝ) (a + T), ∫ ω in B, v ω ∂P :=
          setIntegral_mono_on hsi (integrableOn_const (by simp)) measurableSet_Ioc hbd
      _ = T * ∫ ω in B, v ω ∂P := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab, add_sub_cancel_left]
  have hZcond : P[Z | ℱ a] ≤ᵐ[P] fun ω => (T:ℝ) * (P[v | ℱ a]) ω := by
    have hint1 : Integrable (P[Z | ℱ a]) (P.trim hm) :=
      integrable_condExp.trim hm stronglyMeasurable_condExp
    have hsm2 : StronglyMeasurable[ℱ a] (fun ω => (T:ℝ) * (P[v | ℱ a]) ω) :=
      stronglyMeasurable_condExp.const_mul _
    have hint2 : Integrable (fun ω => (T:ℝ) * (P[v | ℱ a]) ω) (P.trim hm) :=
      (integrable_condExp.const_mul (T:ℝ)).trim hm hsm2
    refine ae_of_ae_trim hm (ae_le_of_forall_setIntegral_le hint1 hint2 (fun B hB _ => ?_))
    rw [← setIntegral_trim hm stronglyMeasurable_condExp hB, ← setIntegral_trim hm hsm2 hB,
      setIntegral_condExp hm hZi hB, integral_const_mul, setIntegral_condExp hm hvi hB]
    exact key B hB
  have hc : P[fun _ => ε * (T:ℝ) | ℱ a] = fun _ => ε * (T:ℝ) := condExp_const hm _
  have hup : P[D | ℱ a] ≤ᵐ[P] P[(fun _ => ε * (T:ℝ)) + Z | ℱ a] :=
    condExp_mono hDi ((integrable_const _).add hZi)
      (ae_of_all _ (fun ω => (le_abs_self _).trans (hDZ ω)))
  have hdn : P[-D | ℱ a] ≤ᵐ[P] P[(fun _ => ε * (T:ℝ)) + Z | ℱ a] :=
    condExp_mono hDi.neg ((integrable_const _).add hZi)
      (ae_of_all _ (fun ω => (neg_le_abs _).trans (hDZ ω)))
  have hadd := condExp_add (m := ℱ a) (μ := P) (integrable_const (ε * (T:ℝ))) hZi
  have hneg := condExp_neg (m := ℱ a) (μ := P) D
  filter_upwards [hup, hdn, hadd, hneg, hZcond] with ω h1 h2 h3 h4 h5
  rw [h3, hc] at h1 h2
  rw [h4] at h2
  simp only [Pi.add_apply, Pi.neg_apply] at h1 h2
  show |(P[D | ℱ a]) ω| ≤ _
  rw [abs_le]; constructor <;> linarith

theorem e51_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hfu : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun i : ℕ => (P[blockIntegral X f T (i + 1) - blockIntegral X (f ∘ Φ T) T i |
        ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω)
      atTop (𝓝 0) := by
  have hf : Continuous f := hfu.continuous
  have hTr : (0:ℝ) < T := hT
  have hδex : ∀ k : ℕ, ∃ δ > 0, ∀ a b, dist a b < δ → |f a - f b| ≤ 1 / ((k:ℝ) + 1) := by
    intro k
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hfu (1 / ((k:ℝ) + 1)) (by positivity)
    exact ⟨δ, hδ, fun a b hab => by have := h hab; rw [Real.dist_eq] at this; exact this.le⟩
  choose δ hδpos hδ using hδex
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun k s =>
    P[(deviationEvent Φ X s (δ k) T).indicator (fun _ => (1:ℝ)) | ℱ s] with hYdef
  set Y' : ℕ → ℝ≥0 → Ω → ℝ≥0∞ := fun k s ω => ENNReal.ofReal (min (Y k s ω) 1) with hY'def
  have hY'm : ∀ k s, Measurable (Y' k s) := fun k s =>
    ENNReal.measurable_ofReal.comp
      ((stronglyMeasurable_condExp.mono (ℱ.le s)).measurable.min measurable_const)
  have hY'1 : ∀ k s ω, Y' k s ω ≤ 1 := fun k s ω => ENNReal.ofReal_le_one.2 (min_le_right _ _)
  have hex : ∀ k m : ℕ, ∃ σ : ℕ → {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s},
      ∀ i : {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s}, Y' k i.1 ≤ᵐ[P] fun ω => ⨆ n, Y' k (σ n).1 ω := by
    intro k m
    have : Nonempty {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s} := ⟨⟨(m:ℝ≥0) * T, le_rfl⟩⟩
    exact e51_exists_seq_ae_sup (ι := {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s}) P
      (fun i : {s : ℝ≥0 // (m:ℝ≥0) * T ≤ s} => Y' k i.1)
      (fun i => hY'm k i.1) (fun i ω => hY'1 k i.1 ω)
  choose σ hσ using hex
  set v : ℕ → ℕ → Ω → ℝ := fun k m ω => (⨆ n, Y' k (σ k m n).1 ω).toReal with hvdef
  have hVle1 : ∀ k m ω, (⨆ n, Y' k (σ k m n).1 ω) ≤ 1 := fun k m ω =>
    iSup_le fun n => hY'1 _ _ _
  have hvm : ∀ k m, Measurable (v k m) := fun k m =>
    (Measurable.iSup fun n => hY'm k _).ennreal_toReal
  have hv01 : ∀ k m ω, 0 ≤ v k m ω ∧ v k m ω ≤ 1 := fun k m ω =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (hVle1 k m ω); simpa using this⟩
  have hv1 : ∀ k m ω, |v k m ω| ≤ 1 := fun k m ω => by
    rw [abs_le]; constructor <;> linarith [hv01 k m ω]
  have hvS : ∀ (k m : ℕ) (s : ℝ≥0), (m:ℝ≥0) * T ≤ s → Y k s ≤ᵐ[P] v k m := by
    intro k m s hs
    have hb : ∀ᵐ ω ∂P, |(deviationEvent Φ X s (δ k) T).indicator (fun _ => (1:ℝ)) ω|
        ≤ ((1:ℝ≥0):ℝ) :=
      ae_of_all _ (fun ω => by
        simp only [Set.indicator]; split_ifs <;> norm_num)
    filter_upwards [hσ k m ⟨s, hs⟩, ae_bdd_condExp_of_ae_bdd (m := ℱ s) hb] with ω h1 h2
    have h2' : Y k s ω ≤ 1 := by have := (abs_le.1 h2).2; simpa using this
    have e : min (Y k s ω) 1 = Y k s ω := min_eq_left h2'
    calc Y k s ω ≤ (Y' k s ω).toReal := by
          simp only [hY'def, e]; rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
      _ ≤ v k m ω := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (hVle1 k m ω)) h1
  let G : Filtration ℕ m0 := ⟨fun n => ℱ ((n:ℝ≥0) * T),
    fun a b hab => ℱ.mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) zero_le), fun n => ℱ.le _⟩
  have hstep : ∀ k m j : ℕ, m ≤ j → ∀ᵐ ω ∂P,
      |(P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω|
        ≤ 1 / ((k:ℝ) + 1) * T + T * (P[v k m | G j]) ω := by
    intro k m j hj
    have heq : blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) =
        fun ω => ∫ s in (((j:ℝ≥0) * T : ℝ≥0):ℝ)..(((j:ℝ≥0) * T : ℝ≥0):ℝ) + T,
          (f (X (s + T).toNNReal ω) - f (Φ T (X s.toNNReal ω))) := by
      funext ω
      have hpath : Measurable (fun s : ℝ => X s.toNNReal ω) :=
        (hX.progMeasurable.measurable_path ω).comp measurable_real_toNNReal
      have hΦm : Measurable (fun x => Φ T x) :=
        (Φ.continuous continuous_const continuous_id).measurable
      have hi1 : ∀ c d, IntervalIntegrable (fun s : ℝ => f (X (s + T).toNNReal ω)) volume c d :=
        fun c d => e51_ii (hf.measurable.comp (hpath.comp (measurable_add_const _))) 1
          (fun s => by
            have := hf01 (X (s + T).toNNReal ω)
            simp only [Function.comp_apply]
            rw [abs_le]; constructor <;> linarith [this.1, this.2]) c d
      have hi2 : ∀ c d, IntervalIntegrable (fun s : ℝ => f (Φ T (X s.toNNReal ω))) volume c d :=
        fun c d => e51_ii (hf.measurable.comp (hΦm.comp hpath)) 1
          (fun s => by
            have := hf01 (Φ T (X s.toNNReal ω))
            simp only [Function.comp_apply]
            rw [abs_le]; constructor <;> linarith [this.1, this.2]) c d
      rw [intervalIntegral.integral_sub (hi1 _ _) (hi2 _ _),
        intervalIntegral.integral_comp_add_right (fun s => f (X s.toNNReal ω)) (T:ℝ)]
      have h0 : ((j:ℕ):ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) := by push_cast; ring
      have h1 : ((j + 1 : ℕ) : ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) + T := by push_cast; ring
      have h2 : ((j + 1 + 1 : ℕ) : ℝ) * T = (((j:ℝ≥0) * T : ℝ≥0):ℝ) + T + T := by push_cast; ring
      simp only [Pi.sub_apply, blockIntegral, Function.comp_apply, Nat.add_sub_cancel]
      rw [h0, h1, h2]
    have h := e51_step P ℱ Φ X hX f hf hf01 T hT (δ k) (1 / ((k:ℝ) + 1)) (hδpos k)
      (by positivity) (hδ k) (v k m) (hvm k m) (hv1 k m) ((m:ℝ≥0) * T) (hvS k m) ((j:ℝ≥0) * T)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le)
    rw [heq, show (j + 1 - 1 : ℕ) = j by omega]
    exact h
  have hlevy : ∀ k m, ∀ᵐ ω ∂P, Tendsto (fun n => (P[v k m | G n]) ω) atTop
      (𝓝 ((P[v k m | ⨆ n, G n]) ω)) := fun k m => tendsto_ae_condExp _
  have hinf : ∀ k, ∀ᵐ ω ∂P, ∀ ε > 0, ∃ m, (P[v k m | ⨆ n, G n]) ω < ε := by
    intro k
    set L : ℕ → Ω → ℝ := fun m => P[v k m | ⨆ n, G n] with hLdef
    have hGle : (⨆ n, G n) ≤ m0 := iSup_le fun n => G.le n
    have hLm : ∀ m, Measurable (L m) := fun m =>
      (stronglyMeasurable_condExp.mono hGle).measurable
    have hL01 : ∀ m, ∀ᵐ ω ∂P, 0 ≤ L m ω ∧ L m ω ≤ 1 := by
      intro m
      filter_upwards [condExp_nonneg (m := ⨆ n, G n) (μ := P) (f := v k m)
        (ae_of_all _ (fun ω => (hv01 k m ω).1)),
        ae_bdd_condExp_of_ae_bdd (m := ⨆ n, G n) (μ := P) (R := 1)
          (ae_of_all _ (fun ω => by simpa using hv1 k m ω))] with ω h1 h2
      exact ⟨h1, by have := (abs_le.1 h2).2; simpa using this⟩
    have hL01' := ae_all_iff.2 hL01
    set ℓ : Ω → ℝ := fun ω => ⨅ m, L m ω with hℓdef
    have hℓm : Measurable ℓ := Measurable.iInf hLm
    have hℓ01 : ∀ᵐ ω ∂P, 0 ≤ ℓ ω ∧ ℓ ω ≤ 1 ∧ ∀ m, ℓ ω ≤ L m ω := by
      filter_upwards [hL01'] with ω h
      have hbdd : BddBelow (Set.range fun m => L m ω) := ⟨0, by rintro _ ⟨m, rfl⟩; exact (h m).1⟩
      exact ⟨le_ciInf fun m => (h m).1, (ciInf_le hbdd 0).trans (h 0).2,
        fun m => ciInf_le hbdd m⟩
    have hℓi : Integrable ℓ P := Integrable.of_bound hℓm.aestronglyMeasurable 1 (by
      filter_upwards [hℓ01] with ω h
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2.1])
    have hgood := hX.tendsto_condProb (δ k) T (hδpos k) hT
    have hvto : ∀ᵐ ω ∂P, Tendsto (fun m => v k m ω) atTop (𝓝 0) := by
      filter_upwards [hgood] with ω hω
      rw [Metric.tendsto_atTop] at hω ⊢
      intro ε hε
      obtain ⟨t0, ht0⟩ := hω (ε / 2) (by positivity)
      obtain ⟨m1, hm1⟩ := exists_nat_ge (t0 / T)
      refine ⟨m1, fun m hm => ?_⟩
      have hle : ∀ s : ℝ≥0, (m:ℝ≥0) * T ≤ s → Y' k s ω ≤ ENNReal.ofReal (ε / 2) := by
        intro s hs
        have hts : t0 ≤ s := by
          have e1 : t0 ≤ (m1:ℝ≥0) * T := (div_le_iff₀ hT).1 hm1
          have e2 : (m1:ℝ≥0) * T ≤ (m:ℝ≥0) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) zero_le
          exact e1.trans (e2.trans hs)
        have := ht0 s hts
        rw [Real.dist_eq, sub_zero] at this
        exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans ((le_abs_self _).trans this.le))
      have hV : (⨆ n, Y' k (σ k m n).1 ω) ≤ ENNReal.ofReal (ε / 2) :=
        iSup_le fun n => hle _ (σ k m n).2
      have hvle : v k m ω ≤ ε / 2 := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hv01 k m ω).1]; linarith
    have hint_to : Tendsto (fun m => ∫ ω, v k m ω ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
        (fun m => (hvm k m).aestronglyMeasurable) (integrable_const 1)
        (fun m => ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hv1 k m ω)) hvto
      simpa using this
    have hℓint : ∫ ω, ℓ ω ∂P ≤ 0 := by
      refine ge_of_tendsto' hint_to (fun m => ?_)
      calc ∫ ω, ℓ ω ∂P ≤ ∫ ω, L m ω ∂P := integral_mono_ae hℓi integrable_condExp
            (by filter_upwards [hℓ01] with ω h; exact h.2.2 m)
        _ = ∫ ω, v k m ω ∂P := integral_condExp hGle
    have hnn : 0 ≤ᵐ[P] ℓ := by filter_upwards [hℓ01] with ω h; exact h.1
    have hℓ0 : ℓ =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hℓi).1
        (le_antisymm hℓint (integral_nonneg_of_ae hnn))
    filter_upwards [hℓ0, hL01'] with ω h0 h
    intro ε hε
    have : ℓ ω < ε := by rw [h0]; exact hε
    exact exists_lt_of_ciInf_lt this
  have hS : ∀ᵐ ω ∂P, ∀ k m j : ℕ, m ≤ j →
      |(P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω|
        ≤ 1 / ((k:ℝ) + 1) * T + T * (P[v k m | G j]) ω := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun m => ae_all_iff.2 fun j => ?_
    by_cases h : m ≤ j
    · filter_upwards [hstep k m j h] with ω hω _; exact hω
    · exact ae_of_all _ (fun ω h' => absurd h' h)
  filter_upwards [hS, ae_all_iff.2 fun k => ae_all_iff.2 fun m => hlevy k m,
    ae_all_iff.2 hinf] with ω hS hL hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / (3 * T) by positivity)
  obtain ⟨m, hm⟩ := hI k (ε / (3 * T)) (by positivity)
  have hev := (hL k m).eventually (gt_mem_nhds (show (P[v k m | ⨆ n, G n]) ω < 2 * (ε / (3 * T))
    by linarith [show 0 < ε / (3 * T) by positivity]))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max (m + 1) (N + 1), fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 := hS k m j (by omega)
  have h2 := hN j (by omega)
  rw [Real.dist_eq, sub_zero]
  have a1 : 1 / ((k:ℝ) + 1) * T < ε / 3 := by
    calc 1 / ((k:ℝ) + 1) * T < ε / (3 * T) * T := mul_lt_mul_of_pos_right hk hTr
      _ = ε / 3 := by field_simp
  have a2 : (T:ℝ) * (P[v k m | G j]) ω < 2 * ε / 3 := by
    calc (T:ℝ) * (P[v k m | G j]) ω < T * (2 * (ε / (3 * T))) := mul_lt_mul_of_pos_left h2 hTr
      _ = 2 * ε / 3 := by field_simp
  linarith


theorem e52_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hfu : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X f T (i + 1) ω -
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X (f ∘ Φ T) T i ω)
      atTop (𝓝 0) := by
  have hf : Continuous f := hfu.continuous
  have hg : Continuous (f ∘ Φ T) := hf.comp (Φ.continuous continuous_const continuous_id)
  have hg01 : ∀ y, (f ∘ Φ T) y ∈ Set.Icc (0:ℝ) 1 := fun y => hf01 _
  have h50 := e50_core P ℱ X hX.progMeasurable f hfu hf01 T hT
  have h47 := e47_core P ℱ X hX.progMeasurable (f ∘ Φ T) hg hg01 T hT
  have h51 := e51_core P ℱ Φ X hX f hfu hf01 T hT
  have hint : ∀ (g : M → ℝ), Continuous g → (∀ y, g y ∈ Set.Icc (0:ℝ) 1) → ∀ n,
      Integrable (blockIntegral X g T (n + 1)) P := fun g hg hg01 n =>
    Integrable.of_bound ((block_meas ℱ X hX.progMeasurable g hg T hT n).mono
      (ℱ.le _)).aestronglyMeasurable T
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact block_bound X g hg01 T n ω))
  have hsub : ∀ᵐ ω ∂P, ∀ j : ℕ,
      (P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω =
      (P[blockIntegral X f T (j + 1 + 1) | ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω -
      (P[blockIntegral X (f ∘ Φ T) T (j + 1) | ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω :=
    ae_all_iff.2 fun j => condExp_sub (hint f hf hf01 (j + 1)) (hint _ hg hg01 j) _
  filter_upwards [h50, h47, h51, hsub] with ω h50 h47 h51 hsub
  have hc : Tendsto (fun j : ℕ =>
      (P[blockIntegral X f T (j + 1 + 1) - blockIntegral X (f ∘ Φ T) T (j + 1) |
        ℱ (((j + 1 - 1 : ℕ) : ℝ≥0) * T)]) ω) atTop (𝓝 0) :=
    h51.comp (tendsto_add_atTop_nat 1)
  have hces := hc.cesaro
  have hall := (h50.sub h47).add hces
  rw [sub_zero, add_zero] at hall
  refine hall.congr (fun n => ?_)
  simp only [sum_Icc_shift, hsub, Finset.sum_sub_distrib, one_div]
  ring



lemma occ_integral_eq {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (f : M → ℝ) (hf : Continuous f) (t : ℝ≥0) (ht : 0 < t) :
    ∫ y, f y ∂(occupationMeasure x t : Measure M) =
      (1 / (t:ℝ)) * ∫ s in (0:ℝ)..t, f (x s.toNNReal) := by
  rw [coe_occupationMeasure hx ht]
  rw [integral_map (φ := fun s : ℝ => x s.toNNReal) (hx.comp measurable_real_toNNReal).aemeasurable
    hf.aestronglyMeasurable]
  rw [ProbabilityTheory.cond, integral_smul_measure, intervalIntegral.integral_of_le (by positivity),
    integral_Icc_eq_integral_Ioc]
  simp [Real.volume_Icc]

lemma e53_alg (C T τ t Aτ At : ℝ) (hC : 0 ≤ C) (hτ : 0 < τ) (hτt : τ ≤ t) (htT : t - τ ≤ T)
    (hd : |Aτ - At| ≤ C * (t - τ)) (hAt : |At| ≤ C * t) :
    |(1 / τ) * Aτ - (1 / t) * At| ≤ 2 * C * T / τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have key : (1 / τ) * Aτ - (1 / t) * At = (Aτ - At) / τ + At * (t - τ) / (τ * t) := by
    field_simp; ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_mul, abs_of_pos hτ, abs_of_pos (mul_pos hτ ht),
    abs_of_nonneg (sub_nonneg.2 hτt)]
  have e1 : |Aτ - At| / τ ≤ C * T / τ := by
    apply div_le_div_of_nonneg_right _ hτ.le
    nlinarith
  have e2 : |At| * (t - τ) / (τ * t) ≤ C * T / τ := by
    rw [div_le_div_iff₀ (mul_pos hτ ht) hτ]
    have h1 : |At| * (t - τ) ≤ C * t * T :=
      mul_le_mul hAt htT (sub_nonneg.2 hτt) (by positivity)
    nlinarith
  linarith [e1, e2, show C * T / τ + C * T / τ = 2 * C * T / τ by ring]

theorem e53_core {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure x (t j)) atTop (𝓝 μ))
    (f : M → ℝ) (hf : Continuous f) (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Tendsto
      (fun j : ℕ => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) *
        ∑ i ∈ Finset.range ⌊t j / T⌋₊, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, f (x s.toNNReal))
      atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (x 0))
  have hgm : Measurable (fun s : ℝ => f (x s.toNNReal)) :=
    hf.measurable.comp (hx.comp measurable_real_toNNReal)
  have hgb : ∀ s : ℝ, ‖f (x s.toNNReal)‖ ≤ C := fun s => by
    rw [Real.norm_eq_abs]; exact hC _
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => f (x s.toNNReal)) volume a b :=
    fun a b => ⟨Measure.integrableOn_of_bounded (s := Set.Ioc a b) (by simp)
      hgm.aestronglyMeasurable (ae_of_all _ hgb), Measure.integrableOn_of_bounded
      (s := Set.Ioc b a) (by simp) hgm.aestronglyMeasurable (ae_of_all _ hgb)⟩
  set A : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, f (x s.toNNReal) with hAdef
  have hA : ∀ a b : ℝ, |A b - A a| ≤ C * |b - a| := by
    intro a b
    simp only [hAdef]
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _), ← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hgb s)
  -- weak convergence
  let F : BoundedContinuousFunction M ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) (fun a b => by
      rw [Real.dist_eq]
      have := abs_sub (f a) (f b)
      simp only [ContinuousMap.coe_mk]
      linarith [hC a, hC b])
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ) F
  have h1' : Tendsto (fun j => (1 / (t j : ℝ)) * A (t j)) atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by
    refine h1.congr' ?_
    filter_upwards [ht.eventually_gt_atTop 0] with j hj
    exact occ_integral_eq x hx f hf (t j) hj
  -- the block sums
  have hT' : (0:ℝ) < T := hT
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T,
      f (x s.toNNReal) = A (n * T) := by
    intro n
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * T)
      (f := fun s : ℝ => f (x s.toNNReal)) (μ := volume) (n := n) (fun k _ => hii _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    rw [this]
  have htR : Tendsto (fun j => (t j : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 ht
  have hfl : ∀ j, (⌊t j / T⌋₊ : ℝ) * T ≤ t j ∧ (t j : ℝ) - T < (⌊t j / T⌋₊ : ℝ) * T := by
    intro j
    have a1 : (⌊t j / T⌋₊ : ℝ≥0) ≤ t j / T := Nat.floor_le zero_le
    have a2 : t j / T < (⌊t j / T⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hT] at a1
    rw [div_lt_iff₀ hT] at a2
    constructor
    · exact_mod_cast (NNReal.coe_le_coe.2 a1)
    · have := NNReal.coe_lt_coe.2 a2
      push_cast at this
      linarith
  have hτ : Tendsto (fun j => (⌊t j / T⌋₊ : ℝ) * T) atTop atTop := by
    have : Tendsto (fun j => (t j : ℝ) - T) atTop atTop := tendsto_atTop_add_const_right _ _ htR
    exact tendsto_atTop_mono (fun j => (hfl j).2.le) this
  have hdiff : Tendsto (fun j => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) * A ((⌊t j / T⌋₊ : ℝ) * T)
      - (1 / (t j : ℝ)) * A (t j)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 2 * C * (T:ℝ))).div_atTop hτ)
    filter_upwards [hτ.eventually_gt_atTop 0] with j hj
    rw [Real.norm_eq_abs]
    refine e53_alg C T _ _ _ _ hC0 hj (hfl j).1 (by linarith [(hfl j).2]) ?_ ?_
    · have := hA (t j) ((⌊t j / T⌋₊ : ℝ) * T)
      rwa [abs_sub_comm (((⌊t j / T⌋₊ : ℝ)) * T) _, abs_of_nonneg (sub_nonneg.2 (hfl j).1)] at this
    · have := hA 0 (t j)
      simpa [hAdef, abs_of_nonneg (NNReal.coe_nonneg (t j))] using this
  have := hdiff.add h1'
  simp only [sub_add_cancel, zero_add] at this
  refine this.congr' (Eventually.of_forall fun j => ?_)
  simp only [hsum]


noncomputable def gapx {M : Type*} [MetricSpace M] (W : Set M) (k : ℕ) (x : M) : ℝ :=
  min 1 ((k:ℝ) * Metric.infDist x Wᶜ)

lemma gapx_mem {M : Type*} [MetricSpace M] (W : Set M) (k : ℕ) (x : M) :
    gapx W k x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg k) Metric.infDist_nonneg), min_le_left _ _⟩

lemma gapx_uc {M : Type*} [MetricSpace M] (W : Set M) (k : ℕ) : UniformContinuous (gapx W k) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε / ((k:ℝ) + 1), by positivity, fun {a b} hab => ?_⟩
  rw [Real.dist_eq]
  unfold gapx
  refine lt_of_le_of_lt (abs_min_sub_min_le_max _ _ _ _) ?_
  rw [sub_self, abs_zero]
  refine max_lt hε ?_
  have h1 := Metric.infDist_le_infDist_add_dist (x := a) (y := b) (s := Wᶜ)
  have h2 := Metric.infDist_le_infDist_add_dist (x := b) (y := a) (s := Wᶜ)
  rw [dist_comm] at h2
  have h3 : |Metric.infDist a Wᶜ - Metric.infDist b Wᶜ| ≤ dist a b := by
    rw [abs_le]; constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  calc (k:ℝ) * |Metric.infDist a Wᶜ - Metric.infDist b Wᶜ| ≤ k * dist a b :=
        mul_le_mul_of_nonneg_left h3 hk
    _ ≤ k * (ε / ((k:ℝ) + 1)) := mul_le_mul_of_nonneg_left hab.le hk
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

lemma gapx_measure_eq {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (W : Set M)
    (hW : IsOpen W) (h : ∀ k, ∫ x, gapx W k x ∂μ = ∫ x, gapx W k x ∂ν) : μ W = ν W := by
  rcases (Wᶜ).eq_empty_or_nonempty with hc | hne
  · have : W = Set.univ := by simpa using hc
    rw [this, measure_univ, measure_univ]
  have hlim : ∀ x, Tendsto (fun k => gapx W k x) atTop (𝓝 (W.indicator 1 x)) := by
    intro x
    by_cases hx : x ∈ W
    · have hd : 0 < Metric.infDist x Wᶜ :=
        (hW.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hx)
      rw [Set.indicator_of_mem hx]
      apply tendsto_nhds_of_eventually_eq
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / Metric.infDist x Wᶜ)
      filter_upwards [eventually_ge_atTop K] with k hk
      unfold gapx
      apply min_eq_left
      have : (K:ℝ) ≤ k := by exact_mod_cast hk
      rw [div_le_iff₀ hd] at hK
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have h0 : Metric.infDist x Wᶜ = 0 := Metric.infDist_zero_of_mem (by simpa using hx)
      have h00 : ∀ k : ℕ, gapx W k x = 0 := fun k => by
        unfold gapx; rw [h0, mul_zero, min_eq_right zero_le_one]
      simp only [h00]; exact tendsto_const_nhds
  have hm : ∀ k, Measurable (gapx W k) := fun k => (gapx_uc W k).continuous.measurable
  have hb : ∀ k x, ‖gapx W k x‖ ≤ 1 := fun k x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(gapx_mem W k x).1, (gapx_mem W k x).2]
  have tμ := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1:ℝ))
    (fun k => (hm k).aestronglyMeasurable) (integrable_const 1)
    (fun k => ae_of_all _ (hb k)) (ae_of_all _ hlim)
  have tν := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (1:ℝ))
    (fun k => (hm k).aestronglyMeasurable) (integrable_const 1)
    (fun k => ae_of_all _ (hb k)) (ae_of_all _ hlim)
  simp_rw [h] at tμ
  have := tendsto_nhds_unique tμ tν
  rw [integral_indicator_one hW.measurableSet, integral_indicator_one hW.measurableSet] at this
  rw [measureReal_def, measureReal_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

lemma exists_enum_basis (M : Type*) [MetricSpace M] [TopologicalSpace.SeparableSpace M] :
    ∃ e : ℕ → Set M, (∀ n, IsOpen (e n)) ∧ ∀ V, IsOpen V → V = ⋃ n, ⋃ (_ : e n ⊆ V), e n := by
  have hb := TopologicalSpace.isBasis_countableBasis M
  have hc := TopologicalSpace.countable_countableBasis M
  rcases (TopologicalSpace.countableBasis M).eq_empty_or_nonempty with h0 | hne
  · refine ⟨fun _ => ∅, fun _ => isOpen_empty, fun V hV => ?_⟩
    have := hb.open_eq_sUnion' hV
    rw [h0] at this
    have hV0 : V = ∅ := by simpa using this
    rw [hV0]; simp
  · obtain ⟨e, he⟩ := hc.exists_eq_range hne
    refine ⟨e, fun n => hb.isOpen (by rw [he]; exact Set.mem_range_self n), fun V hV => ?_⟩
    conv_lhs => rw [hb.open_eq_sUnion' hV]
    ext x
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion, he]
    constructor
    · rintro ⟨s, ⟨⟨n, rfl⟩, hs⟩, hx⟩; exact ⟨n, hs, hx⟩
    · rintro ⟨n, hs, hx⟩; exact ⟨e n, ⟨⟨n, rfl⟩, hs⟩, hx⟩

lemma ext_of_gapx {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (e : ℕ → Set M) (heo : ∀ n, IsOpen (e n))
    (hec : ∀ V, IsOpen V → V = ⋃ n, ⋃ (_ : e n ⊆ V), e n)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (S : Finset ℕ) (k : ℕ),
      ∫ x, gapx (⋃ n ∈ S, e n) k x ∂μ = ∫ x, gapx (⋃ n ∈ S, e n) k x ∂ν) : μ = ν := by
  classical
  have hW : ∀ S : Finset ℕ, μ (⋃ n ∈ S, e n) = ν (⋃ n ∈ S, e n) := fun S =>
    gapx_measure_eq μ ν _ (isOpen_biUnion fun n _ => heo n) (h S)
  have hV : ∀ V : Set M, IsOpen V → μ V = ν V := by
    intro V hV
    let S : ℕ → Finset ℕ := fun N => (Finset.range N).filter (fun n => e n ⊆ V)
    have hmono : Monotone (fun N => ⋃ n ∈ S N, e n) := by
      intro a b hab x hx
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨n, hn, hxn⟩ := hx
      refine ⟨n, ?_, hxn⟩
      simp only [S, Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨lt_of_lt_of_le hn.1 hab, hn.2⟩
    have hU : (⋃ N, ⋃ n ∈ S N, e n) = V := by
      conv_rhs => rw [hec V hV]
      ext x
      simp only [S, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨N, n, ⟨_, hn⟩, hx⟩; exact ⟨n, hn, hx⟩
      · rintro ⟨n, hn, hx⟩; exact ⟨n + 1, n, ⟨Nat.lt_succ_self n, hn⟩, hx⟩
    rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
    simp only [hW]
  exact ext_of_generate_finite {s | IsOpen s} (BorelSpace.measurable_eq (α := M))
    isPiSystem_isOpen hV (by simp)

lemma goal_key {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (Ω : Type*) (X : ℝ≥0 → Ω → M) (ω : Ω) (hx : Measurable (fun s => X s ω))
    (g : M → ℝ) (hgc : Continuous g) (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1)
    (Φ : Flow ℝ≥0 M) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure (fun s => X s ω) (t j)) atTop (𝓝 μ))
    (h52 : Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X g T (i + 1) ω -
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X (g ∘ Φ T) T i ω)
      atTop (𝓝 0)) :
    ∫ y, g (Φ T y) ∂(μ : Measure M) = ∫ y, g y ∂(μ : Measure M) := by
  have hgΦ : Continuous (g ∘ Φ T) := hgc.comp (Φ.continuous continuous_const continuous_id)
  have hb : ∀ y, |g y| ≤ 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [(hg01 y).1, (hg01 y).2]
  have h53f := e53_core (fun s => X s ω) hx T hT t ht μ hμ g hgc ⟨1, hb⟩
  have h53g := e53_core (fun s => X s ω) hx T hT t ht μ hμ (g ∘ Φ T) hgΦ ⟨1, fun y => hb _⟩
  set a : ℕ → ℝ := fun i => ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, g (X s.toNNReal ω) with hadef
  set b : ℕ → ℝ := fun i => ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, (g ∘ Φ T) (X s.toNNReal ω)
    with hbdef
  have hblk : ∀ (h : M → ℝ) (i : ℕ), blockIntegral X h T (i + 1) ω =
      ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, h (X s.toNNReal ω) := by
    intro h i
    simp only [blockIntegral, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have ha : ∀ i, |a i| ≤ T := fun i => by
    have := block_bound X g hg01 T i ω
    rwa [hblk] at this
  have hA : ∀ n : ℕ, (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X g T (i + 1) ω -
      (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X (g ∘ Φ T) T i ω =
      (1 / (n:ℝ)) * (∑ i ∈ Finset.range n, a i + a n - a 0) -
      (1 / (n:ℝ)) * ∑ i ∈ Finset.range n, b i := by
    intro n
    have hs1 : ∑ i ∈ Finset.Icc 1 n, blockIntegral X g T (i + 1) ω =
        ∑ i ∈ Finset.range n, a (i + 1) := by
      rw [sum_Icc_shift]; exact Finset.sum_congr rfl (fun i _ => hblk g (i + 1))
    have hs2 : ∑ i ∈ Finset.Icc 1 n, blockIntegral X (g ∘ Φ T) T i ω =
        ∑ i ∈ Finset.range n, b i := by
      rw [sum_Icc_shift]; exact Finset.sum_congr rfl (fun i _ => hblk _ i)
    have hs3 : ∑ i ∈ Finset.range n, a (i + 1) = ∑ i ∈ Finset.range n, a i + a n - a 0 := by
      have := Finset.sum_range_succ' a n
      rw [Finset.sum_range_succ] at this
      linarith
    rw [hs1, hs2, hs3]
  have hnj : Tendsto (fun j => ⌊t j / T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (ht.atTop_div_const hT)
  have hR : Tendsto (fun n : ℕ => (a n - a 0) * (1 / (n:ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 * (T:ℝ)) * (1 / (n:ℝ))) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (2 * (T:ℝ))
      rw [mul_zero] at this; exact this
    refine squeeze_zero_norm (fun n => ?_) h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc |a n - a 0| ≤ |a n| + |a 0| := abs_sub _ _
      _ ≤ T + T := add_le_add (ha n) (ha 0)
      _ = 2 * T := by ring
  have hE : Tendsto (fun j : ℕ => (1 / (T:ℝ)) *
      ((1 / (⌊t j / T⌋₊ : ℝ)) * ∑ i ∈ Finset.Icc 1 ⌊t j / T⌋₊, blockIntegral X g T (i + 1) ω -
        (1 / (⌊t j / T⌋₊ : ℝ)) * ∑ i ∈ Finset.Icc 1 ⌊t j / T⌋₊, blockIntegral X (g ∘ Φ T) T i ω -
        (a ⌊t j / T⌋₊ - a 0) * (1 / (⌊t j / T⌋₊ : ℝ)))) atTop (𝓝 0) := by
    have := ((h52.comp hnj).sub (hR.comp hnj)).const_mul (1 / (T:ℝ))
    rw [sub_zero, mul_zero] at this; exact this
  have hdiff := h53f.sub h53g
  have heq : ∫ y, g y ∂(μ : Measure M) - ∫ y, (g ∘ Φ T) y ∂(μ : Measure M) = 0 := by
    refine tendsto_nhds_unique hdiff (hE.congr (fun j => ?_))
    rw [hA]
    simp only [hadef, hbdef]
    ring
  have : ∫ y, (g ∘ Φ T) y ∂(μ : Measure M) = ∫ y, g y ∂(μ : Measure M) := by linarith
  exact this

theorem goal_core {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X) :
    ∀ᵐ ω ∂P, occupationLimitPoints X ω ⊆ invariantMeasures Φ := by
  obtain ⟨e, heo, hec⟩ := exists_enum_basis M
  set g : Finset ℕ → ℕ → M → ℝ := fun S k => gapx (⋃ n ∈ S, e n) k with hgdef
  have hae : ∀ᵐ ω ∂P, ∀ (S : Finset ℕ) (k : ℕ) (q : ℚ), 0 < q → Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
          blockIntegral X (g S k) ((q:ℝ).toNNReal) (i + 1) ω -
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
          blockIntegral X (g S k ∘ Φ ((q:ℝ).toNNReal)) ((q:ℝ).toNNReal) i ω)
      atTop (𝓝 0) := by
    refine ae_all_iff.2 fun S => ae_all_iff.2 fun k => ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < q
    · filter_upwards [e52_core P ℱ Φ X hX (g S k) (gapx_uc _ k) (gapx_mem _ k) ((q:ℝ).toNNReal)
        (Real.toNNReal_pos.2 (by exact_mod_cast hq))] with ω h _
      exact h
    · exact ae_of_all _ (fun ω h => absurd h hq)
  filter_upwards [hae] with ω hω
  intro μ hμ
  have hx : Measurable (fun s => X s ω) := hX.progMeasurable.measurable_path ω
  have hμ' : MapClusterPt μ atTop (fun t : ℝ≥0 => occupationMeasure (fun s => X s ω) t) := hμ
  obtain ⟨ψ, hψμ, hψ⟩ := MapClusterPt.exists_seq_tendsto hμ'
  have key1 : ∀ S k (q : ℚ), 0 < q →
      ∫ y, g S k (Φ ((q:ℝ).toNNReal) y) ∂(μ : Measure M) = ∫ y, g S k y ∂(μ : Measure M) :=
    fun S k q hq => goal_key Ω X ω hx (g S k) (gapx_uc _ k).continuous (gapx_mem _ k) Φ
      ((q:ℝ).toNNReal) (Real.toNNReal_pos.2 (by exact_mod_cast hq)) ψ hψ μ hψμ (hω S k q hq)
  have key2 : ∀ S k (t : ℝ≥0),
      ∫ y, g S k (Φ t y) ∂(μ : Measure M) = ∫ y, g S k y ∂(μ : Measure M) := by
    intro S k t
    have hq : ∀ n : ℕ, ∃ q : ℚ, (t:ℝ) < q ∧ (q:ℝ) < t + 1 / ((n:ℝ) + 1) := fun n =>
      exists_rat_btwn (by linarith [show (0:ℝ) < 1 / ((n:ℝ) + 1) by positivity])
    choose q hq1 hq2 using hq
    have hqpos : ∀ n, 0 < q n := fun n => by
      have : (0:ℝ) < q n := lt_of_le_of_lt t.coe_nonneg (hq1 n)
      exact_mod_cast this
    have hqt : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 (t:ℝ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun n => (hq1 n).le) (fun n => (hq2 n).le)
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (t:ℝ)
      rw [add_zero] at this; exact this
    have hτ : Tendsto (fun n => ((q n : ℚ) : ℝ).toNNReal) atTop (𝓝 t) := by
      have := (continuous_real_toNNReal.tendsto (t:ℝ)).comp hqt
      rw [Real.toNNReal_coe] at this; exact this
    have hgc : Continuous (g S k) := (gapx_uc _ k).continuous
    have hlim : Tendsto (fun n => ∫ y, g S k (Φ (((q n : ℚ) : ℝ).toNNReal) y) ∂(μ : Measure M))
        atTop (𝓝 (∫ y, g S k (Φ t y) ∂(μ : Measure M))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
        (fun n => (hgc.comp (Φ.continuous_toFun _)).measurable.aestronglyMeasurable)
        (integrable_const 1) (fun n => ae_of_all _ (fun y => ?_)) (ae_of_all _ (fun y => ?_))
      · rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(gapx_mem (⋃ n ∈ S, e n) k (Φ (((q n : ℚ) : ℝ).toNNReal) y)).1,
          (gapx_mem (⋃ n ∈ S, e n) k (Φ (((q n : ℚ) : ℝ).toNNReal) y)).2]
      · exact ((hgc.comp (Φ.continuous continuous_id
          (continuous_const : Continuous fun _ : ℝ≥0 => y))).tendsto t).comp hτ
    have hconst : Tendsto (fun n => ∫ y, g S k (Φ (((q n : ℚ) : ℝ).toNNReal) y) ∂(μ : Measure M))
        atTop (𝓝 (∫ y, g S k y ∂(μ : Measure M))) := by
      refine tendsto_const_nhds.congr (fun n => ?_)
      exact (key1 S k (q n) (hqpos n)).symm
    exact tendsto_nhds_unique hlim hconst
  intro t
  have hΦm : Measurable (fun y => Φ t y) := (Φ.continuous continuous_const continuous_id).measurable
  haveI : IsProbabilityMeasure ((μ : Measure M).map (Φ t)) :=
    Measure.isProbabilityMeasure_map hΦm.aemeasurable
  refine ext_of_gapx e heo hec _ _ (fun S k => ?_)
  rw [integral_map hΦm.aemeasurable (gapx_uc _ k).continuous.measurable.aestronglyMeasurable]
  exact key2 S k t

end StochApproxDyn.WeakAPT

open StochApproxDyn.WeakAPT
open MeasureTheory Filter Topology
open scoped NNReal

theorem solution
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X) :
    ∀ᵐ ω ∂P, occupationLimitPoints X ω ⊆ invariantMeasures Φ := by
  exact goal_core P ℱ Φ X hX
