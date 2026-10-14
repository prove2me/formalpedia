-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.martingale_slln_eq47
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:43:30.970989+00:00
-- url     : https://prove2.me/submissions/57848115-9891-4f1d-a76e-06532f0cf96c

import Mathlib
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

end StochApproxDyn.WeakAPT

open StochApproxDyn.WeakAPT
open MeasureTheory Filter Topology
open scoped NNReal

theorem solution
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T i ω - (P[blockIntegral X f T i | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by
  exact e47_core P ℱ X hX f hf hf01 T hT
