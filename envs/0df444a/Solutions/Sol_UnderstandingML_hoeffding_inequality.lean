-- Prove2me | solution 1 for UnderstandingML.hoeffding_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:04:37.132364+00:00
-- url     : https://prove2.me/submissions/6b2c854b-7ccb-4440-b505-270d0e0b020a

import Definitions.Def_UnderstandingML_Framework
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory UnderstandingML

/-- One-sided Hoeffding bound for the centred sum under the product law. -/
theorem hoeffding_one_sided_aux {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω)
    [IsProbabilityMeasure D] (Y : Ω → ℝ) (hY : Measurable Y) {a b : ℝ}
    (hab : ∀ᵐ ω ∂D, Y ω ∈ Set.Icc a b) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (iidLaw D m).real {ω | m * t ≤ ∑ i, (Y (ω i) - ∫ x, Y x ∂D)} ≤
      Real.exp (-(2 * m * t ^ 2 / (b - a) ^ 2)) := by
  set P : Measure (Fin m → Ω) := Measure.pi (fun _ ↦ D) with hP
  have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → Ω) ↦ Y (ω i) - ∫ x, Y x ∂D) P :=
    iIndepFun_pi (X := fun _ x ↦ Y x - ∫ x, Y x ∂D) (fun _ ↦ (hY.sub_const _).aemeasurable)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω : Fin m → Ω ↦ Y (ω i) - ∫ x, Y x ∂D)
        ((‖b - a‖₊ / 2) ^ 2) P := by
    intro i _
    have hmp := measurePreserving_eval (fun _ : Fin m ↦ D) i
    have hae : ∀ᵐ ω ∂P, Y (ω i) ∈ Set.Icc a b := hmp.quasiMeasurePreserving.ae hab
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := fun ω ↦ Y (ω i))
      ((hY.comp (measurable_pi_apply i)).aemeasurable) hae
    have hint : ∫ x, Y (x i) ∂P = ∫ x, Y x ∂D := by
      have := integral_map (μ := P) (φ := Function.eval i) (f := Y)
        (measurable_pi_apply i).aemeasurable (by rw [hmp.map_eq]; exact hY.aestronglyMeasurable)
      rw [hmp.map_eq] at this
      exact this.symm
    simpa only [hint] using h
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := m * t) (by positivity)
  have hiid : iidLaw D m = P := rfl
  rw [hiid]
  refine key.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
    Real.norm_eq_abs, NNReal.coe_ofNat]
  rw [div_pow, sq_abs]
  rcases eq_or_ne (b - a) 0 with h0 | h0
  · simp [h0]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω)
    [IsProbabilityMeasure D] (θ : Ω → ℝ) (hθ : Measurable θ) {a b : ℝ}
    (hab : ∀ᵐ ω ∂D, a ≤ θ ω ∧ θ ω ≤ b) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    iidLaw D m {ω | ε < |(∑ i, θ (ω i)) / m - ∫ x, θ x ∂D|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * m * ε ^ 2 / (b - a) ^ 2))) := by
  haveI : IsProbabilityMeasure (iidLaw D m) := by
    unfold iidLaw; infer_instance
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine (prob_le_one).trans ?_
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul, zero_div, neg_zero, Real.exp_zero,
      mul_one]
    rw [ENNReal.one_le_ofReal]
    norm_num
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set μ := ∫ x, θ x ∂D with hμ
  have h1 := hoeffding_one_sided_aux D θ hθ (a := a) (b := b)
    (hab.mono fun ω h ↦ ⟨h.1, h.2⟩) m hε.le
  have h2 := hoeffding_one_sided_aux D (fun x ↦ -θ x) hθ.neg (a := -b) (b := -a)
    (hab.mono fun ω h ↦ ⟨by linarith [h.2], by linarith [h.1]⟩) m hε.le
  have hba : (-a - -b) = b - a := by ring
  rw [hba] at h2
  have hsubset : {ω : Fin m → Ω | ε < |(∑ i, θ (ω i)) / m - μ|} ⊆
      {ω | m * ε ≤ ∑ i, (θ (ω i) - ∫ x, θ x ∂D)} ∪
      {ω | m * ε ≤ ∑ i, (-θ (ω i) - ∫ x, -θ x ∂D)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hsum : (∑ i, θ (ω i)) / m - μ = (∑ i, (θ (ω i) - μ)) / m := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hsum] at hω
    rcases lt_abs.mp hω with h | h
    · left
      simp only [Set.mem_setOf_eq, ← hμ]
      rw [lt_div_iff₀ hm'] at h
      linarith
    · right
      simp only [Set.mem_setOf_eq, integral_neg, ← hμ]
      have h' : (∑ i, (θ (ω i) - μ)) / m < -ε := by linarith
      rw [div_lt_iff₀ hm'] at h'
      have : ∑ i, (-θ (ω i) - -μ) = -∑ i, (θ (ω i) - μ) := by
        rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring
      rw [this]
      linarith
  calc iidLaw D m {ω | ε < |(∑ i, θ (ω i)) / m - μ|}
      ≤ iidLaw D m {ω | m * ε ≤ ∑ i, (θ (ω i) - ∫ x, θ x ∂D)} +
        iidLaw D m {ω | m * ε ≤ ∑ i, (-θ (ω i) - ∫ x, -θ x ∂D)} :=
        (measure_mono hsubset).trans (measure_union_le _ _)
    _ = ENNReal.ofReal ((iidLaw D m).real {ω | m * ε ≤ ∑ i, (θ (ω i) - ∫ x, θ x ∂D)}) +
        ENNReal.ofReal ((iidLaw D m).real
          {ω | m * ε ≤ ∑ i, (-θ (ω i) - ∫ x, -θ x ∂D)}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2 / (b - a) ^ 2))) +
        ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2 / (b - a) ^ 2))) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-(2 * m * ε ^ 2 / (b - a) ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring
