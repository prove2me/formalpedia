-- Prove2me | solution 1 for RobustLP.Counterpart.rc_feasible_almost_reliable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:25:44.895715+00:00
-- url     : https://prove2.me/submissions/0b542118-8b8c-4c40-b8c9-5e6a88fd1e7e

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
import Definitions.Def_RobustLP_Counterpart_AlmostReliable

open MeasureTheory ProbabilityTheory RobustLP.Counterpart in
theorem solution {n p m : ℕ} (L : UncertainLP n p m)
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ξ : Fin m → Fin n → S → ℝ) (hξ : IsSymmetricPerturbation P L.J ξ)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω)
    (x : Fin n → ℝ) (y z : Fin m → Fin n → ℝ) (hRC : L.RCFeasible ε δ Ω x y z) :
    L.AlmostReliable ε δ (Real.exp (-(Ω ^ 2 / 2))) P ξ x := by
  obtain ⟨hE, hA, hrow, hbox, hyz⟩ := hRC
  refine ⟨⟨hE, hA, hbox⟩, fun i => ?_⟩
  set w : Fin n → ℝ := fun j => L.A i j * z i j with hw
  set σ := Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2) with hσ
  have hwsq : ∑ j ∈ L.J i, w j ^ 2 = ∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [hw]
    ring
  -- the violation event is contained in a tail event of a weighted sum
  have hsub : L.violationEvent ε δ ξ x i ⊆
      {ω | Ω * σ < ∑ j ∈ L.J i, w j * ξ i j ω} := by
    intro ω hω
    simp only [UncertainLP.violationEvent, Set.mem_ofPred_eq] at hω ⊢
    have hJ : ∑ j, ξ i j ω * L.A i j * x j = ∑ j ∈ L.J i, ξ i j ω * L.A i j * x j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [hξ.zero_of_not_mem i j hj ω]
      ring
    have h1 : ∑ j, (1 + ε * ξ i j ω) * L.A i j * x j =
        ∑ j, L.A i j * x j + ε * ∑ j ∈ L.J i, ξ i j ω * L.A i j * x j := by
      rw [← hJ, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h2 : ∑ j ∈ L.J i, ξ i j ω * L.A i j * x j ≤
        ∑ j ∈ L.J i, w j * ξ i j ω + ∑ j ∈ L.J i, |L.A i j| * y i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      have hx := hξ.mem_Icc i j ω
      obtain ⟨hl, hr⟩ := hyz i j
      have hb : ξ i j ω * L.A i j * (x j - z i j) ≤ |L.A i j| * y i j := by
        calc ξ i j ω * L.A i j * (x j - z i j)
            ≤ |ξ i j ω * L.A i j * (x j - z i j)| := le_abs_self _
          _ = |ξ i j ω| * |L.A i j| * |x j - z i j| := by rw [abs_mul, abs_mul]
          _ ≤ 1 * |L.A i j| * y i j := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_right (abs_le.2 ⟨hx.1, hx.2⟩) (abs_nonneg _))
              (abs_le.2 ⟨hl, hr⟩) (abs_nonneg _) (by positivity)
          _ = |L.A i j| * y i j := by ring
      have he : ξ i j ω * L.A i j * x j =
          w j * ξ i j ω + ξ i j ω * L.A i j * (x j - z i j) := by
        simp only [hw]
        ring
      rw [he]
      linarith
    have h3 := hrow i
    rw [h1] at hω
    have h4 : ε * (Ω * σ) < ε * ∑ j ∈ L.J i, w j * ξ i j ω := by
      nlinarith
    exact lt_of_mul_lt_mul_left h4 hε.le
  by_cases hσ0 : σ = 0
  · -- degenerate case: all weights vanish, the event is empty
    have hw0 : ∀ j ∈ L.J i, w j = 0 := by
      have hs : ∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2 = 0 := by
        have hnn : 0 ≤ ∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2 :=
          Finset.sum_nonneg (fun j _ => by positivity)
        rw [hσ] at hσ0
        exact (Real.sqrt_eq_zero hnn).1 hσ0
      rw [← hwsq] at hs
      intro j hj
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j))).1 hs j hj
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hempty : {ω | Ω * σ < ∑ j ∈ L.J i, w j * ξ i j ω} = (∅ : Set S) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hσ0, Finset.sum_eq_zero (fun j hj => by rw [hw0 j hj, zero_mul])]
      simp
    rw [hempty] at hsub
    rw [Set.subset_empty_iff.1 hsub]
    simp only [measureReal_empty]
    positivity
  · have hσpos : 0 < σ := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hσ0)
    -- mean zero of each perturbation
    have hmean : ∀ j, ∫ ω, ξ i j ω ∂P = 0 := by
      intro j
      have hm := (hξ.measurable i j)
      have e1 : ∫ ω, ξ i j ω ∂P = ∫ t, t ∂(P.map (ξ i j)) := by
        exact (integral_map (φ := ξ i j) hm.aemeasurable (f := fun t : ℝ => t)
          aestronglyMeasurable_id).symm
      have e2 : ∫ ω, -ξ i j ω ∂P = ∫ t, t ∂(P.map (fun ω => -ξ i j ω)) := by
        exact (integral_map (φ := fun ω => -ξ i j ω) hm.neg.aemeasurable (f := fun t : ℝ => t)
          aestronglyMeasurable_id).symm
      have e3 : ∫ ω, ξ i j ω ∂P = ∫ ω, -ξ i j ω ∂P := by
        rw [e1, e2, hξ.symmetric i j]
      rw [integral_neg] at e3
      linarith
    have hone : (‖(1 : ℝ) - -1‖₊ / 2) ^ 2 = (1 : NNReal) := by
      ext
      simp
      norm_num
    set cw : Fin n → NNReal := fun j => ⟨w j ^ 2, sq_nonneg _⟩ with hcw
    have hsubG : ∀ j ∈ L.J i, HasSubgaussianMGF (fun ω => w j * ξ i j ω) (cw j * 1) P := by
      intro j _
      have h0 : HasSubgaussianMGF (ξ i j) ((‖(1 : ℝ) - -1‖₊ / 2) ^ 2) P :=
        hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hξ.measurable i j).aemeasurable
          (ae_of_all _ (hξ.mem_Icc i j)) (hmean j)
      rw [hone] at h0
      exact h0.const_mul (w j)
    have hind : iIndepFun (fun j => fun ω => w j * ξ i j ω) P :=
      (hξ.indep i).comp (fun j t => w j * t) (fun j => measurable_const_mul (w j))
    have hbound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsubG
      (ε := Ω * σ) (by positivity)
    have hcoe : ((∑ j ∈ L.J i, cw j * 1 : NNReal) : ℝ) = σ ^ 2 := by
      simp only [mul_one, NNReal.coe_sum]
      change ∑ j ∈ L.J i, w j ^ 2 = σ ^ 2
      rw [hwsq, hσ, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by positivity))]
    rw [hcoe] at hbound
    have hexp : -(Ω * σ) ^ 2 / (2 * σ ^ 2) = -(Ω ^ 2 / 2) := by
      field_simp
    rw [hexp] at hbound
    calc P.real (L.violationEvent ε δ ξ x i)
        ≤ P.real {ω | Ω * σ ≤ ∑ j ∈ L.J i, w j * ξ i j ω} := by
          exact measureReal_mono (hsub.trans (fun ω (h : Ω * σ < _) => (h.le : Ω * σ ≤ _)))
      _ ≤ Real.exp (-(Ω ^ 2 / 2)) := hbound
