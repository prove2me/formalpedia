-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_6_24_instance_hinge_loss
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:41:13.276183+00:00
-- url     : https://prove2.me/submissions/8ace1bdd-4fe6-4c74-a62d-5aeac513bc4b

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

set_option autoImplicit false

namespace SvmCex7a

open MeasureTheory SupportVectorMachines.Classification

/-- Evaluation map: the real number `c` is the constant function `c` on `Unit`. -/
noncomputable def tF : ℝ →ₗ[ℝ] (Unit → ℝ) := LinearMap.pi (fun _ => LinearMap.id)

theorem tF_apply (c : ℝ) (u : Unit) : tF c u = c := rfl

/-- Labels `1` and `-100`, each with probability `1/2`. -/
noncomputable def Pm : Measure (Unit × ℝ) :=
  (1/2 : ENNReal) • Measure.dirac ((), (1 : ℝ)) + (1/2 : ENNReal) • Measure.dirac ((), (-100 : ℝ))

instance Pm_prob : IsProbabilityMeasure Pm := ⟨by
  simp [Pm, ENNReal.inv_two_add_inv_two]⟩

theorem Pm_int (f : Unit × ℝ → ℝ) : Integrable f Pm := by
  unfold Pm
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac enorm_lt_top).smul_measure (by simp)
  · exact (integrable_dirac enorm_lt_top).smul_measure (by simp)

theorem Pm_integral (f : Unit × ℝ → ℝ) :
    ∫ p, f p ∂Pm = 1/2 * f ((), 1) + 1/2 * f ((), -100) := by
  have h1 : Integrable f ((1/2 : ENNReal) • Measure.dirac ((), (1 : ℝ))) :=
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  have h2 : Integrable f ((1/2 : ENNReal) • Measure.dirac ((), (-100 : ℝ))) :=
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  unfold Pm
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp

theorem risk_eq (c : ℝ) :
    risk hingeLoss Pm (tF c) = 1/2 * max 0 (1 - c) + 1/2 * max 0 (1 + 100 * c) := by
  unfold risk
  rw [Pm_integral]
  simp only [hingeLoss, tF_apply]
  ring_nf

theorem risk_nonneg (c : ℝ) : 0 ≤ risk hingeLoss Pm (tF c) := by
  rw [risk_eq]
  have := le_max_left (0:ℝ) (1 - c)
  have := le_max_left (0:ℝ) (1 + 100 * c)
  linarith

/-- The exact minimizer of `c ↦ c²/2 + max 0 (1 - y c)`. -/
noncomputable def svm (y : ℝ) : ℝ := if |y| ≤ 1 then y else 1 / y

theorem svm_min (y g : ℝ) :
    1/2 * (svm y) ^ 2 + max 0 (1 - y * svm y) ≤ 1/2 * g ^ 2 + max 0 (1 - y * g) := by
  unfold svm
  split_ifs with h
  · have hy : y * y ≤ 1 := by
      have := abs_le.mp h
      nlinarith
    rw [max_eq_right (by linarith)]
    have := le_max_right (0:ℝ) (1 - y * g)
    nlinarith [sq_nonneg (g - y)]
  · rw [not_le] at h
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0, abs_zero] at h; linarith
    have hyy : 1 < y ^ 2 := by
      have := (one_lt_sq_iff_one_lt_abs y).mpr h
      exact this
    set u := 1 / y with hu
    have hyu : y * u = 1 := by rw [hu]; field_simp
    rw [hyu, sub_self, max_self]
    have hu2 : u ^ 2 < 1 := by
      have : (y * u) ^ 2 = 1 := by rw [hyu]; norm_num
      nlinarith [sq_nonneg u, sq_nonneg y]
    set t := y * g with ht
    have hg : g = t * u := by
      rw [ht, mul_comm y g, mul_assoc, hyu, mul_one]
    rw [hg]
    rcases le_or_gt 1 t with h1 | h1
    · have := le_max_left (0:ℝ) (1 - t)
      have : u ^ 2 ≤ (t * u) ^ 2 := by
        rw [mul_pow]
        have : 1 ≤ t ^ 2 := by nlinarith
        nlinarith [sq_nonneg u]
      linarith
    · rw [max_eq_right (by linarith)]
      have hk : 0 ≤ 2 - (1 + t) * u ^ 2 := by
        rcases le_or_gt (1 + t) 0 with h2 | h2
        · nlinarith [sq_nonneg u]
        · nlinarith [sq_nonneg u]
      have : 0 ≤ (1 - t) * (2 - (1 + t) * u ^ 2) := mul_nonneg (by linarith) hk
      nlinarith

/-- The SVM decision function for one-point samples. -/
noncomputable def fS (D : Fin 1 → Unit × ℝ) : ℝ := svm (D 0).2

theorem fS_svm (D : Fin 1 → Unit × ℝ) : IsSVMSolution ℝ tF hingeLoss (1/2) 1 D (fS D) := by
  intro g
  have := svm_min (D 0).2 g
  simp only [empiricalRisk, hingeLoss, tF_apply, Fin.sum_univ_one, Nat.cast_one, div_one,
    one_mul, Real.norm_eq_abs, sq_abs, fS]
  linarith

theorem rkhs : IsRKHSOfKernel ℝ tF (fun _ _ : Unit => (1 : ℝ)) := by
  refine ⟨?_, ⟨fun _ => 1, fun _ _ => rfl, fun f x => ?_⟩, fun _ => measurable_const⟩
  · intro a b hab
    have := congrFun hab ()
    simpa [tF_apply] using this
  · simp [tF_apply]

theorem A_le :
    sInf {r : ℝ | ∃ f : ℝ, r = 1/2 * ‖f‖ ^ 2 + risk hingeLoss Pm (tF f)} ≤ 1 := by
  have hbdd : BddBelow {r : ℝ | ∃ f : ℝ, r = 1/2 * ‖f‖ ^ 2 + risk hingeLoss Pm (tF f)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, rfl⟩
    have := risk_nonneg f
    positivity
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ f : ℝ, r = 1/2 * ‖f‖ ^ 2 + risk hingeLoss Pm (tF f)} := by
    refine ⟨0, ?_⟩
    rw [risk_eq]; norm_num
  exact csInf_le hbdd hmem

theorem sqrt_bound : Real.sqrt (8 * 1 / ((1:ℕ):ℝ)) + Real.sqrt (4 / ((1:ℕ):ℝ) + 8 * 1 / (3 * ((1:ℕ):ℝ))) ≤ 6 := by
  have e1 : (8 * 1 / ((1:ℕ):ℝ)) = 8 := by norm_num
  have e2 : (4 / ((1:ℕ):ℝ) + 8 * 1 / (3 * ((1:ℕ):ℝ))) = 20 / 3 := by norm_num
  rw [e1, e2]
  have s1 := Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)
  have s2 := Real.sq_sqrt (show (0:ℝ) ≤ 20 / 3 by norm_num)
  have n1 := Real.sqrt_nonneg 8
  have n2 := Real.sqrt_nonneg (20 / 3)
  have a1 : Real.sqrt 8 ≤ 3 := by nlinarith
  have a2 : Real.sqrt (20 / 3) ≤ 3 := by nlinarith
  linarith

theorem box_meas :
    (Measure.pi (fun _ : Fin 1 => Pm)) (Set.univ.pi (fun _ => {p : Unit × ℝ | p.2 = 1})) = 1/2 := by
  rw [Measure.pi_pi]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  simp [Pm, show (-100:ℝ) ≠ 1 by norm_num]

theorem box_meas_real :
    (Measure.pi (fun _ : Fin 1 => Pm)).real
      (Set.univ.pi (fun _ => {p : Unit × ℝ | p.2 = 1}))ᶜ = 1/2 := by
  have hm : MeasurableSet (Set.univ.pi (fun _ : Fin 1 => {p : Unit × ℝ | p.2 = 1})) :=
    MeasurableSet.univ_pi (fun _ => measurable_snd (measurableSet_singleton (1:ℝ)))
  rw [probReal_compl_eq_one_sub hm, Measure.real, box_meas]
  norm_num

theorem excess (D : Fin 1 → Unit × ℝ) (hD : (D 0).2 = 1) :
    ¬ (1/2 * ‖fS D‖ ^ 2 + risk hingeLoss Pm (tF (fS D)) -
          restrictedBayesRisk ℝ tF hingeLoss Pm <
        approxErrorA2 ℝ tF hingeLoss Pm (1/2) +
          (1/2 : ℝ)⁻¹ * (Real.sqrt (8 * 1 / ((1:ℕ):ℝ)) +
            Real.sqrt (4 / ((1:ℕ):ℝ) + 8 * 1 / (3 * ((1:ℕ):ℝ))))) := by
  have hf : fS D = 1 := by simp [fS, svm, hD]
  rw [hf, risk_eq]
  unfold approxErrorA2
  have h1 := A_le
  have h2 := sqrt_bound
  rw [not_lt]
  norm_num at h1 h2 ⊢
  linarith

theorem exp_bound : Real.exp (-1) < 1/2 := by
  have h := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith

end SvmCex7a

open MeasureTheory SupportVectorMachines.Classification in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) (hτ : 0 < τ)
    (fSVM : (Fin n → X × ℝ) → H)
    (hfSVM : ∀ D, IsSVMSolution H toFun hingeLoss lam n D (fSVM D))
    (hInt : ∀ D, Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun (fSVM D) p.1)) P),
    1 - Real.exp (-τ) ≤ (Measure.pi (fun _ : Fin n => P)).real
      {D | lam * ‖fSVM D‖ ^ 2 + risk hingeLoss P (toFun (fSVM D)) -
          restrictedBayesRisk H toFun hingeLoss P <
        approxErrorA2 H toFun hingeLoss P lam +
          lam⁻¹ * (Real.sqrt (8 * τ / n) + Real.sqrt (4 / n + 8 * τ / (3 * n)))}) := by
  intro h
  have key := h (X := Unit) ℝ SvmCex7a.tF (fun _ _ => 1) SvmCex7a.rkhs (fun _ => le_rfl)
    SvmCex7a.Pm 1 one_pos (1/2) (by norm_num) 1 one_pos SvmCex7a.fS SvmCex7a.fS_svm
    (fun _ => SvmCex7a.Pm_int _)
  refine absurd (key.trans (measureReal_mono
    (s₂ := (Set.univ.pi (fun _ : Fin 1 => {p : Unit × ℝ | p.2 = 1}))ᶜ) ?_)) ?_
  · intro D hD hB
    exact SvmCex7a.excess D (hB 0 (Set.mem_univ _)) hD
  · rw [SvmCex7a.box_meas_real]
    have := SvmCex7a.exp_bound
    linarith
