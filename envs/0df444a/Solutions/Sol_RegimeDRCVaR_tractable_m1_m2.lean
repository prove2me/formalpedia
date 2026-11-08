-- Prove2me | solution 1 for RegimeDRCVaR.tractable_m1_m2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:52:38.98655+00:00
-- url     : https://prove2.me/submissions/ad75af88-c3c6-4582-8456-1f7a8e6074d7

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

open scoped ENNReal

open RegimeDRCVaR in
theorem solution {I : ℕ} :
    (0 < I → ∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent 1) x ↔ ∀ i, β ≥ x i ∧ β ≥ -x i) ∧
    (∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent 2) x ↔ (x, β) ∈ PolyhedralSOC.Shared.LorentzCone I) := by
  have h1 : ENNReal.conjExponent 1 = ⊤ := by
    rw [ENNReal.conjExponent, tsub_self, ENNReal.inv_zero, add_top]
  have h2 : ENNReal.conjExponent 2 = 2 := by
    rw [ENNReal.conjExponent, ← one_add_one_eq_two, ENNReal.add_sub_cancel_right ENNReal.one_ne_top,
      inv_one]
  refine ⟨fun hI x β => ?_, fun x β => ?_⟩
  · haveI : Nonempty (Fin I) := ⟨⟨0, hI⟩⟩
    rw [h1]
    unfold normM
    rw [PiLp.norm_eq_ciSup, ge_iff_le, ciSup_le_iff (Set.finite_range _).bddAbove]
    apply forall_congr'
    intro i
    rw [PiLp.toLp_apply, Real.norm_eq_abs, abs_le]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨hb, by linarith⟩
    · rintro ⟨ha, hb⟩; exact ⟨by linarith, ha⟩
  · rw [h2]
    unfold normM
    rw [PiLp.norm_eq_of_L2]
    simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    rfl
