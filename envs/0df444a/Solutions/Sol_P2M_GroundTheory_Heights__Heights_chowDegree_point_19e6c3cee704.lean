-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowDegree_point_19e6c3cee704
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:05.370858+00:00
-- url     : https://prove2.me/submissions/adaa6805-9dff-4e51-be91-ee69d60b6034

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (F : Type*) [Field F] :
    chowDegree (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 = 1 := by
  have hX := isChowForm_point F
  have key : ∀ δ, (∃ f, IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 f ∧ IsMultiHomog δ f) →
      δ = 1 := by
    rintro δ ⟨f, hf, hδ⟩
    have hXf : X (0, 0) ∣ f := (hX.2 f).mp ((hf.2 f).mpr dvd_rfl)
    have hfX : f ∣ X (0, 0) := (hf.2 _).mp ((hX.2 _).mpr dvd_rfl)
    obtain ⟨q, rfl⟩ := hXf
    obtain ⟨r, hr⟩ := hfX
    have hqr : q * r = 1 := by
      have h' : X (0, 0) * (q * r) = X (0, 0) * 1 := by
        rw [mul_one, ← mul_assoc]
        exact hr.symm
      exact mul_left_cancel₀ (X_ne_zero _) h'
    obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)
    have h1 : IsWeightedHomogeneous (groupWeight 1 1) (X (0, 0) * C c : MvPolynomial (Fin 1 × Fin 1) F)
        ((fun _ => 1) + 0) :=
      IsWeightedHomogeneous.mul (isMultiHomog_point F) (isWeightedHomogeneous_C _ c)
    rw [add_zero] at h1
    exact congrFun (IsWeightedHomogeneous.inj_right hf.1 hδ h1) 0
  apply le_antisymm
  · exact Nat.sInf_le ⟨X (0, 0), hX, isMultiHomog_point F⟩
  · exact le_csInf ⟨1, X (0, 0), hX, isMultiHomog_point F⟩ fun δ hδ => (key δ hδ).ge
end GroundTheory.Heights₂.Heights
