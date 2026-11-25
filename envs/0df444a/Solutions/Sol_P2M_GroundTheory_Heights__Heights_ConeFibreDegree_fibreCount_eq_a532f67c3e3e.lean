-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreDegree_fibreCount_eq_a532f67c3e3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:12.984738+00:00
-- url     : https://prove2.me/submissions/a70c1c4d-c908-41b3-9599-575dae522e67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFibreDegree
namespace GroundTheory.Heights₂.Heights.ConeFibreDegree
theorem _root_.solution {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hinj : Function.Injective h.pointOf := by
    intro y y' hyy
    have hv := congrArg (fun v => (h.matᵀ)⁻¹ *ᵥ v) hyy
    simp only [HermNorm.pointOf, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at hv
    exact WithLp.ofLp_injective 2 hv
  have hπ : ∀ y : EuclideanSpace ℂ (Fin n),
      (Matrix.of π * (h.matᵀ)⁻¹) *ᵥ h.pointOf y = WithLp.ofLp (linProj π y) := by
    intro y
    rw [HermNorm.pointOf, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    ext i
    simp [linProj, mulVec, dotProduct]
  rw [fibreCount, ← hinj.injOn.encard_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, ComplexSets.fibre, ComplexSets.zeroSet, coneSet]
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨hy, hπ y⟩
  · rintro ⟨hx, hxw⟩
    have hpt : h.pointOf (WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = x := by
      simp [HermNorm.pointOf, mulVec_mulVec, mul_nonsing_inv _ hu]
    refine ⟨WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x), ⟨?_, ?_⟩, hpt⟩
    · rw [hpt]; exact hx
    · apply WithLp.ofLp_injective 2
      rw [← hπ, hpt, hxw]
end GroundTheory.Heights₂.Heights.ConeFibreDegree
