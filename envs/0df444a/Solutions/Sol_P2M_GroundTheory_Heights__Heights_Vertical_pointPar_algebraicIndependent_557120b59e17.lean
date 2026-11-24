-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_pointPar_algebraicIndependent_557120b59e17
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.432946+00:00
-- url     : https://prove2.me/submissions/6e5f79b7-0ac4-4bf3-9864-5b6f4143dff0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution : AlgebraicIndependent ℚ pointPar := by
  have h := MvPolynomial.algebraicIndependent_X (Par 0 1) ℚ
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) :=
    IsFractionRing.injective (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ))
  have h2 := h.map' hinj
  have e : (⇑(IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) ∘ X) = pointPar := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', pointPar]
  rw [e] at h2
  exact h2
end GroundTheory.Heights₂.Heights.Vertical
