-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:43.785017+00:00
-- url     : https://prove2.me/submissions/4d6baf07-f23a-4c4a-adc4-729eedaf2f92

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (i : (k : K) → ι k) : (evalOne i).comp (ratioMap i) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply]
    have h1 : ratioMap i (Ideal.Quotient.mk (dehomIdeal i) (C c)) =
        algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
      rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio,
        aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
        MvPolynomial.algebraMap_eq]
    rw [h1, evalOne_algebraMap]
    rfl
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, evalOne_algebraMap]
    have hu : evalOne i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      rw [IsUnit.unit_spec, evalOne_algebraMap, dehom_X_self]
    have hinv : evalOne i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      have := congrArg (evalOne i) ((isUnit_coneX i p.1).unit.inv_mul)
      rwa [map_mul, hu, mul_one, map_one] at this
    rw [hinv, one_mul]
end GroundTheory.Heights₂.Heights.Targets
