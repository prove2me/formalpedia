-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:46.487873+00:00
-- url     : https://prove2.me/submissions/7ef6ae98-4707-47f5-b7b3-79588824801a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]
omit [Fintype σ]
namespace GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
theorem _root_.solution :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp
end GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
