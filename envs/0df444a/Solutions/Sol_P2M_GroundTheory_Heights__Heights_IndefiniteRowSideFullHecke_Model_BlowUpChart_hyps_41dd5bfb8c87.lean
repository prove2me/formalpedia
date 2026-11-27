-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_hyps_41dd5bfb8c87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:55.92123+00:00
-- url     : https://prove2.me/submissions/cf175518-b951-480f-a663-d1e2567a0aaf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace BlowUpChart
theorem _root_.solution :
    IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
    ∃ i, ![(2 : ℤ_[2])] i ≠ 0 := by
  refine ⟨inferInstance, inferInstance, ?_, ⟨0, by simp⟩⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  simp
end BlowUpChart
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
