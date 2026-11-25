-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:24.707217+00:00
-- url     : https://prove2.me/submissions/5df9d7f3-f5e4-4824-9b77-dcb7ca7ae56d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointDegCPos

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.PointDegreeComplexPositive
namespace GroundTheory.Heights₂.Heights.PointDegreeComplexPositive
theorem _root_.solution {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos
end GroundTheory.Heights₂.Heights.PointDegreeComplexPositive
