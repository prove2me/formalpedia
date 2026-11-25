-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_isMultiHomogIdeal_e52032a6c383
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:06.344816+00:00
-- url     : https://prove2.me/submissions/b6bb7223-51dc-4989-b4d7-23ba885241fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_component_mem_f04e3a930347
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution (y : (Σ k, ι k) → Ω) : IsMultiHomogIdeal (mCoordIdeal y) := by
  classical
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf m ↦ component_mem y f hf m
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
