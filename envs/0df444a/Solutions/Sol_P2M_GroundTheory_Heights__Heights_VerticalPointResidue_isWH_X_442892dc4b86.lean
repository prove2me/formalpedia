-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_442892dc4b86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:47.160124+00:00
-- url     : https://prove2.me/submissions/73ab2b18-50d4-4704-b6d9-657eddd64410

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X__785d066adc9d

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointResidue
variable {T : Type} [Fintype T]
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointResidue
theorem _root_.solution (c : T) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X ⟨(), c⟩ : MRing (fun _ : Unit => T)) 1 :=
  isWH_X' ⟨(), c⟩
end GroundTheory.Heights₂.Heights.VerticalPointResidue
