-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X__785d066adc9d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:46.207794+00:00
-- url     : https://prove2.me/submissions/b486a760-9301-4de7-81e7-63d87385bf52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue

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
theorem _root_.solution (i : Σ _ : Unit, T) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ())
      (X i : MRing (fun _ : Unit => T)) 1 := by
  have h := isWeightedHomogeneous_X ℤ (blockWeight (ι := fun _ : Unit => T) ()) i
  have e : blockWeight (ι := fun _ : Unit => T) () i = 1 := by simp [blockWeight]
  rwa [e] at h
end GroundTheory.Heights₂.Heights.VerticalPointResidue
