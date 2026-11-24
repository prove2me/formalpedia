-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:40.746942+00:00
-- url     : https://prove2.me/submissions/a0d33bfd-b42b-4718-a73d-bc7844f3d7a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blockWeight


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
namespace GroundTheory.Heights₂.Heights.VerticalPointResidue
theorem _root_.solution {g : MRing (fun _ : Unit => T)} {n : ℕ} :
    IsMultiHomog g (fun _ => n) ↔
      IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n := by
  constructor
  · intro h
    exact isWeightedHomogeneous_of_isMultiHomog h ()
  · intro h m hm k
    cases k
    exact (weight_blockWeight (ι := fun _ : Unit => T) () m).symm.trans (h (mem_support_iff.mp hm))
end GroundTheory.Heights₂.Heights.VerticalPointResidue
