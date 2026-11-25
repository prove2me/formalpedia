-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_sub_2606edba133c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:10.54647+00:00
-- url     : https://prove2.me/submissions/633d558d-172e-4f64-87df-3e8950b4366d

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
theorem _root_.solution {f g : MRing (fun _ : Unit => T)} {n : ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) f n)
    (hg : IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n) :
    IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) (f - g) n := by
  have h := sub_mem ((mem_weightedHomogeneousSubmodule ℤ _ n f).mpr hf)
    ((mem_weightedHomogeneousSubmodule ℤ _ n g).mpr hg)
  exact (mem_weightedHomogeneousSubmodule ℤ _ n _).mp h
end GroundTheory.Heights₂.Heights.VerticalPointResidue
