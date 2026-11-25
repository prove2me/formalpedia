-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_isMultiHomog_comp_8657a988e3db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:27.611367+00:00
-- url     : https://prove2.me/submissions/f0c047f9-991e-4779-bcb1-3e13e8d3141f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6


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
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointNagata
theorem _root_.solution (n : ℕ) (f : MRing (fun _ : Unit => T)) :
    IsMultiHomog (comp n f) (fun _ => n) :=
  Inter.LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
end GroundTheory.Heights₂.Heights.VerticalPointNagata
