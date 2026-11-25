-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_comp_mem_69b2299180fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:34.240824+00:00
-- url     : https://prove2.me/submissions/6518c4ed-5129-464c-920f-28109cf296e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898


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
theorem _root_.solution {J : Ideal (MRing (fun _ : Unit => T))} (hJ : IsMultiHomogIdeal J)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ J) (n : ℕ) : comp n f ∈ J :=
  Inter.LocRingPow.component_mem hJ hf _
end GroundTheory.Heights₂.Heights.VerticalPointNagata
