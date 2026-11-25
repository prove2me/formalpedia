-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_exists_comp_not_mem_3a87519edb73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:05.773305+00:00
-- url     : https://prove2.me/submissions/1f4e191b-e221-4629-b34b-c00d6f017372

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d


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
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointNagata
theorem _root_.solution {J : Ideal (MRing (fun _ : Unit => T))} {f : MRing (fun _ : Unit => T)}
    (hf : f ∉ J) : ∃ n, comp n f ∉ J := by
  obtain ⟨D, hD⟩ := Inter.LocRingPow.exists_component_not_mem hf
  exact ⟨D (), hD⟩
end GroundTheory.Heights₂.Heights.VerticalPointNagata
