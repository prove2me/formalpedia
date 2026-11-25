-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:19.120571+00:00
-- url     : https://prove2.me/submissions/13340d92-626a-42a5-9bf0-db3481c79b19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_conjO_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_conjIdeal_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution {p : Ideal (𝓞 K)} {a : K} (h : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) :
    InI p p (star a) := by
  obtain ⟨r, s, hs, hr, rfl⟩ := h
  refine ⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩
  · exact (mem_conjIdeal_iff p r).1 hr
  · rw [algebraMap_conjO, algebraMap_conjO, star_div₀]
end Formalism.L2.SG.Pf.LatDictZ.Z2
