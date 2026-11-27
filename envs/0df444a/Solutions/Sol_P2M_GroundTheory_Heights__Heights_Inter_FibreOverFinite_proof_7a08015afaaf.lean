-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreOverFinite_proof_7a08015afaaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:04.985288+00:00
-- url     : https://prove2.me/submissions/0a1ceb9a-efe9-424e-b731-e6d733551315

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreOverFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreDivSupp_proof_049847f46d2a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace FibreOverFinite
theorem _root_.solution (h : FibreIncomp.Statement) : FibreOverFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  refine (divSupp_finite P' (rename v s)).subset fun W' hW' => ?_
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    rw [← hW'.2.2] at hsW
    exact hsW
  exact ((FibreDivSupp.proof h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW W').mp ⟨hW', hsW'⟩).1
end FibreOverFinite
end GroundTheory.Heights₂.Heights.Inter
