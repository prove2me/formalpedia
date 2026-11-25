-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.mComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:38.504652+00:00
-- url     : https://prove2.me/submissions/bc01c6d9-e23b-44c3-b8a1-418f8ceb8077

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_CX_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution : MComm := by
  intro R _ ρ α p q p' q'
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add]
  rw [del_CX_mul, del_CX_mul, del_comm p q p' q']
  ring
end PositivityTheory.Rg.Sw.SP.Mi
