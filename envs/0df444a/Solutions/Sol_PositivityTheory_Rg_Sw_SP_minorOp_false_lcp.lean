-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.minorOp_false_lcp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:21.916699+00:00
-- url     : https://prove2.me/submissions/1e8a6ce3-d12b-4793-97fd-610c3abd2af4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_false_lcp
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_foldr

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (minorOp s m false I J) := by
  unfold minorOp
  refine lcp_sum _ _ fun σ _ => lcp_smul _ (lcp_foldr _ (fun k => opH_false_lcp s m _ _ hQ) _)
end PositivityTheory.Rg.Sw.SP
