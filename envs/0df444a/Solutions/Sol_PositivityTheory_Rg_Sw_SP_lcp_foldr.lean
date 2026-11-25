-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:45.450144+00:00
-- url     : https://prove2.me/submissions/251a43c0-1305-43b9-aac8-addec6f11ee4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_id

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
theorem _root_.solution {Q' : Fm n} {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k, LCP Q' (f k)) (L : List (Fin ρ)) :
    LCP Q' (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) := by
  induction L with
  | nil => exact lcp_id
  | cons a L ih => exact lcp_comp (hf a) ih
end PositivityTheory.Rg.Sw.SP
