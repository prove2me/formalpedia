-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:21.908153+00:00
-- url     : https://prove2.me/submissions/317da0d7-1fcc-46b2-8b12-7de04968c713

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_add

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
theorem _root_.solution {Q' : Fm n} {ι : Type*} (t : Finset ι) (T : ι → Fm n →ₗ[ℂ] Fm n) (hT : ∀ i ∈ t, LCP Q' (T i)) :
    LCP Q' (∑ i ∈ t, T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro R; simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact lcp_add (hT a (Finset.mem_insert_self a t)) (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))
end PositivityTheory.Rg.Sw.SP
