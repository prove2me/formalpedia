-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.iterate_AT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:45.405822+00:00
-- url     : https://prove2.me/submissions/c88c516d-e8c5-47f2-8c13-c6b90d91c931

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

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
theorem _root_.solution {T : Fm n →ₗ[ℂ] Fm n} (hT : ∀ Q, Q ∈ AT n → T Q ∈ AT n) (N : ℕ) {Q : Fm n} (hQ : Q ∈ AT n) :
    T^[N] Q ∈ AT n := by
  induction N generalizing Q with
  | zero => exact hQ
  | succ N ih => rw [Function.iterate_succ_apply]; exact ih (hT Q hQ)
end PositivityTheory.Rg.Sw.SP
