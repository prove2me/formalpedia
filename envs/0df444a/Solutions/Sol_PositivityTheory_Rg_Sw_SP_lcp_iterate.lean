-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:57.531362+00:00
-- url     : https://prove2.me/submissions/7dc463d1-befa-45ce-adfa-69d976e438fb

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
theorem _root_.solution {Q' : Fm n} {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (N : ℕ) (R : Fm n) :
    T^[N] (Q' * R) = Q' * T^[N] R := by
  induction N generalizing R with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT R, ih]
end PositivityTheory.Rg.Sw.SP
