-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.sum_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:27.993433+00:00
-- url     : https://prove2.me/submissions/11a09b1b-0c02-4f13-b026-1c1a75bf11da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (d : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.sum fun k e => (e : ℂ) * if k.2.2 then -d k.1 else d k.1) = ∑ a, d a * chg a s := by
  simp only [chg, Finsupp.sum, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.1 (fun b _ hb => by
    have : k.1 ≠ b := Ne.symm hb
    simp [this]) (by simp)]
  rcases k with ⟨a, i, b⟩
  cases b <;> simp [mul_comm]
end PositivityTheory.SiegelWeilFormula.KSplit
