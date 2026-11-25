-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.chg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:41.890991+00:00
-- url     : https://prove2.me/submissions/91cdaaff-da5e-4988-89ac-6f95cf29939b

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
theorem _root_.solution (a : Fin m) (k : Fin m × Fin n × Bool) (e : ℕ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    chg a (Finsupp.single k e + s) = (if k.1 = a then (if k.2.2 then -(e : ℤ) else e) else 0) + chg a s := by
  unfold chg
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> push_cast <;> ring),
    Finsupp.sum_single_index (by simp)]
end PositivityTheory.SiegelWeilFormula.KSplit
