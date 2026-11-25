-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.lf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:15.415102+00:00
-- url     : https://prove2.me/submissions/69f4ebda-b5a8-4c86-8385-876633088700

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
theorem _root_.solution (b : Bool) (M N : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    lf b (M + N) a i = lf b M a i + lf b N a i := by
  simp [lf, add_mul, Finset.sum_add_distrib]
end PositivityTheory.SiegelWeilFormula.KSplit
