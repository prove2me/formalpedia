-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.lf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:18.448748+00:00
-- url     : https://prove2.me/submissions/ddd2cbfd-febe-4f13-8757-8a2e04039586

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
theorem _root_.solution (b : Bool) (z : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    lf b (z • M) a i = z • lf b M a i := by
  simp [lf, C_mul', smul_smul, Finset.smul_sum]
end PositivityTheory.SiegelWeilFormula.KSplit
