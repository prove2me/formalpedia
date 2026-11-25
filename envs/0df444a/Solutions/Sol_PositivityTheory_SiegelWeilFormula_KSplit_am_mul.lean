-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.am_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:35.403015+00:00
-- url     : https://prove2.me/submissions/6ea97153-a9d8-4382-a86d-5cdee9ac4089

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_mstar_mul

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
theorem _root_.solution (b : Bool) (A B : Matrix (Fin m) (Fin m) ℂ) : am b (A * B) = am b A * am b B := by
  cases b <;> simp [am, mstar_mul]
end PositivityTheory.SiegelWeilFormula.KSplit
