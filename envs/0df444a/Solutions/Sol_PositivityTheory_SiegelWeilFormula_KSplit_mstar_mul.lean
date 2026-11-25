-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.mstar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:21.916896+00:00
-- url     : https://prove2.me/submissions/2682e085-e76a-4381-9ee3-52c909658f8e

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
theorem _root_.solution (A B : Matrix (Fin m) (Fin m) ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [mul_apply, star_sum]
end PositivityTheory.SiegelWeilFormula.KSplit
