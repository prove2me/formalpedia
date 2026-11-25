-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.star_exp_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:25.360428+00:00
-- url     : https://prove2.me/submissions/edf68a85-cb0d-4164-b078-ff9b5dd4ca54

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
theorem _root_.solution (t : ℝ) : star (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
  rw [show star (Complex.exp (t * Complex.I)) = Complex.exp (-(t * Complex.I)) by
    rw [Complex.star_def, ← Complex.exp_conj]; simp [Complex.conj_ofReal], ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero]
end PositivityTheory.SiegelWeilFormula.KSplit
