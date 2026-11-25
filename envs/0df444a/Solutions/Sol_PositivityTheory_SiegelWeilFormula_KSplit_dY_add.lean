-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.dY_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:03.78123+00:00
-- url     : https://prove2.me/submissions/d74a99a9-3727-4b7a-89c3-f24891cf3e76

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lf_add

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
theorem _root_.solution (Y Y' : Matrix (Fin m) (Fin m) ℂ) : (dY (Y + Y') : Derivation ℂ (PX m n) (PX m n)) = dY Y + dY Y' := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, i, b⟩
  rw [Derivation.add_apply, dY_X, dY_X, dY_X, ← lf_add]
  congr 1
  cases b <;> simp [dm, add_comm]
end PositivityTheory.SiegelWeilFormula.KSplit
