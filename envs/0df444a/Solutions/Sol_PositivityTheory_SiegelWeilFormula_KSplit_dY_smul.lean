-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.dY_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:02.080266+00:00
-- url     : https://prove2.me/submissions/91f907f2-bd6a-4af0-877d-29236fb25e4f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lf_smul

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
theorem _root_.solution (z : ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : (dY (z • Y) : Derivation ℂ (PX m n) (PX m n)) = z • dY Y := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, i, b⟩
  rw [Derivation.smul_apply, dY_X, dY_X, ← lf_smul]
  congr 1
  cases b <;> simp [dm]
end PositivityTheory.SiegelWeilFormula.KSplit
