-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.actU_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:32.403228+00:00
-- url     : https://prove2.me/submissions/27cdaa5a-be29-4b66-8b6b-6b2232d6b852

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_am_mul
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_lf

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
theorem _root_.solution (A B : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : actU A (actU B P) = actU (B * A) P := by
  have h : (actU (n := n) A).comp (actU B) = actU (B * A) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    rw [AlgHom.comp_apply, actU_X, actU_X, actU_lf, am_mul]
  exact congrArg (fun f : PX m n →ₐ[ℂ] PX m n => f P) h
end PositivityTheory.SiegelWeilFormula.KSplit
