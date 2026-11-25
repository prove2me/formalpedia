-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.actU_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:38.251028+00:00
-- url     : https://prove2.me/submissions/b195c599-4a0c-4045-ae5d-b6cffac1cef5

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
theorem _root_.solution (P : PX m n) : actU 1 P = P := by
  have h : actU (n := n) (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    cases b <;> simp [actU, one_apply]
  rw [h]; rfl
end PositivityTheory.SiegelWeilFormula.KSplit
