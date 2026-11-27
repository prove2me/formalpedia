-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.hOp_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:00.54753+00:00
-- url     : https://prove2.me/submissions/e3dfdfe8-4175-4759-8f09-f7e92212c537

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_dY
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_hOp_eq

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
theorem _root_.solution (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P) (c : ℝ)
    (a b : Fin m) (P : PX m n) : Λ (hOp (fun _ => true) c a b P) = 0 := by
  rw [hOp_eq]; exact kill_dY Λ hΛ _ P
end PositivityTheory.SiegelWeilFormula.KSplit
