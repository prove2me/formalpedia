-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.kill_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:32.354134+00:00
-- url     : https://prove2.me/submissions/3073f996-9e4e-40d0-a23f-c62647a32d92

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_dY_actU
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_diag

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
theorem _root_.solution (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (H : Matrix (Fin m) (Fin m) ℂ) (hH : H.IsHermitian) (P : PX m n) : Λ (dY H P) = 0 := by
  set U := hH.eigenvectorUnitary
  have e := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at e
  have hs : star (U : Matrix (Fin m) (Fin m) ℂ) ∈ unitaryGroup (Fin m) ℂ := Unitary.star_mem U.2
  have e2 : H = star (star (U : Matrix (Fin m) (Fin m) ℂ)) * diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
      star (U : Matrix (Fin m) (Fin m) ℂ) := by rw [star_star]; exact e
  rw [e2, ← actU_dY_actU _ hs, hΛ _ hs]
  exact kill_diag Λ hΛ _ _
end PositivityTheory.SiegelWeilFormula.KSplit
