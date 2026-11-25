-- Prove2me | solution 1 for PI.ScPiFrameW.frame_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:43:02.03683+00:00
-- url     : https://prove2.me/submissions/61b8cf80-2daf-4fee-b2b8-407bb3c49a90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_PosOfPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameCore
import Theorems.Thm_PI_ScPiFrameW_gs_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
  have key : ∀ m, m ≤ k → ∃ w : Fin m → Fin n → ℂ,
      (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨w, h1, h2⟩ := ih (by omega)
      exact gs_step ε hn σ hσ e f z t ht hee hff hef hez hfz hzz m (by omega) w h1 h2
  exact key k le_rfl
end PI.ScPiFrameW
