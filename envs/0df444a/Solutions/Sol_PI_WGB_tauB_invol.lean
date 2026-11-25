-- Prove2me | solution 1 for PI.WGB.tauB_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:17.146299+00:00
-- url     : https://prove2.me/submissions/18254d57-057f-4f12-b9b7-d9bed5cb4d83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_PI_WGB_tauB_val
import Theorems.Thm_PI_WGB_tauB_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a : Fin N) :
    tauB h σ (tauB h σ a) = a := by
  by_cases ha : a.1 < n
  · have h2 : (tauB h σ a).1 < n := by rw [tauB_val h σ a ha]; exact (σ _).isLt
    apply Fin.ext
    rw [tauB_val h σ _ h2]
    have e : (⟨(tauB h σ a).1, h2⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (tauB_val h σ a ha)
    rw [e, hσ]
  · rw [tauB_of_not h σ a ha, tauB_of_not h σ a ha]
end PI.WGB
