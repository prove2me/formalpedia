-- Prove2me | solution 1 for PI.WGB.rename_tau_homog_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:12.745373+00:00
-- url     : https://prove2.me/submissions/6b54eb77-c9a7-4d50-bbcf-3aaad5df78f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_PI_WGB_weight_tau_B

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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ) (hg : IsWeightedHomogeneous (wnB n N) g m) :
    IsWeightedHomogeneous (wnB n N) (rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g)
      (fun j => m (σ j)) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  rw [weight_tau_B h σ hσ, hg hu]
end PI.WGB
