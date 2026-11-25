-- Prove2me | solution 1 for PI.EF.analyticOrderAt_LFunction_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:03.263146+00:00
-- url     : https://prove2.me/submissions/4a31ad68-e666-4740-8964-c27c6d9cff06

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_analyticOnNhd_LFunction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1) : analyticOrderAt (LFunction χ) s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have hz := (analyticOnNhd_LFunction χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs htop
  have h2 := hz (show (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by norm_num)
  exact LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num) h2
end PI.EF
