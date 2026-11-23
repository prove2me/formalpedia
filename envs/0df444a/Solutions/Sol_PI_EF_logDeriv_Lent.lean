-- Prove2me | solution 1 for PI.EF.logDeriv_Lent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:40.508451+00:00
-- url     : https://prove2.me/submissions/b303570a-aa2d-4715-95c2-b9786dd47b3e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_Lent_of_ne
import Theorems.Thm_PI_EF_Lent_eventuallyEq

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
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · have hd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inl hs)
    have he := Lent_eventuallyEq h hs
    have h1 : logDeriv (Lent χ) s = logDeriv (fun z => (z - 1) * LFunction χ z) s := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [he.deriv_eq, he.eq_of_nhds]
      rfl
    have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      simp [logDeriv_apply]
    have hdz : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const (1 : ℂ)
    rw [h1, logDeriv_mul (f := fun z : ℂ => z - 1) (g := LFunction χ) s
      (sub_ne_zero.mpr hs) h0 hdz hd, h2]
    simp only [del1, if_pos h]
    ring
  · rw [Lent_of_ne h]
    simp [del1, h]
end PI.EF
