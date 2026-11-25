-- Prove2me | solution 1 for PI.Witt.witt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:49.916265+00:00
-- url     : https://prove2.me/submissions/3bfca936-6265-4f60-940f-7014dfa0a883

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Nondeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_EnlargeStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_WittOf
import Theorems.Thm_PI_Witt_enlarge_step
import Theorems.Thm_PI_Witt_nondeg_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
namespace PI.Witt
theorem _root_.solution (h1 : OneVector) (h2 : Anisotropic) : PI.WittExtension := by
  intro K V _ _ _ _ _ _ B hB hnd
  have key : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K V - Module.finrank K U = m →
      ∀ f : U →ₗ[K] V, Function.Injective f → (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro U hm f hinj hf
    by_cases hU : ∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0
    · obtain ⟨g, hg, hge, -⟩ := nondeg_extend h1 h2 B hB _ U rfl hU f hf
      exact ⟨g, hg, hge⟩
    · push Not at hU
      obtain ⟨r, hrU, hr, hr0⟩ := hU
      obtain ⟨U', hlt, f', hinj', hf', hext⟩ := enlarge_step B hB hnd U f hinj hf r hrU hr0 hr
      have h3 : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt hlt
      have h4 : Module.finrank K U' ≤ Module.finrank K V := Submodule.finrank_le U'
      obtain ⟨g, hg, hge⟩ := ih (Module.finrank K V - Module.finrank K U') (by omega) U' rfl f' hinj' hf'
      refine ⟨g, hg, fun x => ?_⟩
      rw [← hext x, ← hge]
  intro U f hinj hf
  exact key _ U rfl f hinj hf
end PI.Witt
