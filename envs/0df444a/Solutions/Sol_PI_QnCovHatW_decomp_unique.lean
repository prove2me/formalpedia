-- Prove2me | solution 1 for PI.QnCovHatW.decomp_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:17.876538+00:00
-- url     : https://prove2.me/submissions/62fb7300-9d0c-46f3-b185-f70b79cefdeb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution {m : ℕ} {i i' : Fin (m + 1)} {σ σ' : Equiv.Perm (Fin m)}
    (h : i.succAbove ∘ σ = i'.succAbove ∘ σ') : i = i' ∧ σ = σ' := by
  have hi : i = i' := by
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    have hh := congrFun h (σ'.symm z)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at hh
    rw [hz] at hh
    exact Fin.succAbove_ne _ _ hh
  subst hi
  exact ⟨rfl, Equiv.ext fun x => Fin.succAbove_right_injective (congrFun h x)⟩
end PI.QnCovHatW
