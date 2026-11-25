-- Prove2me | solution 1 for PI.QnCovHatW.inj_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:25.540628+00:00
-- url     : https://prove2.me/submissions/1c8d7b02-36fb-4004-aa6a-76f624eed2e0

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
theorem _root_.solution {m : ℕ} (c : Fin m → Fin (m + 1)) (hc : Function.Injective c) :
    ∃ i : Fin (m + 1), ∃ σ : Equiv.Perm (Fin m), c = i.succAbove ∘ σ := by
  classical
  have hex : ∃ i, i ∉ Set.range c := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective c := fun y => h y
    have := Fintype.card_le_of_surjective c hs
    simp at this
  obtain ⟨i, hi⟩ := hex
  have hne : ∀ x, c x ≠ i := fun x hx => hi ⟨x, hx⟩
  choose f hf using fun x => Fin.exists_succAbove_eq (hne x)
  have finj : Function.Injective f := by
    intro x y hxy
    apply hc
    rw [← hf x, ← hf y, hxy]
  refine ⟨i, Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), ?_⟩
  funext x
  simp [hf]
end PI.QnCovHatW
