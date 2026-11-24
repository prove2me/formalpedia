-- Prove2me | solution 1 for SensitivityPseudoforest.exists_three_coloring
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:47.198423+00:00
-- url     : https://prove2.me/submissions/703dab77-2b06-4aa9-89ed-2efb0b5a40bb

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Tauto

namespace SensitivityPseudoforest
end SensitivityPseudoforest


/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/
open SensitivityPseudoforest
open scoped Classical BigOperators
set_option autoImplicit false
variable {V : Type}

theorem solution (R : V → V → Prop) (hirr : ∀ v, ¬ R v v) :
    ∀ s : Finset V, (∀ v ∈ s, (neighbors R s v).card ≤ 2) →
      ∃ color : V → Fin 3, ∀ v ∈ s, ∀ w ∈ s, R v w → color v ≠ color w := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => 0, by simp⟩
  | @insert v s hv ih =>
    intro hdegree
    have hsmall : ∀ w ∈ s, (neighbors R s w).card ≤ 2 := by
      intro w hw
      apply (Finset.card_le_card ?_).trans (hdegree w (Finset.mem_insert_of_mem hw))
      exact Finset.filter_subset_filter _ (Finset.subset_insert _ _)
    obtain ⟨color, hcolor⟩ := ih hsmall
    let forbidden := (neighbors R s v).image color
    have hforbidden : forbidden.card < (Finset.univ : Finset (Fin 3)).card := by
      have hsub : neighbors R s v ⊆ neighbors R (insert v s) v :=
        Finset.filter_subset_filter _ (Finset.subset_insert _ _)
      have hbound := (Finset.card_image_le (f := color)).trans
        ((Finset.card_le_card hsub).trans (hdegree v (Finset.mem_insert_self _ _)))
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le hbound
    obtain ⟨fresh, _, hfresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hforbidden
    refine ⟨Function.update color v fresh, ?_⟩
    intro a ha b hb hab
    by_cases haeq : a = v
    · subst a
      have hbne : b ≠ v := by intro h; exact hirr v (h ▸ hab)
      rw [Function.update_self, Function.update_of_ne hbne]
      intro heq
      apply hfresh
      apply Finset.mem_image.mpr
      exact ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_of_mem_insert_of_ne hb hbne, Or.inl hab⟩, heq.symm⟩
    · by_cases hbeq : b = v
      · subst b
        rw [Function.update_of_ne haeq, Function.update_self]
        intro heq
        apply hfresh
        apply Finset.mem_image.mpr
        exact ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_of_mem_insert_of_ne ha haeq, Or.inr hab⟩, heq⟩
      · rw [Function.update_of_ne haeq, Function.update_of_ne hbeq]
        exact hcolor a (Finset.mem_of_mem_insert_of_ne ha haeq)
          b (Finset.mem_of_mem_insert_of_ne hb hbeq) hab
