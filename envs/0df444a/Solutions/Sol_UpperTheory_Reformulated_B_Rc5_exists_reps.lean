-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Rc5.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:50.268365+00:00
-- url     : https://prove2.me/submissions/32b32fd7-ba0e-4aef-9d56-af613804c74d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsFurtherSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Rc5
theorem _root_.solution :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by
  intro α r hs _ t
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert y s _ ih =>
    obtain ⟨C, hC, h1, h2⟩ := ih
    by_cases h : ∃ c ∈ C, r y c
    · refine ⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr h
      · exact h2 x hx
    · refine ⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha
        · rcases Finset.mem_insert.1 hb with hb | hb
          · rw [ha, hb]
          · exact absurd ⟨b, hb, ha ▸ hab⟩ h
        · rcases Finset.mem_insert.1 hb with hb | hb
          · exact absurd ⟨a, ha, hb ▸ hs a b hab⟩ h
          · exact h1 a ha b hb hab
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact Or.inl (Finset.mem_insert.2 (Or.inl hx))
        · rcases h2 x hx with h3 | ⟨c, hc, h3⟩
          · exact Or.inl (Finset.mem_insert_of_mem h3)
          · exact Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩
end UpperTheory.Reformulated.B.Rc5
