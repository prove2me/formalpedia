-- Prove2me | solution 1 for RoslingAssembly.total_lead_succ
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:08:17.423838+00:00
-- url     : https://prove2.me/submissions/3ce5fcf5-c4e0-4b8b-ac68-99b5443e2828

import Mathlib
import Definitions.Def_RoslingAssembly_Network_Ms
open RoslingAssembly

theorem solution{N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) :
    net.M ℓ i = ℓ i + net.Ms ℓ i := by
  have hlt : ∀ a b, Relation.TransGen (fun a b => net.s a = some b) a b → b < a := by
    intro a b h
    induction h with
    | single h => exact net.s_lt _ _ h
    | tail _ h ih => exact lt_trans (net.s_lt _ _ h) ih
  unfold Network.M Network.Ms
  rcases hs : net.s i with _ | j
  · have hA : net.A i = ∅ := by
      ext k
      simp only [Network.A, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      intro h
      obtain ⟨b, hb, _⟩ := Relation.TransGen.head'_iff.mp h
      rw [hs] at hb
      cases hb
    rw [hA, Finset.sum_empty]
  · have hA : net.A i = insert j (net.A j) := by
      ext k
      simp only [Network.A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        obtain ⟨b, hb, hrt⟩ := Relation.TransGen.head'_iff.mp h
        rw [hs] at hb
        cases hb
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrt with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · rintro (h | h)
        · subst h; exact Relation.TransGen.single hs
        · exact Relation.TransGen.head hs h
    have hnot : j ∉ net.A j := by
      simp only [Network.A, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact lt_irrefl _ (hlt _ _ h)
    rw [hA, Finset.sum_insert hnot]
    rfl
