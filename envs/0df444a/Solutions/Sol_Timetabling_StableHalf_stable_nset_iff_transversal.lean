-- Prove2me | solution 1 for Timetabling.StableHalf.stable_nset_iff_transversal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:19:58.700209+00:00
-- url     : https://prove2.me/submissions/17f35f2a-4c6c-4e9c-b135-0b23df42a032

import Mathlib
import Definitions.Def_Timetabling_StableHalf_IsStableTransversal

open Timetabling.StableHalf in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hM : ∀ j, G.Adj (j, true) (j, false)) :
    (∃ s, G.IsNIndepSet n s) ↔ ∃ c : Fin n → Bool, IsStableTransversal G c := by
  constructor
  · rintro ⟨s, hs⟩
    have hinj : Set.InjOn Prod.fst (s : Set (Fin n × Bool)) := by
      rintro ⟨j, b⟩ hx ⟨j', b'⟩ hy hxy
      simp only at hxy
      subst hxy
      by_contra hne
      have hbb : b ≠ b' := fun h => hne (by rw [h])
      cases b <;> cases b'
      · exact hbb rfl
      · exact hs.isIndepSet hx hy hne (hM j).symm
      · exact hs.isIndepSet hx hy hne (hM j)
      · exact hbb rfl
    have hcard : (s.image Prod.fst).card = n := by
      rw [Finset.card_image_of_injOn hinj, hs.card_eq]
    have huniv : s.image Prod.fst = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
    classical
    refine ⟨fun j => if (j, true) ∈ s then true else false, ?_⟩
    have hsub : (Set.range fun j => (j, if (j, true) ∈ s then true else false)) ⊆
        (s : Set (Fin n × Bool)) := by
      rintro _ ⟨j, rfl⟩
      have hj : j ∈ s.image Prod.fst := by rw [huniv]; exact Finset.mem_univ j
      obtain ⟨⟨j', b⟩, hb, hj'⟩ := Finset.mem_image.mp hj
      simp only at hj'
      subst hj'
      by_cases ht : (j', true) ∈ s
      · simp [ht]
      · simp only [ht, if_false, Finset.mem_coe]
        cases b
        · exact hb
        · exact absurd hb ht
    exact Set.Pairwise.mono hsub hs.isIndepSet
  · rintro ⟨c, hc⟩
    classical
    refine ⟨Finset.univ.image (fun j => (j, c j)), ⟨?_, ?_⟩⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact hc
    · rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ,
        Fintype.card_fin]
