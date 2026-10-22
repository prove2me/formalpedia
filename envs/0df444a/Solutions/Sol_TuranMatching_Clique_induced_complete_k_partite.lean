-- Prove2me | solution 1 for TuranMatching.Clique.induced_complete_k_partite
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:43:40.076807+00:00
-- url     : https://prove2.me/submissions/93088565-c9b4-45b8-acfe-8ed4e97fd323

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

set_option autoImplicit false
open Finset SimpleGraph
open TuranMatching.Clique

theorem tmk_induced (n k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree (k + 1)) (B : Finset (Fin n))
    (hsame : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v → G.neighborSet u = G.neighborSet v) :
    ∃ cls : Fin n → Fin k, ∀ u ∈ B, ∀ v ∈ B, G.Adj u v ↔ cls u ≠ cls v := by
  classical
  let S : Setoid {v // v ∈ B} :=
    ⟨fun u v => u = v ∨ ¬ G.Adj u.1 v.1,
      ⟨fun u => Or.inl rfl,
       fun {u v} h => by
         rcases h with h | h
         · exact Or.inl h.symm
         · exact Or.inr (fun h' => h h'.symm),
       fun {u v w} huv hvw => by
         rcases huv with huv | huv
         · subst huv; exact hvw
         · rcases hvw with hvw | hvw
           · subst hvw; exact Or.inr huv
           · by_cases huw : u = w
             · exact Or.inl huw
             · right
               intro hadj
               have h1 := hsame u.1 u.2 v.1 v.2 huv
               have : w.1 ∈ G.neighborSet v.1 := by
                 rw [← h1]; exact hadj
               exact hvw this⟩⟩
  have hcard : Fintype.card (Quotient S) ≤ k := by
    by_contra h
    push Not at h
    let rep : Quotient S → {v // v ∈ B} := Quotient.out
    let T : Finset (Fin n) := Finset.univ.image (fun q => (rep q).1)
    have hinj : Function.Injective (fun q : Quotient S => (rep q).1) := by
      intro q1 q2 h12
      have : rep q1 = rep q2 := Subtype.ext h12
      rw [← Quotient.out_eq q1, ← Quotient.out_eq q2]
      exact congrArg _ this
    have hT : T.card = Fintype.card (Quotient S) := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have hcl : G.IsClique (T : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
      obtain ⟨q1, rfl⟩ := ha
      obtain ⟨q2, rfl⟩ := hb
      have hq : q1 ≠ q2 := fun h => hab (by rw [h])
      by_contra hna
      apply hq
      have hr : S.r (rep q1) (rep q2) := Or.inr hna
      have : Quotient.mk S (rep q1) = Quotient.mk S (rep q2) := Quotient.sound hr
      simpa [rep] using this
    obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq (s := T) (n := k + 1) (by omega)
    exact hK T' ⟨hcl.subset (by exact_mod_cast hT'sub), hT'card⟩
  let e : Quotient S ≃ Fin (Fintype.card (Quotient S)) := Fintype.equivFin _
  let cls : Fin n → Fin k := fun v =>
    if hv : v ∈ B then Fin.castLE hcard (e (Quotient.mk S ⟨v, hv⟩)) else ⟨0, by omega⟩
  refine ⟨cls, ?_⟩
  intro u hu v hv
  have key : cls u ≠ cls v ↔ ¬ (Quotient.mk S ⟨u, hu⟩ = Quotient.mk S ⟨v, hv⟩) := by
    simp only [cls, hu, hv, dite_true]
    rw [ne_eq, Fin.castLE_inj, e.apply_eq_iff_eq]
  rw [key]
  constructor
  · intro hadj heq
    have := Quotient.exact heq
    rcases this with h | h
    · have : u = v := congrArg Subtype.val h
      exact G.loopless.irrefl _ (this ▸ hadj)
    · exact h hadj
  · intro h
    by_contra hna
    apply h
    apply Quotient.sound
    by_cases huv : u = v
    · left; exact Subtype.ext huv
    · right; exact hna

theorem solution (n k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree (k + 1)) (B : Finset (Fin n))
    (hsame : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v → G.neighborSet u = G.neighborSet v) :
    ∃ cls : Fin n → Fin k, ∀ u ∈ B, ∀ v ∈ B, G.Adj u v ↔ cls u ≠ cls v :=
  tmk_induced n k hk G hK B hsame
