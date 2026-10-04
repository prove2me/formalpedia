-- Prove2me | solution 1 for TheoryOfGames.Acyclic.acyclic_iff_strictlyAcyclic_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:18:56.209983+00:00
-- url     : https://prove2.me/submissions/62c34cb6-83bf-44a3-8e56-be619468e7f0

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

set_option autoImplicit false

open TheoryOfGames.Acyclic in
theorem solution {α : Type*} (D : Set α) (S : α → α → Prop) :
    (IsStrictlyAcyclic D S → IsAcyclic D S) ∧
      (D.Finite → (IsAcyclic D S ↔ IsStrictlyAcyclic D S)) := by
  have h1 : IsStrictlyAcyclic D S → IsAcyclic D S := by
    intro hs m hm x hD hxm hS
    apply hs
    refine ⟨fun n => x (n % m), fun n => hD _ (Nat.mod_lt _ hm), fun n => ?_⟩
    have hlt : n % m < m := Nat.mod_lt _ hm
    by_cases h : n % m + 1 < m
    · have : (n + 1) % m = n % m + 1 := by
        rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt h]
      simp only [this]
      exact hS _ hlt
    · have he : n % m + 1 = m := by omega
      have : (n + 1) % m = 0 := by
        rw [← Nat.mod_add_mod, he, Nat.mod_self]
      simp only [this]
      have := hS _ hlt
      rw [he, hxm] at this
      exact this
  refine ⟨h1, fun hfin => ⟨fun ha => ?_, h1⟩⟩
  rintro ⟨y, hyD, hyS⟩
  have hmaps : Set.MapsTo y Set.univ D := fun n _ => hyD n
  obtain ⟨i, -, j, -, hij, hyij⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hfin
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hyij.symm (by omega)
  refine ha (j - i) (by omega) (fun k => y (i + k)) (fun k _ => hyD _) ?_ (fun k _ => ?_)
  · simp only [Nat.add_zero]
    rw [Nat.add_sub_cancel' hlt.le]; exact hyij.symm
  · simpa [Nat.add_assoc] using hyS (i + k)
