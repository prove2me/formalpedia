-- Prove2me | solution 1 for UnderstandingML.growth_composition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:03:58.931408+00:00
-- url     : https://prove2.me/submissions/7e0d9d70-bfda-4c62-9098-8306018faabf

import Mathlib
import Definitions.Def_UnderstandingML_NeuralNetworks

set_option autoImplicit false

open MeasureTheory

theorem uml_ncard_restr_le_growth {X Y : Type*} [Finite Y] (H : Set (X → Y)) (m : ℕ)
    (C : Finset X) (hC : C.card ≤ m) :
    (UnderstandingML.restrictionY H C).ncard ≤ UnderstandingML.growthY H m := by
  unfold UnderstandingML.growthY
  refine le_csSup ?_ ⟨C, hC, rfl⟩
  refine ⟨(Nat.card Y + 1) ^ m, ?_⟩
  rintro k ⟨C', hC', rfl⟩
  calc (UnderstandingML.restrictionY H C').ncard
      ≤ (Set.univ : Set (C' → Y)).ncard := Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = Nat.card Y ^ C'.card := by
        rw [Set.ncard_univ, Nat.card_fun]
        simp [Nat.card_eq_fintype_card]
    _ ≤ (Nat.card Y + 1) ^ C'.card := Nat.pow_le_pow_left (Nat.le_succ _) _
    _ ≤ (Nat.card Y + 1) ^ m := Nat.pow_le_pow_right (Nat.succ_pos _) hC'

open MeasureTheory UnderstandingML in
theorem solution {X Z Y : Type*} [Finite Z] [Finite Y] (F₁ : Set (X → Z))
    (F₂ : Set (Z → Y)) (m : ℕ) :
    growthY (compositionClass F₂ F₁) m ≤ growthY F₂ m * growthY F₁ m := by
  classical
  have key : ∀ C : Finset X, C.card ≤ m →
      (restrictionY (compositionClass F₂ F₁) C).ncard ≤ growthY F₂ m * growthY F₁ m := by
    intro C hC
    have hR₁ : (restrictionY F₁ C).Finite := Set.toFinite _
    let D : (C → Z) → Finset Z := fun u => Finset.univ.image u
    have hD : ∀ (u : C → Z) (c : C), u c ∈ D u :=
      fun u c => Finset.mem_image_of_mem u (Finset.mem_univ c)
    let T : (C → Z) → Set (C → Y) := fun u =>
      (fun w : (D u → Y) => fun c => w ⟨u c, hD u c⟩) '' restrictionY F₂ (D u)
    have hsub : restrictionY (compositionClass F₂ F₁) C ⊆ ⋃ u ∈ hR₁.toFinset, T u := by
      rintro g ⟨h, ⟨f₁, hf₁, f₂, hf₂, rfl⟩, hg⟩
      refine Set.mem_iUnion₂.mpr ⟨fun c => f₁ c,
        (Set.Finite.mem_toFinset _).mpr ⟨f₁, hf₁, fun c => rfl⟩, ?_⟩
      refine ⟨fun z => f₂ z, ⟨f₂, hf₂, fun z => rfl⟩, ?_⟩
      funext c
      exact (hg c).symm
    have hT : ∀ u, (T u).ncard ≤ growthY F₂ m := by
      intro u
      refine (Set.ncard_image_le (Set.toFinite _)).trans
        (uml_ncard_restr_le_growth F₂ m (D u) ?_)
      exact Finset.card_image_le.trans (by simpa using hC)
    calc (restrictionY (compositionClass F₂ F₁) C).ncard
        ≤ (⋃ u ∈ hR₁.toFinset, T u).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ∑ u ∈ hR₁.toFinset, (T u).ncard := Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ u ∈ hR₁.toFinset, growthY F₂ m := Finset.sum_le_sum fun u _ => hT u
      _ = (restrictionY F₁ C).ncard * growthY F₂ m := by
          rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ hR₁]
      _ ≤ growthY F₁ m * growthY F₂ m :=
          Nat.mul_le_mul_right _ (uml_ncard_restr_le_growth F₁ m C hC)
      _ = growthY F₂ m * growthY F₁ m := Nat.mul_comm _ _
  show sSup {k | ∃ C : Finset X, C.card ≤ m ∧
    (restrictionY (compositionClass F₂ F₁) C).ncard = k} ≤ _
  refine csSup_le ⟨_, ∅, by simp, rfl⟩ ?_
  rintro k ⟨C, hC, rfl⟩
  exact key C hC
