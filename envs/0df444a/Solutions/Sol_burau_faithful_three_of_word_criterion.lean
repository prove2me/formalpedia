-- Prove2me | solution 1 for burau_faithful_three_of_word_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:18:23.177403+00:00
-- url     : https://prove2.me/submissions/e1305353-972b-405d-8927-10c7b0518067

import Theorems.Thm_BurauFaithful_burau_faithful_three
import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

namespace BurauFaithful

open BraidsLinksMCG

/-- The single braid relation for three strands, as a word in the free group on two generators. -/
def braidRel3_L213 : FreeGroup (Fin 2) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹

lemma braidRels_three_eq_singleton_L213 :
    braidRels 3 = {r | ∃ i j : Fin 2, (j : ℕ) = (i : ℕ) + 1 ∧
      r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
            (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹} := by
  ext r
  simp only [braidRels, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨i, j, h, rfl⟩ | h)
    · exfalso
      have hi : (i : ℕ) < 2 := i.isLt
      have hj : (j : ℕ) < 2 := j.isLt
      omega
    · exact h
  · exact Or.inr

lemma braidRels_three_subset_L213 :
    braidRels 3 ⊆ ({braidRel3_L213} : Set (FreeGroup (Fin 2))) := by
  intro r hr
  rw [braidRels_three_eq_singleton_L213] at hr
  obtain ⟨i, j, hij, rfl⟩ := hr
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  have hi0 : (i : ℕ) = 0 := by omega
  have hj1 : (j : ℕ) = 1 := by omega
  have hieq : i = (0 : Fin 2) := Fin.ext hi0
  have hjeq : j = (1 : Fin 2) := Fin.ext hj1
  subst hieq; subst hjeq
  simp [braidRel3_L213]

lemma singleton_subset_braidRels_three_L213 :
    ({braidRel3_L213} : Set (FreeGroup (Fin 2))) ⊆ braidRels 3 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rw [braidRels_three_eq_singleton_L213]
  exact ⟨0, 1, rfl, rfl⟩

/-- The normal closure of Artin's relations on three strands is the normal closure of the single braid
relation: `B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩`. -/
lemma normalClosure_braidRels_three_L213 :
    Subgroup.normalClosure (braidRels 3) =
      Subgroup.normalClosure ({braidRel3_L213} : Set (FreeGroup (Fin 2))) :=
  le_antisymm
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (braidRels_three_subset_L213 hx))
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (singleton_subset_braidRels_three_L213 hx))

end BurauFaithful

theorem solution
    (hc : ∀ w : FreeGroup (Fin 2),
      BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
        w ∈ Subgroup.normalClosure ({BurauFaithful.braidRel3_L213} : Set (FreeGroup (Fin 2)))) :
    Function.Injective (BurauFaithful.burauRep 3) :=
  BurauFaithful.burau_faithful_three
