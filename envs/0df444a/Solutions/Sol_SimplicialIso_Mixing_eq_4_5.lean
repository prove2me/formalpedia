-- Prove2me | solution 1 for SimplicialIso.Mixing.eq_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:13:38.961351+00:00
-- url     : https://prove2.me/submissions/96bb0cac-8054-4924-bb30-bfb2650a0afa

import Definitions.Def_SimplicialIso_Mixing_DeltaForms

set_option backward.isDefEq.respectTransparency false

open Finset SimplicialIso.Mixing
open scoped InnerProductSpace

noncomputable section

namespace SimplicialDeltaNorm

abbrev Choices {n d : ℕ} (B : Fin d → Finset (Fin n)) := (i : Fin d) → {v // v ∈ B i}

abbrev Transversal {n d : ℕ} (B : Fin d → Finset (Fin n)) :=
  {σ : Cell n d // ∀ i, (σ.val ∩ B i).card = 1}

lemma choice_injective {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (q : Choices B) :
    Function.Injective (fun i => (q i).val) := by
  intro i j hij
  change (q i).val = (q j).val at hij
  by_contra hne
  exact Finset.disjoint_left.mp (hB hne) (q i).property (by rw [hij]; exact (q j).property)

lemma choice_card {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (q : Choices B) :
    (univ.image (fun i => (q i).val)).card = d := by
  classical
  rw [Finset.card_image_of_injective _ (choice_injective B hB q)]
  simp

lemma choice_inter {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (q : Choices B) (i : Fin d) :
    univ.image (fun j => (q j).val) ∩ B i = {(q i).val} := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    have hji : j = i := by
      by_contra hji
      exact Finset.disjoint_left.mp (hB hji) (q j).property (Finset.mem_inter.mp hv).2
    subst j
    exact Finset.mem_singleton_self _
  · intro hv
    have he := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      (q i).property⟩

def choiceToTransversal {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (q : Choices B) : Transversal B := by
  classical
  refine ⟨⟨univ.image (fun i => (q i).val), choice_card B hB q⟩, ?_⟩
  intro i
  rw [choice_inter B hB q i]
  simp

lemma card_transversal {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Fintype.card (Transversal B) = ∏ i, (B i).card := by
  classical
  have hinj : Function.Injective (choiceToTransversal B hB) := by
    intro p q h
    funext i
    apply Subtype.ext
    have hi := congrArg (fun σ : Transversal B => σ.val.val ∩ B i) h
    change univ.image (fun j => (p j).val) ∩ B i =
      univ.image (fun j => (q j).val) ∩ B i at hi
    rw [choice_inter B hB p i, choice_inter B hB q i] at hi
    exact Finset.singleton_inj.mp hi
  have hsurj : Function.Surjective (choiceToTransversal B hB) := by
    intro σ
    have hex (i : Fin d) : ∃ v, v ∈ σ.val.val ∧ v ∈ B i := by
      have hc : 0 < (σ.val.val ∩ B i).card := by rw [σ.property i]; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hc
      exact ⟨v, Finset.mem_inter.mp hv⟩
    choose q hqσ hqB using hex
    let p : Choices B := fun i => ⟨q i, hqB i⟩
    have hs : univ.image (fun i => (p i).val) = σ.val.val := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact hqσ i
      · rw [choice_card B hB p, σ.val.property]
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hs
  have hc := Fintype.card_congr (Equiv.ofBijective (choiceToTransversal B hB) ⟨hinj, hsurj⟩)
  rw [← hc]
  simp [Choices, Fintype.card_pi]

theorem delta_norm {n d : ℕ} (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ‖delta B‖ = Real.sqrt (∏ i, ((B i).card : ℝ)) := by
  classical
  have hsq (σ : Cell n d) : (delta B σ) ^ 2 =
      if ∀ i, (σ.val ∩ B i).card = 1 then (1 : ℝ) else 0 := by
    change (if ∀ i, (σ.val ∩ B i).card = 1 then (-1 : ℝ) ^ invCount B σ.val else 0) ^ 2 = _
    split_ifs
    · rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    · norm_num
  have hn : ‖delta B‖ ^ 2 = (Fintype.card (Transversal B) : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hsq]
    simp [Transversal, Fintype.card_subtype]
  rw [card_transversal B hB, Nat.cast_prod] at hn
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

end SimplicialDeltaNorm

theorem solution (n d : ℕ) (hd : 1 ≤ d) (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ‖delta B‖ = Real.sqrt (∏ i, ((B i).card : ℝ)) :=
  SimplicialDeltaNorm.delta_norm B hB

#print axioms solution
