-- Prove2me | solution 1 for SensitivityCampaign.finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-15T18:22:22.381034+00:00
-- url     : https://prove2.me/submissions/15dea0b2-cc95-4735-a564-6a71bbd8be32

import Mathlib
import Definitions.Def_SensitivityCampaign
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096


-- Reused in full from OpenAI, Basic.lean

namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

@[simp] theorem flip_empty (x : I → Bool) : flip x ∅ = x := by
  funext i
  simp [flip]

@[simp] theorem flip_singleton_self (x : I → Bool) (i : I) :
    flip x {i} i = !(x i) := by
  simp [flip]

theorem flip_singleton_other (x : I → Bool) {i j : I} (h : j ≠ i) :
    flip x {i} j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip (x : I → Bool) (B : Finset I) : flip (flip x B) B = x := by
  funext i
  by_cases h : i ∈ B <;> simp [flip, h]

theorem flip_insert (x : I → Bool) (i : I) (B : Finset I) (hi : i ∉ B) :
    flip x (insert i B) = flip (flip x B) {i} := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flip, hi]
  · simp [flip, hji]

theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]

@[simp] theorem flip_false (B : Finset I) (i : I) :
    flip (fun _ => false) B i = decide (i ∈ B) := by
  by_cases h : i ∈ B <;> simp [flip, h]

section Finite

variable [Fintype I]

theorem flip_differences (x y : I → Bool) :
    flip x (Finset.univ.filter fun i => x i ≠ y i) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [flip, hx, hy]

theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem sensitivityAt_eq_zero_iff (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x = 0 ↔ ∀ i, f (flip x {i}) = f x := by
  simp [sensitivityAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem sensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool) (i : I)
    (hi : f (flip x {i}) ≠ f x) : 0 < sensitivityAt f x :=
  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem exists_sensitivityAt_eq (f : (I → Bool) → Bool) :
    ∃ x, sensitivityAt f x = sensitivity f := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (I → Bool)) (by simp) (sensitivityAt f)
  exact ⟨x, hx.symm⟩

theorem blockSensitivityAt_le_blockSensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem blockSensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, blockSensitivityAt f x ≤ n) : blockSensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem le_blockSensitivityAt (f : (I → Bool) → Bool) (x : I → Bool)
    (blocks : Finset (Finset I))
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B)
    (hb : ∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) :
    blocks.card ≤ blockSensitivityAt f x := by
  have h := Finset.le_sup (s := (Finset.univ : Finset (Finset (Finset I))))
    (f := fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0) (Finset.mem_univ blocks)
  have hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := ⟨hd, hb⟩
  simpa only [blockSensitivityAt, if_pos hv] using h

theorem blockSensitivityAt_le (f : (I → Bool) → Bool) (x : I → Bool) {n : ℕ}
    (h : ∀ blocks : Finset (Finset I),
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) →
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) → blocks.card ≤ n) :
    blockSensitivityAt f x ≤ n := by
  apply Finset.sup_le
  intro blocks _
  split_ifs with hb
  · exact h blocks hb.1 hb.2
  · exact Nat.zero_le _

theorem exists_blockSensitivityAt_family (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ blocks : Finset (Finset I), blocks.card = blockSensitivityAt f x ∧
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := by
  obtain ⟨blocks, _, hb⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Finset (Finset I))) (by simp)
    (fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0)
  by_cases hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
  · exact ⟨blocks, by simpa only [blockSensitivityAt, if_pos hv] using hb.symm, hv⟩
  · have hz : blockSensitivityAt f x = 0 := by
      simpa only [blockSensitivityAt, if_neg hv] using hb
    exact ⟨∅, by simp [hz], by simp, by simp⟩

theorem le_blockSensitivityAt_of_family [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by
  have hinj : Function.Injective blocks := by
    intro k l hkl
    by_contra hnekl
    obtain ⟨i, hi⟩ := hne k
    exact Finset.disjoint_left.mp (hd hnekl) hi (by simpa [← hkl] using hi)
  have hcard := le_blockSensitivityAt f x (Finset.univ.image blocks)
    (by
      intro A hA B hB hAB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
      exact hd (fun h => hAB (congrArg blocks h)))
    (by
      intro B hB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨hne k, hb k⟩)
  simpa only [sensitivityAt, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hcard

theorem eq_of_singleton_invariant (f : (I → Bool) → Bool)
    (h : ∀ x i, f (flip x {i}) = f x) (x y : I → Bool) : f x = f y := by
  have hflip (B : Finset I) : f (flip x B) = f x := by
    induction B using Finset.induction with
    | empty => simp
    | @insert i B hi ih => rw [flip_insert x i B hi, h, ih]
  rw [← flip_differences x y, hflip]

theorem sensitivity_pos_of_nonconstant (f : (I → Bool) → Bool)
    (h : ∃ x y, f x ≠ f y) : 0 < sensitivity f := by
  by_contra hn
  have hz : sensitivity f = 0 := Nat.eq_zero_of_not_pos hn
  have hi (x : I → Bool) (i : I) : f (flip x {i}) = f x := by
    apply (sensitivityAt_eq_zero_iff f x).mp _ i
    exact Nat.eq_zero_of_le_zero ((sensitivityAt_le_sensitivity f x).trans_eq hz)
  obtain ⟨x, y, hxy⟩ := h
  exact hxy (eq_of_singleton_invariant f hi x y)

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Composition.lean

namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}

def compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    (I × J → Bool) → Bool :=
  fun x => f (fun i => g (fun j => x (i, j)))

theorem compose_flip_sensitive_iff (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) (i : I) (j : J) :
    compose f g (flip x {(i, j)}) ≠ compose f g x ↔
      g (flip (fun a => x (i, a)) {j}) ≠ g (fun a => x (i, a)) ∧
      f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
        f (fun k => g (fun a => x (k, a))) := by
  by_cases hg : g (flip (fun a => x (i, a)) {j}) = g (fun a => x (i, a))
  · have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        fun k => g (fun a => x (k, a)) := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, hg]
      · rw [flip_prod_other x j hk]
    simp only [compose, he, ne_eq, not_true_eq_false, hg, false_and]
  · have hn : g (flip (fun a => x (i, a)) {j}) = !(g (fun a => x (i, a))) := by
      cases h₁ : g (flip (fun a => x (i, a)) {j}) <;>
        cases h₂ : g (fun a => x (i, a)) <;> simp_all
    have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        flip (fun k => g (fun a => x (k, a))) {i} := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, flip_singleton_self, hn]
      · rw [flip_prod_other x j hk, flip_singleton_other _ hk]
    simp only [compose, he, ne_eq, hg, not_false_eq_true, true_and]

theorem compose_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = f (fun _ => false) := by
  simp [compose, hg]

theorem compose_flip_product_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (C : Finset I) (D : Finset J) (hg : g (fun _ => false) = false)
    (hD : g (flip (fun _ => false) D) ≠ g (fun _ => false)) :
    compose f g (flip (fun _ => false) (C ×ˢ D)) = f (flip (fun _ => false) C) := by
  have hD' : g (flip (fun _ => false) D) = true := by
    cases he : g (flip (fun _ => false) D) <;> simp_all
  apply congrArg f
  funext i
  by_cases hi : i ∈ C
  · have he : (fun j => flip (fun _ => false) (C ×ˢ D) (i, j)) =
        flip (fun _ => false) D := by
      funext j
      simp [flip, hi]
    rw [he, hD']
    simp [flip, hi]
  · have he : (fun j => flip (fun _ => false) (C ×ˢ D) (i, j)) =
        fun _ => false := by
      funext j
      simp [flip, hi]
    rw [he, hg]
    simp [flip, hi]

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) :
    sensitivityAt (compose f g) x =
      ∑ i ∈ Finset.univ.filter (fun i =>
        f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
          f (fun k => g (fun a => x (k, a)))),
        sensitivityAt g (fun a => x (i, a)) := by
  simp only [sensitivityAt, Finset.card_eq_sum_ones, Finset.sum_filter,
    compose_flip_sensitive_iff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
      f (fun k => g (fun a => x (k, a)))
  · simp [hi]
  · simp [hi]

theorem sensitivity_compose_le (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    sensitivity (compose f g) ≤ sensitivity f * sensitivity g := by
  apply sensitivity_le
  intro x
  rw [sensitivityAt_compose]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
          f (fun k => g (fun a => x (k, a)))), sensitivity g :=
      Finset.sum_le_sum fun i _ => sensitivityAt_le_sensitivity g _
    _ = sensitivityAt f (fun k => g (fun a => x (k, a))) * sensitivity g := by
      simp [sensitivityAt]
    _ ≤ sensitivity f * sensitivity g :=
      Nat.mul_le_mul_right _ (sensitivityAt_le_sensitivity f _)

theorem blockSensitivityAt_compose_zero_le (f : (I → Bool) → Bool)
    (g : (J → Bool) → Bool) (hg : g (fun _ => false) = false) :
    blockSensitivityAt f (fun _ => false) * blockSensitivityAt g (fun _ => false) ≤
      blockSensitivityAt (compose f g) (fun _ => false) := by
  obtain ⟨S, hS, hdS, hbS⟩ := exists_blockSensitivityAt_family f (fun _ => false)
  obtain ⟨T, hT, hdT, hbT⟩ := exists_blockSensitivityAt_family g (fun _ => false)
  have h := le_blockSensitivityAt_of_family (compose f g) (fun _ => false)
    (fun p : S × T => p.1.val ×ˢ p.2.val)
    (by
      intro p
      obtain ⟨i, hi⟩ := (hbS p.1.val p.1.property).1
      obtain ⟨j, hj⟩ := (hbT p.2.val p.2.property).1
      exact ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩⟩)
    (by
      intro p q hpq
      apply Finset.disjoint_left.mpr
      intro a ha hq
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp ha
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
      by_cases hs : p.1 = q.1
      · have ht : p.2.val ≠ q.2.val := by
          intro h
          exact hpq (Prod.ext hs (Subtype.ext h))
        exact Finset.disjoint_left.mp (hdT _ p.2.property _ q.2.property ht) ha₂ hq₂
      · have hs' : p.1.val ≠ q.1.val := fun h => hs (Subtype.ext h)
        exact Finset.disjoint_left.mp (hdS _ p.1.property _ q.1.property hs') ha₁ hq₁)
    (by
      intro p
      rw [compose_flip_product_zero f g _ _ hg (hbT p.2.val p.2.property).2,
        compose_zero f g hg]
      exact (hbS p.1.val p.1.property).2)
  simpa only [Fintype.card_prod, Fintype.card_coe, hS, hT] using h

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Reindex.lean

namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}

def reindex (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => flip x (B.map e.toEmbedding) (e i)) =
      flip (fun i => x (e i)) B := by
  funext i
  simp [flip]

theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => flip x {e i} (e a)) = flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}

@[simp] theorem reindex_symm (e : I ≃ J) (f : (I → Bool) → Bool) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => flip x (B.val.map e.toEmbedding) (e i)) ≠ _
      rw [flip_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x

theorem blockSensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    blockSensitivity (reindex e f) = blockSensitivity f := by
  apply Nat.le_antisymm
  · apply blockSensitivity_le
    intro x
    rw [blockSensitivityAt_reindex]
    exact blockSensitivityAt_le_blockSensitivity f _
  · apply blockSensitivity_le
    intro x
    have h := blockSensitivityAt_le_blockSensitivity (reindex e f) (fun j => x (e.symm j))
    rw [blockSensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Or.lean

namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]

def orBits (x : K → Bool) : Bool := decide (∃ k, x k = true)

@[simp] theorem orBits_eq_true (x : K → Bool) : orBits x = true ↔ ∃ k, x k = true := by
  simp [orBits]

@[simp] theorem orBits_eq_false (x : K → Bool) : orBits x = false ↔ ∀ k, x k = false := by
  simp [orBits]

@[simp] theorem orBits_zero : orBits (fun _ : K => false) = false := by
  simp [orBits]

theorem orBits_flip_of_witness (x : K → Bool) {i j : K}
    (hji : j ≠ i) (hj : x j = true) : orBits (flip x {i}) = orBits x := by
  have h₁ : orBits x = true := (orBits_eq_true x).mpr ⟨j, hj⟩
  have h₂ : orBits (flip x {i}) = true :=
    (orBits_eq_true _).mpr ⟨j, by rw [flip_singleton_other x hji, hj]⟩
  exact h₂.trans h₁.symm

def orCopies (f : (I → Bool) → Bool) : (K × I → Bool) → Bool := compose orBits f

theorem orCopies_zero (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false) :
    orCopies (K := K) f (fun _ => false) = false := by
  rw [orCopies, compose_zero _ _ hf, orBits_zero]

variable [Fintype I]

theorem sensitivity_orCopies_le (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by
  apply sensitivity_le
  intro x
  change sensitivityAt (compose orBits f) x ≤ _
  rw [sensitivityAt_compose]
  let y : K → Bool := fun k => f (fun a => x (k, a))
  let s : Finset K := Finset.univ.filter fun i => orBits (flip y {i}) ≠ orBits y
  change (∑ i ∈ s, sensitivityAt f (fun a => x (i, a))) ≤ _
  by_cases hy : orBits y = false
  · have hall := (orBits_eq_false y).mp hy
    calc
      _ ≤ ∑ _i ∈ s, S₀ := Finset.sum_le_sum fun i _ => h₀ _ (hall i)
      _ = s.card * S₀ := by simp
      _ ≤ Fintype.card K * S₀ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_left _ _
  · have htrue : orBits y = true := by cases h : orBits y <;> simp_all
    obtain ⟨i, hi⟩ := (orBits_eq_true y).mp htrue
    have hs : s ⊆ {i} := by
      intro j hj
      have hc := (Finset.mem_filter.mp hj).2
      by_contra hji
      have hij : i ≠ j := Ne.symm (by simpa only [Finset.mem_singleton] using hji)
      exact hc (orBits_flip_of_witness y hij hi)
    calc
      _ ≤ ∑ j ∈ ({i} : Finset K), sensitivityAt f (fun a => x (j, a)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact Nat.zero_le _)
      _ = sensitivityAt f (fun a => x (i, a)) := by simp
      _ ≤ S₁ := h₁ _ hi
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_right _ _

theorem card_le_blockSensitivityAt_orBits_zero :
    Fintype.card K ≤ blockSensitivityAt (orBits (K := K)) (fun _ => false) := by
  apply le_blockSensitivityAt_of_family orBits (fun _ => false) (fun k : K => {k})
  · intro k
    simp
  · intro k l hkl
    simpa using hkl
  · intro k
    have h : orBits (flip (fun _ : K => false) {k}) = true :=
      (orBits_eq_true _).mpr ⟨k, by simp⟩
    simp [h]

theorem blockSensitivityAt_orCopies_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) :
    Fintype.card K * blockSensitivityAt f (fun _ => false) ≤
      blockSensitivityAt (orCopies (K := K) f) (fun _ => false) := by
  exact (Nat.mul_le_mul_right _ card_le_blockSensitivityAt_orBits_zero).trans
    (blockSensitivityAt_compose_zero_le orBits f hf)

end Paper320

end

end OAI

-- Reused in full from OpenAI, Iterates.lean

namespace OAI

/-! Repeated disjoint composition with explicit finite raw-coordinate types. -/

noncomputable section
open scoped Classical

namespace Paper320

abbrev IterateCoord (I : Type) : ℕ → Type
  | 0 => Unit
  | m + 1 => I × IterateCoord I m

instance iterateCoordFintype {I : Type} [Fintype I] :
    (m : ℕ) → Fintype (IterateCoord I m)
  | 0 => inferInstanceAs (Fintype Unit)
  | m + 1 =>
    letI : Fintype (IterateCoord I m) := iterateCoordFintype (I := I) m
    inferInstanceAs (Fintype (I × IterateCoord I m))

def iterateCompose {I : Type} (f : (I → Bool) → Bool) :
    (m : ℕ) → (IterateCoord I m → Bool) → Bool
  | 0 => fun x => x ()
  | m + 1 => compose f (iterateCompose f m)

theorem iterateCompose_one {I : Type} (f : (I → Bool) → Bool)
    (x : IterateCoord I 1 → Bool) :
    iterateCompose f 1 x = f (fun i => x (i, ())) := rfl

theorem iterateCompose_zero {I : Type} (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateCompose f m (fun _ => false) = false := by
  induction m with
  | zero => rfl
  | succ m ih => exact (compose_zero f (iterateCompose f m) ih).trans hf

variable {I : Type} [Fintype I]

theorem iterateCoord_card (m : ℕ) :
    Fintype.card (IterateCoord I m) = Fintype.card I ^ m := by
  induction m with
  | zero => exact Fintype.card_unique
  | succ m ih =>
    change Fintype.card (I × IterateCoord I m) = _
    rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

theorem sensitivity_iterateCompose_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateCompose f m) ≤ sensitivity f ^ m := by
  induction m with
  | zero =>
    apply sensitivity_le
    intro x
    exact (sensitivityAt_le_card (iterateCompose f 0) x).trans_eq (iterateCoord_card 0)
  | succ m ih =>
    change sensitivity (compose f (iterateCompose f m)) ≤ _
    calc
      _ ≤ sensitivity f * sensitivity (iterateCompose f m) := sensitivity_compose_le _ _
      _ ≤ sensitivity f * sensitivity f ^ m := Nat.mul_le_mul_left _ ih
      _ = sensitivity f ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]

theorem blockSensitivityAt_iterateCompose_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateCompose f m) (fun _ => false) := by
  induction m with
  | zero =>
    have h := le_blockSensitivityAt (iterateCompose f 0) (fun _ => false)
      ({{()}} : Finset (Finset Unit))
      (by
        intro A hA B hB hne
        exact (hne ((Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm)).elim)
      (by
        intro B hB
        have hB' : B = {()} := Finset.mem_singleton.mp hB
        subst B
        exact ⟨Finset.singleton_nonempty _, by simp [iterateCompose, flip]⟩)
    simpa only [Finset.card_singleton, pow_zero] using h
  | succ m ih =>
    change _ ≤ blockSensitivityAt (compose f (iterateCompose f m)) (fun _ => false)
    calc
      _ = blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt f (fun _ => false) ^ m := by rw [pow_succ, Nat.mul_comm]
      _ ≤ blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt (iterateCompose f m) (fun _ => false) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := blockSensitivityAt_compose_zero_le f (iterateCompose f m)
        (iterateCompose_zero f hf m)

def iterateFin (f : (I → Bool) → Bool) (m : ℕ) :
    (Fin (Fintype.card I ^ m) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (iterateCoord_card (I := I) m)) (iterateCompose f m)

theorem iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateFin f m (fun _ => false) = false :=
  iterateCompose_zero f hf m

theorem sensitivity_iterateFin_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateFin f m) ≤ sensitivity f ^ m := by
  rw [iterateFin, sensitivity_reindex]
  exact sensitivity_iterateCompose_le f m

theorem blockSensitivityAt_iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateFin f m) (fun _ => false) := by
  rw [iterateFin, blockSensitivityAt_reindex]
  exact blockSensitivityAt_iterateCompose_zero f hf m

theorem nonconstant_of_blockSensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool)
    (h : 0 < blockSensitivityAt f x) : ∃ y z, f y ≠ f z := by
  obtain ⟨blocks, hc, _, hb⟩ := exists_blockSensitivityAt_family f x
  have hn : blocks.Nonempty := Finset.card_pos.mp (hc.symm ▸ h)
  obtain ⟨B, hB⟩ := hn
  exact ⟨flip x B, x, (hb B hB).2⟩

theorem iterateFin_nonconstant (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false)
    (h : 0 < blockSensitivityAt f (fun _ => false)) (m : ℕ) :
    ∃ x y, iterateFin f m x ≠ iterateFin f m y := by
  exact nonconstant_of_blockSensitivityAt_pos _ _
    ((pow_pos h m).trans_le (blockSensitivityAt_iterateFin_zero f hf m))

end Paper320

end

end OAI

namespace SensitivityCampaign
noncomputable section
open scoped Classical
open OAI.Paper320

private def translate {I : Type} (x y : I → Bool) : I → Bool :=
  fun i => Bool.xor (x i) (y i)

private lemma translate_zero {I : Type} (x : I → Bool) :
    translate x (fun _ => false) = x := by
  funext i
  simp [translate]

private lemma translate_flip {I : Type} (x y : I → Bool) (B : Finset I) :
    translate x (flip y B) = flip (translate x y) B := by
  funext i
  by_cases hi : i ∈ B
  · cases hx : x i <;> cases hy : y i <;> simp [translate, OAI.Paper320.flip, hi, hx, hy]
  · simp [translate, OAI.Paper320.flip, hi]

private def normalize {I : Type} (f : (I → Bool) → Bool) (x : I → Bool) :
    (I → Bool) → Bool := fun y => Bool.xor (f (translate x y)) (f x)

private lemma normalize_zero {I : Type} (f : (I → Bool) → Bool) (x : I → Bool) :
    normalize f x (fun _ => false) = false := by
  simp [normalize, translate_zero]

private lemma normalize_flip_ne {I : Type} (f : (I → Bool) → Bool) (x y : I → Bool)
    (B : Finset I) :
    normalize f x (flip y B) ≠ normalize f x y ↔
      f (flip (translate x y) B) ≠ f (translate x y) := by
  unfold normalize
  rw [translate_flip]
  cases h : f x <;> simp [h]

private lemma sensitivity_normalize_le {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivity (normalize f x) ≤ sensitivity f := by
  apply sensitivity_le
  intro y
  have he : sensitivityAt (normalize f x) y = sensitivityAt f (translate x y) := by
    simp only [sensitivityAt, normalize_flip_ne]
  rw [he]
  exact sensitivityAt_le_sensitivity f _

private lemma blockSensitivityAt_normalize_zero {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt (normalize f x) (fun _ => false) = blockSensitivityAt f x := by
  simp only [blockSensitivityAt, normalize_flip_ne, translate_zero]

private lemma exists_zero_sensitive {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hnc : ∃ x y, f x ≠ f y) :
    ∃ x i, f x = false ∧ f (flip x {i}) = true := by
  obtain ⟨x, hx⟩ := exists_sensitivityAt_eq f
  have hp : 0 < sensitivityAt f x := hx.symm ▸ sensitivity_pos_of_nonconstant f hnc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  have hn := (Finset.mem_filter.mp hi).2
  cases hfx : f x with
  | false =>
    refine ⟨x, i, hfx, ?_⟩
    cases hfi : f (flip x {i}) <;> simp_all
  | true =>
    refine ⟨flip x {i}, i, ?_, ?_⟩
    · cases hfi : f (flip x {i}) <;> simp_all
    · simpa using hfx

private lemma sensitivity_orCopies_lower {I K : Type} [Fintype I] [Fintype K]
    (f : (I → Bool) → Bool) (hnc : ∃ x y, f x ≠ f y) :
    Fintype.card K ≤ sensitivity (orCopies (K := K) f) := by
  obtain ⟨x, i, hx, hi⟩ := exists_zero_sensitive f hnc
  let y : K × I → Bool := fun p => x p.2
  have hs (k : K) : orCopies (K := K) f (flip y {(k, i)}) ≠ orCopies f y := by
    apply (compose_flip_sensitive_iff orBits f y k i).mpr
    constructor
    · simpa [y, hx, hi]
    · have hzero : (fun k : K => f (fun a => y (k, a))) = fun _ => false := by
        funext k
        exact hx
      rw [hzero, orBits_zero]
      have ht : orBits (flip (fun _ : K => false) {k}) = true :=
        (orBits_eq_true _).mpr ⟨k, by simp⟩
      simp [ht]
  have hsub : (Finset.univ.image fun k : K => (k, i)) ⊆
      Finset.univ.filter (fun p => orCopies (K := K) f (flip y {p}) ≠ orCopies f y) := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs k⟩
  have hc := Finset.card_le_card hsub
  have hinj : Function.Injective (fun k : K => (k, i)) := by
    intro k l h
    exact congrArg Prod.fst h
  have hh : Fintype.card K ≤ sensitivityAt (orCopies (K := K) f) y := by
    simpa only [sensitivityAt, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hc
  exact hh.trans (sensitivityAt_le_sensitivity _ _)

end
end SensitivityCampaign

namespace SensitivityCampaign
noncomputable section
open scoped Classical
open OAI.Paper320

private lemma amplified_copies {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false)
    (A B : ℕ) (hB : 1 < B) (hs : sensitivity f ≤ A)
    (hb : B ≤ blockSensitivityAt f (fun _ => false))
    (S : ℕ) (hS : 2 ≤ S) (m : ℕ) :
    ∃ (n : ℕ) (g : (Fin n → Bool) → Bool),
      S ≤ sensitivity g ∧ sensitivity g ≤ S * A ^ m ∧ B ^ m ≤ blockSensitivity g := by
  let h := iterateFin f m
  have hz : h (fun _ => false) = false := iterateFin_zero f hf m
  have hn : ∃ x y, h x ≠ h y := iterateFin_nonconstant f hf (by omega) m
  have hs' : sensitivity h ≤ A ^ m := by
    have hp : sensitivity f ^ m ≤ A ^ m := by gcongr
    exact (sensitivity_iterateFin_le f m).trans hp
  have hb' : B ^ m ≤ blockSensitivityAt h (fun _ => false) := by
    have hp : B ^ m ≤ blockSensitivityAt f (fun _ => false) ^ m := by gcongr
    exact hp.trans (blockSensitivityAt_iterateFin_zero f hf m)
  let F := orCopies (K := Fin S) h
  let e := Fintype.equivFin (Fin S × Fin (Fintype.card I ^ m))
  refine ⟨_, reindex e F, ?_, ?_, ?_⟩
  · rw [sensitivity_reindex]
    simpa only [Fintype.card_fin] using sensitivity_orCopies_lower (K := Fin S) h hn
  · rw [sensitivity_reindex]
    have hm : sensitivity h ≤ S * sensitivity h := by nlinarith
    have hc := sensitivity_orCopies_le (K := Fin S) h (sensitivity h) (sensitivity h)
      (fun x _ => sensitivityAt_le_sensitivity h x)
      (fun x _ => sensitivityAt_le_sensitivity h x)
    simp only [Fintype.card_fin, max_eq_left hm] at hc
    exact hc.trans (Nat.mul_le_mul_left S hs')
  · rw [blockSensitivity_reindex]
    have hc := blockSensitivityAt_orCopies_zero (K := Fin S) h hz
    simp only [Fintype.card_fin] at hc
    have hm : blockSensitivityAt h (fun _ => false) ≤
        S * blockSensitivityAt h (fun _ => false) := by nlinarith
    exact hb'.trans (hm.trans (hc.trans (blockSensitivityAt_le_blockSensitivity F _)))

private theorem finite_certificate_proof
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (a : ℝ)
    (hA : 1 < A) (hB : 1 < B) (ha : 0 ≤ a)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : (A : ℝ) ^ a ≤ (B : ℝ)) : AchievesExponent a := by
  let f₀ := normalize f x
  have hz : f₀ (fun _ => false) = false := normalize_zero f x
  have hs₀ : sensitivity f₀ ≤ A := (sensitivity_normalize_le f x).trans hs
  have hb₀ : B ≤ blockSensitivityAt f₀ (fun _ => false) := by
    simpa only [f₀, blockSensitivityAt_normalize_zero] using hb
  intro ε hε S hS
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
  have hAr : (1 : ℝ) < A := by exact_mod_cast hA
  have hAp : (0 : ℝ) < A := by linarith
  by_cases he : a ≤ ε
  · obtain ⟨N, g, hgs, _, hgb⟩ := amplified_copies f₀ hz A B hB hs₀ hb₀ S hS 0
    refine ⟨N, g, hgs, ?_⟩
    have hg1 : (1 : ℝ) ≤ sensitivity g := by exact_mod_cast (show 1 ≤ sensitivity g by omega)
    have hb1 : (1 : ℝ) ≤ blockSensitivity g := by exact_mod_cast hgb
    exact (Real.rpow_le_one_of_one_le_of_nonpos hg1 (by linarith)).trans hb1
  · have hepos : 0 < a - ε := by linarith
    have hbase : (1 : ℝ) < (A : ℝ) ^ ε := Real.one_lt_rpow hAr hε
    have ht := tendsto_pow_atTop_atTop_of_one_lt hbase
    obtain ⟨m, hm⟩ := (ht.eventually (Filter.eventually_ge_atTop ((S : ℝ) ^ a))).exists
    obtain ⟨N, g, hgs, hgu, hgb⟩ := amplified_copies f₀ hz A B hB hs₀ hb₀ S hS m
    refine ⟨N, g, hgs, ?_⟩
    have hgur : (sensitivity g : ℝ) ≤ (S : ℝ) * (A : ℝ) ^ m := by exact_mod_cast hgu
    have hgbr : (B : ℝ) ^ m ≤ (blockSensitivity g : ℝ) := by exact_mod_cast hgb
    have hcomm : ((A : ℝ) ^ m) ^ (a - ε) = ((A : ℝ) ^ (a - ε)) ^ m := by
      rw [← Real.rpow_natCast_mul hAp.le, mul_comm (m : ℝ), Real.rpow_mul_natCast hAp.le]
    calc
      (sensitivity g : ℝ) ^ (a - ε) ≤ ((S : ℝ) * (A : ℝ) ^ m) ^ (a - ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hgur hepos.le
      _ = (S : ℝ) ^ (a - ε) * ((A : ℝ) ^ (a - ε)) ^ m := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hAp.le _), hcomm]
      _ ≤ (S : ℝ) ^ a * ((A : ℝ) ^ (a - ε)) ^ m := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow_of_exponent_le hSr (by linarith)
        · positivity
      _ ≤ ((A : ℝ) ^ ε) ^ m * ((A : ℝ) ^ (a - ε)) ^ m := by
        exact mul_le_mul_of_nonneg_right hm (by positivity)
      _ = ((A : ℝ) ^ a) ^ m := by
        rw [← mul_pow, ← Real.rpow_add hAp]
        have hex : ε + (a - ε) = a := by ring
        rw [hex]
      _ ≤ (B : ℝ) ^ m := pow_le_pow_left₀ (Real.rpow_nonneg hAp.le _) hpow m
      _ ≤ (blockSensitivity g : ℝ) := hgbr

end
end SensitivityCampaign

open OAI.Paper320

theorem solution
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (a : ℝ)
    (hA : 1 < A) (hB : 1 < B) (ha : 0 ≤ a)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : (A : ℝ) ^ a ≤ (B : ℝ)) :
    SensitivityCampaign.AchievesExponent a :=
  SensitivityCampaign.finite_certificate_proof f x A B a hA hB ha hs hb hpow
