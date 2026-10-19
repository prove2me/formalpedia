-- Prove2me | solution 1 for SensitivityCampaign.rubinstein_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-16T12:09:36.126141+00:00
-- url     : https://prove2.me/submissions/1ae6dcf9-107d-45cf-aed9-ad54faf315a5

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


set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace Rubinstein
noncomputable section
open scoped Classical
open OAI.Paper320

variable {I J K : Type} [Fintype I]

def Certificate (f : (I → Bool) → Bool) (x : I → Bool) (C : Finset I) : Prop :=
  ∀ y, (∀ i ∈ C, y i = x i) → f y = f x

lemma bs_le_certificate (f : (I → Bool) → Bool) (x : I → Bool)
    (C : Finset I) (hc : Certificate f x C) : blockSensitivityAt f x ≤ C.card := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have hit (B) (hB : B ∈ blocks) : ∃ i ∈ C, i ∈ B := by
    by_contra hn
    push Not at hn
    apply (hb B hB).2
    apply hc
    intro i hi
    simp [OAI.Paper320.flip, hn i hi]
  choose pick hpC hpB using hit
  let g : {B // B ∈ blocks} → {i // i ∈ C} :=
    fun B => ⟨pick B.val B.property, hpC B.val B.property⟩
  have hg : Function.Injective g := by
    intro B D he
    apply Subtype.ext
    by_contra hn
    have he' : pick B.val B.property = pick D.val D.property := congrArg Subtype.val he
    exact Finset.disjoint_left.mp (hd B.val B.property D.val D.property hn)
      (hpB B.val B.property) (he'.symm ▸ hpB D.val D.property)
  have hcard := Fintype.card_le_of_injective g hg
  simpa using hcard

def code {m : ℕ} (j : Fin m) : Fin m × Bool → Bool := fun p => decide (p.1 = j)
def row {m : ℕ} (x : Fin m × Bool → Bool) : Bool := decide (∃ j, x = code j)

lemma row_true {m : ℕ} (x : Fin m × Bool → Bool) : row x = true ↔ ∃ j, x = code j := by
  simp [row]

lemma row_code {m : ℕ} (j : Fin m) : row (code j) = true := by
  exact (row_true _).mpr ⟨j, rfl⟩

lemma row_zero {m : ℕ} : row (fun _ : Fin m × Bool => false) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨j, hj⟩ := (row_true _).mp h
  have := congrFun hj (j, false)
  simp [code] at this

lemma code_distance {m : ℕ} (j l : Fin m) (hne : j ≠ l) :
    hammingDist (code j) (code l) = 4 := by
  have hs : Finset.univ.filter (fun p => code j p ≠ code l p) =
      ({j,l} : Finset (Fin m)) ×ˢ (Finset.univ : Finset Bool) := by
    ext p
    by_cases hj : p.1 = j <;> by_cases hl : p.1 = l <;> simp_all [code]
  rw [hammingDist, hs, Finset.card_product]
  simp [hne]

lemma flip_distance (x : I → Bool) (i : I) : hammingDist (OAI.Paper320.flip x {i}) x = 1 := by
  have hs : Finset.univ.filter (fun j => OAI.Paper320.flip x {i} j ≠ x j) = {i} := by
    ext j
    by_cases h : j = i
    · subst j
      cases hxi : x i <;> simp [OAI.Paper320.flip, hxi]
    · simp [OAI.Paper320.flip, h]
  rw [hammingDist, hs]
  simp

lemma flip_injective (x : I → Bool) : Function.Injective (fun i => OAI.Paper320.flip x {i}) := by
  intro i j h
  by_contra hn
  have he := congrFun h i
  cases hx : x i <;> simp [OAI.Paper320.flip, hn, hx] at he

lemma row_flips_unique {m : ℕ} (x : Fin m × Bool → Bool) (p q : Fin m × Bool)
    (hp : row (OAI.Paper320.flip x {p}) = true)
    (hq : row (OAI.Paper320.flip x {q}) = true) : p = q := by
  obtain ⟨j, hj⟩ := (row_true _).mp hp
  obtain ⟨l, hl⟩ := (row_true _).mp hq
  have hdist := hammingDist_triangle_right (OAI.Paper320.flip x {p}) (OAI.Paper320.flip x {q}) x
  rw [flip_distance, flip_distance, hj, hl] at hdist
  have he : j = l := by
    by_contra hn
    rw [code_distance j l hn] at hdist
    omega
  exact flip_injective x (hj.trans (by simpa [he] using hl.symm))

lemma row_sensitivity_zero {m : ℕ} (x : Fin m × Bool → Bool) (hx : row x = false) :
    sensitivityAt row x ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  apply row_flips_unique x p q
  · cases he : row (OAI.Paper320.flip x {p}) <;> simp_all
  · cases he : row (OAI.Paper320.flip x {q}) <;> simp_all

lemma code_flip_false {m : ℕ} (j : Fin m) (p : Fin m × Bool) :
    row (OAI.Paper320.flip (code j) {p}) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨l, hl⟩ := (row_true _).mp h
  have hd := flip_distance (code j) p
  rw [hl] at hd
  by_cases he : l = j
  · subst l
    simp at hd
  · rw [code_distance l j he] at hd
    omega

lemma row_zero_certificate {m : ℕ} (x : Fin m × Bool → Bool) (hx : row x = false) :
    ∃ C : Finset (Fin m × Bool), C.card ≤ m ∧ Certificate row x C := by
  by_cases hz : ∀ j, ∃ b, x (j,b) = false
  · choose bit hbit using hz
    refine ⟨Finset.univ.image (fun j => (j,bit j)), ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simp)
    · intro y hy
      rw [hx]
      apply Bool.eq_false_iff.mpr
      intro hg
      obtain ⟨j, rfl⟩ := (row_true y).mp hg
      have he := hy (j,bit j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      simp [code, hbit] at he
  · push Not at hz
    obtain ⟨j, hj⟩ := hz
    have hj' (b : Bool) : x (j,b) = true := by
      have := hj b
      cases he : x (j,b) <;> simp_all
    have hne : x ≠ code j := by
      intro he
      have ht := row_code j
      rw [← he, hx] at ht
      contradiction
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
    have hpj : p.1 ≠ j := by
      intro he
      rcases p with ⟨a,b⟩
      dsimp at he
      subst a
      simp [code, hj'] at hp
    have hpt : x p = true := by
      simp only [code, hpj, decide_false] at hp
      cases he : x p <;> simp_all
    have hm : 2 ≤ m := by
      have hcard := Finset.card_le_univ ({j,p.1} : Finset (Fin m))
      simpa [Ne.symm hpj] using hcard
    refine ⟨{(j,false),p}, ?_, ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by simp; omega)
    · intro y hy
      rw [hx]
      apply Bool.eq_false_iff.mpr
      intro hg
      obtain ⟨l, rfl⟩ := (row_true y).mp hg
      have ha := hy (j,false) (by simp)
      have hb := hy p (by simp)
      have ha' : j = l := by simpa [code, hj'] using ha
      have hb' : p.1 = l := by simpa [code, hpt] using hb
      exact hpj (hb'.trans ha'.symm)


lemma or_zero_bs [Fintype K] (f : (I → Bool) → Bool) (x : K × I → Bool) (M : ℕ)
    (hx : orCopies f x = false)
    (hc : ∀ y, f y = false → ∃ C, C.card ≤ M ∧ Certificate f y C) :
    blockSensitivityAt (orCopies f) x ≤ Fintype.card K * M := by
  have hall : ∀ k, f (fun i => x (k,i)) = false := (orBits_eq_false _).mp hx
  choose C hcard hcert using fun k => hc (fun i => x (k,i)) (hall k)
  let D : Finset (K × I) := Finset.univ.biUnion fun k => (C k).image fun i => (k,i)
  have hD : D.card ≤ Fintype.card K * M := by
    calc
      D.card ≤ ∑ k : K, ((C k).image fun i => (k,i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _k : K, M := Finset.sum_le_sum fun k _ => (Finset.card_image_le).trans (hcard k)
      _ = _ := by simp
  apply (bs_le_certificate (orCopies f) x D ?_).trans hD
  intro y hy
  rw [hx]
  apply (orBits_eq_false _).mpr
  intro k
  rw [hcert k (fun i => y (k,i)) ?_, hall k]
  intro i hi
  exact hy (k,i) (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)

lemma or_one_bs [Fintype K] (f : (I → Bool) → Bool) (x : K × I → Bool)
    (hx : orCopies f x = true) : blockSensitivityAt (orCopies f) x ≤ Fintype.card I := by
  obtain ⟨k, hk⟩ := (orBits_eq_true _).mp hx
  let D : Finset (K × I) := Finset.univ.image fun i => (k,i)
  have hD : D.card ≤ Fintype.card I := Finset.card_image_le.trans (by simp)
  apply (bs_le_certificate (orCopies f) x D ?_).trans hD
  intro y hy
  rw [hx]
  apply (orBits_eq_true _).mpr
  refine ⟨k, ?_⟩
  have he : (fun i => y (k,i)) = (fun i => x (k,i)) := by
    funext i
    exact hy (k,i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [he, hk]

lemma row_bs_zero {m : ℕ} : m ≤ blockSensitivityAt (@row m) (fun _ => false) := by
  have h := le_blockSensitivityAt_of_family (@row m) (fun _ => false)
    (fun j : Fin m => {(j,false),(j,true)})
  simp only [Fintype.card_fin] at h
  apply h
  · intro j
    simp
  · intro j l hjl
    simp [Finset.disjoint_left, hjl]
  · intro j
    have he : OAI.Paper320.flip (fun _ => false) {(j,false),(j,true)} = code j := by
      funext p
      rcases p with ⟨a,b⟩
      cases b <;> simp [OAI.Paper320.flip, code, eq_comm]
    rw [he, row_code, row_zero]
    decide

lemma full_sensitivity_lower (m : ℕ) (hm : 1 ≤ m) :
    2*m ≤ sensitivity (orCopies (K := Fin (2*m)) (@row m)) := by
  let k₀ : Fin (2*m) := ⟨0, by omega⟩
  let j₀ : Fin m := ⟨0, by omega⟩
  let x : Fin (2*m) × (Fin m × Bool) → Bool :=
    fun p => if p.1 = k₀ then code j₀ p.2 else false
  have hxrow : (fun i => x (k₀,i)) = code j₀ := by funext i; simp [x]
  have hx : orCopies (@row m) x = true := by
    apply (orBits_eq_true _).mpr
    exact ⟨k₀, by rw [hxrow, row_code]⟩
  have hs (p : Fin m × Bool) :
      orCopies (@row m) (OAI.Paper320.flip x {(k₀,p)}) ≠ orCopies (@row m) x := by
    have hf : orCopies (@row m) (OAI.Paper320.flip x {(k₀,p)}) = false := by
      apply (orBits_eq_false _).mpr
      intro k
      by_cases hk : k = k₀
      · subst k
        rw [flip_prod_same, hxrow, code_flip_false]
      · rw [flip_prod_other x p hk]
        have he : (fun i => x (k,i)) = fun _ => false := by funext i; simp [x,hk]
        rw [he, row_zero]
    rw [hx, hf]
    decide
  have hsub : (Finset.univ.image fun p : Fin m × Bool => (k₀,p)) ⊆
      Finset.univ.filter (fun p => orCopies (@row m) (OAI.Paper320.flip x {p}) ≠ orCopies (@row m) x) := by
    intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs a⟩
  have hcard := Finset.card_le_card hsub
  have hinj : Function.Injective (fun p : Fin m × Bool => (k₀,p)) := by
    intro p q h
    exact congrArg Prod.snd h
  have hlocal : 2*m ≤ sensitivityAt (orCopies (@row m)) x := by
    simpa [sensitivityAt, Finset.card_image_of_injective _ hinj, Nat.mul_comm] using hcard
  exact hlocal.trans (sensitivityAt_le_sensitivity _ _)

lemma full_bounds (m : ℕ) (hm : 1 ≤ m) :
    sensitivity (orCopies (K := Fin (2*m)) (@row m)) = 2*m ∧
    blockSensitivity (orCopies (K := Fin (2*m)) (@row m)) = 2*m^2 := by
  constructor
  · apply Nat.le_antisymm _ (full_sensitivity_lower m hm)
    have hs := sensitivity_orCopies_le (K := Fin (2*m)) (@row m) 1 (2*m)
      (fun x hx => row_sensitivity_zero x hx)
      (fun x _ => (sensitivityAt_le_card (@row m) x).trans_eq (by simp [Nat.mul_comm]))
    simpa using hs
  · apply Nat.le_antisymm
    · apply blockSensitivity_le
      intro x
      cases hx : orCopies (@row m) x with
      | false =>
        have h := or_zero_bs (@row m) x m hx (fun y hy => row_zero_certificate y hy)
        convert h using 1 <;> simp <;> ring
      | true =>
        have h := or_one_bs (@row m) x hx
        have hh : 2*m ≤ 2*m^2 := by nlinarith
        exact h.trans (by simpa [Nat.mul_comm] using hh)
    · have h := blockSensitivityAt_orCopies_zero (K := Fin (2*m)) (@row m) row_zero
      have hh := Nat.mul_le_mul_left (2*m) (@row_bs_zero m)
      have hb := hh.trans (by simpa using h)
      calc
        2*m^2 = (2*m)*m := by ring
        _ ≤ blockSensitivityAt (orCopies (K := Fin (2*m)) (@row m)) (fun _ => false) := hb
        _ ≤ _ := blockSensitivityAt_le_blockSensitivity _ _

end
end Rubinstein

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∃ f : (Fin ((2 * m) ^ 2) → Bool) → Bool,
      OAI.Paper320.sensitivity f = 2 * m ∧
      OAI.Paper320.blockSensitivity f = 2 * m ^ 2 := by
  classical
  let e : (Fin (2*m) × (Fin m × Bool)) ≃ Fin ((2*m)^2) :=
    Fintype.equivFinOfCardEq (by simp; ring)
  refine ⟨OAI.Paper320.reindex e (OAI.Paper320.orCopies (@Rubinstein.row m)), ?_, ?_⟩
  · rw [OAI.Paper320.sensitivity_reindex]
    exact (Rubinstein.full_bounds m hm).1
  · rw [OAI.Paper320.blockSensitivity_reindex]
    exact (Rubinstein.full_bounds m hm).2
