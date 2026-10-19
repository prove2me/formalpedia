-- Prove2me | solution 1 for SensitivityCampaign.reach_20635_coupled_tournament
-- status  : ACCEPTED   (prove)
-- author  : @abhishekdpseok
-- created : 2026-10-18T04:24:35.014967+00:00
-- url     : https://prove2.me/submissions/f80a3f37-72fa-4d56-a094-3e4d351764f3

/-
Block sensitivity versus sensitivity: exponent at least 2.0635.
Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

Foundations reuse the proved OpenAI/math sensitivity development and the
accepted Prove2Me 2.05 solution by robinkothari (theorem
4807ab9c-ddde-49d8-83cf-3532a7f795c3). The finite binomial labeling estimate
also follows the accepted 2.0391 proof (theorem
872a88de-6ec2-46b6-a079-9afd4617aa55).
The coupled repair estimate and seven-layer certificate are supplied here.
All theorem proofs are included; the only platform import is the unchanged
campaign definition. The target theorem is not imported.
-/
import Mathlib
import Definitions.Def_SensitivityCampaign
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/- Upstream module: OAI.Combinatorics.Sensitivity.HammingBase -/

namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]

theorem hammingDist_flip_self (x : I → Bool) (i : I) :
    hammingDist x (flip x {i}) = 1 := by
  have h : (Finset.univ.filter fun j => x j ≠ flip x {i} j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases x i <;> simp [flip]
    · simp [flip, hj]
  rw [hammingDist, h]
  simp

theorem hammingDist_le_flip_add_one (x z : I → Bool) (i : I) :
    hammingDist x z ≤ hammingDist (flip x {i}) z + 1 := by
  have h := hammingDist_triangle x (flip x {i}) z
  rw [hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_le_add_one (x z : I → Bool) (i : I) :
    hammingDist (flip x {i}) z ≤ hammingDist x z + 1 := by
  have h := hammingDist_triangle (flip x {i}) x z
  rw [hammingDist_comm (flip x {i}) x, hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_eq_add_one (x z : I → Bool) (i : I) (hi : x i = z i) :
    hammingDist (flip x {i}) z = hammingDist x z + 1 := by
  have h : (Finset.univ.filter fun j => flip x {i} j ≠ z j) =
      insert i (Finset.univ.filter fun j => x j ≠ z j) := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp_all [flip]
    · simp [flip, hj]
  rw [hammingDist, h, Finset.card_insert_of_notMem]
  · rfl
  · simp [hi]

/-- The union of equal-radius Hamming balls. -/
def ballPredicate [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) : Bool :=
  decide (∃ c, hammingDist x (centers c) ≤ R)

theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_nested [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R ≤ S) (x : I → Bool)
    (h : ballPredicate centers R x = true) : ballPredicate centers S x = true := by
  rcases (ballPredicate_eq_true centers R x).1 h with ⟨c, hc⟩
  exact (ballPredicate_eq_true centers S x).2 ⟨c, hc.trans hRS⟩

theorem ballPredicate_zero_flip [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) (i : I) (hx : ballPredicate centers R x = false)
    (hi : ballPredicate centers R (flip x {i}) = true) :
    ∃ c, hammingDist x (centers c) = R + 1 ∧ x i ≠ centers c i := by
  rcases (ballPredicate_eq_true centers R (flip x {i})).1 hi with ⟨c, hc⟩
  have hn : ¬ hammingDist x (centers c) ≤ R := by
    intro h
    have := (ballPredicate_eq_true centers R x).2 ⟨c, h⟩
    simp_all
  have hd := hammingDist_le_flip_add_one x (centers c) i
  refine ⟨c, by omega, ?_⟩
  intro heq
  rw [hammingDist_flip_eq_add_one x (centers c) i heq] at hc
  omega

theorem near_center_unique (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) {a b : C} (ha : hammingDist x (centers a) ≤ R + 1)
    (hb : hammingDist x (centers b) ≤ R + 1) : a = b := by
  by_contra h
  have hs := hsep a b h
  have ht := hammingDist_triangle (centers a) x (centers b)
  rw [hammingDist_comm (centers a) x] at ht
  omega

theorem ballPredicate_sensitivityAt_zero_le [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by
  let A := Finset.univ.filter fun i =>
    ballPredicate centers R (flip x {i}) ≠ ballPredicate centers R x
  change A.card ≤ R + 1
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    have hi' : ballPredicate centers R (flip x {i}) = true := by
      simpa [A, hx] using hi
    obtain ⟨c, hc, _⟩ := ballPredicate_zero_flip centers R x i hx hi'
    have hsub : A ⊆ Finset.univ.filter fun j => x j ≠ centers c j := by
      intro j hj
      have hj' : ballPredicate centers R (flip x {j}) = true := by
        simpa [A, hx] using hj
      obtain ⟨c', hc', hjc⟩ := ballPredicate_zero_flip centers R x j hx hj'
      have heq : c' = c := near_center_unique centers R hsep x (by omega) (by omega)
      simpa [heq] using hjc
    exact (Finset.card_le_card hsub).trans_eq hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

theorem ballPredicate_no_joint_zero [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hS : ballPredicate centers S x = false)
    (hR : ballPredicate centers R (flip x {i}) = true) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R (flip x {i})).1 hR
  have hd := hammingDist_le_flip_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S x).2 ⟨c, by omega⟩
  simp_all

theorem ballPredicate_no_joint_one [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hR : ballPredicate centers R x = true)
    (hS : ballPredicate centers S (flip x {i}) = false) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R x).1 hR
  have hd := hammingDist_flip_le_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S (flip x {i})).2 ⟨c, by omega⟩
  simp_all

/-- Minimum distance to the finite nonempty family of centers. -/
def nearestDistance [Fintype C] [Nonempty C] (centers : C → I → Bool)
    (x : I → Bool) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c => hammingDist x (centers c))

theorem ballPredicate_eq_nearestDistance [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (R : ℕ) (x : I → Bool) :
    ballPredicate centers R x = decide (nearestDistance centers x ≤ R) := by
  simp [ballPredicate, nearestDistance, Finset.inf'_le_iff]

theorem nearestDistance_le_flip_add_one [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (x : I → Bool) (i : I) :
    nearestDistance centers x ≤ nearestDistance centers (flip x {i}) + 1 := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun c => hammingDist (flip x {i}) (centers c))
  apply (Finset.inf'_le _ (Finset.mem_univ c)).trans
  change hammingDist x (centers c) ≤
    (Finset.univ.inf' Finset.univ_nonempty fun c => hammingDist (flip x {i}) (centers c)) + 1
  rw [hc]
  exact hammingDist_le_flip_add_one x (centers c) i

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveProfiles -/

namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

/-- Acceptance at a stronger index implies acceptance at every weaker index. -/
structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true

theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

/-- The number of coordinates whose one-bit flip changes both predicates. -/
def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (flip x {i}) ≠ f x ∧ g (flip x {i}) ≠ g x).card

/-- Maximum sensitivity over all indices and inputs with the indicated output. -/
def sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun x =>
    if F q x = b then sensitivityAt (F q) x else 0

/-- Maximum same-input, same-bit joint sensitivity over two distinct ordered indices. -/
def jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun q' => Finset.univ.sup fun x =>
    if q < q' ∧ F q x = b ∧ F q' x = b then
      jointSensitivityAt (F q) (F q') x else 0

theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

theorem sideSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q x, F q x = b → sensitivityAt (F q) x ≤ B) :
    sideSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q x hx
  · exact Nat.zero_le _

theorem jointSensitivityAt_le_jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q q' : Fin h) (x : I → Bool)
    (hqq : q < q') (hx : F q x = b) (hx' : F q' x = b) :
    jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ q')
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hqq, hx, hx']

theorem jointSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q q' x, q < q' → F q x = b → F q' x = b →
      jointSensitivityAt (F q) (F q') x ≤ B) : jointSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro q' _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q q' x hx.1 hx.2.1 hx.2.2
  · exact Nat.zero_le _

theorem jointSensitivityAt_le_left {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) :
    jointSensitivityAt f g x ≤ sensitivityAt f x := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩

theorem jointSensitivityAt_comm {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) :
    jointSensitivityAt f g x = jointSensitivityAt g f x := by
  simp only [jointSensitivityAt, and_comm]

theorem jointSensitivity_one {I : Type} [Fintype I]
    (F : Fin 1 → (I → Bool) → Bool) (b : Bool) : jointSensitivity F b = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply jointSensitivity_le
  intro q q' x hqq _ _
  exact False.elim (by omega)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Basic -/

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
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hcard

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

/- Upstream module: OAI.Combinatorics.Sensitivity.InitialPredicates -/

namespace OAI

/-! The separated Hamming-ball predicates and their explicit sensitive blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def blockCenter {M L : ℕ} (j : Fin M) : Fin M × Fin L → Bool :=
  fun p => decide (p.1 = j)

def baseBlock {M L : ℕ} (j : Fin M) : Finset (Fin M × Fin L) :=
  Finset.univ.filter fun p => p.1 = j

@[simp] theorem mem_baseBlock {M L : ℕ} (j : Fin M) (p : Fin M × Fin L) :
    p ∈ baseBlock j ↔ p.1 = j := by
  simp [baseBlock]

theorem baseBlock_card {M L : ℕ} (j : Fin M) : (baseBlock (L := L) j).card = L := by
  have h : (baseBlock (L := L) j).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p _
      exact Finset.mem_univ _
    · intro p hp q hq hpq
      exact Prod.ext (((mem_baseBlock j p).mp hp).trans ((mem_baseBlock j q).mp hq).symm) hpq
    · intro b _
      exact ⟨(j, b), (mem_baseBlock j (j, b)).mpr rfl, rfl⟩
  simpa using h

theorem baseBlock_nonempty {M L : ℕ} (hL : 0 < L) (j : Fin M) :
    (baseBlock (L := L) j).Nonempty := by
  rw [← Finset.card_pos, baseBlock_card]
  exact hL

theorem baseBlock_disjoint {M L : ℕ} :
    Pairwise fun i j : Fin M => Disjoint (baseBlock (L := L) i) (baseBlock j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  rintro ⟨a, b⟩ hi hj
  simp only [mem_baseBlock] at hi hj
  exact hij (hi.symm.trans hj)

theorem flip_zero_baseBlock {M L : ℕ} (j : Fin M) :
    flip (fun _ : Fin M × Fin L => false) (baseBlock j) = blockCenter j := by
  ext p
  simp [flip, blockCenter]

theorem hammingDist_zero_blockCenter {M L : ℕ} (j : Fin M) :
    hammingDist (fun _ : Fin M × Fin L => false) (blockCenter j) = L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L => false ≠ blockCenter j p) =
      baseBlock j := by
    ext p
    simp [blockCenter]
  rw [hammingDist, hs, baseBlock_card]

theorem hammingDist_blockCenter {M L : ℕ} (i j : Fin M) (hij : i ≠ j) :
    hammingDist (blockCenter (L := L) i) (blockCenter j) = 2 * L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L =>
      blockCenter i p ≠ blockCenter j p) =
      baseBlock i ∪ baseBlock j := by
    ext ⟨a, b⟩
    by_cases ha : a = i <;> by_cases hb : a = j <;> simp_all [blockCenter]
  rw [hammingDist, hs]
  rw [Finset.card_union_of_disjoint (baseBlock_disjoint hij), baseBlock_card, baseBlock_card]
  omega

def initialFamily (d M : ℕ) : Fin (d + 1) → (Fin M × Fin (d + 2) → Bool) → Bool :=
  fun q => ballPredicate blockCenter (d - q.val)

theorem initialFamily_nested (d M : ℕ) : NestedFamily (initialFamily d M) := by
  constructor
  intro q q' x hqq hx
  exact ballPredicate_nested blockCenter (by omega) x hx

theorem initialFamily_zero (d M : ℕ) (q : Fin (d + 1)) :
    initialFamily d M q (fun _ => false) = false := by
  have hn : ¬ ∃ c : Fin M,
      hammingDist (fun _ : Fin M × Fin (d + 2) => false) (blockCenter c) ≤ d - q.val := by
    rintro ⟨c, hc⟩
    rw [hammingDist_zero_blockCenter] at hc
    omega
  simp [initialFamily, ballPredicate, hn]

theorem initialFamily_baseBlock (d M : ℕ) (q : Fin (d + 1)) (j : Fin M) :
    initialFamily d M q (flip (fun _ => false) (baseBlock j)) = true := by
  rw [flip_zero_baseBlock]
  apply (ballPredicate_eq_true blockCenter (d - q.val) (blockCenter j)).2
  exact ⟨j, by simp⟩

theorem initialFamily_side_zero (d M : ℕ) :
    sideSensitivity (initialFamily d M) false ≤ d + 2 := by
  apply sideSensitivity_le
  intro q x hx
  have hs : ∀ a b : Fin M, a ≠ b →
      2 * ((d - q.val) + 1) < hammingDist (blockCenter (L := d + 2) a) (blockCenter b) := by
    intro a b hab
    rw [hammingDist_blockCenter a b hab]
    omega
  exact (ballPredicate_sensitivityAt_zero_le blockCenter (d - q.val) hs x hx).trans
    (by omega)

theorem initialFamily_side_one (d M : ℕ) :
    sideSensitivity (initialFamily d M) true ≤ (d + 2) * M := by
  apply sideSensitivity_le
  intro q x _
  simpa [Nat.mul_comm] using sensitivityAt_le_card (initialFamily d M q) x

theorem initialFamily_joint (d M : ℕ) (b : Bool) :
    jointSensitivity (initialFamily d M) b = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply jointSensitivity_le
  intro q q' x hqq hx hx'
  have hrad : d - q'.val < d - q.val := by omega
  unfold jointSensitivityAt
  have he : (Finset.univ.filter fun i =>
      initialFamily d M q (flip x {i}) ≠ initialFamily d M q x ∧
      initialFamily d M q' (flip x {i}) ≠ initialFamily d M q' x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    obtain ⟨hi, hi'⟩ := hi
    cases b with
    | false =>
        have hflip : initialFamily d M q' (flip x {i}) = true := by
          simpa [hx'] using hi'
        exact ballPredicate_no_joint_zero blockCenter hrad x i hx hflip
    | true =>
        have hflip : initialFamily d M q (flip x {i}) = false := by
          simpa [hx] using hi
        exact ballPredicate_no_joint_one blockCenter hrad x i hx' hflip
  rw [he]
  simp

theorem nearestDistance_blockCenter_zero (M L : ℕ) [NeZero M] :
    nearestDistance (blockCenter (M := M) (L := L)) (fun _ => false) = L := by
  simp [nearestDistance, hammingDist_zero_blockCenter]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Tournament -/

namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

structure RegularTournament (M : ℕ) extends Tournament (2 * M^2 + 1) where
  outdegree : ∀ i, (Finset.univ.filter (Adj i)).card = M^2

structure GoodLabeling {k : ℕ} (T : Tournament k) (r : ℕ) where
  label : Fin k → Fin k → Fin r
  good : ∀ I : Finset (Fin k), I.card = 16 → ∀ m : Fin k → Fin r,
    ∃ i ∈ I, ∃ j ∈ I, T.Adj i j ∧ label i j ≠ m j

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

theorem good_implies_card_lt_sixteen (I : Finset (Fin k)) (m : Fin k → Fin r)
    (h : ∀ i ∈ I, ∀ j ∈ I, T.Adj i j → A.label i j = m j) : I.card < 16 := by
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show 16 ≤ I.card by omega)
  obtain ⟨i, hi, j, hj, hij, hne⟩ := A.good J hJ m
  exact hne (h i (hJI hi) j (hJI hj) hij)

end GoodLabeling
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveDefinitions -/

namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

def gateIndex {h : ℕ} (q : Fin h) : Fin (h + 1) := (Fin.rev q).castSucc

theorem gateIndex_lt_last {h : ℕ} (q : Fin h) : gateIndex q < Fin.last h :=
  Fin.castSucc_lt_last _

theorem gateIndex_antitone {h : ℕ} {q q' : Fin h} (hqq : q ≤ q') :
    gateIndex q' ≤ gateIndex q := by
  exact Fin.rev_le_rev.mpr hqq

theorem gateIndex_strictAnti {h : ℕ} {q q' : Fin h} (hqq : q < q') :
    gateIndex q' < gateIndex q := by
  exact Fin.rev_lt_rev.mpr hqq

/-- A clause uses every target in its own row and one labeled gate per outgoing edge. -/
def rowClause {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
    ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false)

/-- The next-level predicate is the disjunction of the literal row clauses. -/
def recursiveFamily {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, rowClause T label F q x i = true)

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)

theorem recursiveFamily_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) : NestedFamily (recursiveFamily T label F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx
  exact (recursiveFamily_eq_true_iff T label F q x).mpr
    ⟨i, rowClause_nested T label F hF hqq x i hi⟩

theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht

theorem recursive_coordinates_card {k r : ℕ} {I : Type} [Fintype I] :
    Fintype.card ((Fin k × Fin r) × I) = k * r * Fintype.card I := by
  simp

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveBlocks -/

namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

def rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    Finset ((Fin k × Fin r) × I) :=
  (Finset.univ.product B).map
    ⟨fun p : Fin r × I => ((i, p.1), p.2), by
      intro p q hpq
      exact Prod.ext (congrArg (fun z => z.1.2) hpq) (congrArg (fun z : (Fin k × Fin r) × I => z.2) hpq)⟩

@[simp] theorem mem_rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (p : (Fin k × Fin r) × I) : p ∈ rowLift (r := r) i B ↔ p.1.1 = i ∧ p.2 ∈ B := by
  rcases p with ⟨⟨j, c⟩, a⟩
  unfold rowLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, hb, hp⟩
    change ((i, c'), b) = ((j, c), a) at hp
    cases hp
    exact ⟨rfl, (Finset.mem_product.mp hb).2⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨(c, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

theorem rowLift_card {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    (rowLift (r := r) i B).card = r * B.card := by
  simp [rowLift]

theorem rowLift_nonempty {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (hr : 0 < r) (hB : B.Nonempty) : (rowLift (r := r) i B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  exact ⟨((i, ⟨0, hr⟩), a), (mem_rowLift i B _).mpr ⟨rfl, ha⟩⟩

theorem rowLift_disjoint_of_ne {k r : ℕ} {I : Type} (i j : Fin k)
    (B C : Finset I) (hij : i ≠ j) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij (((mem_rowLift i B p).mp hp).1.symm.trans ((mem_rowLift j C p).mp hq).1)

theorem rowLift_disjoint {k r : ℕ} {I : Type} (i j : Fin k) (B C : Finset I)
    (hBC : Disjoint B C) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hBC ((mem_rowLift i B p).mp hp).2
    ((mem_rowLift j C p).mp hq).2

theorem rowLift_family_disjoint {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hB : Pairwise fun a b => Disjoint (blocks a) (blocks b)) :
    Pairwise fun a b : Fin k × K =>
      Disjoint (rowLift (r := r) a.1 (blocks a.2)) (rowLift b.1 (blocks b.2)) := by
  intro a b hab
  by_cases hrow : a.1 = b.1
  · apply rowLift_disjoint
    apply hB
    intro hcol
    exact hab (Prod.ext hrow hcol)
  · exact rowLift_disjoint_of_ne _ _ _ _ hrow

theorem recursiveChild_rowLift_same {k r : ℕ} {I : Type}
    (i : Fin k) (B : Finset I) (c : Fin r) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) i c =
      flip (fun _ => false) B := by
  funext a
  simp [recursiveChild, flip]

theorem recursiveChild_rowLift_other {k r : ℕ} {I : Type}
    (i j : Fin k) (B : Finset I) (c : Fin r) (hji : j ≠ i) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) j c =
      fun _ => false := by
  funext a
  simp [recursiveChild, flip, hji]

theorem recursiveFamily_rowLift {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hzero : ∀ q, F q (fun _ => false) = false) (B : Finset I)
    (hB : ∀ q, F q (flip (fun _ => false) B) = true) (i : Fin k) (q : Fin h) :
    recursiveFamily T label F q (flip (fun _ => false) (rowLift i B)) = true := by
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  refine ⟨i, (rowClause_eq_true_iff _ _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro c
    rw [recursiveChild_rowLift_same]
    exact hB _
  · intro j hij
    rw [recursiveChild_rowLift_other _ _ _ _ (T.ne_of_adj hij).symm]
    exact hzero _

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveFlips -/

namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveSets -/

namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩

@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _

def childChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c))

def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c) ∧
    F q' (flip (recursiveChild x j c) {a}) ≠ F q' (recursiveChild x j c))

@[simp] theorem childChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childChanges F q x j c).card = sensitivityAt (F q) (recursiveChild x j c) := by
  simp [childChanges, sensitivityAt]

@[simp] theorem childJointChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childJointChanges F q q' x j c).card =
      jointSensitivityAt (F q) (F q') (recursiveChild x j c) := by
  simp [childJointChanges, jointSensitivityAt]

theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

theorem rowClause_joint_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q q' : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i)
    (hc' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c) ∧
      F (gateIndex q') (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q') (recursiveChild x j c)) := by
  rcases rowClause_flip_change T label F q x i j c a hc with ht | ⟨hij, hcl, hq⟩
  · exact Or.inl ht
  · rcases rowClause_flip_change T label F q' x i j c a hc' with ht | hg
    · exact False.elim ((T.ne_of_adj hij) ht.1.symm)
    · exact Or.inr ⟨hij, hcl, hq, hg.2.2⟩

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveOne -/

namespace OAI

/-! The two recurrences for inputs at which the parent predicates accept. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_sensitivity_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true) :
    sensitivityAt (recursiveFamily T label F q) x ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T label F q x).mp hx
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childChanges F (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange (hy.trans hx.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    rcases rowClause_flip_change T label F q x i j c a hic with ⟨rfl, ht⟩ | ⟨hij, rfl, hg⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childChanges] using hg⟩
  have hU : U.card ≤ r * sideSensitivity F true := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (sideSensitivity F true)
      (fun c _ => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F true _ _ (hcond.1 c))
  have hV : V.card ≤ o * sideSensitivity F false := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childChanges F (gateIndex q) x j (label i j)) (sideSensitivity F false)
      (fun j hj => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F false _ _
          (hcond.2 j (Finset.mem_filter.mp hj).2))
  calc
    sensitivityAt (recursiveFamily T label F q) x ≤ (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * sideSensitivity F true + o * sideSensitivity F false := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

theorem recursive_side_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    sideSensitivity (recursiveFamily T label F) true ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_one_at T label F o ho q x hx

theorem recursive_joint_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq.le x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * sideSensitivity F true := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (sideSensitivity F true)
      (fun c _ => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F true _ _ (hcond.1 c))
  have hV : V.card ≤ o * jointSensitivity F false := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (jointSensitivity F false) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact jointSensitivityAt_le_jointSensitivity F false _ _ _
          (gateIndex_strictAnti hqq) (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * sideSensitivity F true + o * jointSensitivity F false := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

theorem recursive_joint_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    jointSensitivity (recursiveFamily T label F) true ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_one_at T label F hF o ho q q' hqq x hx hx'

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.TournamentCounts -/

namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2

theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  have hsum := Finset.sum_le_sum h
  have hc : I.card.choose 2 ≤ I.card := by
    rw [← T.card_internalEdges, ← T.sum_outdegree_eq]
    simpa only [Finset.sum_const_nat, mul_one] using hsum
  have hdouble : I.card * (I.card - 1) ≤ 2 * I.card + 1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have h4 : 4 ≤ I.card := by omega
  have ht : I.card - 1 + 1 = I.card := by omega
  nlinarith

end Paper320.Tournament

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveFailures -/

namespace OAI

/-! Fixed initial-input lists of clauses with exactly one failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

def targetFailures {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F (Fin.last h) (recursiveChild x i c) = false

def gateFailures {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧
    F (gateIndex q) (recursiveChild x j (label i j)) = true

def targetCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (targetFailures F x i).card = 1 ∧ gateFailures T label F q x i = ∅

def gateCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => targetFailures F x i = ∅ ∧ (gateFailures T label F q x i).card = 1

def targetWitness {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if hi : (targetFailures F x i).Nonempty then hi.choose else ⟨0, hr⟩

def gateWitness {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Fin k :=
  if hi : (gateFailures T label F q x i).Nonempty then hi.choose else i

theorem targetFailures_empty_iff {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    targetFailures F x i = ∅ ↔ ∀ c, F (Fin.last h) (recursiveChild x i c) = true := by
  simp [targetFailures, Finset.filter_eq_empty_iff]

theorem gateFailures_empty_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    gateFailures T label F q x i = ∅ ↔
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp [gateFailures, Finset.filter_eq_empty_iff]

theorem targetFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    targetFailures F x i = {targetWitness F x hr i} := by
  have hc := (Finset.mem_filter.mp hi).2.1
  obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (targetFailures F x i).Nonempty := hc' ▸ Finset.singleton_nonempty c
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    simp only [targetWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem gateFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    gateFailures T label F q x i = {gateWitness T label F q x i} := by
  have hc := (Finset.mem_filter.mp hi).2.2
  obtain ⟨j, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (gateFailures T label F q x i).Nonempty := hc' ▸ Finset.singleton_nonempty j
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    simp only [gateWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem targetCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (A : GoodLabeling T r) (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < 16 := by
  apply A.good_implies_card_lt_sixteen _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp (Finset.mem_filter.mp hi).2.2
  have hz := hF.rejects_of_le (gateIndex_lt_last q).le (hgate j hij)
  have hm : A.label i j ∈ targetFailures F x j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  rw [targetFailures_singleton T A.label F q x hr j hj, Finset.mem_singleton] at hm
  exact hm

theorem gateCandidates_neighbor {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j) :
    j = gateWitness T label F q x i := by
  have ht := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1
  have hon := hF.accepts_of_le (gateIndex_lt_last q).le (ht (label i j))
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hon⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateCandidates T label F q x).card ≤ 3 := by
  apply T.card_le_three_of_outdegree_le_one
  intro i hi
  apply le_trans (Finset.card_le_card (t := {gateWitness T label F q x i}) ?_)
    (by simp)
  intro j hj
  have h := Finset.mem_filter.mp hj
  exact Finset.mem_singleton.mpr (gateCandidates_neighbor T label F hF q x i j hi h.1 h.2)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveRepair -/

namespace OAI

/-! A successful raw-bit flip repairs the unique initial failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem repaired_target_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c c' : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hz : F (Fin.last h) (recursiveChild x i c') = false) : (i, c') = (j, c) := by
  by_contra hne
  have ht := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c'
  rw [recursiveChild_flip_other x j i c c' a hne, hz] at ht
  exact Bool.false_ne_true ht

theorem repaired_gate_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j j' : Fin k) (c : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hij' : T.Adj i j') (hon : F (gateIndex q) (recursiveChild x j' (label i j')) = true) :
    (j', label i j') = (j, c) := by
  by_contra hne
  have hg := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j' hij'
  rw [recursiveChild_flip_other x j j' c (label i j') a hne, hon] at hg
  exact Bool.false_ne_true hg.symm

theorem rowClause_repair_cases {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hi : rowClause T label F q x i = false)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true) :
    (i ∈ targetCandidates T label F q x ∧ j = i ∧
      F (Fin.last h) (recursiveChild x j c) = false ∧
      F (Fin.last h) (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ gateCandidates T label F q x ∧ T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (recursiveChild x j c) = true ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) = false) := by
  have hchange : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
    simp [hi, hf]
  rcases rowClause_flip_change T label F q x i j c a hchange with
    ⟨hji, ht⟩ | ⟨hij, rfl, hg⟩
  · subst j
    have hton := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c
    rw [recursiveChild_flip_same] at hton
    have htoff : F (Fin.last h) (recursiveChild x i c) = false := by
      cases hc : F (Fin.last h) (recursiveChild x i c)
      · rfl
      · exact False.elim (ht (hton.trans hc.symm))
    have htargets : targetFailures F x i = {c} := by
      ext c'
      simp only [targetFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hfalse
        exact congrArg Prod.snd (repaired_target_location T label F q x i i c c' a hf hfalse)
      · rintro rfl
        exact htoff
    have hgates : gateFailures T label F q x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j' hj'
      have h := (Finset.mem_filter.mp hj').2
      have heq := repaired_gate_location T label F q x i i j' c a hf h.1 h.2
      exact T.ne_of_adj h.1 (congrArg Prod.fst heq).symm
    have hmem : i ∈ targetCandidates T label F q x := by
      simp [targetCandidates, htargets, hgates]
    exact Or.inl ⟨hmem, rfl, htoff, hton⟩
  · have hgoff := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j hij
    rw [recursiveChild_flip_same] at hgoff
    have hgon : F (gateIndex q) (recursiveChild x j (label i j)) = true := by
      cases hc : F (gateIndex q) (recursiveChild x j (label i j))
      · exact False.elim (hg (hgoff.trans hc.symm))
      · rfl
    have htargets : targetFailures F x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c' hc'
      have heq := repaired_target_location T label F q x i j (label i j) c' a hf
        (Finset.mem_filter.mp hc').2
      exact T.ne_of_adj hij (congrArg Prod.fst heq)
    have hgates : gateFailures T label F q x i = {j} := by
      ext j'
      simp only [gateFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hij', hon⟩
        exact congrArg Prod.fst (repaired_gate_location T label F q x i j j' (label i j) a hf hij' hon)
      · rintro rfl
        exact ⟨hij, hgon⟩
    have hmem : i ∈ gateCandidates T label F q x := by
      simp [gateCandidates, htargets, hgates]
    exact Or.inr ⟨hmem, hij, rfl, hgon, hgoff⟩

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveCandidates -/

namespace OAI

/-! Unique failed children and the unique possible sink of the gate-clause list. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetWitness_false {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    F (Fin.last h) (recursiveChild x i (targetWitness F x hr i)) = false := by
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    rw [targetFailures_singleton T label F q x hr i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem targetWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) (c : Fin r)
    (hc : F (Fin.last h) (recursiveChild x i c) = false) : c = targetWitness F x hr i := by
  have hm : c ∈ targetFailures F x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rwa [targetFailures_singleton T label F q x hr i hi, Finset.mem_singleton] at hm

theorem gateWitness_spec {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    T.Adj i (gateWitness T label F q x i) ∧
      F (gateIndex q) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = true := by
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    rw [gateFailures_singleton T label F q x i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem gateWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) (j : Fin k) (hij : T.Adj i j)
    (hj : F (gateIndex q) (recursiveChild x j (label i j)) = true) :
    j = gateWitness T label F q x i := by
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hj⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

def gateSinks {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  (gateCandidates T label F q x).filter fun i =>
    ∀ j ∈ gateCandidates T label F q x, ¬ T.Adj i j

theorem gateSinks_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateSinks T label F q x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact T.internal_sink_unique (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem nonsink_gateWitness_mem {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hs : i ∉ gateSinks T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  have he : ∃ j ∈ gateCandidates T label F q x, T.Adj i j := by
    by_contra hn
    apply hs
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro j hj hij
    exact hn ⟨j, hj, hij⟩
  obtain ⟨j, hj, hij⟩ := he
  rwa [← gateCandidates_neighbor T label F hF q x i j hi hj hij]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveZero -/

namespace OAI

/-! The zero-side recurrence separates the unique possible gate-list sink. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_sensitivity_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i => childJointChanges F (gateIndex q) (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childChanges F (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x) ⊆ U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon : recursiveFamily T A.label F q (flip x {((j, c), a)}) = true := by
      cases hy : recursiveFamily T A.label F q (flip x {((j, c), a)})
      · exact False.elim (hchange (hy.trans hx.symm))
      · rfl
    obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T A.label F q _).mp hon
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn : F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by simp [hgon, hgoff]
        simpa [childChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q).le hgoff
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 16 * sideSensitivity F false := by
    calc
      U.card ≤ TC.card * sideSensitivity F false :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F false _ _
            (targetWitness_false T A.label F q x hr i hi))
      _ ≤ 16 * sideSensitivity F false := Nat.mul_le_mul_right _
        (Nat.le_of_lt (targetCandidates_card T A F hF q x hr))
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ NC.card * jointSensitivity F true :=
        card_biUnion_le_mul NC _ _ (fun i hi => by
          have hg := Finset.mem_sdiff.mp hi
          have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
          have hgate := (gateWitness_spec T A.label F q x i hg.1).2
          have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1
            (A.label i (w i))
          rw [childJointChanges_card]
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _ (gateIndex_lt_last q) hgate htarget)
      _ ≤ GC.card * jointSensitivity F true := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      _ ≤ 3 * jointSensitivity F true := Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  have hW : W.card ≤ sideSensitivity F true := by
    calc
      W.card ≤ SC.card * sideSensitivity F true :=
        card_biUnion_le_mul SC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F true _ _
            (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2)
      _ ≤ 1 * sideSensitivity F true := Nat.mul_le_mul_right _ (gateSinks_card T A.label F q x)
      _ = _ := Nat.one_mul _
  calc
    sensitivityAt (recursiveFamily T A.label F q) x ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 16 * sideSensitivity F false + (3 * jointSensitivity F true + sideSensitivity F true) :=
      Nat.add_le_add hU (Nat.add_le_add hV hW)
    _ = _ := by omega

theorem recursive_side_zero {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    sideSensitivity (recursiveFamily T A.label F) false ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_zero_at T A F hF hr q x hx

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveJointZero -/

namespace OAI

/-! The joint zero recurrence uses the fixed weaker-threshold failure lists. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_joint_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false) :
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      16 * sideSensitivity F false + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := GC.biUnion fun i => childJointChanges F (gateIndex q') (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x ∧
      recursiveFamily T A.label F q' (flip x {p}) ≠ recursiveFamily T A.label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon' : recursiveFamily T A.label F q' (flip x {((j, c), a)}) = true := by
      cases hy : recursiveFamily T A.label F q' (flip x {((j, c), a)})
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label F q' _).mp hon'
    have hi := rowClause_nested T A.label F hF hqq.le _ i hi'
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      have hgon' := hF.accepts_of_le (gateIndex_strictAnti hqq).le hgon
      have hgoff' := ((rowClause_eq_true_iff T A.label F q' _ i).mp hi').2 j hij
      rw [recursiveChild_flip_same] at hgoff'
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, ?_⟩
      have hn :
          F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
            F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
          F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by
        simp [hgon, hgoff, hgon', hgoff']
      simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 16 * sideSensitivity F false := by
    calc
      U.card ≤ TC.card * sideSensitivity F false :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F false _ _
            (targetWitness_false T A.label F q x hr i hi))
      _ ≤ 16 * sideSensitivity F false := Nat.mul_le_mul_right _
        (Nat.le_of_lt (targetCandidates_card T A F hF q x hr))
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ GC.card * jointSensitivity F true :=
        card_biUnion_le_mul GC _ _ (fun i hi => by
          rw [childJointChanges_card]
          have hg := (gateWitness_spec T A.label F q x i hi).2
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _
            (gateIndex_strictAnti hqq) (hF.accepts_of_le (gateIndex_strictAnti hqq).le hg) hg)
      _ ≤ 3 * jointSensitivity F true := Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  calc
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hU hV

theorem recursive_joint_zero {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    jointSensitivity (recursiveFamily T A.label F) false ≤
      16 * sideSensitivity F false + 3 * jointSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_zero_at T A F hF hr q q' hqq x hx hx'

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Recursive -/

namespace OAI

/-! Four sensitivity recurrences for a regular tournament and a good labeling. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_four_recurrences {M r h : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    let P := recursiveFamily T.toTournament A.label F
    (sideSensitivity P true ≤ M ^ 2 * sideSensitivity F false + r * sideSensitivity F true) ∧
    (jointSensitivity P true ≤ M ^ 2 * jointSensitivity F false + r * sideSensitivity F true) ∧
    (sideSensitivity P false ≤ 16 * sideSensitivity F false + sideSensitivity F true +
      3 * jointSensitivity F true) ∧
    (jointSensitivity P false ≤ 16 * sideSensitivity F false + 3 * jointSensitivity F true) := by
  exact ⟨recursive_side_one T.toTournament A.label F (M ^ 2) T.outdegree,
    recursive_joint_one T.toTournament A.label F hF (M ^ 2) T.outdegree,
    recursive_side_zero T.toTournament A F hF hr,
    recursive_joint_zero T.toTournament A F hF hr⟩

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Tower -/

namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def TowerCoordinates (k r : ℕ) (I : Type) : ℕ → Type
  | 0 => I
  | n + 1 => (Fin k × Fin r) × TowerCoordinates k r I n

instance towerCoordinatesFintype (k r : ℕ) (I : Type) [Fintype I] :
    (n : ℕ) → Fintype (TowerCoordinates k r I n)
  | 0 => inferInstanceAs (Fintype I)
  | n + 1 => by
    letI := towerCoordinatesFintype k r I n
    exact inferInstanceAs (Fintype ((Fin k × Fin r) × TowerCoordinates k r I n))

def TowerBlockIndex (k : ℕ) (K : Type) : ℕ → Type
  | 0 => K
  | n + 1 => Fin k × TowerBlockIndex k K n

instance towerBlockIndexFintype (k : ℕ) (K : Type) [Fintype K] :
    (n : ℕ) → Fintype (TowerBlockIndex k K n)
  | 0 => inferInstanceAs (Fintype K)
  | n + 1 => by
    letI := towerBlockIndexFintype k K n
    exact inferInstanceAs (Fintype (Fin k × TowerBlockIndex k K n))

def towerFamily {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) :
    (n h : ℕ) → Fin h → (TowerCoordinates k r I n → Bool) → Bool
  | 0, h => base h
  | n + 1, h => recursiveFamily T label (towerFamily T label base n (h + 1))

def towerBlocks {k r : ℕ} {I K : Type} (blocks : K → Finset I) :
    (n : ℕ) → TowerBlockIndex k K n → Finset (TowerCoordinates k r I n)
  | 0, b => blocks b
  | n + 1, b => rowLift b.1 (towerBlocks blocks n b.2)

/-- Extend a prescribed initial family to unused index counts without adding assumptions. -/
def baseExtension {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool)
    (h : ℕ) (q : Fin h) (x : I → Bool) : Bool :=
  if he : h = D then F (Fin.cast he q) x else false

@[simp] theorem baseExtension_same {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool) :
    baseExtension D F D = F := by
  funext q x
  simp [baseExtension]

theorem tower_coordinates_card {k r : ℕ} {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (TowerCoordinates k r I n) = (k * r) ^ n * Fintype.card I := by
  induction n with
  | zero =>
    change Fintype.card I = (k * r) ^ 0 * Fintype.card I
    simp
  | succ n ih =>
    change Fintype.card ((Fin k × Fin r) × TowerCoordinates k r I n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem tower_block_index_card {k : ℕ} {K : Type} [Fintype K] (n : ℕ) :
    Fintype.card (TowerBlockIndex k K n) = k ^ n * Fintype.card K := by
  induction n with
  | zero =>
    change Fintype.card K = k ^ 0 * Fintype.card K
    simp
  | succ n ih =>
    change Fintype.card (Fin k × TowerBlockIndex k K n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem towerBlocks_card {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (L : ℕ) (hL : ∀ b, (blocks b).card = L) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).card = r ^ n * L := by
  induction n with
  | zero =>
    change (blocks b).card = r ^ 0 * L
    simpa only [pow_zero, one_mul] using hL b
  | succ n ih =>
    change (rowLift b.1 (towerBlocks blocks n b.2)).card = _
    rw [rowLift_card, ih]
    ring

theorem towerBlocks_nonempty {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).Nonempty := by
  induction n with
  | zero => exact hne b
  | succ n ih => exact rowLift_nonempty b.1 _ hr (ih b.2)

theorem towerBlocks_pairwise {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    Pairwise fun a b => Disjoint (towerBlocks (k := k) (r := r) blocks n a) (towerBlocks blocks n b) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact rowLift_family_disjoint (towerBlocks blocks n) ih

theorem towerFamily_nested {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (n h : ℕ) (hbase : NestedFamily (base (h + n))) :
    NestedFamily (towerFamily T label base n h) := by
  induction n generalizing h with
  | zero =>
    change NestedFamily (base h)
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_nested
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by
  induction n generalizing h with
  | zero =>
    change ∀ b q, base h q (flip (fun _ => false) (blocks b)) = true
    simpa only [Nat.add_zero] using hblocks
  | succ n ih =>
    intro b q
    have he : (h + 1) + n = h + (n + 1) := by omega
    have hz : ∀ q, base ((h + 1) + n) q (fun _ => false) = false := by
      rw [he]
      exact hzero
    have hb : ∀ b q, base ((h + 1) + n) q (flip (fun _ => false) (blocks b)) = true := by
      rw [he]
      exact hblocks
    exact recursiveFamily_rowLift T label _
      (towerFamily_zero T label base hr n (h + 1) hz)
      (towerBlocks blocks n b.2) (ih (h + 1) hz hb b.2) b.1 q

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.RecursiveChildren -/

namespace OAI

/-! Each row clause uses exactly the stated number of distinct child blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def rowChildren {k r : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (i : Fin k) : Finset (Fin k × Fin r) :=
  Finset.univ.image (fun c => (i, c)) ∪
    (Finset.univ.filter (T.Adj i)).image (fun j => (j, label i j))

theorem rowChildren_disjoint {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    Disjoint (Finset.univ.image fun c => (i, c))
      ((Finset.univ.filter (T.Adj i)).image fun j => (j, label i j)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hq
  have hji : j = i := congrArg Prod.fst he
  exact T.loopless i (hji ▸ (Finset.mem_filter.mp hj).2)

theorem rowChildren_card {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    (rowChildren T label i).card = r + (Finset.univ.filter (T.Adj i)).card := by
  rw [rowChildren, Finset.card_union_of_disjoint (rowChildren_disjoint T label i)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

theorem regular_rowChildren_card {M r : ℕ} (T : RegularTournament M)
    (label : Fin (2 * M ^ 2 + 1) → Fin (2 * M ^ 2 + 1) → Fin r)
    (i : Fin (2 * M ^ 2 + 1)) :
    (rowChildren T.toTournament label i).card = r + M ^ 2 := by
  rw [rowChildren_card, T.outdegree]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.TowerProfiles -/

namespace OAI

/-! The fixed-initial-height profiles and their exact four recurrences. -/

noncomputable section
open scoped Classical

namespace Paper320

def towerSide {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  sideSensitivity (towerFamily T label base n (D - n)) b

def towerJoint {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  jointSensitivity (towerFamily T label base n (D - n)) b

@[simp] theorem towerSide_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerSide T label base D 0 b = sideSensitivity (base D) b := by
  rfl

@[simp] theorem towerJoint_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerJoint T label base D 0 b = jointSensitivity (base D) b := by
  rfl

theorem tower_four_recurrences {M r : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (hn : n < D) (hr : 0 < r) (hbase : NestedFamily (base D)) :
    (towerSide T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerSide T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerJoint T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerSide T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      towerSide T.toTournament A.label base D n true +
      3 * towerJoint T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      3 * towerJoint T.toTournament A.label base D n true) := by
  have he : (D - (n + 1) + 1) + n = D := by omega
  have hf : NestedFamily (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) := by
    apply towerFamily_nested
    rwa [he]
  have H := recursive_four_recurrences T A
    (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) hf hr
  dsimp only at H
  change (sideSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (sideSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _) at H
  have hcount : D - (n + 1) + 1 = D - n := by omega
  rw [hcount] at H
  exact H

theorem towerBlocks_family_card {k r : ℕ} {I K : Type} [Fintype K]
    (blocks : K → Finset I) (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    (Finset.univ.image (towerBlocks (k := k) (r := r) blocks n)).card = k ^ n * Fintype.card K := by
  have hinj : Function.Injective (towerBlocks (k := k) (r := r) blocks n) := by
    intro a b hab
    by_contra hneab
    obtain ⟨i, hi⟩ := towerBlocks_nonempty blocks hr hne n a
    exact Finset.disjoint_left.mp (towerBlocks_pairwise blocks hd n hneab) hi (by simpa [← hab] using hi)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, tower_block_index_card]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.ProfileArithmetic -/

namespace OAI

/-! The four raw recurrences imply the two normalized scalar recurrences. -/

noncomputable section

namespace Paper320

def normalizedMax (M : ℝ) (n : ℕ) (s₀ s₁ : ℝ) : ℝ :=
  max (s₀ / M ^ n) (s₁ / M ^ (n + 1))

theorem normalizedMax_nonneg {M s₀ s₁ : ℝ} {n : ℕ}
    (hM : 0 < M) (hs₀ : 0 ≤ s₀) : 0 ≤ normalizedMax M n s₀ s₁ :=
  (div_nonneg hs₀ (pow_pos hM n).le).trans (le_max_left _ _)

theorem le_normalizedMax_zero {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₀ ≤ normalizedMax M n s₀ s₁ * M ^ n :=
  (div_le_iff₀ (pow_pos hM n)).mp (le_max_left _ _)

theorem le_normalizedMax_one {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₁ ≤ normalizedMax M n s₀ s₁ * M ^ (n + 1) :=
  (div_le_iff₀ (pow_pos hM (n + 1))).mp (le_max_right _ _)

theorem normalizedMax_le {M s₀ s₁ u : ℝ} {n : ℕ} (hM : 0 < M)
    (h₀ : s₀ ≤ u * M ^ n) (h₁ : s₁ ≤ u * M ^ (n + 1)) :
    normalizedMax M n s₀ s₁ ≤ u :=
  max_le ((div_le_iff₀ (pow_pos hM n)).mpr h₀)
    ((div_le_iff₀ (pow_pos hM (n + 1))).mpr h₁)

theorem raw_profiles_step {M r ε u v p : ℝ}
    (hM : 0 < M) (hp : 0 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hεr : r ≤ ε * M) (hεt : 16 ≤ ε * M)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ}
    (hs₀ : s₀ ≤ u * p) (hs₁ : s₁ ≤ u * (p * M))
    (hj₀ : j₀ ≤ v * p) (hj₁ : j₁ ≤ v * (p * M))
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    s₀' ≤ ((1 + ε) * u + 3 * v) * (p * M) ∧
    s₁' ≤ ((1 + ε) * u + 3 * v) * (p * M * M) ∧
    j₀' ≤ (ε * u + 3 * v) * (p * M) ∧
    j₁' ≤ (ε * u + 3 * v) * (p * M * M) := by
  have hup : 0 ≤ u * p := mul_nonneg hu hp
  have hupM : 0 ≤ u * (p * M) := mul_nonneg hu (mul_nonneg hp hM.le)
  have hvpMM : 0 ≤ v * (p * M * M) := by positivity
  have ht := mul_le_mul_of_nonneg_right hεt hup
  have hr' := mul_le_mul_of_nonneg_right hεr hupM
  have a₀ := mul_le_mul_of_nonneg_left hs₀ (show (0 : ℝ) ≤ 16 by norm_num)
  have a₁ := mul_le_mul_of_nonneg_left hs₀ (sq_nonneg M)
  have b₀ := mul_le_mul_of_nonneg_left hj₀ (sq_nonneg M)
  have b₁ := mul_le_mul_of_nonneg_left hj₁ (show (0 : ℝ) ≤ 3 by norm_num)
  have c₁ := mul_le_mul_of_nonneg_left hs₁ hr
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem normalized_profiles_step {M r ε : ℝ} {n : ℕ}
    (hM : 0 < M) (hr : 0 ≤ r) (hεr : r / M ≤ ε) (hεt : 16 / M ≤ ε)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ} (hs₀ : 0 ≤ s₀) (hj₀ : 0 ≤ j₀)
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    normalizedMax M (n + 1) s₀' s₁' ≤
      (1 + ε) * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ ∧
    normalizedMax M (n + 1) j₀' j₁' ≤
      ε * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ := by
  have hs₁b := le_normalizedMax_one (s₀ := s₀) (s₁ := s₁) (n := n) hM
  have hj₁b := le_normalizedMax_one (s₀ := j₀) (s₁ := j₁) (n := n) hM
  rw [pow_succ] at hs₁b hj₁b
  obtain ⟨a, b, c, d⟩ := raw_profiles_step hM (pow_pos hM n).le
    (normalizedMax_nonneg hM hs₀) (normalizedMax_nonneg hM hj₀) hr
    ((div_le_iff₀ hM).mp hεr) ((div_le_iff₀ hM).mp hεt)
    (le_normalizedMax_zero hM) hs₁b (le_normalizedMax_zero hM) hj₁b
    hS₀ hS₁ hJ₀ hJ₁
  constructor
  · apply normalizedMax_le hM <;> simpa only [pow_succ] using (by assumption)
  · apply normalizedMax_le hM <;> simpa only [pow_succ] using (by assumption)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.ScalarBounds -/

namespace OAI

/-! Scalar bounds for the two coupled sensitivity profiles. -/

namespace Paper320

theorem geometric_error_le {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ≤ L := by
  have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
  have hb := (mul_le_mul_of_nonneg_left hp hε).trans hbudget
  have hm := mul_le_mul_of_nonneg_right hb hL
  rw [pow_succ] at hm
  nlinarith [mul_nonneg hε hL]

theorem coupled_profiles_bound (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by
  have strong : ∀ n ≤ d,
      u n ≤ L + (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ∧
        v n ≤ ε * L * (3 ^ n - 1) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using And.intro hu0 hv0
    | succ n ih =>
        intro hn
        have hnd : n ≤ d := by omega
        obtain ⟨hun, hvn⟩ := ih hnd
        have he := geometric_error_le hnd hε hL hbudget
        have hun' : u n ≤ 2 * L := by linarith
        have heu := mul_le_mul_of_nonneg_left hun' hε
        have hnu := hu n (by omega)
        have hnv := hv n (by omega)
        constructor
        · rw [pow_succ]
          nlinarith [mul_nonneg hε hL]
        · rw [pow_succ]
          nlinarith
  intro n hn
  obtain ⟨hun, hvn⟩ := strong n hn
  have he := geometric_error_le hn hε hL hbudget
  exact ⟨by linarith, hvn⟩

end Paper320

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.QuantitativeProfiles -/

namespace OAI

/-! Quantitative bounds for any literal profiles satisfying the four recurrences. -/

noncomputable section

namespace Paper320

theorem quantitative_profile_bounds (d L M r : ℕ) (hM : 0 < M)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2)
    (S J : ℕ → Bool → ℕ)
    (hS₀ : S 0 false ≤ L) (hS₁ : S 0 true ≤ L * M)
    (hJ₀ : J 0 false = 0) (hJ₁ : J 0 true = 0)
    (hstepS₀ : ∀ n < d, S (n + 1) false ≤ 16 * S n false + S n true + 3 * J n true)
    (hstepS₁ : ∀ n < d, S (n + 1) true ≤ M ^ 2 * S n false + r * S n true)
    (hstepJ₀ : ∀ n < d, J (n + 1) false ≤ 16 * S n false + 3 * J n true)
    (hstepJ₁ : ∀ n < d, J (n + 1) true ≤ M ^ 2 * J n false + r * S n true) :
    ∀ n ≤ d, S n false ≤ 2 * L * M ^ n ∧ S n true ≤ 2 * L * M ^ (n + 1) := by
  let ε : ℝ := ((max r 16 : ℕ) : ℝ) / M
  let u : ℕ → ℝ := fun n => normalizedMax M n (S n false) (S n true)
  let v : ℕ → ℝ := fun n => normalizedMax M n (J n false) (J n true)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hε : 0 ≤ ε := by positivity
  have hεr : (r : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_left r 16
  have hεt : (16 : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_right r 16
  have hu0 : u 0 ≤ L := by
    apply normalizedMax_le hMr
    · simpa using (show (S 0 false : ℝ) ≤ L by exact_mod_cast hS₀)
    · simpa using (show (S 0 true : ℝ) ≤ (L : ℝ) * M by exact_mod_cast hS₁)
  have hv0 : v 0 ≤ 0 := by simp [v, normalizedMax, hJ₀, hJ₁]
  have hstep (n : ℕ) (hn : n < d) :
      u (n + 1) ≤ (1 + ε) * u n + 3 * v n ∧
      v (n + 1) ≤ ε * u n + 3 * v n := by
    apply normalized_profiles_step hMr (by positivity) hεr hεt (by positivity) (by positivity)
    · exact_mod_cast hstepS₀ n hn
    · exact_mod_cast hstepS₁ n hn
    · exact_mod_cast hstepJ₀ n hn
    · exact_mod_cast hstepJ₁ n hn
  have hb := coupled_profiles_bound d u v ε L hε (by positivity) hbudget hu0 hv0
    (fun n hn => (hstep n hn).1) (fun n hn => (hstep n hn).2)
  intro n hn
  have hu := (hb n hn).1
  have hzero : (S n false : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ n := by
    exact (le_normalizedMax_zero hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  have hone : (S n true : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ (n + 1) := by
    exact (le_normalizedMax_one hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  exact ⟨by exact_mod_cast hzero, by exact_mod_cast hone⟩

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Composition -/

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

/- Upstream module: OAI.Combinatorics.Sensitivity.Or -/

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

/- Upstream module: OAI.Combinatorics.Sensitivity.Reindex -/

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

/- Upstream module: OAI.Combinatorics.Sensitivity.Construction -/

namespace OAI

/-! The initial family, recursively constructed predicates, and final OR. -/

noncomputable section
open scoped Classical

namespace Paper320

def constructionBase (d M : ℕ) := baseExtension (d + 1) (initialFamily d M)

abbrev ConstructionCoordinates (d M r n : ℕ) :=
  TowerCoordinates (2 * M ^ 2 + 1) r (Fin M × Fin (d + 2)) n

def terminalPredicate {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (ConstructionCoordinates d M r d → Bool) → Bool :=
  towerFamily T.toTournament A.label (constructionBase d M) d 1 0

theorem construction_base_nested (d M : ℕ) :
    NestedFamily (constructionBase d M (d + 1)) := by
  simpa only [constructionBase, baseExtension_same] using initialFamily_nested d M

theorem construction_base_zero (d M : ℕ) :
    ∀ q, constructionBase d M (1 + d) q (fun _ => false) = false := by
  rw [Nat.add_comm 1 d]
  simpa only [constructionBase, baseExtension_same] using initialFamily_zero d M

theorem construction_base_blocks (d M : ℕ) :
    ∀ b q, constructionBase d M (1 + d) q
      (flip (fun _ => false) (baseBlock b)) = true := by
  rw [Nat.add_comm 1 d]
  intro b q
  simpa only [constructionBase, baseExtension_same] using initialFamily_baseBlock d M q b

theorem terminalPredicate_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    terminalPredicate d T A (fun _ => false) = false :=
  towerFamily_zero T.toTournament A.label (constructionBase d M) hr d 1
    (construction_base_zero d M) 0

theorem terminalPredicate_blocks {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r)
    (b : TowerBlockIndex (2 * M ^ 2 + 1) (Fin M) d) :
    terminalPredicate d T A (flip (fun _ => false)
      (towerBlocks (r := r) (baseBlock (L := d + 2)) d b)) = true :=
  towerFamily_blocks T.toTournament A.label (constructionBase d M)
    (baseBlock (L := d + 2)) hr d 1 (construction_base_zero d M)
    (construction_base_blocks d M) b 0

theorem terminalPredicate_blockSensitivity {M r : ℕ} (d : ℕ)
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (terminalPredicate d T A) (fun _ => false) := by
  have h := le_blockSensitivityAt_of_family (terminalPredicate d T A) (fun _ => false)
    (towerBlocks (r := r) (baseBlock (L := d + 2)) d)
    (towerBlocks_nonempty (baseBlock (L := d + 2)) hr
      (baseBlock_nonempty (by omega)) d)
    (towerBlocks_pairwise (baseBlock (L := d + 2)) baseBlock_disjoint d)
    (fun b => by rw [terminalPredicate_blocks d T A hr, terminalPredicate_zero d T A hr]; decide)
  simpa only [tower_block_index_card, Fintype.card_fin, Nat.mul_comm] using h

theorem construction_profiles {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    ∀ n ≤ d,
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n false ≤
        2 * (d + 2) * M ^ n ∧
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n true ≤
        2 * (d + 2) * M ^ (n + 1) := by
  have hstep (n : ℕ) (hn : n < d) := tower_four_recurrences T A (constructionBase d M)
    (d + 1) n (by omega) hr (construction_base_nested d M)
  apply quantitative_profile_bounds d (d + 2) M r hM hbudget
    (towerSide T.toTournament A.label (constructionBase d M) (d + 1))
    (towerJoint T.toTournament A.label (constructionBase d M) (d + 1))
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using initialFamily_side_zero d M
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using initialFamily_side_one d M
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using initialFamily_joint d M false
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using initialFamily_joint d M true
  · exact fun n hn => (hstep n hn).2.2.1
  · exact fun n hn => (hstep n hn).1
  · exact fun n hn => (hstep n hn).2.2.2
  · exact fun n hn => (hstep n hn).2.1

theorem terminalPredicate_sensitivityAt {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    (∀ x, terminalPredicate d T A x = false →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ d) ∧
    (∀ x, terminalPredicate d T A x = true →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ (d + 1)) := by
  have hs := construction_profiles d T A hM hr hbudget d (le_refl d)
  have he : d + 1 - d = 1 := by omega
  simp only [towerSide] at hs
  rw [he] at hs
  exact ⟨fun x hx => (sensitivityAt_le_sideSensitivity _ false 0 x hx).trans hs.1,
    fun x hx => (sensitivityAt_le_sideSensitivity _ true 0 x hx).trans hs.2⟩

def finalBoolean {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin M × ConstructionCoordinates d M r d → Bool) → Bool :=
  orCopies (K := Fin M) (terminalPredicate d T A)

theorem finalBoolean_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalBoolean d T A (fun _ => false) = false :=
  orCopies_zero _ (terminalPredicate_zero d T A hr)

theorem finalBoolean_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalBoolean d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  obtain ⟨h₀, h₁⟩ := terminalPredicate_sensitivityAt d T A hM hr hbudget
  have h := sensitivity_orCopies_le (K := Fin M) (terminalPredicate d T A) _ _ h₀ h₁
  have he : M * (2 * (d + 2) * M ^ d) = 2 * (d + 2) * M ^ (d + 1) := by ring
  simpa only [finalBoolean, Fintype.card_fin, he, max_self] using h

theorem finalBoolean_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalBoolean d T A) (fun _ => false) := by
  have h := (Nat.mul_le_mul_left M (terminalPredicate_blockSensitivity d T A hr)).trans
    (by simpa only [Fintype.card_fin] using
      blockSensitivityAt_orCopies_zero (K := Fin M) _ (terminalPredicate_zero d T A hr))
  change M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt
    (orCopies (K := Fin M) (terminalPredicate d T A)) (fun _ => false)
  calc
    _ = M * (M * (2 * M ^ 2 + 1) ^ d) := by ring
    _ ≤ _ := h

def constructionDimension (d M r : ℕ) : ℕ :=
  (d + 2) * M ^ 2 * ((2 * M ^ 2 + 1) * r) ^ d

theorem final_coordinates_card (d M r : ℕ) :
    Fintype.card (Fin M × ConstructionCoordinates d M r d) = constructionDimension d M r := by
  rw [Fintype.card_prod, tower_coordinates_card]
  simp only [Fintype.card_prod, Fintype.card_fin, constructionDimension]
  ring

def finalWitness {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin (constructionDimension d M r) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (final_coordinates_card d M r)) (finalBoolean d T A)

theorem finalWitness_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalWitness d T A (fun _ => false) = false := finalBoolean_zero d T A hr

theorem finalWitness_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalWitness d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  rw [finalWitness, sensitivity_reindex]
  exact finalBoolean_sensitivity d T A hM hr hbudget

theorem finalWitness_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalWitness d T A) (fun _ => false) := by
  rw [finalWitness, blockSensitivityAt_reindex]
  exact finalBoolean_blockSensitivity d T A hr

theorem constructionDimension_pos {d M r : ℕ} (hM : 0 < M) (hr : 0 < r) :
    0 < constructionDimension d M r := by
  unfold constructionDimension
  positivity

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.LabelingConstraints -/

namespace OAI

/-! The labeling constraints are exactly fixed values on the internal edges. -/

noncomputable section
open scoped Classical

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem mem_internalEdges {I : Finset (Fin k)} {p : Fin k × Fin k} :
    p ∈ T.internalEdges I ↔ (p.1 ∈ I ∧ p.2 ∈ I) ∧ T.Adj p.1 p.2 := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_product]

theorem labelingConstraint_iff {α β : Type} [Nonempty α]
    (s : Finset α) (v : α → Fin k) (m : α → β) (hv : Function.Injective v)
    (A : (Fin k × Fin k) → β) :
    (∀ i ∈ s, ∀ j ∈ s, T.Adj (v i) (v j) → A (v i,v j) = m j) ↔
      ∀ p ∈ T.internalEdges (s.image v), A p = m (Function.invFun v p.2) := by
  constructor
  · intro h p hp
    obtain ⟨⟨hp₁,hp₂⟩,ha⟩ := T.mem_internalEdges.mp hp
    obtain ⟨i,hi,hvi⟩ := Finset.mem_image.mp hp₁
    obtain ⟨j,hj,hvj⟩ := Finset.mem_image.mp hp₂
    have he : p = (v i,v j) := Prod.ext hvi.symm hvj.symm
    subst p
    rw [Function.leftInverse_invFun hv j]
    exact h i hi j hj ha
  · intro h i hi j hj ha
    have hp : (v i,v j) ∈ T.internalEdges (s.image v) :=
      T.mem_internalEdges.mpr ⟨⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,
        Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩,ha⟩
    simpa only [Function.leftInverse_invFun hv j] using h (v i,v j) hp

end Paper320.Tournament

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.FixedCoordinates -/

namespace OAI

/-! Exact finite counting when a specified set of coordinates is fixed. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

def fixedCoordinatesEquiv (s : Finset α) (v : α → β) :
    {f : α → β // ∀ i ∈ s, f i = v i} ≃ ({i : α // i ∉ s} → β) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then v i else f ⟨i,h⟩, by
    intro i hi
    simp only [dif_pos hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dif_pos hi]
      exact (f.property i hi).symm
    · simp only [dif_neg hi]
  right_inv f := by
    funext i
    simp only [dif_neg i.property]

theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.LabelingEvents -/

namespace OAI

/-! Exact counts of target-constant label constraints on sixteen vertices. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k r n : ℕ} (T : Tournament k)

def labelingEvent (v : Fin n → Fin k) (m : Fin n → Fin r) :
    Finset ((Fin k × Fin k) → Fin r) :=
  if Function.Injective v then
    Finset.univ.filter fun A => ∀ i j, T.Adj (v i) (v j) → A (v i, v j) = m j
  else ∅

theorem mem_labelingEvent_iff {v : Fin n → Fin k} {m : Fin n → Fin r}
    {A : (Fin k × Fin k) → Fin r} (hv : Function.Injective v) :
    A ∈ T.labelingEvent v m ↔ ∀ i j, T.Adj (v i) (v j) → A (v i,v j) = m j := by
  simp only [labelingEvent, if_pos hv, Finset.mem_filter, Finset.mem_univ, true_and]

theorem labelingEvent_eq [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    T.labelingEvent v m = Finset.univ.filter fun A =>
      ∀ p ∈ T.internalEdges (Finset.univ.image v), A p = m (Function.invFun v p.2) := by
  rw [labelingEvent, if_pos hv]
  apply Finset.filter_congr
  intro A _
  simpa only [Finset.mem_univ, forall_const] using
    T.labelingConstraint_iff Finset.univ v m hv A

theorem card_labelingEvent [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    (T.labelingEvent v m).card = r ^ (k*k-n.choose 2) := by
  rw [T.labelingEvent_eq v m hv]
  have hc := card_fixedCoordinates (T.internalEdges (Finset.univ.image v))
    (fun p => m (Function.invFun v p.2))
  rw [T.card_internalEdges] at hc
  have hi : (Finset.univ.image v).card = n := by
    rw [Finset.card_image_of_injective _ hv]
    exact Fintype.card_fin n
  rw [hi] at hc
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc

theorem card_labelingEvent_le [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r) :
    (T.labelingEvent v m).card ≤ r ^ (k*k-n.choose 2) := by
  by_cases hv : Function.Injective v
  · exact (T.card_labelingEvent v m hv).le
  · simp only [labelingEvent, if_neg hv, Finset.card_empty, Nat.zero_le]

def badLabelings (n r : ℕ) : Finset ((Fin k × Fin k) → Fin r) :=
  Finset.univ.biUnion fun v : Fin n → Fin k =>
    Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m

theorem labelingEvent_subset_bad {v : Fin n → Fin k} {m : Fin n → Fin r} :
    T.labelingEvent v m ⊆ T.badLabelings n r := by
  intro A hA
  exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨m,Finset.mem_univ _,hA⟩⟩

theorem card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by
  calc
    (T.badLabelings n r).card ≤ ∑ v : Fin n → Fin k,
        (Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n → Fin k, ∑ _m : Fin n → Fin r, r^(k*k-n.choose 2) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ =>
        T.card_labelingEvent_le v m)
    _ = k^n * r^n * r^(k*k-n.choose 2) := by
      simp [Nat.mul_assoc]

end Paper320.Tournament

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.LabelingBounds -/

namespace OAI

/-! Symbolic estimates for the sixteen-vertex labeling union bound. -/

namespace Paper320

theorem le_ceil_sqrt_sq (M : ℕ) : M ≤ (Nat.ceil (Real.sqrt M))^2 := by
  have hs := Nat.le_ceil (Real.sqrt (M : ℝ))
  have hr := Real.sqrt_nonneg (M : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh : (M : ℝ) ≤ (Nat.ceil (Real.sqrt M) : ℝ)^2 := by nlinarith
  exact_mod_cast hh

theorem labeling_space_large {M : ℕ} (hM : 3 ≤ M) :
    120 ≤ (2*M^2+1)*(2*M^2+1) := by
  have : 19 ≤ 2*M^2+1 := by nlinarith
  nlinarith

end Paper320

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.LabelingEstimate -/

namespace OAI

/-! An explicit numerical union-bound estimate. -/

namespace Paper320

theorem labeling_union_bound_numerator {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 * M^20 ≤ 3^16 * r^104 := by
  have hk : 2*M^2+1 ≤ 3*M^2 := by nlinarith
  have hp : M^52 ≤ r^104 := by
    calc
      M^52 ≤ (r^2)^52 := Nat.pow_le_pow_left hMr 52
      _ = r^104 := by rw [← pow_mul]
  calc
    (2*M^2+1)^16 * M^20 ≤ (3*M^2)^16 * M^20 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk 16)
    _ = 3^16 * M^52 := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 3^16 * r^104 := Nat.mul_le_mul_left _ hp

theorem labeling_union_bound_constant {M : ℕ} (hM : 3 ≤ M) :
    3^16 < M^20 := by
  calc
    3^16 ≤ M^16 := Nat.pow_le_pow_left hM 16
    _ < M^20 := Nat.pow_lt_pow_right (by omega) (by omega)

theorem labeling_power_bound {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 < r^104 := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := M^20)
  calc
    (2*M^2+1)^16 * M^20 ≤ 3^16*r^104 := labeling_union_bound_numerator hM hMr
    _ < M^20*r^104 := Nat.mul_lt_mul_of_pos_right (labeling_union_bound_constant hM)
      (pow_pos hr 104)
    _ = r^104*M^20 := Nat.mul_comm _ _

theorem labeling_union_bound_real {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (((2*M^2+1)^16 : ℕ) : ℝ) / (r : ℝ)^104 ≤ 3^16 / (M : ℝ)^20 ∧
      3^16 / (M : ℝ)^20 < 1 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hrp : (0 : ℝ) < r := by
    have hr : 0 < r := (Nat.pow_pos_iff.mp
      (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
    exact_mod_cast hr
  constructor
  · apply (div_le_div_iff₀ (pow_pos hrp 104) (pow_pos hMp 20)).mpr
    exact_mod_cast labeling_union_bound_numerator hM hMr
  · apply (div_lt_one (pow_pos hMp 20)).mpr
    exact_mod_cast labeling_union_bound_constant hM

theorem labeling_sqrt_expression {M : ℕ} (hM : 0 < M) :
    (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 = 3^16 / (M : ℝ)^20 := by
  have hp : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : (Real.sqrt M)^104 = (M : ℝ)^52 := by
    rw [show 104 = 2*52 from rfl, pow_mul, Real.sq_sqrt hp.le]
  rw [hd, div_eq_div_iff (pow_ne_zero _ hp.ne') (pow_ne_zero _ hp.ne'),
    mul_pow, ← pow_mul, mul_assoc, ← pow_add]

theorem labeling_source_estimate {M : ℕ} (hM : 3 ≤ M) :
    (((2*M^2+1)^16 : ℕ) : ℝ) / (Nat.ceil (Real.sqrt M) : ℝ)^104 ≤
        (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 ∧
      (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 = 3^16 / (M : ℝ)^20 ∧
      3^16 / (M : ℝ)^20 < 1 := by
  have h := labeling_union_bound_real hM (le_ceil_sqrt_sq M)
  have he := labeling_sqrt_expression (show 0 < M by omega)
  exact ⟨he.symm ▸ h.1, he, h.2⟩

end Paper320

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.TournamentCyclic -/

namespace OAI

/-! The literal regular tournament on an odd cyclic set. -/

noncomputable section
open scoped Classical

namespace Paper320

def cyclicTournament (a : ℕ) : Tournament (2*a+1) where
  Adj i j := 0 < (j-i).val ∧ (j-i).val ≤ a
  loopless i := by simp
  edge_compl := by
    intro i j hij
    have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
    have hb := (j-i).isLt
    have hn : (i-j).val = 2*a+1-(j-i).val := by
      rw [← neg_sub j i, Fin.val_neg, if_neg hδ]
    change (0 < (j-i).val ∧ (j-i).val ≤ a) ↔ ¬ (0 < (i-j).val ∧ (i-j).val ≤ a)
    rw [hn]
    omega

theorem cyclicTournament_outdegree (a : ℕ) (i : Fin (2*a+1)) :
    (Finset.univ.filter ((cyclicTournament a).Adj i)).card = a := by
  let z : Fin (2*a+1) := 0
  let b : Fin (2*a+1) := ⟨a, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter ((cyclicTournament a).Adj i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ a) ↔
        (0 < ((i+x)-i).val ∧ ((i+x)-i).val ≤ a)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change a - 0 = a
  exact Nat.sub_zero a

def regularCyclicTournament (M : ℕ) : RegularTournament M where
  toTournament := cyclicTournament (M^2)
  outdegree := cyclicTournament_outdegree (M^2)

end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Labeling -/

namespace OAI

/-! A finite union bound supplies a good edge labeling. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k r : ℕ} (T : Tournament k)

theorem goodLabeling_exists_of_power_bound (hr : 0 < r) (hN : 120 ≤ k*k)
    (hkr : k^16 < r^104) : Nonempty (GoodLabeling T r) := by
  have htotal : k^16*r^16*r^(k*k-120) < r^(k*k) := by
    calc
      k^16*r^16*r^(k*k-120) < r^104*r^16*r^(k*k-120) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right hkr (pow_pos hr 16)) (pow_pos hr _)
      _ = r^(104+16+(k*k-120)) := by rw [pow_add, pow_add]
      _ = r^(k*k) := congrArg (fun e : ℕ => r^e) (by omega)
  have hc : (T.badLabelings 16 r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := 16)).trans_lt htotal
  obtain ⟨A,_,hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I hI m
  by_contra hn
  let e : Fin 16 ≃ I := (Finset.equivFinOfCardEq hI).symm
  let v : Fin 16 → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have hevent : A ∈ T.labelingEvent v (fun i => m (v i)) := by
    apply T.mem_labelingEvent_iff hv |>.mpr
    intro i j ha
    by_contra h
    exact hn ⟨v i,(e i).property,v j,(e j).property,ha,h⟩
  apply hA
  exact T.labelingEvent_subset_bad hevent

end Tournament

theorem goodLabeling_exists {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2)
    (T : Tournament (2*M^2+1)) : Nonempty (GoodLabeling T r) := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  exact T.goodLabeling_exists_of_power_bound hr (labeling_space_large hM)
    (labeling_power_bound hM hMr)

theorem regular_goodLabeling_exists {M : ℕ} (hM : 3 ≤ M) :
    Nonempty (GoodLabeling (regularCyclicTournament M).toTournament
      (Nat.ceil (Real.sqrt M))) :=
  goodLabeling_exists hM (le_ceil_sqrt_sq M) _

namespace GoodLabeling

theorem good_on_subset {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)
    (I : Finset (Fin k)) (hI : I.card = 16) (m : I → Fin r) :
    ∃ i ∈ I, ∃ j, ∃ hj : j ∈ I,
      T.Adj i j ∧ A.label i j ≠ m ⟨j,hj⟩ := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  let m' : Fin k → Fin r := fun i => if hi : i ∈ I then m ⟨i,hi⟩ else m ⟨j,hj⟩
  obtain ⟨a,ha,b,hb,hab,hne⟩ := A.good I hI m'
  refine ⟨a,ha,b,hb,hab,?_⟩
  simpa only [m', dif_pos hb] using hne

end GoodLabeling
end Paper320

end

end OAI

/- Upstream module: OAI.Combinatorics.Sensitivity.Iterates -/

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

/- Upstream module: OAI.Combinatorics.Sensitivity.PowerAmplification -/

namespace OAI

/-! A fixed seed with a strict quadratic gap gives a fixed power separation. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem log_exponent_gt_two {A B : ℝ} (hA : 1 < A) (hB : A ^ 2 < B) :
    2 < Real.log B / Real.log A := by
  apply (lt_div_iff₀ (Real.log_pos hA)).mpr
  calc
    2 * Real.log A = Real.log (A ^ 2) := by rw [Real.log_pow]; norm_num
    _ < Real.log B := Real.log_lt_log (pow_pos (by linarith) _) hB

theorem rpow_log_exponent {A B : ℝ} (hA : 1 < A) (hB : 0 < B) :
    A ^ (Real.log B / Real.log A) = B := by
  apply (Real.mul_log_eq_log_iff (by linarith) hB).mp
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hA))

theorem power_amplification {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false)
    (A B : ℕ) (hs : sensitivity f ≤ A)
    (hb : B ≤ blockSensitivityAt f (fun _ => false))
    (hA : 1 < A) (hB : A ^ 2 < B) :
    let α := Real.log (B : ℝ) / Real.log (A : ℝ)
    2 < α ∧
      (∀ m : ℕ,
        0 < Fintype.card I ^ m ∧
        iterateFin f m (fun _ => false) = false ∧
        (∃ x y, iterateFin f m x ≠ iterateFin f m y) ∧
        (sensitivity (iterateFin f m) : ℝ) ^ α ≤
          (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) ∧
        ((B : ℝ) / (A : ℝ) ^ 2) ^ m ≤
          (blockSensitivity (iterateFin f m) : ℝ) /
            (sensitivity (iterateFin f m) : ℝ) ^ 2) ∧
      Filter.Tendsto
        (fun m : ℕ => (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ))
        Filter.atTop Filter.atTop := by
  have hAr : 1 < (A : ℝ) := by exact_mod_cast hA
  have hBr : (A : ℝ) ^ 2 < (B : ℝ) := by exact_mod_cast hB
  have hAp : 0 < (A : ℝ) := by linarith
  have hB1 : 1 < (B : ℝ) := by nlinarith
  have hBp : 0 < (B : ℝ) := by linarith
  have hBn : 0 < B := by exact_mod_cast hBp
  have hbf : 0 < blockSensitivityAt f (fun _ => false) := lt_of_lt_of_le hBn hb
  have hcard : 0 < Fintype.card I := by
    by_contra h
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    obtain ⟨x, y, hxy⟩ := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) hbf
    exact hxy (congrArg f (funext fun i => isEmptyElim i))
  have hα := log_exponent_gt_two hAr hBr
  have hpow := rpow_log_exponent hAr hBp
  have hs' (m : ℕ) : (sensitivity (iterateFin f m) : ℝ) ≤ (A : ℝ) ^ m := by
    have hp : sensitivity f ^ m ≤ A ^ m := by gcongr
    exact_mod_cast (sensitivity_iterateFin_le f m).trans hp
  have hb' (m : ℕ) : (B : ℝ) ^ m ≤
      (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := by
    have hp : B ^ m ≤ blockSensitivityAt f (fun _ => false) ^ m := by gcongr
    exact_mod_cast hp.trans (blockSensitivityAt_iterateFin_zero f hf m)
  refine ⟨hα, ?_, Filter.tendsto_atTop_mono hb' (tendsto_pow_atTop_atTop_of_one_lt hB1)⟩
  intro m
  have hnc := iterateFin_nonconstant f hf hbf m
  have hspos : 0 < (sensitivity (iterateFin f m) : ℝ) := by
    exact_mod_cast sensitivity_pos_of_nonconstant (iterateFin f m) hnc
  refine ⟨pow_pos hcard m, iterateFin_zero f hf m, hnc, ?_, ?_⟩
  · calc
      _ ≤ ((A : ℝ) ^ m) ^ (Real.log (B : ℝ) / Real.log (A : ℝ)) :=
        Real.rpow_le_rpow (le_of_lt hspos) (hs' m) (by linarith)
      _ = ((A : ℝ) ^ (Real.log (B : ℝ) / Real.log (A : ℝ))) ^ m := by
        rw [← Real.rpow_natCast_mul hAp.le,
          mul_comm (m : ℝ), Real.rpow_mul_natCast hAp.le]
      _ = (B : ℝ) ^ m := by rw [hpow]
      _ ≤ _ := hb' m
  · apply (le_div_iff₀ (pow_pos hspos 2)).mpr
    have hsq : (sensitivity (iterateFin f m) : ℝ) ^ 2 ≤ ((A : ℝ) ^ m) ^ 2 := by
      gcongr
      exact hs' m
    have hden : ((A : ℝ) ^ 2) ^ m = ((A : ℝ) ^ m) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
    calc
      _ ≤ ((B : ℝ) / (A : ℝ) ^ 2) ^ m * ((A : ℝ) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (B : ℝ) ^ m := by
        rw [div_pow, hden]
        exact div_mul_cancel₀ _ (ne_of_gt (pow_pos (pow_pos hAp m) 2))
      _ ≤ (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := hb' m
      _ ≤ (blockSensitivity (iterateFin f m) : ℝ) := by
        exact_mod_cast blockSensitivityAt_le_blockSensitivity (iterateFin f m) (fun _ => false)

end Paper320

end

end OAI


/- Local proof component: Base205. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/- Adapted unchanged components from accepted Prove2Me 2.05 solution by robinkothari.
Original source: research-frontier/reconciliation-2026-10-16/public/205-solution.lean.
AllSensitivity contains fully proved OpenAI/math foundations. No theorem stubs imported. -/



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

theorem SensitivityCampaign.finite_certificate
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (a : ℝ)
    (hA : 1 < A) (hB : 1 < B) (ha : 0 ≤ a)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : (A : ℝ) ^ a ≤ (B : ℝ)) :
    SensitivityCampaign.AchievesExponent a :=
  SensitivityCampaign.finite_certificate_proof f x A B a hA hB ha hs hb hpow


-- Source component: Solutions/Transfer.lean
section Component9

open OAI.Paper320
open scoped Classical

namespace Sensitivity205
noncomputable section

structure Labeling {k : ℕ} (T : Tournament k) (r t : ℕ) where
  label : Fin k → Fin k → Fin r
  coherent_card : ∀ (I : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ I, ∀ j ∈ I, T.Adj i j → label i j = m j) → I.card < t

theorem labeling_exists {k r t : ℕ} [NeZero t] (T : Tournament k)
    (hr : 0 < r) (ht : t.choose 2 ≤ k*k)
    (hp : k^t * r^t < r^(t.choose 2)) : Nonempty (Labeling T r t) := by
  have htotal : k^t*r^t*r^(k*k-t.choose 2) < r^(k*k) := by
    calc
      _ < r^(t.choose 2)*r^(k*k-t.choose 2) :=
        Nat.mul_lt_mul_of_pos_right hp (pow_pos hr _)
      _ = r^(k*k) := by rw [← pow_add, Nat.add_sub_of_le ht]
  have hc : (T.badLabelings t r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := t)).trans_lt htotal
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I m hcoh
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  let e : Fin t ≃ J := (Finset.equivFinOfCardEq hJ).symm
  let v : Fin t → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  apply hA
  apply Finset.mem_biUnion.mpr
  refine ⟨v, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨fun i => m (v i),
    Finset.mem_univ _, ?_⟩⟩
  simp only [Tournament.labelingEvent, if_pos hv, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i j hij
  exact hcoh (v i) (hJI (e i).property) (v j) (hJI (e j).property) hij

theorem targetCandidates_card {k r h t : ℕ} {I : Type}
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < t := by
  apply A.coherent_card _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp
    (Finset.mem_filter.mp hi).2.2 j hij
  have htarget := hF.rejects_of_le (gateIndex_lt_last q).le hgate
  exact targetWitness_unique T A.label F q x hr j hj (A.label i j) htarget

def PairBound {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (b : Bool) (V : Fin n → Fin n → ℕ) : Prop :=
  ∀ (q q' : Fin n), q ≤ q' → ∀ x, F q x = b → F q' x = b →
    jointSensitivityAt (F q) (F q') x ≤ V q q'

@[simp] theorem joint_self {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    jointSensitivityAt f f x = sensitivityAt f x := by
  simp [jointSensitivityAt, sensitivityAt]

theorem PairBound.self {n : ℕ} {I : Type} [Fintype I]
    {F : Fin n → (I → Bool) → Bool} {b : Bool} {V : Fin n → Fin n → ℕ}
    (hV : PairBound F b V) (q : Fin n) (x : I → Bool) (hx : F q x = b) :
    sensitivityAt (F q) x ≤ V q q := by
  simpa using hV q q le_rfl x hx hx

theorem recursive_pair_zero {k r h t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q')
    (hYC : Y (gateIndex q') (Fin.last h) ≤ Y (gateIndex q') (gateIndex q))
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false) :
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      (t-1) * Z (Fin.last h) (Fin.last h) +
        Y (gateIndex q') (gateIndex q) + 2 * Y (gateIndex q') (Fin.last h) := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i => childJointChanges F (gateIndex q') (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childJointChanges F (gateIndex q') (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x ∧
      recursiveFamily T A.label F q' (flip x {p}) ≠ recursiveFamily T A.label F q' x) ⊆ U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon' : recursiveFamily T A.label F q' (flip x {((j,c),a)}) = true := by
      cases hy : recursiveFamily T A.label F q' (flip x {((j,c),a)})
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label F q' _).mp hon'
    have hi := rowClause_nested T A.label F hF hqq _ i hi'
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      have hgon' := hF.accepts_of_le (gateIndex_antitone hqq) hgon
      have hgoff' := ((rowClause_eq_true_iff T A.label F q' _ i).mp hi').2 j hij
      rw [recursiveChild_flip_same] at hgoff'
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn :
            F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
            F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hgon', hgoff']
        simpa [childJointChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q').le hgoff'
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon', hgoff', hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ (t-1) * Z (Fin.last h) (Fin.last h) := by
    calc
      U.card ≤ TC.card * Z (Fin.last h) (Fin.last h) :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact hZ.self _ _ (targetWitness_false T A.label F q x hr i hi))
      _ ≤ _ := Nat.mul_le_mul_right _ (by
        have hc := targetCandidates_card T A F hF q x hr
        dsimp only [TC]; omega)
  have hV : V.card ≤ NC.card * Y (gateIndex q') (Fin.last h) := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := Finset.mem_sdiff.mp hi
    have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
    have hgate := (gateWitness_spec T A.label F q x i hg.1).2
    have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1 (A.label i (w i))
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_lt_last q').le _
      (hF.accepts_of_le (gateIndex_antitone hqq) hgate) htarget
  have hW : W.card ≤ SC.card * Y (gateIndex q') (gateIndex q) := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_antitone hqq) _
      (hF.accepts_of_le (gateIndex_antitone hqq) hg) hg
  have hVW : V.card + W.card ≤ Y (gateIndex q') (gateIndex q) +
      2 * Y (gateIndex q') (Fin.last h) := by
    have hgc : GC.card ≤ 3 := gateCandidates_card T A.label F hF q x
    have hsc : SC.card ≤ 1 := gateSinks_card T A.label F q x
    by_cases hSC : SC.Nonempty
    · have hcs : SC ⊆ GC := Finset.filter_subset _ _
      have hc : NC.card + SC.card = GC.card := Finset.card_sdiff_add_card_eq_card hcs
      have hpos := Finset.card_pos.mpr hSC
      have hn : NC.card ≤ 2 := by omega
      have hv := hV.trans (Nat.mul_le_mul_right _ hn)
      have hw := hW.trans (Nat.mul_le_mul_right _ hsc)
      omega
    · have hSC0 : SC = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSC
      have hw : W = ∅ := by simp only [W, hSC0, Finset.biUnion_empty]
      have hn : NC.card ≤ 3 := (Finset.card_le_card Finset.sdiff_subset).trans hgc
      have hv := hV.trans (Nat.mul_le_mul_right _ hn)
      simp only [hw, Finset.card_empty] at *
      omega
  calc
    jointSensitivityAt _ _ x ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ _ := by have := Nat.add_le_add hU hVW; omega

theorem recursive_pair_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * Z (gateIndex q') (gateIndex q) + r * Y (Fin.last h) (Fin.last h) := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * Y (Fin.last h) (Fin.last h) := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (Y (Fin.last h) (Fin.last h))
      (fun c _ => by
        rw [childChanges_card]
        exact hY.self _ _ (hcond.1 c))
  have hV : V.card ≤ o * Z (gateIndex q') (gateIndex q) := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (Z (gateIndex q') (gateIndex q)) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact hZ _ _ (gateIndex_antitone hqq) _ (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * Y (Fin.last h) (Fin.last h) + o * Z (gateIndex q') (gateIndex q) := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

end
end Sensitivity205

end Component9

-- Source component: Solutions/Base.lean
section Component10

open OAI.Paper320
open scoped Classical BigOperators

namespace Sensitivity205
noncomputable section

def threshold (q : Fin 3) (x : Fin 3 → Bool) : Bool :=
  decide (q.val + 1 ≤ (Finset.univ.filter fun i => x i = true).card)

theorem threshold_nested : NestedFamily threshold := by
  constructor
  intro q q' x hqq hx
  simp only [threshold, decide_eq_true_eq] at *
  exact le_trans (Nat.add_le_add_right hqq 1) hx

def flip3 (x : Fin 3 → Bool) (i : Fin 3) : Fin 3 → Bool :=
  fun j => if j = i then !(x j) else x j

theorem flip_eq3 (x : Fin 3 → Bool) (i : Fin 3) : OAI.Paper320.flip x {i} = flip3 x i := by
  funext j
  simp [OAI.Paper320.flip, flip3]

theorem sensitivityAt_threshold (q : Fin 3) (x : Fin 3 → Bool) :
    sensitivityAt (threshold q) x =
      (Finset.univ.filter fun i => threshold q (flip3 x i) ≠ threshold q x).card := by
  unfold sensitivityAt
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [flip_eq3]

theorem threshold_side_table :
    ∀ (q : Fin 3) (x : Fin 3 → Bool) (b : Bool), threshold q x = b →
      sensitivityAt (threshold q) x ≤ (if b then q.val+1 else 3-q.val) ∧
      ∀ i, threshold q (flip x {i}) ≠ threshold q x → x i = b := by
  simp_rw [sensitivityAt_threshold, flip_eq3]
  decide

theorem threshold_joint_table :
    ∀ (q q' : Fin 3) (x : Fin 3 → Bool) (b : Bool), q < q' →
      threshold q x = b → threshold q' x = b →
      ∀ i, ¬ (threshold q (flip x {i}) ≠ threshold q x ∧
        threshold q' (flip x {i}) ≠ threshold q' x) := by
  simp_rw [flip_eq3]
  decide

def base {I : Type} (g : (I → Bool) → Bool) (q : Fin 3) :
    (Fin 3 × I → Bool) → Bool := compose (threshold q) g

def Z0 (q q' : Fin 3) : ℕ := if q = q' then 3-q.val else 0
def Y0 (q q' : Fin 3) : ℕ := if q = q' then (q.val+1)*4800 else 0

theorem base_nested {I : Type} (g : (I → Bool) → Bool) : NestedFamily (base g) := by
  constructor
  intro q q' x hqq hx
  exact threshold_nested.accepts_of_le hqq hx

theorem base_side {I : Type} [Fintype I] (g : (I → Bool) → Bool)
    (b : Bool) (u : ℕ) (hg : ∀ x, g x = b → sensitivityAt g x ≤ u)
    (q : Fin 3) (x : Fin 3 × I → Bool) (hx : base g q x = b) :
    sensitivityAt (base g q) x ≤ (if b then q.val+1 else 3-q.val)*u := by
  let y : Fin 3 → Bool := fun i => g (fun a => x (i,a))
  have hy : threshold q y = b := hx
  obtain ⟨hcard, hvalue⟩ := threshold_side_table q y b hy
  rw [base, sensitivityAt_compose]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => threshold q (flip y {i}) ≠ threshold q y), u := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg _ (hvalue i (Finset.mem_filter.mp hi).2)
    _ = sensitivityAt (threshold q) y * u := by simp [sensitivityAt]
    _ ≤ _ := Nat.mul_le_mul_right u hcard

theorem base_joint_zero {I : Type} [Fintype I] (g : (I → Bool) → Bool)
    (q q' : Fin 3) (hqq : q < q') (x : Fin 3 × I → Bool) (b : Bool)
    (hx : base g q x = b) (hx' : base g q' x = b) :
    jointSensitivityAt (base g q) (base g q') x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i,a⟩ hi
  have hchange := (Finset.mem_filter.mp hi).2
  have h₁ := (compose_flip_sensitive_iff (threshold q) g x i a).mp hchange.1
  have h₂ := (compose_flip_sensitive_iff (threshold q') g x i a).mp hchange.2
  exact threshold_joint_table q q' (fun i => g (fun a => x (i,a))) b hqq hx hx' i ⟨h₁.2,h₂.2⟩

theorem base_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ 4800*u) :
    PairBound (base g) false (fun q q' => Z0 q q'*u) ∧
    PairBound (base g) true (fun q q' => Y0 q q'*u) := by
  constructor
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Z0] using base_side g false u h0 q x hx
    · rw [base_joint_zero g q q' hlt x false hx hx']; exact Nat.zero_le _
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Y0, Nat.mul_assoc] using base_side g true (4800*u) h1 q x hx
    · rw [base_joint_zero g q q' hlt x true hx hx']; exact Nat.zero_le _

end
end Sensitivity205

end Component10


namespace Sensitivity205
noncomputable section
open OAI.Paper320
open scoped Classical

def clip (i : Fin 4) : Fin 3 := ⟨min i.val 2, by omega⟩

theorem clip_mono : Monotone clip := by
  intro i j hij
  change min i.val 2 ≤ min j.val 2
  exact min_le_min_right 2 hij

@[simp] theorem clip_gate (q : Fin 3) : clip (gateIndex q) = Fin.rev q := by
  fin_cases q <;> rfl

@[simp] theorem clip_last : clip (Fin.last 3) = 2 := rfl
@[simp] theorem clip_three : clip 3 = 2 := rfl

def extend {I : Type} (F : Fin 3 → (I → Bool) → Bool) (q : Fin 4) := F (clip q)

theorem extend_nested {I : Type} {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (extend F) := by
  constructor
  intro q q' x hqq hx
  exact hF.accepts_of_le (clip_mono hqq) hx


structure Blocks {I : Type} {h : ℕ} (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  zero : ∀ q, F q (fun _ => false) = false
  sets : Fin n → Finset I
  nonempty : ∀ i, (sets i).Nonempty
  disjoint : Pairwise fun i j => Disjoint (sets i) (sets j)
  on : ∀ q i, F q (flip (fun _ => false) (sets i)) = true

theorem threshold_false (q : Fin 3) : threshold q (fun _ => false) = false := by
  fin_cases q <;> decide

theorem threshold_true (q : Fin 3) : threshold q (fun _ => true) = true := by
  fin_cases q <;> decide

def baseBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) : Blocks (base g) n where
  zero q := by
    change threshold q (fun _ => g (fun _ => false)) = false
    simp only [w.zero 0]
    exact threshold_false q
  sets i := Finset.univ.product (w.sets i)
  nonempty i := by
    obtain ⟨a, ha⟩ := w.nonempty i
    exact ⟨(0,a), Finset.mem_product.mpr ⟨Finset.mem_univ _,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (w.disjoint hij)
      (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hq).2
  on q i := by
    have he (j : Fin 3) :
        (fun a => flip (fun _ => false) (Finset.univ.product (w.sets i)) (j,a)) =
          flip (fun _ => false) (w.sets i) := by
      funext a; simp [OAI.Paper320.flip]
    change threshold q (fun j => g (fun a =>
      flip (fun _ => false) (Finset.univ.product (w.sets i)) (j,a))) = true
    simp only [he, w.on 0 i]
    exact threshold_true q


end
end Sensitivity205


/- Local proof component: CoupledArithmetic. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Sensitivity20635

theorem coupled_weighted_bound (n0 n1 m0 m1 t A B J K : ℕ)
    (ht : 4 ≤ t) (hJA : J ≤ A) (hKB : K ≤ B)
    (hn1 : n1 ≤ 1) (hm0 : m0 ≤ 1) (hm : m0 + m1 ≤ 3)
    (hn : n0 + n1 ≤ t - 1)
    (hnzero : 2 ≤ m0 + m1 → n1 = 0)
    (htwo0 : m0 + m1 = 2 → m0 = 0 → n0 ≤ t - 2)
    (htwo1 : m0 + m1 = 2 → m0 = 1 → n0 ≤ t - 3)
    (hthree : m0 + m1 = 3 → m0 = 0 ∧ n0 ≤ t - 4) :
    n1 * A + n0 * J + m0 * B + m1 * K ≤
      max (max (max (A+B+(t-2)*J) (B+K+(t-3)*J))
        (2*K+(t-2)*J)) (3*K+(t-4)*J) := by
  let R := max (max (max (A+B+(t-2)*J) (B+K+(t-3)*J))
        (2*K+(t-2)*J)) (3*K+(t-4)*J)
  have hR0 : A+B+(t-2)*J ≤ R :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hR1 : B+K+(t-3)*J ≤ R :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hR2 : 2*K+(t-2)*J ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR3 : 3*K+(t-4)*J ≤ R := le_max_right _ _
  change _ ≤ R
  by_cases hsmall : m0 + m1 ≤ 1
  · have hg : m0*B+m1*K ≤ B := by
      have hmul := Nat.mul_le_mul_right B hsmall
      have hmk := Nat.mul_le_mul_left m1 hKB
      simp only [Nat.add_mul, Nat.one_mul] at hmul
      omega
    have htargets : n1*A+n0*J ≤ A+(t-2)*J := by
      have ht2 : t-2+1 = t-1 := by omega
      interval_cases n1
      · have hmul := Nat.mul_le_mul_right J hn
        simp only [Nat.add_zero, Nat.zero_mul] at *
        rw [← ht2, Nat.add_mul, Nat.one_mul] at hmul
        omega
      · have hbound : n0 ≤ t-2 := by omega
        have hmul := Nat.mul_le_mul_right J hbound
        simp only [Nat.one_mul]
        omega
    exact (show n1*A+n0*J+m0*B+m1*K ≤ A+B+(t-2)*J by omega).trans hR0
  · have hnzero' := hnzero (by omega)
    subst n1
    by_cases htwo : m0+m1=2
    · interval_cases m0
      · have hbound := htwo0 htwo rfl
        have hm1 : m1 = 2 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+0*B+2*K ≤ 2*K+(t-2)*J by omega).trans hR2
      · have hbound := htwo1 htwo rfl
        have hm1 : m1 = 1 := by omega
        subst m1
        have hmul := Nat.mul_le_mul_right J hbound
        exact (show 0*A+n0*J+1*B+1*K ≤ B+K+(t-3)*J by omega).trans hR1
    · have hsum : m0+m1=3 := by omega
      obtain ⟨hmzero, hbound⟩ := hthree hsum
      subst m0
      have hm1 : m1=3 := by omega
      subst m1
      have hmul := Nat.mul_le_mul_right J hbound
      exact (show 0*A+n0*J+0*B+3*K ≤ 3*K+(t-4)*J by omega).trans hR3

end Sensitivity20635


/- Local proof component: BinomialLabeling. -/

/-! A finite union bound over subsets, rather than ordered vertex tuples.
The argument is adapted from the accepted public 2.0391 proof.
-/

open OAI.Paper320
open scoped Classical BigOperators

namespace Sensitivity205
noncomputable section

theorem labeling_exists_choose {k r t : ℕ} (T : Tournament k)
    (hr : 0 < r) (hp : k.choose t * r ^ t < r ^ (t.choose 2)) :
    Nonempty (Labeling T r t) := by
  rcases lt_or_ge k t with hkt | hkt
  · refine ⟨⟨fun _ _ => ⟨0, hr⟩, ?_⟩⟩
    intro I m hcoh
    exact lt_of_le_of_lt (by simpa using I.card_le_univ) hkt
  let good : (I : Finset (Fin k)) → (I → Fin r) → Finset (Fin k → Fin k → Fin r) :=
    fun I m => Finset.univ.filter (fun a =>
      ∀ i (hi : i ∈ I) j (hj : j ∈ I), T.Adj i j → a i j = m ⟨j, hj⟩)
  have hgood : ∀ I : Finset (Fin k), I.card = t → ∀ m : I → Fin r,
      (good I m).card ≤ r ^ (k*k - t.choose 2) := by
    intro I hI m
    let S := T.internalEdges I
    have hS : S.card = t.choose 2 := by rw [T.card_internalEdges, hI]
    let f : (Fin k → Fin k → Fin r) → ((Sᶜ : Finset _) → Fin r) :=
      fun a p => a p.1.1 p.1.2
    have hinj : Set.InjOn f (good I m) := by
      intro a ha b hb hab
      simp only [good, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      funext i j
      by_cases hpair : (i, j) ∈ S
      · simp only [S, Tournament.internalEdges, Finset.mem_filter, Finset.mem_product] at hpair
        obtain ⟨⟨hi, hj⟩, hc⟩ := hpair
        rw [ha i hi j hj hc, hb i hi j hj hc]
      · exact congrFun hab ⟨(i, j), Finset.mem_compl.2 hpair⟩
    calc (good I m).card ≤ (Finset.univ : Finset ((Sᶜ : Finset _) → Fin r)).card :=
          Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
      _ = r ^ (k*k - t.choose 2) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
            Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hS]
  let bad := (Finset.powersetCard t (Finset.univ : Finset (Fin k))).biUnion
    (fun I => (Finset.univ : Finset (I → Fin r)).biUnion (fun m => good I m))
  have hbad : bad.card ≤ k.choose t * (r ^ t * r ^ (k*k - t.choose 2)) := by
    refine Finset.card_biUnion_le.trans ?_
    have hI : ∀ I ∈ Finset.powersetCard t (Finset.univ : Finset (Fin k)),
        ((Finset.univ : Finset (I → Fin r)).biUnion (fun m => good I m)).card ≤
          r ^ t * r ^ (k*k - t.choose 2) := by
      intro I hI
      rw [Finset.mem_powersetCard] at hI
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum (fun m _ => hgood I hI.2 m)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
        Fintype.card_coe, Fintype.card_fin, hI.2]
    refine (Finset.sum_le_sum hI).trans ?_
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  have hlt : k.choose t * (r ^ t * r ^ (k*k - t.choose 2)) < r ^ (k*k) := by
    have hle : t.choose 2 ≤ k*k := by
      rw [Nat.choose_two_right]
      calc t * (t - 1) / 2 ≤ t * (t - 1) := Nat.div_le_self _ _
        _ ≤ t * t := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ k * k := Nat.mul_le_mul hkt hkt
    have hpos : 0 < r ^ (k*k - t.choose 2) := pow_pos hr _
    calc k.choose t * (r ^ t * r ^ (k*k - t.choose 2))
        = (k.choose t * r ^ t) * r ^ (k*k - t.choose 2) := by rw [mul_assoc]
      _ < r ^ (t.choose 2) * r ^ (k*k - t.choose 2) := Nat.mul_lt_mul_of_pos_right hp hpos
      _ = r ^ (k*k) := by rw [← pow_add, Nat.add_sub_cancel' hle]
  have hex : ∃ a, a ∉ bad := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin k → Fin k → Fin r)) ⊆ bad := fun a _ => hcon a
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, ← pow_mul] at hc
    exact absurd (hc.trans hbad) (not_le.2 hlt)
  obtain ⟨a, ha⟩ := hex
  refine ⟨⟨a, ?_⟩⟩
  intro I m hcoh
  by_contra hI
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hI)
  apply ha
  simp only [bad, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_univ, true_and]
  refine ⟨J, ⟨Finset.subset_univ _, hJ⟩, fun x => m x.1, ?_⟩
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi j hj e => hcoh i (hJI hi) j (hJI hj) e

end
end Sensitivity205

namespace Sensitivity20635
noncomputable section

theorem labeling_exists_binomial {k r t : ℕ} (T : Tournament k)
    (hr : 0 < r) (hp : k.choose t * r ^ t < r ^ (t.choose 2)) :
    Nonempty (Sensitivity205.Labeling T r t) :=
  Sensitivity205.labeling_exists_choose T hr hp

theorem choose_bound_of_descFactorial {k r t : ℕ}
    (h : k.descFactorial t * r ^ t < t.factorial * r ^ (t.choose 2)) :
    k.choose t * r ^ t < r ^ (t.choose 2) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] at h
  exact Nat.lt_of_mul_lt_mul_left h

set_option maxRecDepth 10000 in
theorem label_condition_768219 :
    (1536439 : ℕ).choose 37 * 2 ^ 37 < 2 ^ ((37 : ℕ).choose 2) := by
  apply choose_bound_of_descFactorial
  decide

set_option maxRecDepth 10000 in
theorem label_condition_529416 :
    (1058833 : ℕ).choose 36 * 2 ^ 36 < 2 ^ ((36 : ℕ).choose 2) := by
  apply choose_bound_of_descFactorial
  decide

set_option maxRecDepth 10000 in
theorem label_condition_661770 :
    (1323541 : ℕ).choose 36 * 2 ^ 36 < 2 ^ ((36 : ℕ).choose 2) := by
  apply choose_bound_of_descFactorial
  decide

theorem labeling_exists_layer1 (T : Tournament 1536439) :
    Nonempty (Sensitivity205.Labeling T 2 37) :=
  labeling_exists_binomial T (by decide) label_condition_768219

theorem labeling_exists_layer2 (T : Tournament 1058833) :
    Nonempty (Sensitivity205.Labeling T 2 36) :=
  labeling_exists_binomial T (by decide) label_condition_529416

theorem labeling_exists_layer3 (T : Tournament 1323541) :
    Nonempty (Sensitivity205.Labeling T 2 36) :=
  labeling_exists_binomial T (by decide) label_condition_661770

end
end Sensitivity20635



/- Local proof component: ArithmeticAlternate. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Sensitivity20635Arithmetic

theorem block_power_gap (a b l c d n m r s u e : ℕ) (hd : 0 < d)
    (hblock : c * b^n * l^r ≤ d * a^n)
    (hrest : (2:ℕ)^e * d^m * b^s * l^u ≤ c^m * a^s) :
    (2:ℕ)^e * b^(n*m+s) * l^(r*m+u) ≤ a^(n*m+s) := by
  apply Nat.le_of_mul_le_mul_left (c := d^m) _ (pow_pos hd m)
  calc
    d^m * ((2:ℕ)^e * b^(n*m+s) * l^(r*m+u)) =
        ((2:ℕ)^e * d^m * b^s * l^u) * (b^n*l^r)^m := by
      simp only [pow_add, pow_mul, mul_pow]
      ac_rfl
    _ ≤ (c^m * a^s) * (b^n*l^r)^m := Nat.mul_le_mul_right _ hrest
    _ = a^s * (c*b^n*l^r)^m := by
      simp only [mul_pow]
      ac_rfl
    _ ≤ a^s * (d*a^n)^m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hblock m)
    _ = d^m * a^(n*m+s) := by
      simp only [pow_add, pow_mul, mul_pow]
      ac_rfl

theorem block_certificate :
    1279 * 125^63 * (487391996355227766580:ℕ)^4 ≤ 1000 * 2583^63 := by
  decide

theorem remainder_certificate :
    (2:ℕ)^10 * 1000^31 * 125^47 * 487391996355227766580^3 ≤
      1279^31 * 2583^47 := by
  decide

theorem hgap_short :
    (2:ℕ)^10 * 125^2000 * 487391996355227766580^127 ≤ 2583^2000 :=
  block_power_gap 2583 125 487391996355227766580 1279 1000 63 31 4 47 3 10
    (by decide) block_certificate remainder_certificate


end Sensitivity20635Arithmetic


/- Local proof component: Numeric20635. -/

/- Exact arithmetic for the seven-layer 2.0635 construction. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace Sensitivity20635

abbrev rho : ℕ := 1074
abbrev L : ℕ := 487391996355227766580
abbrev B : ℕ := 4908941403403970434876045518285525005668537

def D : ℕ → ℕ
  | 0 => 768219
  | 1 => 529416
  | 2 => 529416
  | 3 => 529416
  | 4 => 661770
  | 5 => 661770
  | _ => 768219

def t : ℕ → ℕ
  | 0 => 37
  | 1 => 36
  | 2 => 36
  | 3 => 36
  | 4 => 36
  | 5 => 36
  | _ => 37

def K (d : ℕ) : ℕ := 2*D d+1

def repairBound (t A B J K : ℕ) : ℕ :=
  max (max (max (A+B+(t-2)*J) (B+K+(t-3)*J)) (2*K+(t-2)*J))
    (3*K+(t-4)*J)

def Z0 (i j : Fin 3) : ℕ := if i = j then 3-i.val else 0
def Y0 (i j : Fin 3) : ℕ := if i = j then (i.val+1)*rho else 0

def nextProfile (d : ℕ) (p : (Fin 3 → Fin 3 → ℕ) × (Fin 3 → Fin 3 → ℕ)) :=
  let (z,y) := p
  (fun i j => repairBound (t d) (z 2 2) (y (Fin.rev j) (Fin.rev i))
      (z (Fin.rev j) 2) (y (Fin.rev j) 2),
   fun i j => D d*z (Fin.rev j) (Fin.rev i) + 2*y 2 2)

/- Cached finite profile tables avoid exponential reduction of shared subexpressions.
   The recurrence is independently kernel checked immediately below. -/
def profiles : ℕ → (Fin 3 → Fin 3 → ℕ) × (Fin 3 → Fin 3 → ℕ)
  | 0 => (Z0, Y0)
  | 1 => (![![9699, 1, 1], ![9699, 2149, 1], ![9699, 1, 1075]],
      ![![774663, 6444, 6444], ![6444, 1542882, 6444], ![6444, 6444, 2311101]])
  | 2 => (![![6967703, 19364, 19364], ![6967703, 1549359, 19364], ![6967703, 19364, 781140]],
      ![![573744402, 5151618, 5151618], ![5151618, 1142337186, 5151618], ![5139427986, 5139427986, 5139427986]])
  | 3 => (![![15443280438, 16074502, 16074502], ![15443280438, 1148127816, 16074502], ![15443280438, 16074502, 579535032]],
      ![![423826870212, 20530467396, 20530467396], ![20530467396, 830534300316, 20530467396], ![3699092307420, 3699092307420, 3699092307420]])
  | 4 => (![![11115822043284, 62105786252, 62105786252], ![11115822043284, 851595226278, 62105786252], ![11115822043284, 62105786252, 444887796174]],
      ![![314213303116152, 15908283165672, 15908283165672], ![15908283165672, 615235420450296, 15908283165672], ![8183317940979048, 8183317940979048, 8183317940979048]])
  | 5 => (![![24564190232414712, 49712234657080, 49712234657080], ![24564190232414712, 633193194562284, 49712234657080], ![24564190232414712, 49712234657080, 332171077228140]],
      ![![310780032756026076, 57466382049944136, 57466382049944136], ![57466382049944136, 579926808775950156, 57466382049944136], ![7372484189466010776, 7372484189466010776, 7372484189466010776]])
  | 6 => (![![22128082042869332808, 173989937658858968, 173989937658858968], ![22128082042869332808, 639033694569577932, 173989937658858968], ![22128082042869332808, 173989937658858968, 369886918549653852]],
      ![![234565822156198229352, 47643033907947853152, 47643033907947853152], ![47643033907947853152, 433773228744414704232, 47643033907947853152], ![16270589138484015981792, 16270589138484015981792, 16270589138484015981792]])
  | _ => (![![48823973683764186522492, 148670769666585905400, 148670769666585905400], ![48823973683764186522492, 487331920532763762296, 148670769666585905400], ![48823973683764186522492, 148670769666585905400, 288124513944547287416]],
      ![![316695336958264564493172, 166203554195319009501576, 166203554195319009501576], ![166203554195319009501576, 523459004085514621306692, 166203554195319009501576], ![17031754237168004012392536, 17031754237168004012392536, 17031754237168004012392536]])

theorem profiles_succ (d : ℕ) (hd : d < 7) :
    profiles (d+1) = nextProfile d (profiles d) := by
  have htable : ∀ d : Fin 7, profiles (d.val+1) = nextProfile d.val (profiles d.val) := by decide
  exact htable ⟨d, hd⟩

def blockGain : ℕ → ℕ
  | 0 => 1
  | d+1 => K d * blockGain d

theorem blockGain_seven : blockGain 7 = B := by decide

theorem final_bounds : (profiles 7).1 1 1 ≤ L ∧ (profiles 7).2 1 1 ≤ rho*L := by
  decide

theorem compatible_tables : ∀ (d : Fin 7) (i j : Fin 3), i ≤ j →
    (profiles d.val).1 i 2 ≤ (profiles d.val).1 2 2 ∧
    (profiles d.val).2 i 2 ≤ (profiles d.val).2 i j := by
  decide

theorem quotient_power_gap (l b p q n r e : ℕ) (hq : 0 < q)
    (hbase : p*l^2 ≤ q*b)
    (hgap : (2:ℕ)^e*q^n*l^r ≤ p^n) :
    (2:ℕ)^e*l^(2*n+r) ≤ b^n := by
  apply Nat.le_of_mul_le_mul_left (c := q^n) _ (pow_pos hq n)
  calc
    q^n * ((2:ℕ)^e*l^(2*n+r)) = ((2:ℕ)^e*q^n*l^r)*l^(2*n) := by
      rw [pow_add]
      ac_rfl
    _ ≤ p^n*l^(2*n) := Nat.mul_le_mul_right _ hgap
    _ = (p*l^2)^n := by rw [mul_pow, ← pow_mul]
    _ ≤ (q*b)^n := Nat.pow_le_pow_left hbase n
    _ = q^n*b^n := mul_pow _ _ _

theorem arithmetic_gap : (2:ℕ)^10 * L^4127 ≤ B^2000 := by
  apply quotient_power_gap L B 2583 125 2000 127 10 (by decide)
  · norm_num [L, B]
  · exact Sensitivity20635Arithmetic.hgap_short

theorem initial_factor : rho^4127 ≤ ((2:ℕ)^10)^4753 := by
  calc
    rho^4127 ≤ ((2:ℕ)^11)^4127 := Nat.pow_le_pow_left (by decide) _
    _ = (2:ℕ)^(11*4127) := by rw [pow_mul]
    _ ≤ (2:ℕ)^(10*4753) := Nat.pow_le_pow_right (by decide) (by decide)
    _ = ((2:ℕ)^10)^4753 := by rw [pow_mul]

theorem pow_exchange (a m n : ℕ) : (a^m)^n = (a^n)^m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm m n]

theorem iterated_power_bound (l b c m p q e : ℕ)
    (hinit : c^p ≤ ((2:ℕ)^e)^m) (hgap : (2:ℕ)^e*l^p ≤ b^q) :
    (c*l^m)^p ≤ (b^m)^q := by
  calc
    (c*l^m)^p = c^p * (l^p)^m := by
      rw [mul_pow, pow_exchange l m p]
    _ ≤ ((2:ℕ)^e)^m * (l^p)^m := Nat.mul_le_mul_right _ hinit
    _ = ((2^e)*l^p)^m := (mul_pow _ _ _).symm
    _ ≤ (b^q)^m := Nat.pow_le_pow_left hgap _
    _ = (b^m)^q := pow_exchange b q m

theorem seed_power : (rho*L^4753)^4127 ≤ (B^4753)^2000 :=
  iterated_power_bound L B rho 4753 4127 2000 10 initial_factor arithmetic_gap

theorem real_power_of_nat_power {a b : ℕ} (h : a^4127 ≤ b^2000) :
    (a : ℝ) ^ (2.0635 : ℝ) ≤ (b : ℝ) := by
  have hr : (a : ℝ)^4127 ≤ (b : ℝ)^2000 := by
    exact_mod_cast h
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _) (by norm_num : (2000:ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),
    show (2.0635 : ℝ) * (2000:ℕ) = ((4127:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  exact hr

theorem seed_real_power : ((rho*L^4753 : ℕ) : ℝ) ^ (2.0635 : ℝ) ≤
    ((B^4753 : ℕ) : ℝ) := real_power_of_nat_power seed_power

end Sensitivity20635


/- Local proof component: CoupledRepair. -/

open OAI.Paper320 Sensitivity205
open scoped Classical

namespace Sensitivity20635
noncomputable section
set_option maxHeartbeats 3000000

section Geometry
variable {k r h : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin (h+1) → (I → Bool) → Bool)
  (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)

 theorem target_gate_disjoint : Disjoint (targetCandidates T label F q x)
    (gateCandidates T label F q x) := by
  apply Finset.disjoint_left.mpr
  intro i ht hg
  have ht' := (Finset.mem_filter.mp ht).2.1
  have hg' := (Finset.mem_filter.mp hg).2.1
  simp [hg'] at ht'

include hF in
 theorem target_not_to_gate {i j : Fin k}
    (hi : i ∈ targetCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) : ¬ T.Adj i j := by
  intro hij
  have hz := (gateFailures_empty_iff T label F q x i).mp
    (Finset.mem_filter.mp hi).2.2 j hij
  have ho := hF.accepts_of_le (gateIndex_lt_last q).le
    ((targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1 (label i j))
  simp [hz] at ho

include hF in
 theorem gate_to_target {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ targetCandidates T label F q x) : T.Adj i j := by
  have hne : i ≠ j := by
    intro hij; subst j
    exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) hj hi
  rcases T.adj_or_reverse hne with ha | ha
  · exact ha
  · exact False.elim (target_not_to_gate T label F hF q x hj hi ha)

 theorem gate_passes {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x) (hij : T.Adj i j)
    (hne : j ≠ gateWitness T label F q x i) :
    F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  cases ho : F (gateIndex q) (recursiveChild x j (label i j))
  · rfl
  · exact False.elim (hne (gateWitness_unique T label F q x i hi j hij ho))

include hF in
 theorem target_incoming_label (hr : 0 < r) {i j : Fin k}
    (hj : j ∈ targetCandidates T label F q x)
    (hz : F (gateIndex q) (recursiveChild x j (label i j)) = false) :
    label i j = targetWitness F x hr j := by
  exact targetWitness_unique T label F q x hr j hj (label i j)
    (hF.rejects_of_le (gateIndex_lt_last q).le hz)

include hF in
 theorem target_incoming_zero (hr : 0 < r) {i j : Fin k}
    (hj : j ∈ targetCandidates T label F q x)
    (hz : F (gateIndex q) (recursiveChild x j (label i j)) = false) :
    F (gateIndex q) (recursiveChild x j (targetWitness F x hr j)) = false := by
  rwa [target_incoming_label T label F hF q x hr hj hz] at hz

include hF in
 theorem gate_incoming_unique {i j v : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x)
    (hv : v ∈ gateCandidates T label F q x)
    (hiv : T.Adj i v) (hjv : T.Adj j v) : i = j := by
  by_contra hne
  rcases T.adj_or_reverse hne with hij | hji
  · have h1 := gateCandidates_neighbor T label F hF q x i j hi hj hij
    have h2 := gateCandidates_neighbor T label F hF q x i v hi hv hiv
    exact T.ne_of_adj hjv (h1.trans h2.symm)
  · have h1 := gateCandidates_neighbor T label F hF q x j i hj hi hji
    have h2 := gateCandidates_neighbor T label F hF q x j v hj hv hjv
    exact T.ne_of_adj hiv (h1.trans h2.symm)

include hF in
 theorem target_sources_card (hr : 0 < r) :
    ((targetCandidates T label F q x).filter fun i =>
      F (gateIndex q) (recursiveChild x i (targetWitness F x hr i)) = true).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hio⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjo⟩ := Finset.mem_filter.mp hj
  by_contra hne
  rcases T.adj_or_reverse hne with hij | hji
  · have hz := (gateFailures_empty_iff T label F q x i).mp
      (Finset.mem_filter.mp hi).2.2 j hij
    have hz' := target_incoming_zero T label F hF q x hr hj hz
    simp [hz'] at hjo
  · have hz := (gateFailures_empty_iff T label F q x j).mp
      (Finset.mem_filter.mp hj).2.2 i hji
    have hz' := target_incoming_zero T label F hF q x hr hi hz
    simp [hz'] at hio

include hF in
 theorem gate_internal_forces_targets (hr : 0 < r) {i j : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j)
    {v : Fin k} (hv : v ∈ targetCandidates T label F q x) :
    F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false := by
  have hw := gateCandidates_neighbor T label F hF q x i j hi hj hij
  have hvj : v ≠ j := by
    intro e
    exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) (e ▸ hv) hj
  apply target_incoming_zero T label F hF q x hr hv
  apply gate_passes T label F q x hi (gate_to_target T label F hF q x hi hv)
  rwa [← hw]

include hF in
 theorem gate_card_two_targets_zero (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card)
    {v : Fin k} (hv : v ∈ targetCandidates T label F q x) :
    F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false := by
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (gateCandidates T label F q x).card)
  rcases T.adj_or_reverse hne with hij | hji
  · exact gate_internal_forces_targets T label F hF q x hr hi hj hij hv
  · exact gate_internal_forces_targets T label F hF q x hr hj hi hji hv

 theorem gate_targets_false_witness_not_target (hr : 0 < r)
    (hz : ∀ v ∈ targetCandidates T label F q x,
      F (gateIndex q) (recursiveChild x v (targetWitness F x hr v)) = false)
    {i : Fin k} (hi : i ∈ gateCandidates T label F q x)
    (ht : F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
      (label i (gateWitness T label F q x i))) = false) :
    gateWitness T label F q x i ∉ targetCandidates T label F q x := by
  intro hw
  have he := targetWitness_unique T label F q x hr _ hw _ ht
  have hon := (gateWitness_spec T label F q x i hi).2
  rw [he, hz _ hw] at hon
  exact Bool.false_ne_true hon

include hF in
 theorem gate_false_target_sink {i : Fin k}
    (hi : i ∈ gateCandidates T label F q x)
    (ht : F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
      (label i (gateWitness T label F q x i))) = false) :
    i ∈ gateSinks T label F q x := by
  apply Finset.mem_filter.mpr
  refine ⟨hi, ?_⟩
  intro j hj hij
  have hw := gateCandidates_neighbor T label F hF q x i j hi hj hij
  have hon := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1 (label i j)
  rw [hw, ht] at hon
  exact Bool.false_ne_true hon

include hF in
 theorem gate_false_targets_card :
    ((gateCandidates T label F q x).filter fun i =>
      F (Fin.last h) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = false).card ≤ 1 := by
  apply le_trans (Finset.card_le_card (t := gateSinks T label F q x) ?_)
    (gateSinks_card T label F q x)
  intro i hi
  exact gate_false_target_sink T label F hF q x (Finset.mem_filter.mp hi).1
    (Finset.mem_filter.mp hi).2

include hF in
 theorem gate_sink_card_le_two {v : Fin k}
    (hv : v ∈ gateSinks T label F q x) : (gateCandidates T label F q x).card ≤ 2 := by
  have hvin := (Finset.mem_filter.mp hv).1
  have hout := (Finset.mem_filter.mp hv).2
  have he : ((gateCandidates T label F q x).erase v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := Finset.mem_erase.mp hi
    have hj' := Finset.mem_erase.mp hj
    have hiv : T.Adj i v := (T.adj_or_reverse hi'.1).resolve_right (hout i hi'.2)
    have hjv : T.Adj j v := (T.adj_or_reverse hj'.1).resolve_right (hout j hj'.2)
    exact gate_incoming_unique T label F hF q x hi'.2 hj'.2 hvin hiv hjv
  have hc := Finset.card_erase_add_one hvin
  omega

include hF in
 theorem gate_card_three_witness_mem
    (hg : (gateCandidates T label F q x).card = 3) {i : Fin k}
    (hi : i ∈ gateCandidates T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  apply nonsink_gateWitness_mem T label F hF q x i hi
  intro hs
  have hc := gate_sink_card_le_two T label F hF q x hs
  omega

include hF in
 theorem coherent_targets_gates {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r) (E : Finset (Fin k))
    (hE : E ⊆ gateCandidates T label F q x)
    (hw : ∀ i ∈ E, gateWitness T label F q x i ∉ targetCandidates T label F q x) :
    (targetCandidates T label F q x).card + E.card < t := by
  let pred : Fin k → Fin k := fun j =>
    if h : ∃ i ∈ E, T.Adj i j then h.choose else j
  let m : Fin k → Fin r := fun j =>
    if j ∈ targetCandidates T label F q x then targetWitness F x hr j else label (pred j) j
  have hc : ((targetCandidates T label F q x) ∪ E).card < t := by
    apply A.coherent_card _ m
    intro i hi j hj hij
    rw [heq]
    rcases Finset.mem_union.mp hj with hj | hj
    · have hz : F (gateIndex q) (recursiveChild x j (label i j)) = false := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact (gateFailures_empty_iff T label F q x i).mp (Finset.mem_filter.mp hi).2.2 j hij
        · exact gate_passes T label F q x (hE hi) hij (fun e => hw i hi (e ▸ hj))
      simpa [m, hj] using target_incoming_label T label F hF q x hr hj hz
    · have hjn : j ∉ targetCandidates T label F q x := fun h =>
        Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h (hE hj)
      have hie : i ∈ E := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact False.elim (target_not_to_gate T label F hF q x hi (hE hj) hij)
        · exact hi
      have hex : ∃ a ∈ E, T.Adj a j := ⟨i, hie, hij⟩
      have hp : pred j ∈ E ∧ T.Adj (pred j) j := by
        simp only [pred, dif_pos hex]
        exact hex.choose_spec
      have hip : i = pred j := gate_incoming_unique T label F hF q x
        (hE hie) (hE hp.1) (hE hj) hij hp.2
      simpa [m, hjn, hip]
  rw [Finset.card_union_of_disjoint] at hc
  · exact hc
  · exact (target_gate_disjoint T label F q x).mono_right hE


include hF in
 theorem targets_card_sub_two {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card) :
    (targetCandidates T label F q x).card ≤ t-2 := by
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (gateCandidates T label F q x).card)
  have step : ∀ i ∈ gateCandidates T label F q x, ∀ j ∈ gateCandidates T label F q x,
      T.Adj i j → (targetCandidates T label F q x).card ≤ t-2 := by
    intro a ha b hb hab
    have hc := coherent_targets_gates T label F hF q x A heq hr {a}
      (by simpa using ha) (by
        intro c hc
        have hc' : c = a := Finset.mem_singleton.mp hc
        subst c
        rw [← gateCandidates_neighbor T label F hF q x a b ha hb hab]
        exact fun h => Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h hb)
    simp only [Finset.card_singleton] at hc
    omega
  rcases T.adj_or_reverse hne with hij | hji
  · exact step i hi j hj hij
  · exact step j hj i hi hji

include hF in
 theorem targets_card_with_ordinary {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : 2 ≤ (gateCandidates T label F q x).card)
    {b : Fin k} (hb : b ∈ gateCandidates T label F q x)
    (hbo : F (Fin.last h) (recursiveChild x (gateWitness T label F q x b)
      (label b (gateWitness T label F q x b))) = false) :
    (targetCandidates T label F q x).card + (gateCandidates T label F q x).card < t := by
  apply coherent_targets_gates T label F hF q x A heq hr _ (fun _ h => h)
  intro i hi
  by_cases he : i = b
  · subst i
    exact gate_targets_false_witness_not_target T label F q x hr
      (fun v hv => gate_card_two_targets_zero T label F hF q x hr hg hv) hb hbo
  · have hs := (Finset.mem_filter.mp (gate_false_target_sink T label F hF q x hb hbo)).2
    have hib := (T.adj_or_reverse he).resolve_right (hs i hi)
    rw [← gateCandidates_neighbor T label F hF q x i b hi hb hib]
    exact fun h => Finset.disjoint_left.mp (target_gate_disjoint T label F q x) h hb

include hF in
 theorem targets_card_with_three {t : ℕ} (A : Labeling T r t)
    (heq : A.label = label) (hr : 0 < r)
    (hg : (gateCandidates T label F q x).card = 3) :
    (targetCandidates T label F q x).card ≤ t-4 := by
  have hc := coherent_targets_gates T label F hF q x A heq hr
    (gateCandidates T label F q x) (fun _ h => h) (by
      intro i hi ht
      exact Finset.disjoint_left.mp (target_gate_disjoint T label F q x) ht
        (gate_card_three_witness_mem T label F hF q x hg hi))
  omega

end Geometry

section Repair
variable {k r h : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin (h+1) → (I → Bool) → Bool)
  (hF : NestedFamily F) (q q' : Fin h) (hqq : q ≤ q')
  (x : ((Fin k × Fin r) × I) → Bool)

include hF hqq in
 theorem stronger_gate_weaker_true
    (hx : recursiveFamily T label F q x = false) {i : Fin k}
    (hi : i ∈ gateCandidates T label F q' x) :
    F (gateIndex q) (recursiveChild x (gateWitness T label F q' x i)
      (label i (gateWitness T label F q' x i))) = true := by
  cases ho : F (gateIndex q) (recursiveChild x (gateWitness T label F q' x i)
      (label i (gateWitness T label F q' x i)))
  · have hrow : rowClause T label F q x i = true := by
      apply (rowClause_eq_true_iff T label F q x i).mpr
      refine ⟨(targetFailures_empty_iff F x i).mp (Finset.mem_filter.mp hi).2.1, ?_⟩
      intro j hij
      by_cases he : j = gateWitness T label F q' x i
      · simpa [he] using ho
      · exact hF.rejects_of_le (gateIndex_antitone hqq)
          (gate_passes T label F q' x hi hij he)
    have hz := (recursiveFamily_eq_false_iff T label F q x).mp hx i
    simp [hz] at hrow
  · rfl

end Repair


 theorem recursive_pair_zero_coupled {k r h t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (ht : 4 ≤ t)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q')
    (hZA : Z (gateIndex q') (Fin.last h) ≤ Z (Fin.last h) (Fin.last h))
    (hYK : Y (gateIndex q') (Fin.last h) ≤ Y (gateIndex q') (gateIndex q))
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false) :
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      max (max (max (Z (Fin.last h) (Fin.last h) + Y (gateIndex q') (gateIndex q) +
        (t-2)*Z (gateIndex q') (Fin.last h))
        (Y (gateIndex q') (gateIndex q)+Y (gateIndex q') (Fin.last h)+
          (t-3)*Z (gateIndex q') (Fin.last h)))
        (2*Y (gateIndex q') (Fin.last h)+(t-2)*Z (gateIndex q') (Fin.last h)))
        (3*Y (gateIndex q') (Fin.last h)+(t-4)*Z (gateIndex q') (Fin.last h)) := by
  let TC := targetCandidates T A.label F q' x
  let GC := gateCandidates T A.label F q' x
  let tw := targetWitness F x hr
  let gw := gateWitness T A.label F q' x
  let T0 := TC.filter fun i => F (gateIndex q') (recursiveChild x i (tw i)) = false
  let T1 := TC.filter fun i => F (gateIndex q') (recursiveChild x i (tw i)) = true
  let G0 := GC.filter fun i => F (Fin.last h) (recursiveChild x (gw i) (A.label i (gw i))) = false
  let G1 := GC.filter fun i => F (Fin.last h) (recursiveChild x (gw i) (A.label i (gw i))) = true
  let U := T1.biUnion fun i => childChanges F (Fin.last h) x i (tw i)
  let V := T0.biUnion fun i => childJointChanges F (gateIndex q') (Fin.last h) x i (tw i)
  let W := G0.biUnion fun i => childJointChanges F (gateIndex q') (gateIndex q) x (gw i) (A.label i (gw i))
  let X := G1.biUnion fun i => childJointChanges F (gateIndex q') (Fin.last h) x (gw i) (A.label i (gw i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x ∧
      recursiveFamily T A.label F q' (flip x {p}) ≠ recursiveFamily T A.label F q' x) ⊆
      (U ∪ V) ∪ (W ∪ X) := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hon' : recursiveFamily T A.label F q' (flip x {((j,c),a)}) = true := by
      cases hy : recursiveFamily T A.label F q' (flip x {((j,c),a)})
      · exact False.elim (hc.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label F q' _).mp hon'
    have hi := rowClause_nested T A.label F hF hqq _ i hi'
    have hioff := (recursiveFamily_eq_false_iff T A.label F q' x).mp hx' i
    rcases rowClause_repair_cases T A.label F q' x i j c a hioff hi' with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hcw := targetWitness_unique T A.label F q' x hr i hit c htoff
      have hgon := hF.accepts_of_le (gateIndex_lt_last q').le hton
      apply Finset.mem_union_left
      cases hz : F (gateIndex q') (recursiveChild x i c)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F (gateIndex q') (flip (recursiveChild x i c) {a}) ≠
                F (gateIndex q') (recursiveChild x i c) ∧
              F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
                F (Fin.last h) (recursiveChild x i c) := by simp [hgon, hz, hton, htoff]
          simpa [childJointChanges, tw, hcw] using hn
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, ?_⟩
        · simpa only [tw, ← hcw] using hz
        · have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
              F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
          simpa [childChanges, tw, hcw] using hn
    · have hjw := gateWitness_unique T A.label F q' x i hig j hij hgon
      have hwgon := stronger_gate_weaker_true T A.label F hF q q' hqq x hx hig
      have hweakon : F (gateIndex q) (recursiveChild x j (A.label i j)) = true := by
        simpa [hjw] using hwgon
      have hweakoff := ((rowClause_eq_true_iff T A.label F q _ i).mp hi).2 j hij
      rw [recursiveChild_flip_same] at hweakoff
      apply Finset.mem_union_right
      cases hto : F (Fin.last h) (recursiveChild x j (A.label i j))
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have hn : F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
              F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F (gateIndex q) (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hweakon, hweakoff]
          simpa [childJointChanges, gw, hjw] using hn
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨hig, ?_⟩, ?_⟩
        · simpa only [gw, ← hjw] using hto
        · have htf := hF.rejects_of_le (gateIndex_lt_last q').le hgoff
          have hn : F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
              F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
                F (Fin.last h) (recursiveChild x j (A.label i j)) := by
            simp [hgon, hgoff, hto, htf]
          simpa [childJointChanges, gw, hjw] using hn
  have hU : U.card ≤ T1.card * Z (Fin.last h) (Fin.last h) := by
    apply card_biUnion_le_mul
    intro i hi
    rw [childChanges_card]
    exact hZ.self _ _ (targetWitness_false T A.label F q' x hr i (Finset.mem_filter.mp hi).1)
  have hV : V.card ≤ T0.card * Z (gateIndex q') (Fin.last h) := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, hz⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hZ _ _ (gateIndex_lt_last q').le _ hz (targetWitness_false T A.label F q' x hr i hi)
  have hW : W.card ≤ G0.card * Y (gateIndex q') (gateIndex q) := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := (Finset.mem_filter.mp hi).1
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_antitone hqq) _ (gateWitness_spec T A.label F q' x i hg).2
      (stronger_gate_weaker_true T A.label F hF q q' hqq x hx hg)
  have hX : X.card ≤ G1.card * Y (gateIndex q') (Fin.last h) := by
    apply card_biUnion_le_mul
    intro i hi
    obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_lt_last q').le _ (gateWitness_spec T A.label F q' x i hi).2 ht
  have hcost : jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      T1.card * Z (Fin.last h) (Fin.last h) + T0.card * Z (gateIndex q') (Fin.last h) +
      G0.card * Y (gateIndex q') (gateIndex q) + G1.card * Y (gateIndex q') (Fin.last h) := by
    have hu := Finset.card_union_le U V
    have hw := Finset.card_union_le W X
    have hc := Finset.card_union_le (U ∪ V) (W ∪ X)
    have hs := Finset.card_le_card hsub
    change jointSensitivityAt _ _ x ≤ _ at hs
    omega
  have hnsum : T0.card + T1.card = TC.card := by
    simpa [T0, T1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := TC)
        (fun i => F (gateIndex q') (recursiveChild x i (tw i)) = false))
  have hmsum : G0.card + G1.card = GC.card := by
    simpa [G0, G1, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := GC)
        (fun i => F (Fin.last h) (recursiveChild x (gw i) (A.label i (gw i))) = false))
  have hn1 : T1.card ≤ 1 := target_sources_card T A.label F hF q' x hr
  have hm0 : G0.card ≤ 1 := gate_false_targets_card T A.label F hF q' x
  have hm : G0.card + G1.card ≤ 3 := by
    rw [hmsum]
    exact gateCandidates_card T A.label F hF q' x
  have hn : T0.card + T1.card ≤ t-1 := by
    have hc := Sensitivity205.targetCandidates_card T A F hF q' x hr
    change TC.card < t at hc
    omega
  have hnzero : 2 ≤ G0.card + G1.card → T1.card = 0 := by
    intro hg
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi, hon⟩ := Finset.mem_filter.mp hi
    have hz := gate_card_two_targets_zero T A.label F hF q' x hr
      (by simpa [hmsum] using hg) hi
    simp [T1, tw, hz] at hon
  have htwo0 : G0.card + G1.card = 2 → G0.card = 0 → T0.card ≤ t-2 := by
    intro hg _
    have hc := targets_card_sub_two T A.label F hF q' x A rfl hr (by omega : 2 ≤ GC.card)
    change TC.card ≤ t-2 at hc
    omega
  have htwo1 : G0.card + G1.card = 2 → G0.card = 1 → T0.card ≤ t-3 := by
    intro hg hzero
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < G0.card)
    obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
    have hc := targets_card_with_ordinary T A.label F hF q' x A rfl hr
      (by omega : 2 ≤ GC.card) hb hbo
    change TC.card + GC.card < t at hc
    omega
  have hthree : G0.card + G1.card = 3 → G0.card = 0 ∧ T0.card ≤ t-4 := by
    intro hg
    have hgc : GC.card = 3 := by omega
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hi
      have hs := gate_false_target_sink T A.label F hF q' x hi ho
      have hc := gate_sink_card_le_two T A.label F hF q' x hs
      change GC.card ≤ 2 at hc
      omega
    · have hc := targets_card_with_three T A.label F hF q' x A rfl hr hgc
      change TC.card ≤ t-4 at hc
      omega
  exact hcost.trans (coupled_weighted_bound T0.card T1.card G0.card G1.card t
    (Z (Fin.last h) (Fin.last h)) (Y (gateIndex q') (gateIndex q))
    (Z (gateIndex q') (Fin.last h)) (Y (gateIndex q') (Fin.last h))
    ht hZA hYK hn1 hm0 hm hn hnzero htwo0 htwo1 hthree)

end
end Sensitivity20635


/- Local proof component: WordFamily. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open OAI.Paper320 Sensitivity205
open scoped Classical

namespace Sensitivity20635
noncomputable section

/- Specialized interface, with the threshold separate from the family width. -/
def CoupledZeroRule : Prop :=
  ∀ {k r h τ : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r τ)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (hr : 0 < r) (ht : 4 ≤ τ)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q')
    (hZA : Z (gateIndex q') (Fin.last h) ≤ Z (Fin.last h) (Fin.last h))
    (hYK : Y (gateIndex q') (Fin.last h) ≤ Y (gateIndex q') (gateIndex q))
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false),
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      repairBound τ (Z (Fin.last h) (Fin.last h))
        (Y (gateIndex q') (gateIndex q))
        (Z (gateIndex q') (Fin.last h)) (Y (gateIndex q') (Fin.last h))

theorem base_bounds1074 {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ rho*u) :
    PairBound (base g) false (fun q q' => Z0 q q'*u) ∧
    PairBound (base g) true (fun q q' => Y0 q q'*u) := by
  constructor
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Z0] using base_side g false u h0 q x hx
    · rw [base_joint_zero g q q' hlt x false hx hx']; exact Nat.zero_le _
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Y0, Nat.mul_assoc] using base_side g true (rho*u) h1 q x hx
    · rw [base_joint_zero g q q' hlt x true hx hx']; exact Nat.zero_le _

def tournament (d : ℕ) : Tournament (K d) := cyclicTournament (D d)

theorem labeling_nonempty (d : ℕ) : Nonempty (Labeling (tournament d) 2 (t d)) := by
  rcases d with _ | _ | _ | _ | _ | _ | d
  · exact labeling_exists_layer1 _
  · exact labeling_exists_layer2 _
  · exact labeling_exists_layer2 _
  · exact labeling_exists_layer2 _
  · exact labeling_exists_layer3 _
  · exact labeling_exists_layer3 _
  · exact labeling_exists_layer1 _

def labeling (d : ℕ) : Labeling (tournament d) 2 (t d) :=
  Classical.choice (labeling_nonempty d)

theorem t_ge_four (d : ℕ) : 4 ≤ t d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> simp [t]

def step {I : Type} (d : ℕ) (F : Fin 3 → (I → Bool) → Bool) :
    Fin 3 → ((Fin (K d) × Fin 2) × I → Bool) → Bool :=
  recursiveFamily (tournament d) (labeling d).label (extend F)

theorem step_nested {I : Type} (d : ℕ) {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step d F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff _ _ _ _ _).mp hx
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  exact ⟨i, rowClause_nested _ _ _ (extend_nested hF) hqq x i hi⟩

theorem repairBound_mul (t A B J K u : ℕ) :
    repairBound t (A*u) (B*u) (J*u) (K*u) = repairBound t A B J K*u := by
  simp only [repairBound, Nat.add_mul, Nat.mul_assoc, max_mul]

theorem step_bounds (repair : CoupledZeroRule) {I : Type} [Fintype I]
    (F : Fin 3 → (I → Bool) → Bool) (hF : NestedFamily F)
    (d u : ℕ) (hd : d < 7)
    (hz : PairBound F false (fun i j => (profiles d).1 i j*u))
    (hy : PairBound F true (fun i j => (profiles d).2 i j*u)) :
    PairBound (step d F) false (fun i j => (profiles (d+1)).1 i j*u) ∧
    PairBound (step d F) true (fun i j => (profiles (d+1)).2 i j*u) := by
  have hz' : PairBound (extend F) false
      (fun i j => (profiles d).1 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hz _ _ (clip_mono hij) x hx hx'
  have hy' : PairBound (extend F) true
      (fun i j => (profiles d).2 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hy _ _ (clip_mono hij) x hx hx'
  constructor
  · intro q q' hqq x hx hx'
    have hcompat := compatible_tables ⟨d, hd⟩ (Fin.rev q') (Fin.rev q)
      (Fin.rev_le_rev.mpr hqq)
    have hZA : (profiles d).1 (clip (gateIndex q')) (clip (Fin.last 3))*u ≤
        (profiles d).1 (clip (Fin.last 3)) (clip (Fin.last 3))*u := by
      simp only [clip_gate, clip_last]
      exact Nat.mul_le_mul_right u hcompat.1
    have hYK : (profiles d).2 (clip (gateIndex q')) (clip (Fin.last 3))*u ≤
        (profiles d).2 (clip (gateIndex q')) (clip (gateIndex q))*u := by
      simp only [clip_gate, clip_last]
      exact Nat.mul_le_mul_right u hcompat.2
    have hh := repair (tournament d) (labeling d) (extend F) (extend_nested hF)
      (by norm_num) (t_ge_four d) _ _ hz' hy' q q' hqq hZA hYK x hx hx'
    simpa only [step, profiles_succ d hd, nextProfile, clip_last, clip_gate, repairBound_mul] using hh
  · intro q q' hqq x hx hx'
    have hh := recursive_pair_one (tournament d) (labeling d).label (extend F)
      (extend_nested hF) (D d) (cyclicTournament_outdegree (D d)) _ _ hz' hy'
      q q' hqq x hx hx'
    simpa [step, profiles_succ d hd, nextProfile, Nat.add_mul, Nat.mul_assoc] using hh

abbrev LevelCoord (I : Type) : ℕ → Type
  | 0 => Fin 3 × I
  | d+1 => (Fin (K d) × Fin 2) × LevelCoord I d

instance levelFintype (I : Type) [Fintype I] (d : ℕ) : Fintype (LevelCoord I d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 3 × I))
  | succ d ih => exact inferInstanceAs (Fintype ((Fin (K d) × Fin 2) × LevelCoord I d))

def levels {I : Type} (g : (I → Bool) → Bool) :
    (d : ℕ) → Fin 3 → (LevelCoord I d → Bool) → Bool
  | 0 => base g
  | d+1 => step d (levels g d)

theorem levels_nested {I : Type} (g : (I → Bool) → Bool) (d : ℕ) :
    NestedFamily (levels g d) := by
  induction d with
  | zero => exact base_nested g
  | succ d ih => exact step_nested d ih

theorem levels_bounds (repair : CoupledZeroRule) {I : Type} [Fintype I]
    (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ rho*u)
    (d : ℕ) (hd : d ≤ 7) :
    PairBound (levels g d) false (fun i j => (profiles d).1 i j*u) ∧
    PairBound (levels g d) true (fun i j => (profiles d).2 i j*u) := by
  induction d with
  | zero => exact base_bounds1074 g u h0 h1
  | succ d ih =>
    have hh := ih (by omega)
    exact step_bounds repair (levels g d) (levels_nested g d) d u (by omega) hh.1 hh.2

def amplify {I : Type} (g : (I → Bool) → Bool) : (LevelCoord I 7 → Bool) → Bool :=
  levels g 7 1

theorem amplify_bounds (repair : CoupledZeroRule) {I : Type} [Fintype I]
    (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ rho*u) :
    (∀ x, amplify g x = false → sensitivityAt (amplify g) x ≤ L*u) ∧
    (∀ x, amplify g x = true → sensitivityAt (amplify g) x ≤ rho*(L*u)) := by
  have hh := levels_bounds repair g u h0 h1 7 le_rfl
  constructor
  · intro x hx
    exact (hh.1.self 1 x hx).trans (Nat.mul_le_mul_right u final_bounds.1)
  · intro x hx
    exact (hh.2.self 1 x hx).trans
      (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right u final_bounds.2)

def stepBlocks {I : Type} (d : ℕ) {F : Fin 3 → (I → Bool) → Bool} {n : ℕ}
    (w : Blocks F n) : Blocks (step d F) (K d*n) where
  zero q := recursiveFamily_zero (tournament d) (labeling d).label (extend F) (by norm_num)
    (fun j => w.zero (clip j)) q
  sets i := rowLift (finProdFinEquiv.symm i).1 (w.sets (finProdFinEquiv.symm i).2)
  nonempty i := by
    obtain ⟨a, ha⟩ := w.nonempty (finProdFinEquiv.symm i).2
    exact ⟨(((finProdFinEquiv.symm i).1,0),a), (mem_rowLift _ _ _).mpr ⟨rfl,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := (mem_rowLift _ _ _).mp hp
    have hj := (mem_rowLift _ _ _).mp hq
    have he : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 := hi.1.symm.trans hj.1
    have hne : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
      intro he'
      exact hij (finProdFinEquiv.symm.injective (Prod.ext he he'))
    exact Finset.disjoint_left.mp (w.disjoint hne) hi.2 hj.2
  on q i := recursiveFamily_rowLift (tournament d) (labeling d).label (extend F)
    (fun j => w.zero (clip j)) _ (fun j => w.on (clip j) _) _ q

def levelsBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) :
    (d : ℕ) → Blocks (levels g d) (blockGain d*n)
  | 0 => by simpa [levels, blockGain] using baseBlocks w
  | d+1 => by
    simpa [levels, blockGain, Nat.mul_assoc] using stepBlocks d (levelsBlocks w d)

def amplifyBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) : Blocks (fun _ : Fin 1 => amplify g) (B*n) := by
  have wb : Blocks (levels g 7) (B*n) := by
    simpa only [blockGain_seven] using levelsBlocks w 7
  exact {
    zero := fun _ => wb.zero 1
    sets := wb.sets
    nonempty := wb.nonempty
    disjoint := wb.disjoint
    on := fun _ => wb.on 1 }

abbrev IterCoord : ℕ → Type
  | 0 => Fin 1
  | m+1 => LevelCoord (IterCoord m) 7

instance iterFintype (m : ℕ) : Fintype (IterCoord m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ m ih => exact levelFintype (IterCoord m) 7

def iter : (m : ℕ) → (IterCoord m → Bool) → Bool
  | 0 => fun x => x 0
  | m+1 => amplify (iter m)

def iterBlocks : (m : ℕ) → Blocks (fun _ : Fin 1 => iter m) (B^m)
  | 0 => {
      zero := fun _ => rfl
      sets := fun _ => {0}
      nonempty := fun _ => Finset.singleton_nonempty _
      disjoint := by
        intro i j hij
        have he : i = j := by apply Fin.ext; have := i.isLt; have := j.isLt; simp at *
        exact False.elim (hij he)
      on := by intro q i; simp [iter, OAI.Paper320.flip] }
  | m+1 => by simpa [iter, pow_succ, Nat.mul_comm] using amplifyBlocks (iterBlocks m)

theorem iter_sides (repair : CoupledZeroRule) (m : ℕ) :
    (∀ x, iter m x = false → sensitivityAt (iter m) x ≤ L^m) ∧
    (∀ x, iter m x = true → sensitivityAt (iter m) x ≤ rho*L^m) := by
  induction m with
  | zero =>
    constructor <;> intro x hx
    · exact (sensitivityAt_le_card _ _).trans (by simp [IterCoord])
    · exact (sensitivityAt_le_card _ _).trans (by simp [IterCoord])
  | succ m ih =>
    simpa [iter, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      amplify_bounds repair (iter m) (L^m) ih.1 ih.2

theorem iter_sensitivity (repair : CoupledZeroRule) (m : ℕ) :
    sensitivity (iter m) ≤ rho*L^m := by
  apply sensitivity_le
  intro x
  cases hx : iter m x
  · exact ((iter_sides repair m).1 x hx).trans (by simp only [rho]; omega)
  · exact (iter_sides repair m).2 x hx

theorem iter_blocksensitivity (m : ℕ) : B^m ≤ blockSensitivityAt (iter m) (fun _ => false) := by
  have w := iterBlocks m
  simpa only [Fintype.card_fin] using
    le_blockSensitivityAt_of_family (iter m) (fun _ => false) w.sets w.nonempty w.disjoint
      (fun i => by rw [w.on 0 i, w.zero 0]; decide)

theorem finite_seed (repair : CoupledZeroRule) (m : ℕ) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ rho*L^m ∧ B^m ≤ blockSensitivityAt f (fun _ => false) := by
  let e := Fintype.equivFin (IterCoord m)
  refine ⟨Fintype.card (IterCoord m), reindex e (iter m), ?_, ?_⟩
  · rw [sensitivity_reindex]; exact iter_sensitivity repair m
  · rw [blockSensitivityAt_reindex]; exact iter_blocksensitivity m

theorem achieves_20635 (repair : CoupledZeroRule) :
    SensitivityCampaign.AchievesExponent (2.0635 : ℝ) := by
  obtain ⟨n, f, hs, hb⟩ := finite_seed repair 4753
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (rho*L^4753) (B^4753) (2.0635:ℝ) _ _ (by norm_num) hs hb seed_real_power
  · have hp : 0 < L^4753 := pow_pos (by norm_num [L]) _
    simp only [rho]
    omega
  · exact one_lt_pow₀ (by norm_num [B]) (by norm_num)

end
end Sensitivity20635


/- Local proof component: Final20635. -/
set_option autoImplicit false

namespace Sensitivity20635

theorem coupled_zero_rule : CoupledZeroRule := by
  intro k r h t I inst T A F hF hr ht Z Y hZ hY q q' hqq hZA hYK x hx hx'
  exact recursive_pair_zero_coupled T A F hF hr ht Z Y hZ hY
    q q' hqq hZA hYK x hx hx'

theorem reach_20635 : SensitivityCampaign.AchievesExponent (2.0635 : ℝ) :=
  achieves_20635 coupled_zero_rule

end Sensitivity20635

theorem solution : SensitivityCampaign.AchievesExponent (2.0635 : ℝ) :=
  Sensitivity20635.reach_20635



#print axioms solution
