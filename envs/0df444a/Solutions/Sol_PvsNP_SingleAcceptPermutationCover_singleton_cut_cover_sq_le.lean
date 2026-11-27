-- Prove2me | solution 1 for PvsNP.SingleAcceptPermutationCover.singleton_cut_cover_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T05:35:15.063477+00:00
-- url     : https://prove2.me/submissions/68bb6a0d-e243-45a3-a470-c9e64de6f3ee

import Mathlib

set_option autoImplicit false

namespace PvsNP.SingletonCutAux

open scoped BigOperators

abbrev Word (r : ℕ) := Fin r → Bool

def DisjointPair {r : ℕ} (left right : Word r) : Prop :=
  ∀ i, ¬ (left i = true ∧ right i = true)

def Fiber {A Q : Type*} (f : A → Q) (q : Q) :=
  {a : A // f a = q}

private def fiberTypes {A Q : Type*} (f : A → Q) : A ≃ (Σ q, Fiber f q) where
  toFun a := ⟨f a, a, rfl⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨q, a, h⟩
    subst q
    rfl

private def matchingTypes {A B Q : Type*} (f : A → Q) (g : B → Q) :
    {p : A × B // f p.1 = g p.2} ≃ (Σ q, Fiber f q × Fiber g q) where
  toFun p := ⟨f p.val.1, ⟨⟨p.val.1, rfl⟩, ⟨p.val.2, p.property.symm⟩⟩⟩
  invFun p := ⟨(p.2.1.val, p.2.2.val), p.2.1.property.trans p.2.2.property.symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨q, ⟨a, ha⟩, ⟨b, hb⟩⟩
    subst q
    rfl

private theorem fiber_bound {r : ℕ} {Q : Type*}
    (left right : Word r → Q)
    (safe : ∀ x y, left x = right y → DisjointPair x y) (q : Q) :
    Nat.card (Fiber left q) * Nat.card (Fiber right q) ≤ 2 ^ r := by
  classical
  let join : Fiber left q × Fiber right q → Word r :=
    fun p i => p.1.val i || p.2.val i
  have hinj : Function.Injective join := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hab := safe a.val b.val (a.property.trans b.property.symm)
    have had := safe a.val d.val (a.property.trans d.property.symm)
    have hcb := safe c.val b.val (c.property.trans b.property.symm)
    have hcd := safe c.val d.val (c.property.trans d.property.symm)
    have hb_eq (i : Fin r) : a.val i = c.val i ∧ b.val i = d.val i := by
      have he := congrFun h i
      change (a.val i || b.val i) = (c.val i || d.val i) at he
      have hAB := hab i
      have hAD := had i
      have hCB := hcb i
      have hCD := hcd i
      cases ha : a.val i <;> cases hb : b.val i <;>
        cases hc : c.val i <;> cases hd : d.val i <;>
        simp_all
    exact Prod.ext (Subtype.ext (funext fun i => (hb_eq i).1))
      (Subtype.ext (funext fun i => (hb_eq i).2))
  have h := Nat.card_le_card_of_injective join hinj
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fun] using h

/-- If acceptance at a cut is equality of a forward state and a backward state, then a sound
checker for disjoint pairs covers at most 8^r after squaring its number of accepted inputs. -/
theorem cut_cover_sq_le {r : ℕ} {Q : Type*} [Fintype Q]
    (left right : Word r → Q)
    (safe : ∀ x y, left x = right y → DisjointPair x y) :
    (Nat.card {p : Word r × Word r // left p.1 = right p.2}) ^ 2 ≤ 8 ^ r := by
  classical
  let a (q : Q) := Nat.card (Fiber left q)
  let b (q : Q) := Nat.card (Fiber right q)
  have source (f : Word r → Q) : (∑ q, Nat.card (Fiber f q)) = 2 ^ r := by
    have c := Nat.card_congr (fiberTypes f)
    have hr : Nat.card (Word r) = 2 ^ r := by simp [Word, Nat.card_eq_fintype_card]
    rw [hr] at c
    have (q : Q) : Fintype (Fiber f q) := by
      unfold Fiber
      infer_instance
    exact (by simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using c.symm)
  have count : Nat.card {p : Word r × Word r // left p.1 = right p.2} =
      ∑ q, a q * b q := by
    have (q : Q) : Fintype (Fiber left q) := by
      unfold Fiber
      infer_instance
    have (q : Q) : Fintype (Fiber right q) := by
      unfold Fiber
      infer_instance
    convert Nat.card_congr (matchingTypes left right) using 1
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_prod, a, b]
  rw [count]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset Q)
    (r := fun q => a q * b q) (f := fun q => 2 ^ r * a q) (g := b)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)
    (fun q _ => by
      have hb := fiber_bound left right safe q
      change a q * b q ≤ 2 ^ r at hb
      calc
        (a q * b q)^2 ≤ (2^r) * (a q * b q) := by
          rw [sq]
          exact Nat.mul_le_mul_right _ hb
        _ = (2^r * a q) * b q := by ring)
  rw [← Finset.mul_sum] at h
  change (∑ q, a q * b q) ^ 2 ≤ (2 ^ r * ∑ q, a q) * ∑ q, b q at h
  change (∑ q, a q * b q) ^ 2 ≤
    (2 ^ r * ∑ q, Nat.card (Fiber left q)) * ∑ q, Nat.card (Fiber right q) at h
  rw [source left, source right, ← mul_pow, ← mul_pow] at h
  exact h

/-- In a one-accept permutation program, the suffix can be run backward from the
prescribed accepting state. Acceptance is exactly equality at the cut. -/
theorem singleton_accept_iff {A B Q : Type*}
    (startState : A → Q) (suffix : B → Equiv.Perm Q) (accept : Q) (x : A) (y : B) :
    suffix y (startState x) = accept ↔ startState x = (suffix y).symm accept := by
  constructor
  · intro h
    exact (suffix y).injective (h.trans ((suffix y).apply_symm_apply accept).symm)
  · intro h
    rw [h, Equiv.apply_symm_apply]

/-- A single accepting state after permutational suffix transitions yields the squared
cover bound for input orders that separate the two sets of variables. -/
theorem singleton_cut_cover_sq_le {r : ℕ} {Q : Type*} [Fintype Q]
    (startState : Word r → Q) (suffix : Word r → Equiv.Perm Q) (accept : Q)
    (safe : ∀ x y, suffix y (startState x) = accept → DisjointPair x y) :
    (Nat.card {p : Word r × Word r // suffix p.2 (startState p.1) = accept})^2 ≤ 8^r := by
  have h := cut_cover_sq_le startState (fun y => (suffix y).symm accept)
    (fun x y hxy => safe x y ((singleton_accept_iff startState suffix accept x y).mpr hxy))
  convert h using 2
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun p => singleton_accept_iff startState suffix accept p.1 p.2


end PvsNP.SingletonCutAux

theorem solution {r : ℕ} {Q : Type*} [Fintype Q]
    (startState : (Fin r → Bool) → Q)
    (suffix : (Fin r → Bool) → Equiv.Perm Q) (accept : Q)
    (safe : ∀ x y, suffix y (startState x) = accept →
      ∀ i, ¬ (x i = true ∧ y i = true)) :
    (Nat.card {p : (Fin r → Bool) × (Fin r → Bool) //
      suffix p.2 (startState p.1) = accept}) ^ 2 ≤ 8 ^ r :=
  PvsNP.SingletonCutAux.singleton_cut_cover_sq_le startState suffix accept safe

