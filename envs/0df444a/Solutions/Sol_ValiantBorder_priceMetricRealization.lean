-- Prove2me | solution 1 for ValiantBorder.priceMetricRealization
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:08:35.044223+00:00
-- url     : https://prove2.me/submissions/44795038-bbb3-42b8-a43d-46b5fe3b3cd0

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_priceMidpointCN

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, sections “Tensors”,
“The metrics of the spectral points” and “Flat or contracting”, and Appendix N. Source:
`anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/`, Apache-2.0. -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Restrictions and sums of restrictions: the basic calculus

Paper: the subsection "Tensors". `Restr s t` says that s is a restriction of t, and `SumRestr s b` that s
is covered by the b k. Restriction is reflexive and
transitive and compatible with products, powers, products of families and `push` (giving legs to
parties); sums of restrictions can be substituted in one another and multiplied, and are compatible
with the same operations.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Values of the constructions -/

@[simp] theorem one_val (x : ∀ p, (1 : Ten K I).ι p) : (1 : Ten K I).val x = 1 := rfl

theorem mul_val (s t : Ten K I) (x : ∀ p, (s * t).ι p) :
    (s * t).val x = s.val (fun p => (x p).1) * t.val (fun p => (x p).2) := rfl

theorem prod_val {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I)
    (x : ∀ p, (prod b).ι p) : (prod b).val x = ∏ k, (b k).val (fun p => x p k) := rfl

theorem push_val (π : J → I) (t : Ten K J) (x : ∀ q, (push π t).ι q) :
    (push π t).val x = t.val (fun j => x (π j) ⟨j, rfl⟩) := rfl

theorem unit_val (r : ℕ) (x : J → Fin r) :
    (unit K J r).val x = if ∀ i j, x i = x j then 1 else 0 := rfl

/-- The k-th power is the product of k equal tensors. -/
theorem kpow_eq_prod (t : Ten K I) (k : ℕ) : kpow t k = prod (fun _ : Fin k => t) := rfl

/-- The same legs with another array. -/
def withVal (t : Ten K I) (v : (∀ p, t.ι p) → K) : Ten K I where
  ι := t.ι
  val := v

@[simp] theorem withVal_val (t : Ten K I) (v : (∀ p, t.ι p) → K) : (t.withVal v).val = v := rfl

/-! ### Local maps applied to arrays -/

/-- Local maps L applied to an array f; this is `app` for plain index sets in the place of the legs of
tensors. -/
def appG {α β : I → Type} [∀ p, Fintype (β p)] (L : ∀ p, α p → β p → K)
    (f : (∀ p, β p) → K) (x : ∀ p, α p) : K :=
  ∑ y, (∏ p, L p (x p) (y p)) * f y

theorem app_eq_appG {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : app L x = appG L t.val x := rfl

/-- Local maps compose. -/
theorem appG_comp {α β γ : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (γ p)]
    (L : ∀ p, α p → β p → K) (M : ∀ p, β p → γ p → K) (f : (∀ p, γ p) → K) (x : ∀ p, α p) :
    appG L (appG M f) x = appG (fun p a c => ∑ b, L p a b * M p b c) f x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- Local maps applied to a sum. -/
theorem appG_sum {α β : I → Type} [∀ p, Fintype (β p)] {κ : Type} [Fintype κ]
    (L : ∀ p, α p → β p → K) (f : κ → (∀ p, β p) → K) (x : ∀ p, α p) :
    appG L (fun y => ∑ k, f k y) x = ∑ k, appG L (f k) x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Local maps applied to a product of two arrays. -/
theorem appG_mul {α β α' β' : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (β' p)]
    (L : ∀ p, α p → β p → K) (L' : ∀ p, α' p → β' p → K)
    (f : (∀ p, β p) → K) (g : (∀ p, β' p) → K) (x : ∀ p, α p × α' p) :
    appG (β := fun p => β p × β' p) (fun p a b => L p a.1 b.1 * L' p a.2 b.2)
      (fun y => f (fun p => (y p).1) * g (fun p => (y p).2)) x =
    appG L f (fun p => (x p).1) * appG L' g (fun p => (x p).2) := by
  simp only [appG]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ⟨fun y => (fun p => (y p).1, fun p => (y p).2), fun z p => (z.1 p, z.2 p),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun y => ?_
  simp only [Equiv.coe_fn_mk, Finset.prod_mul_distrib]
  ring

/-- Local maps applied to a product of a family of arrays. -/
theorem appG_prod {κ : Type} [Fintype κ] [DecidableEq κ] {α β : κ → I → Type}
    [∀ k p, Fintype (β k p)] (L : ∀ k p, α k p → β k p → K) (f : ∀ k, (∀ p, β k p) → K)
    (x : ∀ p k, α k p) :
    appG (β := fun p => ∀ k, β k p) (fun p a b => ∏ k, L k p (a k) (b k))
      (fun y => ∏ k, f k (fun p => y p k)) x =
    ∏ k, appG (L k) (f k) (fun p => x p k) := by
  simp only [appG]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun y => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

/-- The index tuples of the legs sorted by their parties correspond to the index tuples of all
legs. -/
def pushEquiv (π : J → I) (β : J → Type) :
    (∀ q, ∀ j : {j : J // π j = q}, β j.1) ≃ (∀ j, β j) where
  toFun y j := y (π j) ⟨j, rfl⟩
  invFun z _ j := z j.1
  left_inv y := by
    funext q j
    obtain ⟨j, rfl⟩ := j
    rfl
  right_inv _ := rfl

/-- Local maps applied to an array whose legs are sorted by parties. -/
theorem appG_push (π : J → I) {α β : J → Type} [∀ j, Fintype (β j)]
    (L : ∀ j, α j → β j → K) (f : (∀ j, β j) → K) (x : ∀ q, ∀ j : {j : J // π j = q}, α j.1) :
    appG (β := fun q => ∀ j : {j : J // π j = q}, β j.1)
      (fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j))
      (fun y => f (fun j => y (π j) ⟨j, rfl⟩)) x =
    appG L f (fun j => x (π j) ⟨j, rfl⟩) := by
  simp only [appG]
  refine Fintype.sum_equiv (pushEquiv π β) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise π]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨j, rfl⟩ := j
  rfl

/-- Local maps whose matrices have at most one entry that is not 0 in each row: the row a of the
matrix of p has the entry w p a in the column g p a. -/
theorem appG_map {α β : I → Type} [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)]
    (w : ∀ p, α p → K) (g : ∀ p, α p → β p) (f : (∀ p, β p) → K) (x : ∀ p, α p) :
    appG (fun p a b => if b = g p a then w p a else 0) f x =
      (∏ p, w p (x p)) * f (fun p => g p (x p)) := by
  unfold appG
  rw [Finset.sum_eq_single (fun p => g p (x p))]
  · simp
  · intro y _ hy
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
    rw [Finset.prod_eq_zero (Finset.mem_univ p), zero_mul]
    exact if_neg hp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Restrictions -/

/-- A tensor is a restriction of itself. -/
theorem Restr.refl (t : Ten K I) : Restr t t :=
  ⟨fun _ a b => if b = a then 1 else 0, fun x => by
    rw [app_eq_appG]
    exact ((appG_map (fun p _ => (1 : K)) (fun p a => a) t.val x).trans (by simp)).symm⟩

/-- A restriction of a restriction is a restriction. -/
theorem Restr.trans {s t u : Ten K I} (h : Restr s t) (h' : Restr t u) : Restr s u := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a c => ∑ b, L p a b * M p b c, fun x => ?_⟩
  rw [hL, app_eq_appG, app_eq_appG, ← appG_comp]
  congr 1
  funext y
  exact hM y

/-- Products of restrictions. -/
theorem Restr.mul {s t s' t' : Ten K I} (h : Restr s s') (h' : Restr t t') :
    Restr (s * t) (s' * t') := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a b => L p a.1 b.1 * M p a.2 b.2, fun x => ?_⟩
  rw [mul_val, hL, hM]
  exact (appG_mul L M s'.val t'.val x).symm

/-- Products of a family of restrictions. -/
theorem Restr.prod {κ : Type} [Fintype κ] [DecidableEq κ] {a b : κ → Ten K I}
    (h : ∀ k, Restr (a k) (b k)) : Restr (Ten.prod a) (Ten.prod b) := by
  choose L hL using h
  refine ⟨fun p x y => ∏ k, L k p (x k) (y k), fun x => ?_⟩
  rw [prod_val]
  exact (Finset.prod_congr rfl fun k _ => hL k _).trans
    (appG_prod (α := fun k p => (a k).ι p) (β := fun k p => (b k).ι p) L
      (fun k => (b k).val) x).symm

/-- Restrictions stay restrictions if the legs are given to other parties. -/
theorem Restr.push (π : J → I) {s t : Ten K J} (h : Restr s t) :
    Restr (push π s) (push π t) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j), fun x => ?_⟩
  rw [push_val, hL]
  exact (appG_push π L t.val x).symm

/-- If the entry of s at x is a product of local factors times the entry of t at g(x), where g acts
leg by leg, then s is a restriction of t. -/
theorem Restr.of_map {s t : Ten K I} (w : ∀ p, s.ι p → K) (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = (∏ p, w p (x p)) * t.val (fun p => g p (x p))) : Restr s t :=
  ⟨fun p a b => if b = g p a then w p a else 0, fun x => by
    rw [h, app_eq_appG]; exact (appG_map w g t.val x).symm⟩

/-- If the entry of s at x is the entry of t at g(x), where g acts leg by leg, then s is a
restriction of t. -/
theorem Restr.of_map' {s t : Ten K I} (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => g p (x p))) : Restr s t :=
  Restr.of_map (fun _ _ => 1) g (by simpa using h)

/-- 1 is a restriction of every tensor with an entry that is not 0, if there is a party. -/
theorem Restr.one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) :
    Restr 1 t := by
  classical
  let p₀ : I := Classical.arbitrary I
  refine Restr.of_map (fun p _ => if p = p₀ then (t.val y)⁻¹ else 1) (fun p _ => y p) fun x => ?_
  rw [Finset.prod_ite_eq' Finset.univ p₀]
  simp [h]

/-! ### Sums of restrictions -/

section Sum

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

/-- s is a sum of restrictions of the b k if and only if its array is a sum of arrays, the k-th
of which is a restriction of b k. -/
theorem sumRestr_iff {s : Ten K I} {b : κ → Ten K I} :
    SumRestr s b ↔ ∃ v : κ → (∀ p, s.ι p) → K,
      (∀ x, s.val x = ∑ k, v k x) ∧ ∀ k, Restr (s.withVal (v k)) (b k) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun k x => appG (L k) (b k).val x, hL, fun k => ⟨L k, fun x => rfl⟩⟩
  · rintro ⟨v, hv, h⟩
    choose L hL using h
    exact ⟨L, fun x => (hv x).trans (Finset.sum_congr rfl fun k _ => hL k x)⟩

/-- If the array of s is the sum of the arrays v k, then s is a sum of restrictions of the tensors
with these arrays. -/
theorem SumRestr.of_withVal (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : SumRestr s (fun k => s.withVal (v k)) :=
  sumRestr_iff.2 ⟨v, h, fun _ => Restr.refl _⟩

/-- A restriction is a sum of restrictions with one term. -/
theorem Restr.sumRestr {s t : Ten K I} (h : Restr s t) : SumRestr s (fun _ : Unit => t) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun _ => L, fun x => by simpa using hL x⟩

/-- A tensor whose array is 0 is a sum of restrictions of the empty family. -/
theorem SumRestr.of_zero [IsEmpty κ] {s : Ten K I} (h : ∀ x, s.val x = 0) (b : κ → Ten K I) :
    SumRestr s b :=
  ⟨fun k => isEmptyElim k, fun x => by simp [h]⟩

/-- A sum of restrictions of tensors that are themselves sums of restrictions is a sum of restrictions
(covers are transitive). -/
theorem SumRestr.bind {μ : κ → Type} [∀ k, Fintype (μ k)] {s : Ten K I} {b : κ → Ten K I}
    {c : ∀ k, μ k → Ten K I} (h : SumRestr s b) (h' : ∀ k, SumRestr (b k) (c k)) :
    SumRestr s (fun x : Σ k, μ k => c x.1 x.2) := by
  obtain ⟨L, hL⟩ := h
  choose M hM using h'
  refine ⟨fun x p a d => ∑ b, L x.1 p a b * M x.1 x.2 p b d, fun x => ?_⟩
  rw [hL, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (b k).val = fun y => ∑ m, appG (M k m) (c k m).val y := funext fun y => hM k y
  rw [app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- A restriction of a sum of restrictions is a sum of restrictions of the same tensors. -/
theorem Restr.trans_sum {s t : Ten K I} {b : κ → Ten K I} (h : Restr s t) (h' : SumRestr t b) :
    SumRestr s b := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p a d => ∑ b, L p a b * M k p b d, fun x => ?_⟩
  have e : t.val = fun y => ∑ k, appG (M k) (b k).val y := funext fun y => hM y
  rw [hL, app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- In a sum of restrictions every term may be replaced by a tensor of which it is a restriction. -/
theorem SumRestr.mono {s : Ten K I} {b c : κ → Ten K I} (h : SumRestr s b)
    (h' : ∀ k, Restr (b k) (c k)) : SumRestr s c := by
  obtain ⟨v, hv, h⟩ := sumRestr_iff.1 h
  exact sumRestr_iff.2 ⟨v, hv, fun k => (h k).trans (h' k)⟩

/-- The terms of a sum of restrictions may be renamed. -/
theorem SumRestr.reindex {s : Ten K I} {b : κ → Ten K I} (h : SumRestr s b) (e : κ' ≃ κ) :
    SumRestr s (fun k => b (e k)) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun k => L (e k), fun x => (hL x).trans (Fintype.sum_equiv e _ _ fun _ => rfl).symm⟩

/-- The product of two sums of restrictions is a sum of restrictions of the products of two terms. -/
theorem SumRestr.mul {s t : Ten K I} {b : κ → Ten K I} {c : κ' → Ten K I} (h : SumRestr s b)
    (h' : SumRestr t c) : SumRestr (s * t) (fun k : κ × κ' => b k.1 * c k.2) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p x y => L k.1 p x.1 y.1 * M k.2 p x.2 y.2, fun x => ?_⟩
  rw [mul_val, hL, hM, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Finset.sum_congr rfl fun k _ => (appG_mul (L k.1) (M k.2) (b k.1).val (c k.2).val x).symm

/-- A sum of restrictions stays one if the legs are given to other parties. -/
theorem SumRestr.push (π : J → I) {s : Ten K J} {b : κ → Ten K J} (h : SumRestr s b) :
    SumRestr (push π s) (fun k => Ten.push π (b k)) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k q x y => ∏ j : {j : J // π j = q}, L k j.1 (x j) (y j), fun x => ?_⟩
  rw [push_val, hL]
  exact Finset.sum_congr rfl fun k _ => (appG_push π (L k) (b k).val x).symm

end Sum

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Equivalence of tensors

The paper identifies tensors that are restrictions of one another (in the subsection "Tensors"). Here they are called equivalent, `Equi`, and this file has the laws of products,
powers, products of families and `push` (giving legs to parties) up to equivalence.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every tensor is equivalent to itself. -/
theorem Equi.refl (t : Ten K I) : Equi t t := ⟨Restr.refl t, Restr.refl t⟩

/-- Equivalence is symmetric. -/
theorem Equi.symm {s t : Ten K I} (h : Equi s t) : Equi t s := ⟨h.2, h.1⟩

/-- Equivalence is transitive. -/
theorem Equi.trans {s t u : Ten K I} (h : Equi s t) (h' : Equi t u) : Equi s u :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Products of equivalent tensors are equivalent. -/
theorem Equi.mul {s t s' t' : Ten K I} (h : Equi s s') (h' : Equi t t') :
    Equi (s * t) (s' * t') := ⟨h.1.mul h'.1, h.2.mul h'.2⟩

/-- Giving the legs of equivalent tensors to parties. -/
theorem Equi.push (π : J → I) {s t : Ten K J} (h : Equi s t) :
    Equi (push π s) (push π t) := ⟨h.1.push π, h.2.push π⟩

/-- Tensors whose index sets correspond to one another, leg by leg, with equal entries are
equivalent. -/
theorem Equi.of_equiv {s t : Ten K I} (e : ∀ p, s.ι p ≃ t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => e p (x p))) : Equi s t :=
  ⟨Restr.of_map' (fun p => e p) h, Restr.of_map' (fun p => (e p).symm) fun y => by
    rw [h]; simp⟩

/-! ### Products -/

/-- The product is commutative. -/
theorem Equi.mul_comm (s t : Ten K I) : Equi (s * t) (t * s) :=
  Equi.of_equiv (fun _ => Equiv.prodComm _ _) fun _ => _root_.mul_comm _ _

/-- The product is associative. -/
theorem Equi.mul_assoc (s t u : Ten K I) : Equi (s * t * u) (s * (t * u)) :=
  Equi.of_equiv (fun _ => Equiv.prodAssoc _ _ _) fun _ => _root_.mul_assoc _ _ _

/-- 1 is neutral. -/
theorem Equi.one_mul (t : Ten K I) : Equi (1 * t) t :=
  Equi.of_equiv (fun p => Equiv.punitProd (t.ι p)) fun _ => _root_.one_mul _

/-- 1 is neutral. -/
theorem Equi.mul_one (t : Ten K I) : Equi (t * 1) t :=
  Equi.of_equiv (fun p => Equiv.prodPUnit (t.ι p)) fun _ => _root_.mul_one _

section Prod

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Renaming the factors of a product. -/
theorem Equi.prod_reindex (b : κ → Ten K I) (e : κ' ≃ κ) :
    Equi (Ten.prod b) (Ten.prod fun k => b (e k)) :=
  Equi.symm <| Equi.of_equiv (fun p => Equiv.piCongrLeft (fun k => (b k).ι p) e) fun x => by
    rw [prod_val, prod_val]
    refine Fintype.prod_equiv e _ _ fun k => ?_
    congr 1
    funext p
    exact (Equiv.piCongrLeft_apply_apply (fun k => (b k).ι p) e (x p) k).symm

/-- The product of the empty family. -/
theorem Equi.prod_empty [IsEmpty κ] (b : κ → Ten K I) : Equi (Ten.prod b) 1 :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ Unit from Equiv.equivPUnit _)
    fun x => by rw [prod_val]; simp

/-- The product of a family with one member. -/
theorem Equi.prod_unique [Unique κ] (b : κ → Ten K I) : Equi (Ten.prod b) (b default) :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ (b default).ι p from Equiv.piUnique _)
    fun x => by rw [prod_val]; simp; rfl

/-- The product over a disjoint union. -/
theorem Equi.prod_sum (b : κ ⊕ κ' → Ten K I) :
    Equi (Ten.prod b) (Ten.prod (fun k => b (Sum.inl k)) * Ten.prod (fun k => b (Sum.inr k))) :=
  Equi.of_equiv (fun p => Equiv.sumPiEquivProdPi fun k => (b k).ι p)
    fun x => by rw [prod_val, Fintype.prod_sum_type]; rfl

end Prod

/-- The product of a family indexed by 0, …, n is its first member times the product of the others. -/
theorem Equi.prod_fin_succ {n : ℕ} (b : Fin (n + 1) → Ten K I) :
    Equi (Ten.prod b) (b 0 * Ten.prod fun k : Fin n => b k.succ) :=
  Equi.of_equiv (fun p => (Fin.consEquiv fun k => (b k).ι p).symm)
    fun x => by rw [prod_val, Fin.prod_univ_succ]; rfl

/-- The product of a family of two tensors. -/
theorem Equi.prod_fin_two (b : Fin 2 → Ten K I) : Equi (Ten.prod b) (b 0 * b 1) :=
  (Equi.prod_fin_succ b).trans ((Equi.refl _).mul (Equi.prod_unique _))

/-! ### Powers -/

/-- The power with exponent 0. -/
theorem Equi.kpow_zero (t : Ten K I) : Equi (Ten.kpow t 0) 1 :=
  Equi.prod_empty (fun _ : Fin 0 => t)

/-- The power with exponent k + 1. -/
theorem Equi.kpow_succ (t : Ten K I) (k : ℕ) : Equi (Ten.kpow t (k + 1)) (t * Ten.kpow t k) :=
  Equi.prod_fin_succ (fun _ : Fin (k + 1) => t)

/-! ### Giving legs to parties -/

section Push

variable {L : Type} [Fintype L] [DecidableEq L]

/-- Giving each leg to the party of its own name changes nothing, up to equivalence. -/
theorem Equi.push_id (t : Ten K I) : Equi (Ten.push id t) t :=
  Equi.of_equiv
    (fun q => ⟨fun y => y ⟨q, rfl⟩, fun a j => (show q = j.1 from j.2.symm) ▸ a, fun y => by
        funext j; obtain ⟨j, hj⟩ := j; cases hj; rfl, fun a => rfl⟩)
    fun x => rfl

/-- Giving legs away twice. -/
theorem Equi.push_push (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y i => y ⟨ρ i.1, i.2⟩ ⟨i.1, rfl⟩, fun z j i => z ⟨i.1, by
        rw [Function.comp, i.2]; exact j.2⟩, fun y => by
        funext j i
        obtain ⟨j, hj⟩ := j
        obtain ⟨i, hi⟩ := i
        cases hj
        cases hi
        rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for a product. -/
theorem Equi.push_mul (π : J → I) (s t : Ten K J) :
    Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.of_equiv
    (fun _ => ⟨fun y => (fun j => (y j).1, fun j => (y j).2), fun z j => (z.1 j, z.2 j),
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for 1. -/
theorem Equi.push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 :=
  Equi.of_equiv
    (fun q => show (({j : J // π j = q}) → Unit) ≃ Unit from Equiv.equivPUnit _) fun _ => rfl

/-- Giving legs away, for the product of a family. -/
theorem Equi.push_prod {κ : Type} [Fintype κ] [DecidableEq κ] (π : J → I) (b : κ → Ten K J) :
    Equi (Ten.push π (Ten.prod b)) (Ten.prod fun k => Ten.push π (b k)) :=
  Equi.of_equiv (fun _ => Equiv.piComm _) fun _ => rfl

/-- Giving legs away, for a power. -/
theorem Equi.push_kpow (π : J → I) (t : Ten K J) (k : ℕ) :
    Equi (Ten.push π (Ten.kpow t k)) (Ten.kpow (Ten.push π t) k) :=
  Equi.push_prod π (fun _ : Fin k => t)

end Push

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Spectral points: the basic calculus

Paper: the subsection "Tensors". A spectral point F is multiplicative and
monotone for restriction, F(s) ≤ F(t_1) + … + F(t_m) if s = t_1 + … + t_m, and 1 ≤ F(t) ≤ rank of t for
a tensor t that is not 0. A spectral point can be pulled back along a map g of sets of parties (the
paper's t ↦ φ(gt)).
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Rank, in coordinates: a tensor has rank at most r if and only if it is a sum of r products of
vectors. -/
theorem rankLE_iff [Nonempty I] {t : Ten K I} {r : ℕ} :
    RankLE t r ↔ ∃ u : Fin r → ∀ p, t.ι p → K, ∀ x, t.val x = ∑ s, ∏ p, u s p (x p) := by
  have key : ∀ (L : ∀ p, t.ι p → Fin r → K) (x : ∀ p, t.ι p),
      (∑ y : I → Fin r, (∏ p, L p (x p) (y p)) * (if ∀ i j, y i = y j then 1 else 0)) =
        ∑ s, ∏ p, L p (x p) s := by
    intro L x
    let p₀ : I := Classical.arbitrary I
    symm
    refine Finset.sum_of_injOn (fun s _ => s) (fun a _ b _ h => congr_fun h p₀) (fun _ _ => by simp)
      (fun y _ hy => ?_) (fun s _ => by simp)
    rw [if_neg, mul_zero]
    intro h
    exact hy ⟨y p₀, by simp, funext fun p => h p₀ p⟩
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun s p a => L p a s, fun x => (hL x).trans (key L x)⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun p a s => u s p a, fun x => (hu x).trans (key (fun p a s => u s p a) x).symm⟩

/-- A tensor of rank at most r is a sum of r restrictions of 1. -/
theorem RankLE.sumRestr [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) :
    SumRestr t (fun _ : Fin r => (1 : Ten K I)) := by
  obtain ⟨u, hu⟩ := rankLE_iff.1 h
  refine sumRestr_iff.2 ⟨fun s x => ∏ p, u s p (x p), hu, fun s => ?_⟩
  exact Restr.of_map (fun p a => u s p a) (fun _ _ => ()) fun x => (mul_one _).symm

/-- Every tensor has a rank bound: the number of its entries. -/
theorem rankLE_card [Nonempty I] (t : Ten K I) : RankLE t (Fintype.card (∀ p, t.ι p)) := by
  classical
  let p₀ : I := Classical.arbitrary I
  let e := (Fintype.equivFin (∀ p, t.ι p)).symm
  refine rankLE_iff.2 ⟨fun s p a => if a = e s p then (if p = p₀ then t.val (e s) else 1) else 0,
    fun x => ?_⟩
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro s _ hs
    have : x ≠ e s := fun h => hs (by rw [h]; simp)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 this
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
  · simp

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F is monotone for restriction. -/
theorem mono {s t : Ten K I} (h : Restr s t) : F.F s ≤ F.F t := by
  simpa using F.le_sum s _ h.sumRestr

/-- Equivalent tensors have the same price. -/
theorem congr {s t : Ten K I} (h : Equi s t) : F.F s = F.F t :=
  le_antisymm (F.mono h.1) (F.mono h.2)

/-- F of the product of a family indexed by 0, …, n-1. -/
theorem prod_fin {n : ℕ} (b : Fin n → Ten K I) : F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  induction n with
  | zero => rw [F.congr (Equi.prod_empty b), F.one]; simp
  | succ n ih => rw [F.congr (Equi.prod_fin_succ b), F.mul, ih, Fin.prod_univ_succ]

/-- F of the product of a family. -/
theorem prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  rw [F.congr (Equi.prod_reindex b (Fintype.equivFin κ).symm), F.prod_fin]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- F of a power. -/
theorem kpow (t : Ten K I) (k : ℕ) : F.F (Ten.kpow t k) = F.F t ^ k := by
  rw [kpow_eq_prod, F.prod]; simp

/-- F is 0 at a tensor whose array is 0. -/
theorem zero {t : Ten K I} (h : ∀ x, t.val x = 0) : F.F t = 0 := by
  refine le_antisymm ?_ (F.nonneg t)
  simpa using F.le_sum t (fun k : Empty => k.elim) (SumRestr.of_zero h _)

/-- F is at least 1 at a tensor with an entry that is not 0. -/
theorem one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) : 1 ≤ F.F t := by
  rw [← F.one]
  exact F.mono (Restr.one_le h)

/-- F is at most the rank. -/
theorem le_rank [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) : F.F t ≤ r := by
  simpa [F.one] using F.le_sum t _ h.sumRestr

/-- F is at most the number of entries. -/
theorem le_card [Nonempty I] (t : Ten K I) : F.F t ≤ Fintype.card (∀ p, t.ι p) :=
  F.le_rank (rankLE_card t)

/-- F is subadditive for sums of arrays. -/
theorem le_sum_val {κ : Type} [Fintype κ] (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : F.F s ≤ ∑ k, F.F (s.withVal (v k)) :=
  F.le_sum s _ (SumRestr.of_withVal s v h)

/-- A restriction of a product costs at most the product of the prices. -/
theorem le_mul {s t u : Ten K I} (h : Restr s (t * u)) : F.F s ≤ F.F t * F.F u := by
  rw [← F.mul]; exact F.mono h

/-- A restriction of the product of a family costs at most the product of the prices. -/
theorem le_prod {κ : Type} [Fintype κ] [DecidableEq κ] {s : Ten K I} {b : κ → Ten K I}
    (h : Restr s (Ten.prod b)) : F.F s ≤ ∏ k, F.F (b k) := by
  rw [← F.prod]; exact F.mono h

/-- The pull-back of a spectral point along a map π of parties: a tensor over J costs what it costs
if the leg j is held by π j. -/
def pull (F : Spec K I) (π : J → I) : Spec K J where
  F t := F.F (Ten.push π t)
  nonneg _ := F.nonneg _
  one := by rw [F.congr (Equi.push_one π), F.one]
  mul s t := by rw [F.congr (Equi.push_mul π s t), F.mul]
  le_sum s b h := F.le_sum _ _ (h.push π)

@[simp] theorem pull_F (π : J → I) (t : Ten K J) : (F.pull π).F t = F.F (Ten.push π t) := rfl

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Networks

A tensor that is the value of a network is a restriction of the product of the wires on the edges of the
network, wherever its vertices are placed. The paper uses special cases: in Lemma lem:exponents, that ⟨q⟩_uw
is a restriction of ⟨q⟩_uv ⟨q⟩_vw, and the same for trees; and Lemma lem:hubs. The statements are about
functions, not graphs: a vertex v has a table T v, a function of all labels, which is *local*: it depends
only on the labels of the edges at v and on the indices held by the party of v.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Contraction with one tensor. The legs of t are at vertices (the leg l at ρ l), every vertex v is
placed at the party ξ v and has a local table T v: it depends only on the legs of s that are held by
the party ξ v and on the legs of t at v. If s is the sum over all labels of the legs of t of the
product of the tables and of t, then s is a restriction of t, with the legs at their places. -/
theorem Restr.of_contract {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (ξ : V → I)
    (ρ : L → V) (s : Ten K J) (t : Ten K L) (T : V → (∀ j, s.ι j) → (∀ l, t.ι l) → K)
    (hT : ∀ v x x' y y', (∀ j, π j = ξ v → x j = x' j) → (∀ l, ρ l = v → y l = y' l) →
      T v x y = T v x' y')
    (h : ∀ x, s.val x = ∑ y, (∏ v, T v x y) * t.val y) :
    Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ l)) t) := by
  classical
  rcases isEmpty_or_nonempty (∀ j, s.ι j) with hs | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ _ _ => 0, fun x => (hs.false fun j => x (π j) ⟨j, rfl⟩).elim⟩
  rcases isEmpty_or_nonempty (∀ l, t.ι l) with ht | ⟨⟨y₀⟩⟩
  · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
    rw [push_val, h, Finset.univ_eq_empty, Finset.sum_empty]
    have : IsEmpty (∀ q, (Ten.push (fun l => ξ (ρ l)) t).ι q) :=
      ⟨fun y => ht.false fun l => y (ξ (ρ l)) ⟨l, rfl⟩⟩
    rw [app, Finset.univ_eq_empty, Finset.sum_empty]
  let ex : ∀ q, (∀ j : {j : J // π j = q}, s.ι j.1) → ∀ j, s.ι j :=
    fun q a j => if hj : π j = q then a ⟨j, hj⟩ else x₀ j
  let ey : ∀ q, (∀ l : {l : L // ξ (ρ l) = q}, t.ι l.1) → ∀ l, t.ι l :=
    fun q b l => if hl : ξ (ρ l) = q then b ⟨l, hl⟩ else y₀ l
  refine ⟨fun q a b => ∏ v : {v : V // ξ v = q}, T v.1 (ex q a) (ey q b), fun x => ?_⟩
  rw [push_val, h, app_eq_appG, appG]
  symm
  refine Fintype.sum_equiv (pushEquiv (fun l => ξ (ρ l)) t.ι) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise ξ]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨v, rfl⟩ := v
  refine hT v _ _ _ _ (fun j hj => ?_) (fun l hl => ?_)
  · have : ex (ξ v) (x (ξ v)) j = x (ξ v) ⟨j, hj⟩ := dif_pos hj
    rw [this]
    clear this
    revert hj
    generalize ξ v = q
    rintro rfl
    rfl
  · subst hl
    exact dif_pos rfl

section Outer

variable {κ : Type} [Fintype κ] [DecidableEq κ] {M : κ → Type} [∀ k, Fintype (M k)]
  [∀ k, DecidableEq (M k)]

/-- The product of tensors with separate legs. -/
def outer (t : ∀ k, Ten K (M k)) : Ten K (Σ k, M k) where
  ι l := (t l.1).ι l.2
  val y := ∏ k, (t k).val fun m => y ⟨k, m⟩

theorem outer_val (t : ∀ k, Ten K (M k)) (y : ∀ l, (outer t).ι l) :
    (outer t).val y = ∏ k, (t k).val fun m => y ⟨k, m⟩ := rfl

/-- Giving the legs of a product with separate legs to parties. -/
theorem Equi.push_outer (π : (Σ k, M k) → I) (t : ∀ k, Ten K (M k)) :
    Equi (Ten.push π (outer t)) (Ten.prod fun k => Ten.push (fun m => π ⟨k, m⟩) (t k)) :=
  Equi.of_equiv
    (fun _ => ⟨fun y k j => y ⟨⟨k, j.1⟩, j.2⟩, fun z l => z l.1.1 ⟨l.1.2, l.2⟩,
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

end Outer

section Two

variable {L L' : Type} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- The product of two tensors with separate legs. -/
def outer₂ (s : Ten K L) (t : Ten K L') : Ten K (L ⊕ L') where
  ι l := Sum.elim s.ι t.ι l
  fin l := match l with
    | Sum.inl l => s.fin l
    | Sum.inr l => t.fin l
  dec l := match l with
    | Sum.inl l => s.dec l
    | Sum.inr l => t.dec l
  val y := s.val (fun l => y (Sum.inl l)) * t.val (fun l => y (Sum.inr l))

/-- Giving the legs of a product of two tensors with separate legs to parties. -/
theorem Equi.push_outer₂ (π : L ⊕ L' → I) (s : Ten K L) (t : Ten K L') :
    Equi (Ten.push π (outer₂ s t))
      (Ten.push (fun l => π (Sum.inl l)) s * Ten.push (fun l => π (Sum.inr l)) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y => (fun l => y ⟨Sum.inl l.1, l.2⟩, fun l => y ⟨Sum.inr l.1, l.2⟩),
      fun z l => match l with
        | ⟨Sum.inl l, h⟩ => z.1 ⟨l, h⟩
        | ⟨Sum.inr l, h⟩ => z.2 ⟨l, h⟩,
      fun y => by funext l; obtain ⟨l | l, h⟩ := l <;> rfl, fun z => rfl⟩)
    fun _ => rfl

end Two

/-- A sum over pairs of labels that must be equal. -/
theorem sum_unit_two {E : Type} [Fintype E] [DecidableEq E] (n : E → ℕ)
    (g : (∀ e, Fin 2 → Fin (n e)) → K) :
    ∑ z : ∀ e, Fin 2 → Fin (n e), g z * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
      ∑ l : ∀ e, Fin (n e), g fun e _ => l e := by
  symm
  refine Finset.sum_of_injOn (fun l e _ => l e) (fun l _ l' _ h => ?_) (fun _ _ => by simp)
    (fun z _ hz => ?_) (fun l _ => ?_)
  · funext e
    exact congr_fun (congr_fun h e) 0
  · have : ∃ e, ¬ ∀ i j, z e i = z e j := by
      by_contra hcon
      push Not at hcon
      exact hz ⟨fun e => z e 0, by simp, funext fun e => funext fun i => hcon e 0 i⟩
    obtain ⟨e, he⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ e), mul_zero]
    exact if_neg he
  · rw [Finset.prod_eq_one, mul_one]
    intro e _
    exact if_pos fun _ _ => rfl

/-- **Networks.** The vertices v are placed at the parties ξ v, the legs j of s are held
by the parties π j. There are edges e with labels in Λ e and ends a e, b e, and tensors t k with
their legs m at the vertices ρ k m. Each vertex has a local table T v: it depends only on the legs of
s held by the party ξ v, on the labels of the edges at v, and on the legs of the t k at v. If s is
the sum over all labels of the product of the tables and of the t k, then s is a restriction of the
product of the edges and of the t k, all at their places. -/
theorem Restr.of_network {E κ : Type} [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ]
    {M : κ → Type} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (t : ∀ k, Ten K (M k)) (ρ : ∀ k, M k → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → (∀ k m, (t k).ι m) → K)
    (hT : ∀ v x x' l l' y y', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → (∀ k m, ρ k m = v → y k m = y' k m) →
      T v x l y = T v x' l' y')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∑ y : ∀ k m, (t k).ι m,
      (∏ v, T v x l y) * ∏ k, (t k).val (y k)) :
    Restr (Ten.push π s)
      (Ten.prod (fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) *
        Ten.prod (fun k => Ten.push (fun m => ξ (ρ k m)) (t k))) := by
  classical
  let n : E → ℕ := fun e => Fintype.card (Λ e)
  let eq : ∀ e, Fin (n e) ≃ Λ e := fun e => (Fintype.equivFin (Λ e)).symm
  let U : Ten K (Σ _ : E, Fin 2) := outer fun e => unit K (Fin 2) (n e)
  let ρ' : (Σ _ : E, Fin 2) ⊕ (Σ k, M k) → V :=
    Sum.elim (fun l => ![a l.1, b l.1] l.2) (fun l => ρ l.1 l.2)
  let T' : V → (∀ j, s.ι j) → (∀ l, (outer₂ U (outer t)).ι l) → K := fun v x y =>
    T v x (fun e => eq e (if a e = v then y (Sum.inl ⟨e, 0⟩) else y (Sum.inl ⟨e, 1⟩)))
      (fun k m => y (Sum.inr ⟨k, m⟩))
  have key : Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ' l)) (outer₂ U (outer t))) := by
    refine Restr.of_contract π ξ ρ' s (outer₂ U (outer t)) T' (fun v x x' y y' hx hy => ?_)
      fun x => ?_
    · refine hT v _ _ _ _ _ _ hx (fun e he => ?_) fun k m hm => hy (Sum.inr ⟨k, m⟩) hm
      by_cases ha : a e = v
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 0⟩) ha)
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 1⟩) (he.resolve_left ha))
    · rw [h]
      let Φ : (∀ l, (outer₂ U (outer t)).ι l) ≃
          (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m) :=
        ⟨fun y => (fun e i => y (Sum.inl ⟨e, i⟩), fun k m => y (Sum.inr ⟨k, m⟩)),
          fun z l => match l with
            | Sum.inl l => z.1 l.1 l.2
            | Sum.inr l => z.2 l.1 l.2,
          fun y => by funext l; rcases l with l | l <;> rfl, fun z => rfl⟩
      let g : (∀ e, Fin 2 → Fin (n e)) → (∀ k m, (t k).ι m) → K := fun z y =>
        (∏ v, T v x (fun e => eq e (if a e = v then z e 0 else z e 1)) y) *
          ∏ k, (t k).val (y k)
      have e1 : ∑ y, (∏ v, T' v x y) * (outer₂ U (outer t)).val y =
          ∑ z : (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m),
            g z.1 z.2 * ∏ e, (unit K (Fin 2) (n e)).val (z.1 e) := by
        refine Fintype.sum_equiv Φ _ _ fun y => ?_
        show (∏ v, T' v x y) * ((∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)) *
          ∏ k, (t k).val ((Φ y).2 k)) = (∏ v, T' v x y) * (∏ k, (t k).val ((Φ y).2 k)) *
            ∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)
        ring
      have e2 : ∀ y : ∀ k m, (t k).ι m,
          ∑ z : ∀ e, Fin 2 → Fin (n e), g z y * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
            ∑ l : ∀ e, Λ e, (∏ v, T v x l y) * ∏ k, (t k).val (y k) := by
        intro y
        rw [sum_unit_two n fun z => g z y]
        refine Fintype.sum_equiv (Equiv.piCongrRight eq) _ _ fun l => ?_
        simp only [g, ite_self]
        rfl
      rw [e1, Fintype.sum_prod_type_right, Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => (e2 y).symm
  refine key.trans ((Equi.push_outer₂ _ U (outer t)).1.trans (Restr.mul ?_ ?_))
  · refine (Equi.push_outer (fun l : Σ _ : E, Fin 2 => ξ (ρ' (Sum.inl l))) _).1.trans
      (Restr.prod fun e => ?_)
    have : (fun m => ξ (ρ' (Sum.inl ⟨e, m⟩))) = ![ξ (a e), ξ (b e)] := by
      funext m
      fin_cases m <;> rfl
    rw [this]
    exact Restr.refl _
  · exact (Equi.push_outer (fun l : Σ k, M k => ξ (ρ' (Sum.inr l))) t).1

/-- Networks without other tensors: if s is the sum over all labels of the edges of the product of
local tables, then s is a restriction of the product of the wires on the edges, at their places. -/
theorem Restr.of_edges {E : Type} [Fintype E] [DecidableEq E]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → K)
    (hT : ∀ v x x' l l', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → T v x l = T v x' l')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∏ v, T v x l) :
    Restr (Ten.push π s) (Ten.prod fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) := by
  have := Restr.of_network (κ := Empty) (M := fun _ => Empty) π ξ s Λ a b
    (fun k => k.elim) (fun k => k.elim) (fun v x l _ => T v x l)
    (fun v x x' l l' _ _ hx hl _ => hT v x x' l l' hx hl)
    (fun x => by rw [h]; refine Finset.sum_congr rfl fun l _ => ?_
                 rw [Fintype.sum_unique]; simp)
  exact this.trans (((Equi.refl _).mul (Equi.prod_empty _)).trans (Equi.mul_one _)).1

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Unit tensors and wires

Relations between unit tensors, whose legs may be at any parties, also several at one party, and between wires. They are
what the proof of Lemma lem:exponents (`Paper/Tensors.lean`) uses.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

/-- A function f ≥ 1 on the positive integers that is multiplicative and monotone is a power function:
f(n) = n^e with e = log₂ f(2). -/
theorem eq_rpow_of_mul_mono (f : ℕ → ℝ) (h1 : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n, 1 ≤ m → m ≤ n → f m ≤ f n) (n : ℕ) (hn : 1 ≤ n) :
    f n = (n : ℝ) ^ Real.logb 2 (f 2) := by
  have hone : f 1 = 1 := by
    have := hmul 1 1 le_rfl le_rfl
    have h0 := h1 1 le_rfl
    nlinarith
  have hpow : ∀ m, 1 ≤ m → ∀ k, f (m ^ k) = f m ^ k := by
    intro m hm k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hm) hm, ih, pow_succ]
  have hfpos : ∀ m, 1 ≤ m → 0 < f m := fun m hm => lt_of_lt_of_le one_pos (h1 m hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.log (f 2) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (h1 2 (by norm_num))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x := Real.log (f n) * Real.log 2 - a * Real.log n with hx
  have key : ∀ k : ℕ, |(k : ℝ) * x| ≤ a * Real.log 2 := by
    intro k
    set m := Nat.log 2 (n ^ k)
    have hnk : n ^ k ≠ 0 := pow_ne_zero _ (by omega)
    have hm1 : 2 ^ m ≤ n ^ k := Nat.pow_log_le_self 2 hnk
    have hm2 : n ^ k ≤ 2 ^ (m + 1) := (Nat.lt_pow_succ_log_self (by norm_num) _).le
    have f1 : f 2 ^ m ≤ f n ^ k := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_two_pow) hm1
    have f2 : f n ^ k ≤ f 2 ^ (m + 1) := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_pow _ _ hn) hm2
    have g1 : (m : ℝ) * a ≤ k * Real.log (f n) := by
      have := Real.log_le_log (pow_pos (hfpos 2 (by norm_num)) m) f1
      rwa [Real.log_pow, Real.log_pow] at this
    have g2 : (k : ℝ) * Real.log (f n) ≤ (m + 1) * a := by
      have := Real.log_le_log (pow_pos (hfpos n hn) k) f2
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    have g3 : (m : ℝ) * Real.log 2 ≤ k * Real.log n := by
      have : ((2 : ℝ) ^ m) ≤ (n : ℝ) ^ k := by exact_mod_cast hm1
      have := Real.log_le_log (by positivity) this
      rwa [Real.log_pow, Real.log_pow] at this
    have g4 : (k : ℝ) * Real.log n ≤ (m + 1) * Real.log 2 := by
      have : ((n : ℝ) ^ k) ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hm2
      have := Real.log_le_log (by positivity) this
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    rw [abs_le]
    constructor
    · have e1 := mul_le_mul_of_nonneg_right g1 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g4 ha0
      rw [hx]
      nlinarith
    · have e1 := mul_le_mul_of_nonneg_right g2 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g3 ha0
      rw [hx]
      nlinarith
  have hx0 : x = 0 := by
    by_contra hne
    have hxp : 0 < |x| := abs_pos.2 hne
    obtain ⟨k, hk⟩ := exists_nat_gt (a * Real.log 2 / |x|)
    have := key k
    rw [abs_mul, Nat.abs_cast] at this
    rw [div_lt_iff₀ hxp] at hk
    linarith
  have hfin : Real.log (f n) = Real.logb 2 (f 2) * Real.log n := by
    rw [Real.logb, div_mul_eq_mul_div, eq_div_iff hl2.ne']
    linarith
  rw [Real.rpow_def_of_pos hnpos, mul_comm, ← hfin, Real.exp_log (hfpos n hn)]

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Unit tensors -/

/-- The entry of a unit tensor at equal indices is 1. -/
theorem unit_val_of {r : ℕ} {x : J → Fin r} (h : ∀ i j, x i = x j) : (unit K J r).val x = 1 :=
  if_pos h

/-- The other entries of a unit tensor are 0. -/
theorem unit_val_not {r : ℕ} {x : J → Fin r} (h : ¬ ∀ i j, x i = x j) :
    (unit K J r).val x = 0 :=
  if_neg h

theorem unit_val_congr {L : Type} [Fintype L] [DecidableEq L] {r r' : ℕ} {x : J → Fin r}
    {y : L → Fin r'} (h : (∀ i j, x i = x j) ↔ ∀ i j, y i = y j) :
    (unit K J r).val x = (unit K L r').val y := by
  by_cases hx : ∀ i j, x i = x j
  · rw [unit_val_of hx, unit_val_of (h.1 hx)]
  · rw [unit_val_not hx, unit_val_not fun hy => hx (h.2 hy)]

/-- A smaller unit tensor is a restriction of a larger one. -/
theorem Restr.unit_mono {m n : ℕ} (h : m ≤ n) : Restr (unit K J m) (unit K J n) :=
  Restr.of_map' (fun _ => Fin.castLE h) fun x =>
    unit_val_congr (x := x) (y := fun p => Fin.castLE h (x p))
      ⟨fun hx i j => congr_arg _ (hx i j), fun hx i j => Fin.castLE_injective h (hx i j)⟩

/-- The product of the unit tensors of sizes m and n is the one of size m·n. -/
theorem Equi.unit_mul (m n : ℕ) : Equi (unit K J (m * n)) (unit K J m * unit K J n) :=
  Equi.symm <| Equi.of_equiv (fun _ => finProdFinEquiv) fun x => by
    change J → Fin m × Fin n at x
    show (unit K J m).val (fun p => (x p).1) * (unit K J n).val (fun p => (x p).2) =
      (unit K J (m * n)).val fun p => finProdFinEquiv (x p)
    by_cases h1 : ∀ i j, (x i).1 = (x j).1
    · by_cases h2 : ∀ i j, (x i).2 = (x j).2
      · rw [unit_val_of h1, unit_val_of h2, unit_val_of, _root_.mul_one]
        exact fun i j => congr_arg _ (Prod.ext (h1 i j) (h2 i j))
      · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
          h2 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).2
        rw [unit_val_not hn, unit_val_not h2, mul_zero]
    · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
        h1 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).1
      rw [unit_val_not hn, unit_val_not h1, zero_mul]

/-- The unit tensor of size 1 is 1. -/
theorem Equi.unit_one : Equi (unit K J 1) 1 :=
  Equi.of_equiv (fun _ => show Fin 1 ≃ Unit from Equiv.ofUnique _ _) fun x => by
    exact unit_val_of fun i j => Subsingleton.elim (α := Fin 1) _ _

/-- Several legs of a unit tensor at one party are as good as one leg. -/
theorem Equi.push_unit {L : Type} [Fintype L] [DecidableEq L] (ρ : L → J) (hρ : ρ.Surjective)
    (n : ℕ) : Equi (Ten.push ρ (unit K L n)) (unit K J n) := by
  classical
  constructor
  · let w : ∀ q, ({l : L // ρ l = q} → Fin n) → K := fun q a =>
      if ∀ l l', a l = a l' then 1 else 0
    refine Restr.of_map w (fun q a => a ⟨(hρ q).choose, (hρ q).choose_spec⟩) fun x => ?_
    change ∀ q, {l : L // ρ l = q} → Fin n at x
    show (unit K L n).val (fun l => x (ρ l) ⟨l, rfl⟩) =
      (∏ q, w q (x q)) *
        (unit K J n).val fun q => x q ⟨(hρ q).choose, (hρ q).choose_spec⟩
    have cast : ∀ l q (h' : ρ l = q), x (ρ l) ⟨l, rfl⟩ = x q ⟨l, h'⟩ := by rintro l _ rfl; rfl
    by_cases h : ∀ l l', x (ρ l) ⟨l, rfl⟩ = x (ρ l') ⟨l', rfl⟩
    · rw [unit_val_of h, unit_val_of, Finset.prod_eq_one, _root_.mul_one]
      · rintro q -
        refine if_pos (show ∀ l l', x q l = x q l' from fun l l' => ?_)
        rw [← cast l.1 q l.2, ← cast l'.1 q l'.2]
        exact h _ _
      · intro q q'
        rw [← cast _ _ (hρ q).choose_spec, ← cast _ _ (hρ q').choose_spec]
        exact h _ _
    · rw [unit_val_not h]
      by_cases h1 : ∀ q l l', x q l = x q l'
      · rw [unit_val_not, mul_zero]
        intro h2
        refine h fun i j => ?_
        rw [h1 (ρ i) ⟨i, rfl⟩ ⟨_, (hρ (ρ i)).choose_spec⟩,
          h1 (ρ j) ⟨j, rfl⟩ ⟨_, (hρ (ρ j)).choose_spec⟩]
        exact h2 _ _
      · push Not at h1
        obtain ⟨q, l, l', hq⟩ := h1
        rw [Finset.prod_eq_zero (Finset.mem_univ q), zero_mul]
        exact if_neg (show ¬ ∀ l l', x q l = x q l' from fun h => hq (h l l'))
  · refine Restr.of_map' (fun q a _ => a) fun x => ?_
    refine unit_val_congr (x := x) (y := fun l => x (ρ l)) ⟨fun h i j => h _ _, fun h i j => ?_⟩
    obtain ⟨i, rfl⟩ := hρ i
    obtain ⟨j, rfl⟩ := hρ j
    exact h i j

/-- A pushed unit tensor depends only on the set of parties that hold a leg. -/
theorem Equi.push_unit_congr {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (π' : L → I)
    (h : Set.range π = Set.range π') (n : ℕ) :
    Equi (Ten.push π (unit K J n)) (Ten.push π' (unit K L n)) := by
  classical
  have key : ∀ {L : Type} [Fintype L] [DecidableEq L] (π' : L → I) (S : Finset I)
      (_ : Set.range π' = S),
      Equi (Ten.push π' (unit K L n)) (Ten.push (fun q : S => (q : I)) (unit K S n)) := by
    intro L _ _ π' S hS
    let ρ : L → S := fun l => ⟨π' l, by
      have : π' l ∈ (S : Set I) := hS ▸ Set.mem_range_self l
      exact this⟩
    have hρ : ρ.Surjective := by
      rintro ⟨q, hq⟩
      have : q ∈ Set.range π' := hS ▸ (show q ∈ (S : Set I) from hq)
      obtain ⟨l, hl⟩ := this
      exact ⟨l, Subtype.ext hl⟩
    exact ((Equi.push_push (fun q : S => (q : I)) ρ (unit K L n)).symm.trans
      ((Equi.push_unit ρ hρ n).push _))
  exact (key π (Set.toFinset (Set.range π)) (by simp)).trans
    (key π' (Set.toFinset (Set.range π)) (by simp [h])).symm

/-- A tensor with all its legs at one party is a restriction of 1. -/
theorem Restr.push_const (q : I) (t : Ten K J) : Restr (Ten.push (fun _ => q) t) 1 := by
  classical
  refine Restr.of_map (fun p a => if h : q = p then t.val fun j => a ⟨j, h⟩ else 1)
    (fun _ _ => ()) fun x => ?_
  have key : ∀ f : ∀ p, ∀ j : {j : J // q = p}, t.ι j.1, t.val (fun j => f q ⟨j, rfl⟩) =
      ∏ p, if h : q = p then t.val fun j => f p ⟨j, h⟩ else 1 := by
    intro f
    rw [Finset.prod_eq_single q]
    · simp
    · intro p _ hp
      rw [dif_neg fun h => hp h.symm]
    · simp
  exact (key x).trans (_root_.mul_one _).symm

/-! ### Wires -/

/-- A wire may be read in both directions. -/
theorem Equi.wire_comm (n : ℕ) (p q : I) : Equi (wire K n p q) (wire K n q p) :=
  Equi.push_unit_congr _ _ (by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons]
    simp [Set.pair_comm]) n

/-- A wire with both ends at one party is a restriction of 1. -/
theorem Restr.wire_self (n : ℕ) (p : I) : Restr (wire K n p p) 1 := by
  have : (![p, p] : Fin 2 → I) = fun _ => p := by
    funext i; fin_cases i <;> rfl
  rw [wire, this]
  exact Restr.push_const p _

/-- Two parallel wires are one wire, whose dimension is the product. -/
theorem Equi.wire_mul (m n : ℕ) (p q : I) :
    Equi (wire K (m * n) p q) (wire K m p q * wire K n p q) :=
  ((Equi.unit_mul m n).push _).trans (Equi.push_mul _ _ _)

/-- A wire of dimension 1 is 1. -/
theorem Equi.wire_one (p q : I) : Equi (wire K 1 p q) 1 :=
  (Equi.unit_one.push _).trans (Equi.push_one _)

private def tr {n : ℕ} (v : Fin 3) (x l : Fin 2 → Fin n) : K :=
  if v = 0 then (if x 0 = l 0 then 1 else 0) else
    if v = 1 then (if l 0 = l 1 then 1 else 0) else (if x 1 = l 1 then 1 else 0)

private theorem tr_sum {n : ℕ} (x : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val x = ∑ l : Fin 2 → Fin n, ∏ v, tr (K := K) v x l := by
  rw [Finset.sum_eq_single (fun _ => x 0)]
  · rcases eq_or_ne (x 0) (x 1) with h | h
    · rw [unit_val_of (by simp [Fin.forall_fin_two, h])]
      simp [tr, h]
    · rw [unit_val_not (by simp [Fin.forall_fin_two, h])]
      simp [Fin.prod_univ_succ, tr, h.symm]
  · intro l _ hl
    by_cases h0 : x 0 = l 0
    · by_cases h1 : l 0 = l 1
      · refine absurd (funext fun i => ?_) hl
        fin_cases i
        · exact h0.symm
        · exact (h0.trans h1).symm
      · simp [Fin.prod_univ_succ, tr, h1]
    · simp [Fin.prod_univ_succ, tr, h0]
  · simp

/-- The wire from p to q is a restriction of the product of the wires from p to r and from r to q. -/
theorem Restr.wire_trans (n : ℕ) (p q r : I) :
    Restr (wire K n p q) (wire K n p r * wire K n r q) := by
  classical
  have h := Restr.of_edges (V := Fin 3) (E := Fin 2) (J := Fin 2) (K := K) ![p, q] ![p, r, q]
    (unit K (Fin 2) n) (fun _ => Fin n) ![0, 1] ![1, 2] tr
    (by
      intro v x x' l l' hx hl
      change Fin 2 → Fin n at x x'
      fin_cases v
      · have h0 : x 0 = x' 0 := hx 0 rfl
        have h1 := hl 0 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 := hl 0 (Or.inr rfl)
        have h1 := hl 1 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 : x 1 = x' 1 := hx 1 rfl
        have h1 := hl 1 (Or.inr rfl)
        simp [tr, h0, h1]) tr_sum
  refine h.trans ((Equi.prod_fin_two _).1.trans ?_)
  simp only [Fintype.card_fin]
  exact Restr.refl _

/-- Moving legs: the leg j can be moved from π' j to π j through a wire of its dimension. -/
theorem Restr.move (π π' : J → I) (t : Ten K J) :
    Restr (Ten.push π t)
      (Ten.prod (fun j => wire K (Fintype.card (t.ι j)) (π j) (π' j)) * Ten.push π' t) := by
  classical
  have h := Restr.of_network (V := J ⊕ J) (E := J) (κ := Unit) (M := fun _ => J) π
    (Sum.elim π π') t t.ι Sum.inl Sum.inr (fun _ => t) (fun _ j => Sum.inr j)
    (fun v x l y => match v with
      | Sum.inl j => if x j = l j then 1 else 0
      | Sum.inr j => if l j = y () j then 1 else 0)
    (by
      intro v x x' l l' y y' hx hl hy
      rcases v with j | j
      · simp only [hx j rfl, hl j (Or.inl rfl)]
      · simp only [hl j (Or.inr rfl), hy () j rfl])
    (by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single (fun _ => x)]
        · simp
        · intro y _ hy
          have : ∃ j, ¬ x j = y () j := by
            by_contra hcon
            push Not at hcon
            exact hy (funext fun _ => funext fun j => (hcon j).symm)
          obtain ⟨j, hj⟩ := this
          rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) (if_neg hj), zero_mul]
        · simp
      · intro l _ hl
        have : ∃ j, ¬ x j = l j := by
          by_contra hcon
          push Not at hcon
          exact hl (funext fun j => (hcon j).symm)
        obtain ⟨j, hj⟩ := this
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl j)) (if_neg hj), zero_mul]
      · simp)
  refine h.trans (Restr.mul (Restr.refl _) ?_)
  exact (Equi.prod_unique _).1

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F of a pushed unit tensor of size at least 1 is at least 1. -/
theorem one_le_unit [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ F.F (Ten.push π (unit K J n)) := by
  refine F.one_le (y := fun _ _ => ⟨0, hn⟩) ?_
  show ite _ _ _ ≠ (0 : K)
  simp

/-- F of a unit tensor that has a leg is at most its size. -/
theorem unit_le [Nonempty J] (π : J → I) (n : ℕ) : F.F (Ten.push π (unit K J n)) ≤ n := by
  have h : SumRestr (unit K J n) (fun _ : Fin n => (1 : Ten K J)) :=
    RankLE.sumRestr (Restr.refl (unit K J n))
  have := F.le_sum _ _ (h.push π)
  simpa [F.congr (Equi.push_one π), F.one] using this

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent as a coefficient

The permanent of a matrix is the coefficient of the product of all variables in the product of the linear
forms given by the rows. This coefficient does not change modulo the squares of the variables.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]

/-- The exponent of the product of all variables. -/
noncomputable def ones (C : Type*) [Fintype C] : C →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp] theorem ones_apply {C : Type*} [Fintype C] (c : C) : ones C c = 1 := rfl

section Bij

variable {C I : Type*} [Fintype C] [Fintype I]

theorem sum_single_eq_ones [DecidableEq C] (f : I → C) :
    (∑ i, Finsupp.single (f i) 1 = ones C) ↔ Function.Bijective f := by
  classical
  have hap : ∀ c, (∑ i, Finsupp.single (f i) 1 : C →₀ ℕ) c = #{i | f i = c} := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.single_apply]
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h c
    have := hap c
    rw [h, ones_apply] at this
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 this.symm
    refine ⟨i, ?_, fun j hj => ?_⟩
    · have : i ∈ ({i | f i = c} : Finset I) := by rw [hi]; simp
      simpa using this
    · have : j ∈ ({i | f i = c} : Finset I) := by simpa using hj
      rw [hi] at this
      simpa using this
  · intro h
    ext c
    rw [hap, ones_apply, Finset.card_eq_one]
    obtain ⟨i, hi, hu⟩ := h c
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨hu j, fun e => e ▸ hi⟩

variable {N J κ : Type*} [Fintype N] [Fintype J] [Fintype κ] [DecidableEq N]

open scoped Classical in
/-- Expanding a product of sums of terms and taking the coefficient of the product of all variables. -/
theorem coeff_ones_prod (w : N → κ → R) (g : N → κ → J → C) :
    coeff (ones C) (∏ i, ∑ a, MvPolynomial.C (w i a) * ∏ j, (X (g i a j) : MvPolynomial C R)) =
      ∑ f : N → κ, if Function.Bijective (fun p : N × J => g p.1 (f p.1) p.2) then ∏ i, w i (f i)
        else 0 := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, ← Fintype.prod_prod_type'
    (f := fun i j => (X (g i (f i) j) : MvPolynomial C R))]
  have : (∏ p : N × J, (X (g p.1 (f p.1) p.2) : MvPolynomial C R)) =
      monomial (∑ p : N × J, Finsupp.single (g p.1 (f p.1) p.2) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [this, coeff_monomial]
  simp only [sum_single_eq_ones (fun p : N × J => g p.1 (f p.1) p.2)]
  split_ifs <;> simp

open scoped Classical in
theorem sum_perm_eq [DecidableEq C] (w : C → C → R) :
    ∑ σ : Equiv.Perm C, ∏ i, w i (σ i) =
      ∑ f : C → C, if Function.Bijective f then ∏ i, w i (f i) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (i := fun f hf => Equiv.ofBijective f (Finset.mem_filter.1 hf).2)
    (j := fun σ _ => (σ : C → C)) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    exact σ.bijective
  · intros; rfl
  · intros; ext; rfl
  · intros; rfl

/-- The permanent is a coefficient. -/
theorem permanent_eq_coeff [DecidableEq C] (M : Matrix C C R) :
    M.permanent = coeff (ones C) (∏ i, ∑ j, MvPolynomial.C (M i j) * (X j : MvPolynomial C R)) := by
  classical
  have h := coeff_ones_prod (N := C) (J := Unit) (κ := C) (C := C) (fun i j => M i j) (fun _ a _ => a)
  have h2 : M.permanent = ∑ σ : Equiv.Perm C, ∏ i, M i (σ i) := by
    rw [← Matrix.permanent_transpose]
    rfl
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, h2]
  refine (sum_perm_eq (fun i j => M i j)).trans (Finset.sum_congr rfl fun f _ => ?_)
  have hiff : Function.Bijective f ↔ Function.Bijective fun p : C × Unit => f p.1 :=
    ⟨fun hb => hb.comp (Equiv.prodPUnit C).bijective, fun hb => hb.comp (Equiv.prodPUnit C).symm.bijective⟩
  by_cases hb : Function.Bijective f
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (fun h' => hb (hiff.2 h'))]

end Bij

section Squares

variable {C : Type*} [Fintype C]

variable (C R) in
/-- The ideal of the squares of the variables. -/
noncomputable def sqIdeal : Ideal (MvPolynomial C R) := Ideal.span (Set.range fun c => X c * X c)

theorem coeff_ones_of_mem {p : MvPolynomial C R} (h : p ∈ sqIdeal R C) : coeff (ones C) p = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, coeff_mul_X', coeff_mul_X']
  simp [Finsupp.mem_support_iff]

theorem coeff_ones_congr {p q : MvPolynomial C R}
    (h : Ideal.Quotient.mk (sqIdeal R C) p = Ideal.Quotient.mk (sqIdeal R C) q) :
    coeff (ones C) p = coeff (ones C) q := by
  have := coeff_ones_of_mem (Ideal.Quotient.eq.1 h)
  rwa [coeff_sub, sub_eq_zero] at this

omit [Fintype C] in
theorem mk_X_sq (c : C) : Ideal.Quotient.mk (sqIdeal R C) (X c) ^ 2 = 0 := by
  rw [sq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨c, rfl⟩)

omit [Fintype C] in
/-- Modulo squares, a product of two linear forms in four variables has only two terms. -/
theorem mk_gadget (h : R) (hh : h * 2 = 1) (p q r s : C) :
    Ideal.Quotient.mk (sqIdeal R C)
      ((MvPolynomial.C h * X p + MvPolynomial.C h * X q + MvPolynomial.C h * X r - MvPolynomial.C h * X s) *
        (X p + X q - X r + X s)) = Ideal.Quotient.mk (sqIdeal R C) (X p * X q + X r * X s) := by
  simp only [map_mul, map_add, map_sub]
  have h1 := mk_X_sq (R := R) p
  have h2 := mk_X_sq (R := R) q
  have h3 := mk_X_sq (R := R) r
  have h4 := mk_X_sq (R := R) s
  have h5 : Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) * 2 = 1 := by
    rw [← map_ofNat (Ideal.Quotient.mk (sqIdeal R C)) 2, ← map_mul, ← map_ofNat MvPolynomial.C 2,
      ← map_mul, hh, map_one, map_one]
  generalize Ideal.Quotient.mk (sqIdeal R C) (X p) = p at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X q) = q at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X r) = r at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X s) = s at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) = e at *
  linear_combination e * h1 + e * h2 - e * h3 - e * h4 + (p * q + r * s) * h5

end Squares

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits as permanents

`N` is a finite set of incidences with two permutations `σ`, `ρ`. A bit for every orbit of `σ` and a bit for
every orbit of `ρ` are summed over, and every incidence contributes a weight that depends on its two bits.
The sum is a permanent of size `3 * |N|`.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The row that is chosen at `n`: `n` itself or its successor. -/
def pick (σ : Equiv.Perm N) (s : N → Bool) (n : N) : N := if s n then n else σ n

omit [Fintype N] [DecidableEq N] in
theorem pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : ∀ n, s (σ n) = s n) :
    Function.Injective (pick σ s) := by
  intro n m e
  unfold pick at e
  rcases hn : s n <;> rcases hm : s m <;> simp only [hn, hm, if_true, if_false, Bool.false_eq_true] at e
  · exact σ.injective e
  · have := h n
    rw [e, hn, hm] at this
    cases this
  · have := h m
    rw [← e, hn, hm] at this
    cases this
  · exact e

omit [DecidableEq N] in
theorem inv_of_pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : Function.Injective (pick σ s)) (n : N) :
    s (σ n) = s n := by
  rcases hn : s n <;> rcases hm : s (σ n)
  · rfl
  · have : pick σ s n = pick σ s (σ n) := by simp [pick, hn, hm]
    have := h this
    rw [← this, hn] at hm
    cases hm
  · obtain ⟨m, hm'⟩ := (Finite.injective_iff_surjective.1 h) (σ n)
    unfold pick at hm'
    rcases hs : s m <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at hm'
    · have := σ.injective hm'
      rw [this, hn] at hs
      cases hs
    · rw [hm', hm] at hs
      cases hs
  · rfl

/-- The columns used by the three rows of an incidence. -/
def slot (σ ρ : Equiv.Perm N) (n : N) (a : Bool × Bool × Bool) : Option Bool → N × Option Bool
  | none => (if a.1 then n else σ n, none)
  | some true => (n, some a.1)
  | some false => (if a.2.1 then n else ρ n, some !a.2.2)

omit [DecidableEq N] in
theorem slot_bijective (σ ρ : Equiv.Perm N) (s r q : N → Bool) :
    Function.Bijective (fun p : N × Option Bool => slot σ ρ p.1 (s p.1, r p.1, q p.1) p.2) ↔
      (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) ∧ ∀ n, s (pick ρ r n) = q n := by
  constructor
  · rintro ⟨h, -⟩
    have h3 : ∀ n, s (pick ρ r n) = q n := by
      intro n
      by_contra hne
      have : ((n, some false) : N × Option Bool) = (pick ρ r n, some true) := by
        apply h
        simp only [slot, pick] at hne ⊢
        congr 2
        revert hne
        generalize s _ = x
        generalize q n = y
        revert x y
        decide
      simp at this
    refine ⟨fun n => inv_of_pick_injective (fun n m e => ?_) n,
      fun n => inv_of_pick_injective (fun n m e => ?_) n, h3⟩
    · have : ((n, none) : N × Option Bool) = (m, none) := h (by
        simp only [slot]
        exact congrArg (fun x => (x, none)) e)
      exact (Prod.mk.inj this).1
    · have : ((n, some false) : N × Option Bool) = (m, some false) := h (by
        simp only [slot]
        rw [← h3 n, ← h3 m, e]
        exact congrArg (fun x => (x, some !s (pick ρ r m))) e)
      exact (Prod.mk.inj this).1
  · intro ⟨h1, h2, h3⟩
    rw [← Finite.injective_iff_bijective]
    have i1 := pick_injective h1
    have i2 := pick_injective h2
    rintro ⟨n, _ | _ | _⟩ ⟨m, _ | _ | _⟩ e <;> simp only [slot, Prod.mk.injEq, reduceCtorEq, and_false,
      Option.some.injEq] at e
    · rw [i1 e.1]
    · rw [i2 e.1]
    · obtain ⟨e1, e2⟩ := e
      have := h3 n
      unfold pick at this
      rw [e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q n <;> decide)
    · obtain ⟨e1, e2⟩ := e
      have := h3 m
      unfold pick at this
      rw [← e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q m <;> decide)
    · rw [e.1]

/-- The indicator of a column. -/
def ind (c₀ : N × Option Bool) (a : R) (c : N × Option Bool) : R := if c = c₀ then a else 0

/-- The matrix. -/
def gridMatrix (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    Matrix (N × Option Bool) (N × Option Bool) R
  | (n, none), c => ind (n, none) h c + ind (n, some true) h c + ind (σ n, none) h c - ind (n, some false) h c
  | (n, some true), c =>
    ind (n, none) 1 c + ind (n, some true) 1 c - ind (σ n, none) 1 c + ind (n, some false) 1 c
  | (n, some false), c =>
    ind (n, some false) (W n true true) c + ind (n, some true) (W n false true) c +
      ind (ρ n, some false) (W (ρ n) true false) c + ind (ρ n, some true) (W (ρ n) false false) c

theorem sum_ind (c₀ : N × Option Bool) (a : R) :
    ∑ c, MvPolynomial.C (ind c₀ a c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C a * X c₀ := by
  simp [ind, apply_ite MvPolynomial.C, ite_mul]

/-- The weight of a choice. -/
def wt (ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) (a : Bool × Bool × Bool) : R :=
  if a.2.1 then W n a.2.2 true else W (ρ n) a.2.2 false

theorem sum_row_none (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, none) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C h * X (n, none) + MvPolynomial.C h * X (n, some true) +
        MvPolynomial.C h * X (σ n, none) - MvPolynomial.C h * X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind]

theorem sum_row_true (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some true) c) * (X c : MvPolynomial (N × Option Bool) R) =
      X (n, none) + X (n, some true) - X (σ n, none) + X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind, map_one, one_mul]

theorem sum_row_false (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some false) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C (W n true true) * X (n, some false) + MvPolynomial.C (W n false true) * X (n, some true) +
        MvPolynomial.C (W (ρ n) true false) * X (ρ n, some false) +
        MvPolynomial.C (W (ρ n) false false) * X (ρ n, some true) := by
  simp only [gridMatrix, map_add, add_mul, Finset.sum_add_distrib, sum_ind]

theorem gridMatrix_permanent_aux (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = coeff (ones (N × Option Bool))
      (∏ n, ∑ a, MvPolynomial.C (wt ρ W n a) * ∏ j, (X (slot σ ρ n a j) : MvPolynomial (N × Option Bool) R)) := by
  rw [permanent_eq_coeff]
  apply coeff_ones_congr
  rw [Fintype.prod_prod_type, map_prod, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  simp only [Fintype.prod_option, Fintype.prod_bool]
  rw [sum_row_none, sum_row_true, sum_row_false, ← mul_assoc, map_mul, mk_gadget h hh, ← map_mul]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slot, wt, if_true, if_false, Bool.false_eq_true,
    Bool.not_true, Bool.not_false]
  ring

open scoped Classical in
theorem gridMatrix_permanent (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = ∑ s : N → Bool, ∑ r : N → Bool,
      if (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) then ∏ n, W n (s n) (r n) else 0 := by
  classical
  rw [gridMatrix_permanent_aux h hh, coeff_ones_prod]
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool × Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (fun n => s (pick ρ r n))]
  · have key := slot_bijective σ ρ s r (fun n => s (pick ρ r n))
    simp only [implies_true, and_true] at key
    by_cases hc : (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n)
    · rw [if_pos hc]
      refine (if_pos (key.2 hc)).trans ?_
      have e1 : ∀ n, wt ρ W n (s n, r n, s (pick ρ r n)) =
          (if r n then W n (s n) (r n) else 1) *
            (if r (ρ n) then 1 else W (ρ n) (s (ρ n)) (r (ρ n))) := by
        intro n
        rw [hc.2 n]
        rcases hr : r n <;> simp [wt, pick, hr]
      refine (Finset.prod_congr rfl fun n _ => e1 n).trans ?_
      rw [Finset.prod_mul_distrib, Equiv.prod_comp ρ (fun n => if r n then 1 else W n (s n) (r n)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      split_ifs <;> simp
    · rw [if_neg hc]
      exact if_neg fun hb => hc (key.1 hb)
  · intro q _ hq
    apply if_neg
    intro hb
    apply hq
    have := (slot_bijective σ ρ s r q).1 hb
    funext n
    exact (this.2.2 n).symm
  · intro hc
    exact absurd (mem_univ _) hc

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits, indexed by maps

The permutations of the grid are replaced by maps: all incidences with the same value of a map share a bit.
-/

namespace Nc

open Finset MvPolynomial

section Fibres

variable {N V : Type*} [Fintype N] [DecidableEq N]

/-- A permutation whose cycles are the fibres of a map. -/
theorem exists_perm_fibres (v : N → V) : ∃ σ : Equiv.Perm N, (∀ n, v (σ n) = v n) ∧
    ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m := by
  classical
  have h : ∀ y, ∃ f : Equiv.Perm {n // v n = y}, f.IsCycleOn ((univ : Finset {n // v n = y}) : Set _) :=
    fun y => (Finset.exists_cycleOn univ).imp fun f hf => hf.1
  choose f hf using h
  let e := Equiv.sigmaFiberEquiv v
  let σ : Equiv.Perm N := (e.symm.trans (Equiv.sigmaCongrRight f)).trans e
  have hσ : ∀ n, σ n = (f (v n) ⟨n, rfl⟩).1 := fun n => rfl
  refine ⟨σ, fun n => ?_, fun s hs n m e => ?_⟩
  · rw [hσ]
    exact (f (v n) ⟨n, rfl⟩).2
  · have h1 : ∀ y, ∀ x : {n // v n = y}, s (f y x).1 = s x.1 := by
      rintro y ⟨x, rfl⟩
      rw [← hσ]
      exact hs x
    obtain ⟨i, -, hi⟩ := (hf (v m)).exists_pow_eq (mem_univ ⟨n, e⟩) (mem_univ ⟨m, rfl⟩)
    have h2 : ∀ i : ℕ, s ((f (v m) ^ i) ⟨n, e⟩).1 = s n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
    rw [← h2 i, hi]

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- A sum over the functions that are constant on the fibres. -/
theorem sum_invariant [Fintype V] [DecidableEq V] {v : N → V} (hv : Function.Surjective v) {σ : Equiv.Perm N}
    (h1 : ∀ n, v (σ n) = v n)
    (h2 : ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m) (Φ : (N → Bool) → R) :
    ∑ s : N → Bool, (if ∀ n, s (σ n) = s n then Φ s else 0) = ∑ x : V → Bool, Φ fun n => x (v n) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ n => x (v n)) ?_ ?_ ?_ ?_
  · intro x _
    simp [h1]
  · intro x _ y _ e
    exact hv.injective_comp_right e
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨fun y => s (Function.surjInv hv y), mem_univ _, ?_⟩
    funext n
    exact h2 s hs _ _ (Function.surjInv_eq hv _)
  · intros
    rfl

/-- A sum over two families of bits is a permanent. -/
theorem exists_grid {K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K)
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    ∃ σ ρ : Equiv.Perm N, (∀ n, w (ρ n) = w n) ∧ ∀ (h : R) (_ : h * 2 = 1) (W : N → Bool → Bool → R),
      (gridMatrix h σ ρ W).permanent =
        ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, s1, s2⟩ := exists_perm_fibres v
  obtain ⟨ρ, r1, r2⟩ := exists_perm_fibres w
  refine ⟨σ, ρ, r1, fun h hh W => ?_⟩
  rw [gridMatrix_permanent h hh]
  refine Eq.trans ?_ (sum_invariant hv s1 s2 fun s => ∑ r : K → Bool, ∏ n, W n (s n) (r (w n)))
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ n, s (σ n) = s n
  · rw [if_pos hs]
    refine Eq.trans ?_ (sum_invariant hw r1 r2 fun r => ∏ n, W n (s n) (r n))
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hs]
  · rw [if_neg hs]
    exact Finset.sum_eq_zero fun r _ => if_neg fun hc => hs hc.1

end Fibres

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent under renaming and padding
-/

namespace Nc

open Finset

variable {R : Type*} [CommSemiring R]
variable {C D E : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem permanent_submatrix_equiv (e : D ≃ C) (M : Matrix C C R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv e.permCongr _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Matrix.submatrix_apply, Equiv.permCongr_apply]

/-- A diagonal of ones does not change the permanent. -/
theorem permanent_pad (M : Matrix C C R) :
    (Matrix.fromBlocks M 0 0 (1 : Matrix E E R)).permanent = M.permanent := by
  unfold Matrix.permanent
  symm
  refine Finset.sum_of_injOn (fun τ => Equiv.Perm.sumCongr τ 1) ?_ ?_ ?_ ?_
  · intro τ _ τ' _ e
    have := Equiv.Perm.sumCongrHom_injective (α := C) (β := E) (a₁ := (τ, 1)) (a₂ := (τ', 1)) e
    exact (Prod.mk.inj this).1
  · intro τ _
    simp
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hfix : ∀ k : E, σ (Sum.inr k) = Sum.inr k := by
      intro k
      by_contra hk
      apply hne
      refine Finset.prod_eq_zero (mem_univ (Sum.inr k)) ?_
      rcases hs : σ (Sum.inr k) with c | e
      · rw [Matrix.fromBlocks_apply₁₂]
        rfl
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_ne]
        rintro rfl
        exact hk hs
    have hmaps : Set.MapsTo σ (Set.range (Sum.inl : C → C ⊕ E)) (Set.range Sum.inl) := by
      rintro _ ⟨c, rfl⟩
      rcases hs : σ (Sum.inl c) with c' | e
      · exact ⟨c', rfl⟩
      · have := σ.injective (hs.trans (hfix e).symm)
        cases this
    obtain ⟨⟨τ, κ⟩, rfl⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    have : κ = 1 := by
      ext k
      have := hfix k
      simpa using this
    subst this
    exact ⟨τ, by simp, rfl⟩
  · intro τ _
    rw [Fintype.prod_sum_type]
    simp

/-- A square matrix sits in every larger one with the same permanent. -/
theorem exists_permanent_fin (M : Matrix C C R) {S : ℕ} (hS : Fintype.card C ≤ S) :
    ∃ M' : Matrix (Fin S) (Fin S) R, M'.permanent = M.permanent ∧
      ∀ i j, (M' i j = 0 ∨ M' i j = 1) ∨ ∃ c d, M' i j = M c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hS
  let e : Fin (Fintype.card C + k) ≃ C ⊕ Fin k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _))
  refine ⟨(Matrix.fromBlocks M 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e, ?_, fun i j => ?_⟩
  · rw [permanent_submatrix_equiv, permanent_pad]
  · rw [Matrix.submatrix_apply]
    rcases e i with c | a <;> rcases e j with d | b
    · exact Or.inr ⟨c, d, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Low degree is fast (Lemma 1)

A polynomial of degree at most `d` that is computed by an arithmetic circuit with `s` gates has, at every
point, a value that is a sum over parse trees. A parse tree with `i` leaves reads `2 * i - 1` entries of
fixed tables of the circuit and `i` coordinates of the point; only `i ≤ d` occurs.
-/

namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}

/-- Entry `k` of the list `l` is a variable, a constant, or the sum or product of two earlier entries. -/
def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

/-- `p` is computed by an arithmetic circuit with `s` gates (inputs and constants count as gates). -/
def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

section Proof

/-- `p` along the line through 0 and `u`. -/
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

end Proof

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Affine substitutions and the generic permanent

Entries that are affine in one variable, the generic permanent, and circuits under affine substitutions.
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F]
variable {ι α θ : Type*} [Fintype ι] [Fintype α] [Fintype θ] [DecidableEq ι] [DecidableEq α] [DecidableEq θ]

/-- Constant, or affine in one variable. -/
def IsAffine (p : MvPolynomial ι F) : Prop := (∃ b, p = C b) ∨ ∃ i a b, p = C a * X i + C b

section Proof

/-- The constants and, for `some i`, the span of the constants and `X i`. -/
noncomputable def affIn (o : Option ι) : Submodule F (MvPolynomial ι F) :=
  match o with
  | none => Submodule.span F {1}
  | some i => Submodule.span F {X i, 1}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_affIn (o : Option ι) : (1 : MvPolynomial ι F) ∈ affIn (F := F) o := by
  cases o
  · exact Submodule.subset_span rfl
  · exact Submodule.subset_span (by simp)

omit [Fintype ι] [DecidableEq ι] in
theorem C_mem_affIn (o : Option ι) (b : F) : (C b : MvPolynomial ι F) ∈ affIn (F := F) o := by
  have := (affIn (F := F) o).smul_mem b (one_mem_affIn o)
  rwa [MvPolynomial.smul_eq_C_mul, mul_one] at this

omit [Fintype ι] [DecidableEq ι] in
theorem isAffine_of_mem {o : Option ι} {p : MvPolynomial ι F} (h : p ∈ affIn (F := F) o) : IsAffine p := by
  cases o with
  | none =>
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact Or.inl ⟨b, by rw [MvPolynomial.smul_eq_C_mul, mul_one]⟩
  | some i =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
    exact Or.inr ⟨i, a, b, by rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, mul_one]⟩

end Proof

section Circuits

/-- The permanent of the generic matrix. -/
noncomputable def genPerm (F : Type*) [Field F] (S : ℕ) : MvPolynomial (Fin S × Fin S) F :=
  (Matrix.of fun i j => X (i, j) : Matrix (Fin S) (Fin S) (MvPolynomial (Fin S × Fin S) F)).permanent

omit [Fintype ι] [DecidableEq ι] in
theorem aeval_genPerm {S : ℕ} (M : Matrix (Fin S) (Fin S) (MvPolynomial ι F)) :
    aeval (fun p : Fin S × Fin S => M p.1 p.2) (genPerm F S) = M.permanent := by
  simp [genPerm, Matrix.permanent, map_sum, map_prod]

omit [Fintype ι] [DecidableEq ι] in
/-- Substituting affine polynomials into a circuit costs a factor 5. -/
theorem Computes.aeval {κ : Type*} {p : MvPolynomial κ F} {s : ℕ} (h : Computes p s)
    (E : κ → MvPolynomial ι F) (hE : ∀ k, IsAffine (E k)) : Computes (MvPolynomial.aeval E p) (5 * s) := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  have hblock : ∀ n, n < s → ∃ b : ℕ → MvPolynomial ι F, b 4 = MvPolynomial.aeval E (l n) ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := by
    intro n hn
    have hconst : ∀ a : F, ∃ b : ℕ → MvPolynomial ι F, b 4 = C a ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := fun a =>
      ⟨fun _ => C a, rfl, fun m _ hb t ht => Or.inr (Or.inl ⟨a, hb t ht⟩)⟩
    rcases hl n hn with ⟨x, hx⟩ | ⟨a, ha⟩ | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · rw [hx, aeval_X]
      rcases hE x with ⟨b, hb⟩ | ⟨i, a, b, hab⟩
      · rw [hb]
        exact hconst b
      · rw [hab]
        refine ⟨fun t => if t = 0 then C a else if t = 1 then X i else if t = 2 then C a * X i else
          if t = 3 then C b else C a * X i + C b, rfl, fun m _ hm t ht => ?_⟩
        have h0 := hm 0 (by omega)
        have h1 := hm 1 (by omega)
        have h2 := hm 2 (by omega)
        have h3 := hm 3 (by omega)
        have h4 := hm 4 (by omega)
        simp only [if_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, one_ne_zero,
          Nat.reduceEqDiff] at h0 h1 h2 h3 h4
        interval_cases t
        · exact Or.inr (Or.inl ⟨a, h0⟩)
        · exact Or.inl ⟨i, h1⟩
        · exact Or.inr (Or.inr (Or.inr ⟨5 * n + 0, by omega, 5 * n + 1, by omega, by rw [h0, h1, h2]⟩))
        · exact Or.inr (Or.inl ⟨b, h3⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨5 * n + 2, by omega, 5 * n + 3, by omega, by rw [h2, h3, h4]⟩))
    · rw [ha, algHom_C]
      exact hconst a
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inl ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_add]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inr ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_mul]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
  choose! b hb4 hb using hblock
  refine ⟨fun q => b (q / 5) (q % 5), fun q hq => ?_, 5 * k + 4, by omega, ?_⟩
  · have hlt : q % 5 < 5 := Nat.mod_lt _ (by omega)
    have := hb (q / 5) (by omega) (fun q => b (q / 5) (q % 5)) (fun i hi => ?_) (fun t ht => ?_) (q % 5) hlt
    · rwa [Nat.div_add_mod] at this
    · have e1 : (5 * i + 4) / 5 = i := by omega
      have e2 : (5 * i + 4) % 5 = 4 := by omega
      simp only [e1, e2]
      exact hb4 i (by omega)
    · have e1 : (5 * (q / 5) + t) / 5 = q / 5 := by omega
      have e2 : (5 * (q / 5) + t) % 5 = t := by omega
      simp only [e1, e2]
  · have e1 : (5 * k + 4) / 5 = k := by omega
    have e2 : (5 * k + 4) % 5 = 4 := by omega
    simp only [e1, e2]
    exact hb4 k hk

end Circuits

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Definitions for the quantitative theorem

Approximate circuits; families of polynomials that are complete for grid sums (the permanent, the Hamiltonian cycle
polynomial); the exponent of a unit tensor; sums of restrictions up to ε.
-/

namespace Nc

open Finset MvPolynomial

section Approx

variable {F X : Type*} [Field F]

/-- `f` is approximated by a circuit with at most `s` gates: a circuit over the Laurent series in ε computes some
`f + ε * g`, every coefficient of `g` being a power series. -/
def Approximates (f : MvPolynomial X F) (s : ℕ) : Prop :=
  ∃ p : MvPolynomial X (LaurentSeries F), Computes p s ∧
    ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0

end Approx

/-- The Hamiltonian cycle polynomial: the sum over the permutations with one cycle through all points. -/
noncomputable def genHC (F : Type*) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  open Classical in ∑ σ : Equiv.Perm (Fin m) with σ.IsCycleOn Set.univ, ∏ i, X (i, σ i)

/-- The polynomials `G S`, one for every size `S`, are complete for grid sums with the blow-up `κ`: a sum over two
families of bits of a product of weights, one for every incidence, each affine in the variable of its incidence, is a
projection with affine entries of `G S` for all `S ≥ κ * #incidences`. -/
def GridComplete (F : Type) [Field F] (G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) F) (κ : ℕ) : Prop :=
  ∀ {ι N V W' : Type} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype W'] [DecidableEq W']
    (v : N → V) (w : N → W'), Function.Surjective v → Function.Surjective w →
    ∀ (W : N → Bool → Bool → MvPolynomial ι F) (o : W' → Option ι),
    (∀ n x r, W n x r ∈ affIn (F := F) (o (w n))) → ∀ S : ℕ, κ * Fintype.card N ≤ S →
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧
      aeval M (G S) = ∑ x : V → Bool, ∑ r : W' → Bool, ∏ n, W n (x (v n)) (r (w n))

end Nc

namespace Nc.Price

open Ov Finset

variable {K : Type} [Field K] {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- The exponent g of the unit tensor with a leg at `π a` for every `a`: a spectral point has the value n ^ g at the
one of size n. -/
noncomputable def hexp (F : Spec K I) (π : A → I) : ℝ :=
  Real.logb 2 (F.F (Ten.push π (Ten.unit K A 2)))

/-- `t` is a sum of restrictions of the `b k` up to ε, with denominators at most ε ^ D: with local maps that are
polynomials in ε, the sum is ε ^ D * t + ε ^ (D + 1) * (anything). For D = 0 constant maps give the exact relation. -/
def BSum {κ : Type} [Fintype κ] (D : ℕ) (t : Ten K I) (b : κ → Ten K I) : Prop :=
  ∃ L : ∀ k p, t.ι p → (b k).ι p → Polynomial K, ∀ x, ∀ i ≤ D,
    (∑ k, ∑ y : ∀ p, (b k).ι p, (∏ p, L k p (x p) (y p)) * Polynomial.C ((b k).val y)).coeff i =
      if i = D then t.val x else 0

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": tensors

The subsection "Tensors". One theorem for every numbered statement, in the order of the paper and named by its label, and
one for every step of the running text that is used later. Tensors are arrays over a field K with one finite index set for
each party (Ov.Ten); tensors that are restrictions of one another (Ov.Ten.Equi) are not identified, instead a spectral point
has the same value on them (def_spectral_congr). The other subsections are in Paper/Gauges.lean, Paper/Extension.lean and
Paper/Prices.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-! ## Tensors -/

section Tensors

variable {J L : Type} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- "Tensors that are restrictions of each other are identified, so that the product is commutative, with unit the tensor
1"; it is also associative. -/
theorem tensor_mul_laws (s t u : Ten K I) :
    Equi (s * t) (t * s) ∧ Equi (s * t * u) (s * (t * u)) ∧ Equi (1 * t) t ∧ Equi (t * 1) t :=
  ⟨Equi.mul_comm s t, Equi.mul_assoc s t u, Equi.one_mul t, Equi.mul_one t⟩

/-- "Every nonzero t has 1 as a restriction". -/
theorem tensor_one_restr [Nonempty I] {t : Ten K I} (ht : ∃ x, t.val x ≠ 0) : Restr 1 t :=
  Restr.one_le ht.choose_spec

/-- "Every t is covered by finitely many copies of 1." -/
theorem tensor_covered_by_ones [Nonempty I] (t : Ten K I) : ∃ r : ℕ, SumRestr t fun _ : Fin r => (1 : Ten K I) :=
  ⟨_, (rankLE_card t).sumRestr⟩

/-- "Push-forward commutes with products". -/
theorem tensor_push_mul (π : J → I) (s t : Ten K J) : Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.push_mul π s t

/-- "Push-forward commutes with … compositions". -/
theorem tensor_push_comp (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.push_push π ρ t

/-- The push-forward along the identity does nothing. -/
theorem tensor_push_id (t : Ten K I) : Equi (Ten.push id t) t := Equi.push_id t

/-- "Push-forward … sends 1 to 1". -/
theorem tensor_push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 := Equi.push_one π

/-- "Push-forward … sends … covers to covers"; in particular restrictions to restrictions. -/
theorem tensor_push_cover (π : J → I) :
    (∀ {κ : Type} [Fintype κ] {s : Ten K J} {b : κ → Ten K J}, SumRestr s b →
      SumRestr (Ten.push π s) fun k => Ten.push π (b k)) ∧
    ∀ {s t : Ten K J}, Restr s t → Restr (Ten.push π s) (Ten.push π t) :=
  ⟨fun h => h.push π, fun h => h.push π⟩

end Tensors

/-- **Paper: Definition def:spectral.** "A spectral point on I is a function φ ≥ 0 on tensors with φ(1) = 1,
φ(st) = φ(s)φ(t), and φ(s) ≤ ∑ φ(t_j) whenever s is covered by t_1, …, t_r." -/
theorem def_spectral (φ : Ten K I → ℝ) :
    (∃ F : Spec K I, F.F = φ) ↔ (∀ t, 0 ≤ φ t) ∧ φ 1 = 1 ∧ (∀ s t, φ (s * t) = φ s * φ t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → φ s ≤ ∑ j, φ (t j) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.nonneg, F.one, F.mul, fun r s t h => F.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨φ, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- The text after the definition: "So φ(t) ≥ 1 if t ≠ 0, and φ(0) = 0 (the empty sum)." -/
theorem def_spectral_values [Nonempty I] (φ : Spec K I) (t : Ten K I) :
    ((∃ x, t.val x ≠ 0) → 1 ≤ φ.F t) ∧ ((∀ x, t.val x = 0) → φ.F t = 0) :=
  ⟨fun ⟨_, hx⟩ => φ.one_le hx, φ.zero⟩

/-- Tensors that are restrictions of each other are identified: a spectral point is monotone under restriction, so it has
the same value on them. -/
theorem def_spectral_congr (φ : Spec K I) {s t : Ten K I} :
    (Restr s t → φ.F s ≤ φ.F t) ∧ (Equi s t → φ.F s = φ.F t) :=
  ⟨φ.mono, φ.congr⟩

open Classical in
/-- The first example after Definition def:spectral: "An example is φ(t) = 1 for all t ≠ 0". -/
noncomputable def trivialPoint (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Spec K I where
  F t := if ∃ x, t.val x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  one := if_pos ⟨fun _ => (), one_ne_zero⟩
  mul s t := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · by_cases ht : ∃ x, t.val x ≠ 0
      · rw [if_pos hs, if_pos ht, if_pos, mul_one]
        obtain ⟨x, hx⟩ := hs
        obtain ⟨y, hy⟩ := ht
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
      · rw [if_neg ht, mul_zero, if_neg]
        rintro ⟨x, hx⟩
        exact ht ⟨fun p => (x p).2, right_ne_zero_of_mul hx⟩
    · rw [if_neg hs, zero_mul, if_neg]
      rintro ⟨x, hx⟩
      exact hs ⟨fun p => (x p).1, left_ne_zero_of_mul hx⟩
  le_sum {κ} _ s b h := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · rw [if_pos hs]
      obtain ⟨x, hx⟩ := hs
      obtain ⟨L, hL⟩ := h
      rw [hL] at hx
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      have h1 : ∃ x, (b k).val x ≠ 0 := ⟨y, right_ne_zero_of_mul hy⟩
      calc (1 : ℝ) = if ∃ x, (b k).val x ≠ 0 then 1 else 0 := (if_pos h1).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun k => if ∃ x, (b k).val x ≠ 0 then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

/-- The last example after Definition def:spectral: "φ^s is again a spectral point for 0 < s ≤ 1." -/
noncomputable def powerPoint (φ : Spec K I) (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : Spec K I where
  F t := φ.F t ^ s
  nonneg t := Real.rpow_nonneg (φ.nonneg t) s
  one := by rw [φ.one, Real.one_rpow]
  mul a b := by rw [φ.mul, Real.mul_rpow (φ.nonneg a) (φ.nonneg b)]
  le_sum {κ} _ a b h := by
    classical
    refine (Real.rpow_le_rpow (φ.nonneg a) (φ.le_sum a b h) h0.le).trans ?_
    have key : ∀ S : Finset κ, (∑ k ∈ S, φ.F (b k)) ^ s ≤ ∑ k ∈ S, φ.F (b k) ^ s := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [Real.zero_rpow h0.ne']
      | insert k S hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        exact (Real.rpow_add_le_add_rpow (φ.nonneg _) (Finset.sum_nonneg fun _ _ => φ.nonneg _) h0.le h1).trans
          (by gcongr)
    exact key Finset.univ

/-- Proof of Lemma lem:exponents: "The function q ↦ φ(⟨q⟩_P) is at least 1, multiplicative and monotone, hence a power of q."
The unit tensor has a leg at π a for every a; the exponent is Nc.Price.hexp. -/
theorem lem_exponents_power [Nonempty I] (φ : Spec K I) {A : Type} [Fintype A] [DecidableEq A] (π : A → I) :
    0 ≤ hexp φ π ∧ ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push π (Ten.unit K A q)) = (q : ℝ) ^ hexp φ π :=
  ⟨Real.logb_nonneg (by norm_num) (φ.one_le_unit π (by norm_num)), fun _ hq =>
    eq_rpow_of_mul_mono (fun n => φ.F (Ten.push π (Ten.unit K A n))) (fun _ h => φ.one_le_unit π h)
      (fun m n _ _ => by
        rw [(def_spectral_congr φ).2 ((Equi.unit_mul m n).push π), (def_spectral_congr φ).2 (tensor_push_mul _ _ _), φ.mul])
      (fun _ _ _ h => (def_spectral_congr φ).1 ((Restr.unit_mono h).push π)) _ hq⟩

/-- The case of a wire: φ(⟨q⟩_uv) = q ^ d_φ(u,v). -/
theorem lem_exponents_wire (φ : Spec K I) (u v : I) {q : ℕ} (hq : 1 ≤ q) :
    φ.F (Ten.wire K q u v) = (q : ℝ) ^ φ.e u v :=
  have : Nonempty I := ⟨u⟩
  (lem_exponents_power φ ![u, v]).2 q hq

theorem lem_exponents_wire_two (φ : Spec K I) (u v : I) : φ.F (Ten.wire K 2 u v) = 2 ^ φ.e u v := by
  have := lem_exponents_wire φ u v (q := 2) (by norm_num)
  exact_mod_cast this

/-- Proof of Lemma lem:exponents: "A wire of dimension q is covered by q copies of 1, so d_φ ≤ 1." (The cover and its
consequence φ(⟨q⟩_uv) ≤ q are Ov.Spec.unit_le.) Also d_φ ≥ 0, as for every exponent. -/
theorem lem_exponents_unit_interval (φ : Spec K I) (u v : I) : 0 ≤ φ.e u v ∧ φ.e u v ≤ 1 := by
  have : Nonempty I := ⟨u⟩
  refine ⟨(lem_exponents_power φ ![u, v]).1, ?_⟩
  have h : φ.F (Ten.wire K 2 u v) ≤ (2 : ℕ) := φ.unit_le ![u, v] 2
  rw [lem_exponents_wire_two] at h
  have h2 : (2 : ℝ) ^ φ.e u v ≤ 2 ^ (1 : ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h2

/-- "We put ⟨q⟩_uu = 1": a wire from u to u is a restriction of 1, so d_φ(u,u) = 0. -/
theorem lem_exponents_self (φ : Spec K I) (u : I) : φ.e u u = 0 := by
  have : Nonempty I := ⟨u⟩
  have h : φ.F (Ten.wire K 2 u u) = 1 := by
    refine le_antisymm ?_ (φ.one_le_unit ![u, u] (by norm_num))
    rw [← φ.one]
    exact (def_spectral_congr φ).1 (Restr.wire_self 2 u)
  rw [Spec.e, h, Real.logb_one]

/-- A wire has no direction. -/
theorem lem_exponents_symm (φ : Spec K I) (u v : I) : φ.e u v = φ.e v u := by
  rw [Spec.e, Spec.e, (def_spectral_congr φ).2 (Equi.wire_comm 2 u v)]

/-- Proof of Lemma lem:exponents: "Contracting the two indices at v shows that ⟨q⟩_uw is a restriction of ⟨q⟩_uv ⟨q⟩_vw". -/
theorem lem_exponents_contract (q : ℕ) (u v w : I) :
    Restr (Ten.wire K q u w) (Ten.wire K q u v * Ten.wire K q v w) :=
  Restr.wire_trans q u w v

/-- Proof of Lemma lem:exponents: "… this is the triangle inequality." -/
theorem lem_exponents_triangle (φ : Spec K I) (u v w : I) : φ.e u w ≤ φ.e u v + φ.e v w := by
  have h := φ.le_mul (lem_exponents_contract (K := K) 2 u v w)
  rw [lem_exponents_wire_two, lem_exponents_wire_two, lem_exponents_wire_two, ← Real.rpow_add (by norm_num)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

/-- Proof of Lemma lem:exponents: "Identifying the indices at every vertex in the same way shows that ⟨q⟩_P is a restriction of
the product of the wires on the edges of the tree." The unit tensor has a leg at π p for every vertex p ∈ A; the edge e joins
a e and b e; of the graph only connectedness is used, in the form that a function to Fin q that is constant along edges is
constant. -/
theorem lem_exponents_tree {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype E] [DecidableEq E] (q : ℕ)
    (π : A → I) (a b : E → A) (hconn : ∀ f : A → Fin q, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    Restr (Ten.push π (Ten.unit K A q)) (Ten.prod fun e => Ten.wire K q (π (a e)) (π (b e))) := by
  classical
  have key := Restr.of_edges π (ξ := fun o : Option A => o.elim (π (Classical.arbitrary A)) π) (Ten.unit K A q)
    (fun _ : E => Fin q) (fun e => some (a e)) (fun e => some (b e))
    (fun o x l => o.elim 1 fun p => ∏ e, if a e = p ∨ b e = p then (if l e = x p then (1 : K) else 0) else 1)
    (by
      rintro (_ | p) x x' l l' hx hl
      · rfl
      · refine Finset.prod_congr rfl fun e _ => ?_
        by_cases he : a e = p ∨ b e = p
        · have h2 : l e = l' e := hl e (he.imp (congrArg some) (congrArg some))
          have h3 : x p = x' p := hx p rfl
          rw [if_pos he, if_pos he, h2, h3]
        · rw [if_neg he, if_neg he])
    (by
      intro x
      refine Eq.trans ?_ (Fintype.sum_eq_single (fun e => (x (a e) : Fin q)) ?_).symm
      · rw [Fintype.prod_option]
        show _ = 1 * _
        rw [one_mul]
        by_cases h : ∀ i j, x i = x j
        · rw [Ten.unit_val_of h]
          refine (Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun e _ => ?_).symm
          exact (ite_eq_right_iff.2 fun _ => if_pos (h (a e) p))
        · rw [Ten.unit_val_not h]
          obtain ⟨e, he⟩ : ∃ e, x (a e) ≠ x (b e) := by
            by_contra hne
            push Not at hne
            exact h (hconn x hne)
          refine (Finset.prod_eq_zero (Finset.mem_univ (b e)) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)).symm
          exact (if_pos (Or.inr rfl)).trans (if_neg he)
      · intro l hl
        obtain ⟨e, he⟩ := Function.ne_iff.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (some (a e))) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)
        exact (if_pos (Or.inl rfl)).trans (if_neg he))
  simpa only [Fintype.card_fin, Option.elim_some] using key

/-- The consequence of lem_exponents_tree in exponents: g_φ(P) ≤ ∑ d_φ(e) over the edges. -/
theorem lem_exponents_tree_le [Nonempty I] (φ : Spec K I) {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E] (π : A → I) (a b : E → A)
    (hconn : ∀ f : A → Fin 2, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    hexp φ π ≤ ∑ e, φ.e (π (a e)) (π (b e)) := by
  rw [hexp, Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le (φ.one_le_unit π (by norm_num)))]
  refine (φ.le_prod (lem_exponents_tree 2 π a b hconn)).trans (le_of_eq ?_)
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Finset.prod_congr rfl fun e _ => lem_exponents_wire_two φ _ _

/-- **Paper: Lemma lem:exponents.** "Let φ be a spectral point on I. For every nonempty P ⊆ I there is g_φ(P) ≥ 0 with
φ(⟨q⟩_P) = q ^ g_φ(P) for all q ≥ 1. The function d_φ(u,v) = g_φ({u,v}), d_φ(u,u) = 0, is a pseudometric with values in
[0,1], and g_φ(P) ≤ ∑ d_φ(e) over the edges of any tree on P." The function d_φ is Ov.Spec.e. -/
theorem lem_exponents [Nonempty I] (φ : Spec K I) :
    ∃ g : Finset I → ℝ,
      (∀ P : Finset I, P.Nonempty → 0 ≤ g P ∧
        ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push (Subtype.val : P → I) (Ten.unit K P q)) = (q : ℝ) ^ g P) ∧
      (∀ u v, u ≠ v → φ.e u v = g {u, v}) ∧ (∀ u, φ.e u u = 0) ∧
      (∀ u v, φ.e u v = φ.e v u) ∧ (∀ u v w, φ.e u w ≤ φ.e u v + φ.e v w) ∧ (∀ u v, φ.e u v ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (P : Finset I) (G : SimpleGraph P) [DecidableRel G.Adj], G.IsTree →
        g P ≤ ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => φ.e u v, fun _ _ => lem_exponents_symm φ _ _⟩ (e.map Subtype.val) := by
  classical
  refine ⟨fun P => hexp φ (Subtype.val : P → I), fun P _ =>
    ⟨(lem_exponents_power φ _).1, (lem_exponents_power φ _).2⟩,
    fun u v _ => ?_, lem_exponents_self φ, lem_exponents_symm φ, lem_exponents_triangle φ,
    lem_exponents_unit_interval φ, ?_⟩
  · show hexp φ ![u, v] = hexp φ (Subtype.val : ({u, v} : Finset I) → I)
    have h : Set.range ![u, v] = Set.range (Subtype.val : ({u, v} : Finset I) → I) := by
      simp only [Matrix.range_cons, Matrix.range_empty, Subtype.range_coe_subtype]
      ext x
      simp [or_comm]
    rw [hexp, hexp, (def_spectral_congr φ).2 (Ten.Equi.push_unit_congr _ _ h 2)]
  · intro P G _ hT
    have : Nonempty P := hT.connected.nonempty
    refine (lem_exponents_tree_le φ (Subtype.val : P → I) (E := G.edgeFinset)
      (fun e => e.1.out.1) (fun e => e.1.out.2) fun f hf p q => ?_).trans (le_of_eq ?_)
    · obtain ⟨w⟩ := hT.connected.preconnected p q
      induction w with
      | nil => rfl
      | @cons u v _ hadj _ ih =>
        refine Eq.trans ?_ ih
        have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hadj
        have h1 : f (s(u, v) : Sym2 P).out.1 = f (s(u, v) : Sym2 P).out.2 := hf ⟨_, hmem⟩
        have h2 : (s((s(u, v) : Sym2 P).out.1, (s(u, v) : Sym2 P).out.2) : Sym2 P) = s(u, v) := Quot.out_eq _
        rcases Sym2.eq_iff.1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at h1
        exacts [h1, h1.symm]
    · rw [← Finset.sum_coe_sort G.edgeFinset]
      refine Finset.sum_congr rfl fun e _ => ?_
      conv_rhs => rw [← Quot.out_eq e.1]
      rfl

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges on a commutative monoid with a covering relation

Let M be a commutative monoid (the tensors up to equivalence) with a relation "t is covered by the finite
family b" (t is a sum of restrictions of the members of b). A gauge is a function p ≥ 0 on M with p(1) = 1,
p(st) ≤ p(s)p(t), and p(t) ≤ ∑ p(b) whenever b covers t. This file has the definitions, infima of directed families of
gauges (`isPre_iInf`, `keeps_iInf`), and the first facts on the numbers a with p(tⁿ) ≤ C·aⁿ (`IsPre.rad`). The proof of
Proposition prop:gauge is in Paper/Gauges.lean.
-/

namespace Ov.Duality

variable {M : Type*} [CommMonoid M]

/-- A covering relation between elements and finite families of elements: reflexive, transitive,
and compatible with multiplication by an element. -/
structure Cover (M : Type*) [CommMonoid M] where
  /-- the element is covered by the family -/
  cov : ∀ {κ : Type} [Fintype κ], M → (κ → M) → Prop
  refl : ∀ t, cov t (fun _ : Unit => t)
  bind : ∀ {κ : Type} [Fintype κ] {μ : κ → Type} [∀ k, Fintype (μ k)] {t : M} {b : κ → M}
    {c : ∀ k, μ k → M}, cov t b → (∀ k, cov (b k) (c k)) → cov t (fun x : Σ k, μ k => c x.1 x.2)
  mul : ∀ {κ : Type} [Fintype κ] {t : M} {b : κ → M} (s : M), cov t b →
    cov (t * s) (fun k => b k * s)

/-- The function p is a gauge: p ≥ 0, p(1) = 1, submultiplicative,
and subadditive under covers. -/
structure IsPre (D : Cover M) (p : M → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → p t ≤ ∑ k, p (b k)

/-- The inequality p(tx) ≤ c·p(ty) for all t. -/
def Keeps (p : M → ℝ) (x y : M) (c : ℝ) : Prop := ∀ t, p (t * x) ≤ c * p (t * y)

variable {D : Cover M} {p : M → ℝ}

omit [CommMonoid M] in
/-- For finitely many elements, one member of a directed family is close to its infimum. -/
theorem le_iInf_add {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    {q : M → ℝ} (hq : ∀ t, q t = ⨅ i, P i t) {ε : ℝ} (hε : 0 < ε) (b : Finset M) :
    ∃ i, ∀ t ∈ b, P i t ≤ q t + ε := by
  classical
  induction b using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a b _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt (show ⨅ i, P i a < q a + ε by rw [← hq]; linarith)
    obtain ⟨k, hki, hkj⟩ := dir i j
    refine ⟨k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact (hkj t).trans hj.le
    · exact (hki t).trans (hi t ht)

/-- A directed infimum of functions P i is a gauge if each of them is, where instead of
P i (st) ≤ P i (s)·P i (t) it is enough that P j (st) ≤ P i (s)·P i (t) for some j. -/
theorem isPre_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (nonneg : ∀ i t, 0 ≤ P i t) (one : ∀ i, P i 1 = 1)
    (mul_le : ∀ i s t, ∃ j, P j (s * t) ≤ P i s * P i t)
    (le_sum : ∀ i, ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b →
      P i t ≤ ∑ k, P i (b k)) :
    IsPre D (fun t => ⨅ i, P i t) := by
  classical
  have bdd : ∀ t, BddBelow (Set.range fun i => P i t) := fun t =>
    ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩
  have hle : ∀ i t, ⨅ j, P j t ≤ P i t := fun i t => ciInf_le (bdd t) i
  have h0 : ∀ t, 0 ≤ ⨅ i, P i t := fun t => le_ciInf fun i => nonneg i t
  refine ⟨h0, ?_, ?_, ?_⟩
  · simp [one]
  · intro s t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := ⨅ i, P i s with hA
    set B := ⨅ i, P i t with hB
    have hA0 : 0 ≤ A := h0 s
    have hB0 : 0 ≤ B := h0 t
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε {s, t}
    have h1 := hi s (by simp)
    have h2 := hi t (by simp)
    obtain ⟨j, hj⟩ := mul_le i s t
    have h3 : P i s * P i t ≤ (A + ε) * (B + ε) :=
      mul_le_mul h1 h2 (nonneg _ _) (by positivity)
    have h4 := hle j (s * t)
    nlinarith
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε
      (Finset.univ.image b)
    have h1 : ∑ k, P i (b k) ≤ ∑ k, ((⨅ i, P i (b k)) + ε) :=
      Finset.sum_le_sum fun k _ => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h3 := (hle i t).trans (le_sum i t b hb)
    linarith

theorem keeps_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (nonneg : ∀ i t, 0 ≤ P i t)
    {x y : M} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, Keeps (P i) x y c) :
    Keeps (fun t => ⨅ i, P i t) x y c := by
  intro t
  rw [Real.mul_iInf_of_nonneg hc]
  refine le_ciInf fun i => (ciInf_le ⟨0, ?_⟩ i).trans (h i t)
  rintro _ ⟨i, rfl⟩
  exact nonneg i _

namespace IsPre

theorem pow_le (h : IsPre D p) (t : M) (n : ℕ) : p (t ^ n) ≤ p t ^ n := by
  induction n with
  | zero => simp [h.one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (h.mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (h.nonneg _))

/-- The numbers a > 0 for which there is a C with p(t^m) ≤ C·a^m for all m. Their infimum is the
spectral radius of p at t. -/
def rad (p : M → ℝ) (t : M) : Set ℝ := {a | 0 < a ∧ ∃ C : ℝ, ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m}

theorem rad_const_pos (h : IsPre D p) {t : M} {a C : ℝ} (hC : ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m) :
    1 ≤ C := by simpa [h.one] using hC 0

theorem rad_mono (h : IsPre D p) {t : M} {a b : ℝ} (ha : a ∈ rad p t) (hab : a ≤ b) :
    b ∈ rad p t := by
  obtain ⟨ha0, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  refine ⟨ha0.trans_le hab, C, fun m => (hC m).trans ?_⟩
  gcongr

theorem rad_bdd (p : M → ℝ) (t : M) : BddBelow (rad p t) := ⟨0, fun _ ha => ha.1.le⟩

theorem mem_rad (h : IsPre D p) (t : M) {δ : ℝ} (hδ : 0 < δ) : p t + δ ∈ rad p t :=
  ⟨by linarith [h.nonneg t], 1, fun m => by
    rw [one_mul]
    exact (h.pow_le t m).trans (pow_le_pow_left₀ (h.nonneg t) (by linarith) m)⟩

theorem mem_rad_of_lt (h : IsPre D p) {t : M} {a : ℝ} (ha : sInf (rad p t) < a) :
    a ∈ rad p t := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt ⟨_, h.mem_rad t one_pos⟩ ha
  exact h.rad_mono hb hba.le

/-- The bound for a product of powers, by the bounds for the powers. -/
theorem prod_bound (h : IsPre D p) (S : Finset M) (a C : M → ℝ)
    (ha : ∀ y, 0 < a y) (hC : ∀ y, ∀ m : ℕ, p (y ^ m) ≤ C y * a y ^ m) (e : M → ℕ) :
    p (∏ y ∈ S, y ^ e y) ≤ (∏ y ∈ S, C y) * ∏ y ∈ S, a y ^ e y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [h.one]
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.prod_insert hy, Finset.prod_insert hy]
    have h1 := mul_le_mul (hC y (e y)) ih (h.nonneg _)
      (mul_nonneg (zero_le_one.trans (h.rad_const_pos (hC y))) (pow_nonneg (ha y).le _))
    calc _ ≤ _ := (h.mul_le _ _).trans h1
      _ = _ := by ring

end IsPre

end Ov.Duality
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges as infima of weights

For an abstract commutative monoid with a covering relation: a function that is defined as the infimum of the weights of
certificates is a gauge, if certificates can be multiplied and added along covers. Used for Theorem thm:duality
(`Paper/Gauges.lean`) and Proposition prop:extend (`Paper/Extension.lean`).
-/

namespace Ov.Duality

open Finset

variable {M : Type*} [CommMonoid M] {D : Cover M}

theorem le_sInf_mul_sInf {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (hS0 : ∀ a ∈ S, 0 ≤ a) (hT0 : ∀ b ∈ T, 0 ≤ b) {x : ℝ} (h : ∀ a ∈ S, ∀ b ∈ T, x ≤ a * b) :
    x ≤ sInf S * sInf T := by
  have key : ∀ {S : Set ℝ} (_ : S.Nonempty) {b : ℝ} (_ : 0 ≤ b), (∀ a ∈ S, x ≤ a * b) →
      x ≤ sInf S * b := by
    intro S hS b hb h
    rcases hb.eq_or_lt with rfl | hb
    · obtain ⟨a, ha⟩ := hS
      simpa using h a ha
    · rw [← div_le_iff₀ hb]
      exact le_csInf hS fun a ha => (div_le_iff₀ hb).2 (h a ha)
  rw [mul_comm]
  refine key hT (Real.sInf_nonneg hS0) fun b hb => ?_
  rw [mul_comm]
  exact key hS (hT0 b hb) fun a ha => h a ha b hb

/-- Let S t be sets of numbers ≥ 0, the weights of the certificates for t. Their infimum is a gauge
if certificates can be multiplied and put together along covers, 1 has a certificate of weight
1, and none of a weight below 1. -/
theorem isPre_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    (h1 : (1 : ℝ) ∈ S 1) (h1' : ∀ w ∈ S 1, 1 ≤ w)
    (hmul : ∀ s t, ∀ a ∈ S s, ∀ b ∈ S t, a * b ∈ S (s * t))
    (hsum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → ∀ w : κ → ℝ,
      (∀ k, w k ∈ S (b k)) → ∃ w' ∈ S t, w' ≤ ∑ k, w k) :
    IsPre D (fun t => sInf (S t)) := by
  have bdd : ∀ t, BddBelow (S t) := fun t => ⟨0, fun _ hw => h0 t _ hw⟩
  refine ⟨fun t => Real.sInf_nonneg (h0 t), ?_, ?_, ?_⟩
  · exact le_antisymm (csInf_le (bdd 1) h1) (le_csInf (hne 1) h1')
  · intro s t
    exact le_sInf_mul_sInf (hne s) (hne t) (h0 s) (h0 t) fun a ha b hb =>
      csInf_le (bdd _) (hmul s t a ha b hb)
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    have hex : ∀ k, ∃ w ∈ S (b k), w < sInf (S (b k)) + ε := fun k =>
      exists_lt_of_csInf_lt (hne _) (by linarith)
    choose w hw hw' using hex
    obtain ⟨w', hw'S, hle⟩ := hsum t b hb w hw
    have h2 : ∑ k, w k ≤ ∑ k, (sInf (S (b k)) + ε) := Finset.sum_le_sum fun k _ => (hw' k).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h4 := csInf_le (bdd t) hw'S
    linarith

theorem keeps_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    {x y : M} {c : ℝ} (hc : 0 < c) (h : ∀ t, ∀ w ∈ S (t * y), c * w ∈ S (t * x)) :
    Keeps (fun t => sInf (S t)) x y c := by
  intro t
  have h2 : sInf (S (t * x)) / c ≤ sInf (S (t * y)) := by
    refine le_csInf (hne _) fun a ha => ?_
    rw [div_le_iff₀ hc]
    exact (csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (h t a ha)).trans (mul_comm _ _).le
  rw [div_le_iff₀ hc] at h2
  exact h2.trans (mul_comm _ _).le

/-- Covers can be multiplied. -/
theorem Cover.mul_mul (D : Cover M) {κ κ' : Type} [Fintype κ] [Fintype κ'] {s t : M} {b : κ → M}
    {c : κ' → M} (h : D.cov s b) (h' : D.cov t c) :
    D.cov (s * t) (fun x : Σ _ : κ, κ' => b x.1 * c x.2) := by
  refine D.bind (b := fun k => b k * t) (c := fun k j => b k * c j) (D.mul t h) fun k => ?_
  have := D.mul (b k) h'
  simpa only [mul_comm _ (b k)] using this

end Ov.Duality
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges

A gauge (in Lean: `PreSpec`) is what a spectral point becomes when "multiplicative"
is weakened to "submultiplicative". Such a function is easy to write down, as an infimum over
certificates; `Paper.prop_gauge` finds a spectral point below it.
(Paper: the subsection "Gauges". The zero tensor is covered by the empty family, so a gauge is 0 at it.)
-/

namespace Ov

/-- A gauge on the parties I: a real function p ≥ 0 on tensors with p(1) = 1,
p(st) ≤ p(s)p(t), and p(s) ≤ ∑ p(b k) whenever s is a sum of restrictions of the b k. -/
structure PreSpec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  p : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b →
    p s ≤ ∑ k, p (b k)

namespace PreSpec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- A gauge is monotone under restriction. -/
theorem mono (P : PreSpec K I) {s t : Ten K I} (h : Ten.Restr s t) : P.p s ≤ P.p t := by
  obtain ⟨L, hL⟩ := h
  have h1 : Ten.SumRestr s (fun _ : Unit => t) := ⟨fun _ => L, fun x => by simpa using hL x⟩
  simpa using P.le_sum s _ h1

end PreSpec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Tensors up to equivalence

Tensors that are restrictions of one another are identified; their classes form a commutative monoid with a covering
relation (`Ov.Duality.Abstract`). The proofs of Proposition prop:gauge and Theorem thm:duality (`Paper/Gauges.lean`) and of
Proposition prop:extend (`Paper/Extension.lean`) work there.
-/

namespace Ov

open Finset Duality

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

namespace Duality

/-- Tensors up to equivalence. -/
def tenSetoid (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Setoid (Ten K I) where
  r := Ten.Equi
  iseqv := ⟨Ten.Equi.refl, Ten.Equi.symm, Ten.Equi.trans⟩

/-- The classes of tensors over I under equivalence. -/
def Cls (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Type 1 :=
  Quotient (tenSetoid K I)

/-- The class of a tensor. -/
def cls (t : Ten K I) : Cls K I := Quotient.mk (tenSetoid K I) t

theorem cls_eq {s t : Ten K I} : cls s = cls t ↔ Ten.Equi s t :=
  ⟨fun h => Quotient.exact (s := tenSetoid K I) h, fun h => Quotient.sound (s := tenSetoid K I) h⟩

/-- A tensor of a given class. -/
noncomputable def rep (m : Cls K I) : Ten K I := Quotient.out (s := tenSetoid K I) m

@[simp] theorem cls_rep (m : Cls K I) : cls (rep m) = m := Quotient.out_eq _

theorem rep_cls (t : Ten K I) : Ten.Equi (rep (cls t)) t := cls_eq.1 (cls_rep _)

/-- The classes form a commutative monoid under the product. -/
noncomputable instance : CommMonoid (Cls K I) where
  one := cls 1
  mul x y := cls (rep x * rep y)
  mul_assoc x y z := by
    refine cls_eq.2 ?_
    exact (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.mul_assoc _ _ _)).trans
      ((Ten.Equi.refl _).mul (rep_cls _).symm)
  one_mul x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.one_mul _))
  mul_one x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((Ten.Equi.refl _).mul (rep_cls _)).trans (Ten.Equi.mul_one _))
  mul_comm x y := cls_eq.2 (Ten.Equi.mul_comm _ _)

theorem cls_one : cls (1 : Ten K I) = 1 := rfl

theorem cls_mul (s t : Ten K I) : cls (s * t) = cls s * cls t :=
  cls_eq.2 ((rep_cls s).symm.mul (rep_cls t).symm)

theorem cls_kpow (t : Ten K I) (n : ℕ) : cls (Ten.kpow t n) = cls t ^ n := by
  induction n with
  | zero => rw [pow_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.kpow_zero t)
  | succ n ih => rw [pow_succ', ← ih, ← cls_mul]; exact cls_eq.2 (Ten.Equi.kpow_succ t n)

/-- The covering relation on classes: sums of restrictions. -/
noncomputable def tenCover (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] :
    Cover (Cls K I) where
  cov t b := Ten.SumRestr (rep t) (fun k => rep (b k))
  refl t := (Ten.Restr.refl _).sumRestr
  bind h h' := h.bind h'
  mul {κ _ t b} s h := by
    have h1 : Ten.SumRestr (rep t * rep s) (fun k => rep (b k) * rep s) := by
      have h2 := (h.mul (Ten.Restr.refl (rep s)).sumRestr).reindex (Equiv.prodPUnit κ).symm
      exact h2
    exact ((rep_cls _).1.trans_sum h1).mono fun k => (rep_cls _).2

theorem tenCover_cov {κ : Type} [Fintype κ] {t : Ten K I} {b : κ → Ten K I} :
    (tenCover K I).cov (cls t) (fun k => cls (b k)) ↔ Ten.SumRestr t b :=
  ⟨fun h => ((rep_cls t).2.trans_sum h).mono fun k => (rep_cls (b k)).1,
    fun h => ((rep_cls t).1.trans_sum h).mono fun k => (rep_cls (b k)).2⟩

/-- Equivalent tensors have the same value. -/
theorem _root_.Ov.PreSpec.congr (P : PreSpec K I) {s t : Ten K I} (h : Ten.Equi s t) :
    P.p s = P.p t := le_antisymm (P.mono h.1) (P.mono h.2)

/-- A gauge as a function on classes. -/
noncomputable def onCls (P : PreSpec K I) (m : Cls K I) : ℝ := P.p (rep m)

@[simp] theorem onCls_cls (P : PreSpec K I) (t : Ten K I) : onCls P (cls t) = P.p t :=
  P.congr (rep_cls t)

theorem isPre_onCls (P : PreSpec K I) : IsPre (tenCover K I) (onCls P) where
  nonneg _ := P.nonneg _
  one := by rw [← cls_one, onCls_cls, P.one]
  mul_le s t := by
    rw [← cls_rep s, ← cls_rep t, ← cls_mul, onCls_cls, onCls_cls, onCls_cls]
    exact P.mul_le _ _
  le_sum t b h := P.le_sum _ _ h

/-- The gauge given by a function on classes. -/
def ofCls {q : Cls K I → ℝ} (h : IsPre (tenCover K I) q) : PreSpec K I where
  p t := q (cls t)
  nonneg _ := h.nonneg _
  one := h.one
  mul_le s t := by rw [cls_mul]; exact h.mul_le _ _
  le_sum s b hb := h.le_sum _ _ (tenCover_cov.2 hb)

theorem keeps_onCls {P : PreSpec K I} {x y : Ten K I} {c : ℝ} (h : ∀ t, P.p (t * x) ≤ c * P.p (t * y)) :
    Duality.Keeps (onCls P) (cls x) (cls y) c := by
  intro m
  rw [← cls_rep m, ← cls_mul, ← cls_mul, onCls_cls, onCls_cls]
  exact h _

end Duality

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Certificates

For the proof of Theorem thm:duality (`Paper/Gauges.lean`), in a commutative monoid with a covering relation, with an
element C and a finite family of elements A β: certificates, their products and sums.
-/

namespace Nc.Price

open Ov Ov.Duality Finset

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- A product of the members of a family. -/
def mon (A : B → M) (v : B → ℕ) : M := ∏ β, A β ^ v β

theorem mon_zero (A : B → M) : mon A (fun _ => 0) = 1 := by simp [mon]

theorem mon_add (A : B → M) (v w : B → ℕ) : mon A (fun β => v β + w β) = mon A v * mon A w := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

theorem mon_single [DecidableEq B] (A : B → M) (β : B) (n : ℕ) :
    mon A (fun γ => if γ = β then n else 0) = A β ^ n := by
  rw [mon, Finset.prod_eq_single β]
  · simp
  · intro γ _ h
    simp [h]
  · simp

/-- A certificate of level k and weight at most W for t: t·C^k is covered by products
C^u·∏A^v with u + Σv = k, and the numbers η^(Σv) add up to at most W. -/
def Cert (D : Cover M) (C : M) (A : B → M) (η : ℝ) (t : M) (k : ℕ) (W : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k) ∧
    D.cov (t * C ^ k) (fun j => C ^ u j * mon A (v j)) ∧ ∑ j, η ^ (∑ β, v j β) ≤ W

namespace Cert

variable {C : M} {A : B → M} {η : ℝ} {s t : M} {k l : ℕ} {W V : ℝ}

theorem nonneg (hη : 0 < η) (h : Cert D C A η t k W) : 0 ≤ W := by
  obtain ⟨κ, _, u, v, -, -, hW⟩ := h
  exact (Finset.sum_nonneg fun j _ => by positivity).trans hW

theorem one (k : ℕ) : Cert D C A η 1 k 1 :=
  ⟨Unit, inferInstance, fun _ => k, fun _ _ => 0, by simp,
    by simpa [mon_zero] using D.refl (C ^ k), by simp⟩

theorem mul (hη : 0 < η) (h : Cert D C A η s k W) (h' : Cert D C A η t l V) :
    Cert D C A η (s * t) (k + l) (W * V) := by
  have hW0 := h.nonneg hη
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  obtain ⟨κ', _, u', v', hu', hc', hW'⟩ := h'
  refine ⟨Σ _ : κ, κ', inferInstance, fun x => u x.1 + u' x.2, fun x β => v x.1 β + v' x.2 β,
    fun x => ?_, ?_, ?_⟩
  · have h1 := hu x.1
    have h2 := hu' x.2
    rw [Finset.sum_add_distrib]
    dsimp only
    omega
  · have h1 := D.mul_mul hc hc'
    have e1 : s * t * C ^ (k + l) = s * C ^ k * (t * C ^ l) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [e1]
    convert h1 using 2 with x
    rw [mon_add, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  · rw [Fintype.sum_sigma]
    calc ∑ j, ∑ j', η ^ (∑ β, (v j β + v' j' β)) =
        (∑ j, η ^ (∑ β, v j β)) * ∑ j', η ^ (∑ β, v' j' β) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [← pow_add, Finset.sum_add_distrib]
      _ ≤ W * V := mul_le_mul hW hW' (Finset.sum_nonneg fun j _ => by positivity) hW0

theorem raise (hη : 0 < η) (h : Cert D C A η t k W) (hkl : k ≤ l) : Cert D C A η t l W := by
  have h1 := h.mul hη (one (D := D) (C := C) (A := A) (η := η) (l - k))
  rwa [mul_one, mul_one, Nat.add_sub_cancel' hkl] at h1

theorem cover {κ : Type} [Fintype κ] {b : κ → M} {W : κ → ℝ} (h : D.cov t b)
    (hb : ∀ j, Cert D C A η (b j) k (W j)) : Cert D C A η t k (∑ j, W j) := by
  choose μ i u v hu hc hW using hb
  refine ⟨Σ j, μ j, inferInstance, fun x => u x.1 x.2, fun x => v x.1 x.2,
    fun x => hu _ _, D.bind (b := fun j => b j * C ^ k) (D.mul _ h) hc, ?_⟩
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum fun j _ => hW j

theorem mul_gen (hη : 0 < η) (β : B) (h : Cert D C A η (t * C) k W) :
    Cert D C A η (t * A β) (k + 1) (η * W) := by
  classical
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  have hs : ∀ j, ∑ γ, (v j γ + if γ = β then 1 else 0) = ∑ γ, v j γ + 1 := fun j => by
    rw [Finset.sum_add_distrib]; simp
  refine ⟨κ, inferInstance, u, fun j γ => v j γ + if γ = β then 1 else 0,
    fun j => by have := hu j; rw [hs]; omega, ?_, ?_⟩
  · have h1 := D.mul (A β) hc
    have e1 : t * A β * C ^ (k + 1) = t * C * C ^ k * A β := by rw [pow_succ]; ac_rfl
    rw [e1]
    convert h1 using 2 with j
    rw [mon_add, mon_single, pow_one, mul_assoc]
  · calc ∑ j, η ^ (∑ γ, (v j γ + if γ = β then 1 else 0)) = η * ∑ j, η ^ (∑ γ, v j γ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hs, ← pow_succ']
      _ ≤ η * W := by gcongr

end Cert

section Tensors

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

theorem cls_prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    cls (Ten.prod b) = ∏ k, cls (b k) := by
  have key : ∀ {n : ℕ} (b : Fin n → Ten K I), cls (Ten.prod b) = ∏ k, cls (b k) := by
    intro n
    induction n with
    | zero => intro b; rw [Fin.prod_univ_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.prod_empty b)
    | succ n ih =>
      intro b
      rw [Fin.prod_univ_succ, ← ih, ← cls_mul]
      exact cls_eq.2 (Ten.Equi.prod_fin_succ b)
  rw [cls_eq.2 (Ten.Equi.prod_reindex b (Fintype.equivFin κ).symm), key]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

theorem cls_mon [DecidableEq B] (A : B → Ten K I) (v : B → ℕ) :
    mon (fun β => cls (A β)) v = cls (Ten.prod fun β => Ten.kpow (A β) (v β)) := by
  rw [cls_prod]
  exact Finset.prod_congr rfl fun β _ => (cls_kpow _ _).symm

end Tensors

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": gauges and duality

The subsection "Gauges": Proposition prop:gauge and Theorem thm:duality, with the steps of their proofs. Both proofs are
carried out in the commutative monoid of the classes of tensors (Ov.Duality.Cls) with its covering relation.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Ov.Duality.IsPre Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- "A gauge on I is a function p ≥ 0 on tensors with p(1) = 1, p(st) ≤ p(s)p(t) and p(s) ≤ ∑ p(t_j) whenever s is covered by
the t_j." -/
theorem def_gauge (p : Ten K I → ℝ) :
    (∃ P : PreSpec K I, P.p = p) ↔ (∀ t, 0 ≤ p t) ∧ p 1 = 1 ∧ (∀ s t, p (s * t) ≤ p s * p t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → p s ≤ ∑ j, p (t j) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.nonneg, P.one, P.mul_le, fun r s t h => P.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨p, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

section Monoid

/-! The proof of Proposition prop:gauge, for a commutative monoid M with a covering relation D (for us: the classes of
tensors). A gauge on M is a function with Ov.Duality.IsPre; Ov.Duality.Keeps p x y c says that p keeps (x, y, c). -/

variable {M : Type*} [CommMonoid M] {D : Cover M} {p : M → ℝ}

/-- Proof of Proposition prop:gauge: "The gauges below the given one that keep its triples are closed under infima of
chains." The infimum of a chain (or a directed family) of gauges is a gauge below them that keeps every triple which all
of them keep. -/
theorem prop_gauge_chain {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (hP : ∀ i, IsPre D (P i)) :
    IsPre D (fun t => ⨅ i, P i t) ∧ (∀ i t, ⨅ j, P j t ≤ P i t) ∧
      ∀ x y c, 0 ≤ c → (∀ i, Keeps (P i) x y c) → Keeps (fun t => ⨅ i, P i t) x y c :=
  ⟨isPre_iInf dir (fun i => (hP i).nonneg) (fun i => (hP i).one) (fun i s t => ⟨i, (hP i).mul_le s t⟩)
      (fun i _ _ t b hb => (hP i).le_sum t b hb),
    fun i t => ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact (hP j).nonneg t⟩ i,
    fun _ _ _ hc h => keeps_iInf (fun i => (hP i).nonneg) hc h⟩

/-- Proof of Proposition prop:gauge: "By Zorn's lemma there is a minimal one, p": a gauge below p₀ that keeps the triples of
p₀, and that is equal to every such gauge below it. -/
theorem prop_gauge_minimal {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ p : M → ℝ, IsPre D p ∧ (∀ t, p t ≤ p₀ t) ∧ (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c) ∧
      ∀ q : M → ℝ, IsPre D q → (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps q x y c) → (∀ t, q t ≤ p t) →
        ∀ t, q t = p t := by
  set Q : Set (M → ℝ)ᵒᵈ := {q | IsPre D (OrderDual.ofDual q) ∧
    ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps (OrderDual.ofDual q) x y c} with hQ
  obtain ⟨m, hm0, hmax⟩ := zorn_le_nonempty₀ Q (by
    intro c hcQ hchain y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    obtain ⟨h1, h2, h3⟩ := prop_gauge_chain (D := D) (P := fun i : c => OrderDual.ofDual i.1) (by
      intro i j
      rcases hchain.total i.2 j.2 with hij | hij
      · exact ⟨j, hij, le_refl _⟩
      · exact ⟨i, le_refl _, hij⟩) fun i => (hcQ i.2).1
    exact ⟨OrderDual.toDual (fun t => ⨅ i : c, (OrderDual.ofDual i.1) t),
      ⟨h1, fun x y c hc hk => h3 x y c hc fun i => (hcQ i.2).2 x y c hc hk⟩, fun z hz t => h2 ⟨z, hz⟩ t⟩)
    (OrderDual.toDual p₀) ⟨h₀, fun _ _ _ _ hk => hk⟩
  refine ⟨OrderDual.ofDual m, hmax.1.1, hm0, hmax.1.2, fun q h1 h2 h3 t => ?_⟩
  have h4 : OrderDual.ofDual m ≤ q := hmax.2 (y := OrderDual.toDual q) ⟨h1, h2⟩ h3
  exact le_antisymm (h3 t) (h4 t)

/-- Proof of Proposition prop:gauge, for r(t) = inf p(tⁿ)^(1/n): "If s is covered by t_1, …, t_l, then sⁿ is covered by their
words of length n; grouping these … and bounding p(t_jᵃ) ≤ c_δ (r(t_j) + δ)ᵃ gives r(s) ≤ ∑ r(t_j)." In Lean r(t) is the infimum
of the a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n (Ov.Duality.IsPre.rad; it is the printed number by prop_gauge_radius_eq),
and the words are bounded by induction on n. -/
theorem prop_gauge_radius_cover (h : IsPre D p) {κ : Type} [Fintype κ] (t : M) (b : κ → M) (hb : D.cov t b) :
    sInf (rad p t) ≤ ∑ k, sInf (rad p (b k)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Fintype.card κ + 1) with hεd
  have hε : 0 < ε := by positivity
  set a : M → ℝ := fun y => sInf (rad p y) + ε with ha
  have ha0 : ∀ y, 0 < a y := fun y => by have := h0 y; simp only [ha]; linarith
  have hmem : ∀ y, ∃ C : ℝ, ∀ m : ℕ, p (y ^ m) ≤ C * a y ^ m := fun y =>
    (h.mem_rad_of_lt (show sInf (rad p y) < a y by simp only [ha]; linarith)).2
  choose C hC using hmem
  set S := Finset.univ.image b with hS
  set A := ∑ k, a (b k) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => (ha0 _).le
  have key : ∀ n : ℕ, ∀ e : M → ℕ, p ((∏ y ∈ S, y ^ e y) * t ^ n) ≤
      (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n := by
    intro n
    induction n with
    | zero => intro e; simpa using h.prod_bound S a C ha0 hC e
    | succ n ih =>
      intro e
      have h1 := h.le_sum _ _ (D.mul ((∏ y ∈ S, y ^ e y) * t ^ n) hb)
      have h2 : t * ((∏ y ∈ S, y ^ e y) * t ^ n) = (∏ y ∈ S, y ^ e y) * t ^ (n + 1) := by
        rw [pow_succ', mul_left_comm]
      rw [h2] at h1
      refine h1.trans ?_
      have h3 : ∀ k, p (b k * ((∏ y ∈ S, y ^ e y) * t ^ n)) ≤
          (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n * a (b k) := by
        intro k
        set y := b k with hy
        have hyS : y ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have h4 := ih (fun z => if z = y then e z + 1 else e z)
        have e1 : ∏ z ∈ S, z ^ (if z = y then e z + 1 else e z) =
            y * ∏ z ∈ S, z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS, ← Finset.mul_prod_erase S (fun z => z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        have e2 : ∏ z ∈ S, a z ^ (if z = y then e z + 1 else e z) =
            a y * ∏ z ∈ S, a z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS,
            ← Finset.mul_prod_erase S (fun z => a z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        rw [e1, e2] at h4
        rw [← mul_assoc]
        refine h4.trans (le_of_eq ?_)
        ring
      refine (Finset.sum_le_sum fun k _ => h3 k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, ← hA]
      ring
  have h5 : sInf (rad p t) ≤ A + ε := by
    refine csInf_le (rad_bdd p t) ⟨by linarith, ∏ y ∈ S, C y, fun m => ?_⟩
    have h6 := key m (fun _ => 0)
    simp only [pow_zero, Finset.prod_const_one, one_mul, mul_one] at h6
    refine h6.trans ?_
    have : (0 : ℝ) ≤ ∏ y ∈ S, C y :=
      Finset.prod_nonneg fun y _ => zero_le_one.trans (h.rad_const_pos (hC y))
    gcongr
    linarith
  have h7 : A = ∑ k, sInf (rad p (b k)) + Fintype.card κ * ε := by
    rw [hA, ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h8 : ((Fintype.card κ : ℝ) + 1) * ε = δ := by rw [hεd]; field_simp
  linarith

/-- Proof of Proposition prop:gauge: r is a gauge. "Clearly r(1) = 1 and r(st) ≤ r(s)r(t)"; for covers see
prop_gauge_radius_cover. -/
theorem prop_gauge_radius (h : IsPre D p) : IsPre D (fun t => sInf (rad p t)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine ⟨h0, le_antisymm ?_ ?_, ?_, fun t b hb => prop_gauge_radius_cover h t b hb⟩
  · refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p 1) ?_
    simpa [h.one] using h.mem_rad 1 hδ
  · refine le_csInf ⟨_, h.mem_rad 1 one_pos⟩ ?_
    rintro a ⟨ha, C, hC⟩
    by_contra hlt
    rw [not_le] at hlt
    have hC1 := h.rad_const_pos hC
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / C by positivity) hlt
    have := hC m
    rw [one_pow, h.one] at this
    rw [lt_div_iff₀ (by positivity)] at hm
    linarith
  · intro s t
    have key : ∀ a ∈ rad p s, ∀ b ∈ rad p t, sInf (rad p (s * t)) ≤ a * b := by
      rintro a ⟨ha, C, hC⟩ b ⟨hb, C', hC'⟩
      refine csInf_le (rad_bdd p _) ⟨by positivity, C * C', fun m => ?_⟩
      rw [mul_pow, mul_pow]
      have h1 := h.rad_const_pos hC
      calc p (s ^ m * t ^ m) ≤ p (s ^ m) * p (t ^ m) := h.mul_le _ _
        _ ≤ (C * a ^ m) * (C' * b ^ m) :=
          mul_le_mul (hC m) (hC' m) (h.nonneg _) (by positivity)
        _ = _ := by ring
    have hs := h0 s
    have ht := h0 t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := sInf (rad p s) with hA
    set B := sInf (rad p t) with hB
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    have := key (A + ε) (h.mem_rad_of_lt (by linarith)) (B + ε) (h.mem_rad_of_lt (by linarith))
    nlinarith

/-- Proof of Proposition prop:gauge: r ≤ p. -/
theorem prop_gauge_radius_le (h : IsPre D p) (t : M) : sInf (rad p t) ≤ p t :=
  le_of_forall_pos_le_add fun _ hδ => csInf_le (rad_bdd p t) (h.mem_rad t hδ)

/-- Proof of Proposition prop:gauge: "If p keeps (x, y, c), then p(tⁿxⁿ) ≤ cⁿ p(tⁿyⁿ), so r keeps it." -/
theorem prop_gauge_radius_keeps (h : IsPre D p) {x y : M} {c : ℝ} (hc : 0 ≤ c) (hk : Keeps p x y c) :
    Keeps (fun t => sInf (rad p t)) x y c := by
  intro t
  -- first p(s x^m) ≤ c^m p(s y^m) for all m and s
  have h1 : ∀ (m : ℕ) (s : M), p (s * x ^ m) ≤ c ^ m * p (s * y ^ m) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      calc p (s * x ^ (m + 1)) = p (s * x * x ^ m) := by rw [pow_succ', mul_assoc]
        _ ≤ c ^ m * p (s * x * y ^ m) := ih _
        _ = c ^ m * p (s * y ^ m * x) := by rw [mul_right_comm]
        _ ≤ c ^ m * (c * p (s * y ^ m * y)) := by gcongr; exact hk _
        _ = c ^ (m + 1) * p (s * y ^ (m + 1)) := by
          rw [mul_assoc s, ← pow_succ, pow_succ c m, mul_assoc]
  have h2 : ∀ a ∈ rad p (t * y), sInf (rad p (t * x)) ≤ c * a := by
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p _) ⟨by positivity, C, fun m => ?_⟩
    calc p ((t * x) ^ m) = p (t ^ m * x ^ m) := by rw [mul_pow]
      _ ≤ c ^ m * p (t ^ m * y ^ m) := h1 m _
      _ ≤ c ^ m * (C * a ^ m) := by rw [← mul_pow]; gcongr; exact hC m
      _ = C * (c * a) ^ m := by ring
      _ ≤ C * (c * a + δ) ^ m := by gcongr; linarith
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h2 _ (h.mem_rad _ one_pos)
  · have h3 : sInf (rad p (t * x)) / c ≤ sInf (rad p (t * y)) := by
      refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
      rw [div_le_iff₀ hc]
      exact (h2 a ha).trans (mul_comm _ _).le
    rw [div_le_iff₀ hc] at h3
    exact h3.trans (mul_comm _ _).le

/-- If p((tⁿ)ᵐ) ≤ C·aᵐ for all m, then p(tᵐ) ≤ C′·bᵐ for all m, with bⁿ = a. -/
theorem prop_gauge_radius_root (h : IsPre D p) {t : M} {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : a ∈ rad p (t ^ n)) :
    a ^ ((n : ℝ)⁻¹) ∈ rad p t := by
  obtain ⟨ha, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  set b := a ^ ((n : ℝ)⁻¹) with hb
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hbn : b ^ n = a := Real.rpow_inv_natCast_pow ha.le (by omega)
  set E := max 1 (p t / b) with hE
  have hE1 : 1 ≤ E := le_max_left _ _
  refine ⟨hb0, C * E ^ n, fun m => ?_⟩
  have h1 : t ^ m = (t ^ n) ^ (m / n) * t ^ (m % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : b ^ m = a ^ (m / n) * b ^ (m % n) := by
    rw [← hbn, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h3 : p t ≤ E * b := by
    rw [← div_le_iff₀ hb0]; exact le_max_right _ _
  have h4 : p (t ^ (m % n)) ≤ E ^ n * b ^ (m % n) := by
    calc p (t ^ (m % n)) ≤ p t ^ (m % n) := h.pow_le _ _
      _ ≤ (E * b) ^ (m % n) := pow_le_pow_left₀ (h.nonneg t) h3 _
      _ = E ^ (m % n) * b ^ (m % n) := mul_pow _ _ _
      _ ≤ E ^ n * b ^ (m % n) := by
        gcongr
        exact (Nat.mod_lt _ hn).le
  rw [h1, h2]
  calc _ ≤ p ((t ^ n) ^ (m / n)) * p (t ^ (m % n)) := h.mul_le _ _
    _ ≤ (C * a ^ (m / n)) * (E ^ n * b ^ (m % n)) :=
      mul_le_mul (hC _) h4 (h.nonneg _) (by positivity)
    _ = _ := by ring

/-- Proof of Proposition prop:gauge: "Let r(t) = inf_{n≥1} p(tⁿ)^(1/n)". The number r(t) of the Lean proof, the infimum of the
a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n, is the printed one. (That r(t) + δ is such an a, Ov.Duality.IsPre.mem_rad_of_lt,
is the printed bound p(tᵃ) ≤ c_δ (r(t) + δ)ᵃ, which the paper takes from Fekete's lemma.) -/
theorem prop_gauge_radius_eq (h : IsPre D p) (t : M) :
    sInf (rad p t) = ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (h.nonneg _) _⟩
  refine le_antisymm (le_ciInf fun n => ?_) (le_csInf ⟨_, h.mem_rad t one_pos⟩ ?_)
  · -- (p(tⁿ) + δ)^(1/n) is such an a, for every δ > 0
    have h1 : ∀ δ : ℝ, 0 < δ → sInf (rad p t) ≤ (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := fun δ hδ =>
      csInf_le (rad_bdd p t) (prop_gauge_radius_root h n.succ_pos (h.mem_rad _ hδ))
    have h2 : Filter.Tendsto (fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹))) := by
      have h3 : Continuous fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.continuous_rpow_const (by positivity)).comp (continuous_const.add continuous_id)
      have h4 := h3.tendsto 0
      rw [add_zero] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => h1 δ hδ)
  · -- p(tⁿ)^(1/n) ≤ C^(1/n)·a, and C^(1/n) tends to 1
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    have h1 : ∀ n : ℕ, ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
      intro n
      refine (ciInf_le hbdd n).trans ?_
      calc p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (C * a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (h.nonneg _) (hC _) (by positivity)
        _ = C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
          rw [Real.mul_rpow (by linarith) (by positivity), Real.pow_rpow_inv_natCast ha.le n.succ_ne_zero]
    have h2 : Filter.Tendsto (fun n : ℕ => C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a) Filter.atTop (nhds (C ^ (0 : ℝ) * a)) := by
      refine Filter.Tendsto.mul_const a ?_
      refine ((Real.continuous_const_rpow (by linarith : C ≠ 0)).tendsto 0).comp ?_
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    rw [Real.rpow_zero, one_mul] at h2
    exact ge_of_tendsto' h2 h1

/-- Proof of Proposition prop:gauge: "r = p, that is, p(tⁿ) = p(t)ⁿ." -/
theorem prop_gauge_radius_pow (h : IsPre D p) (hr : ∀ t, sInf (rad p t) = p t) (t : M) (n : ℕ) :
    p (t ^ n) = p t ^ n := by
  refine le_antisymm (h.pow_le t n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h.one]
  rw [← hr (t ^ n)]
  refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
  have h5 : p t ≤ a ^ ((n : ℝ)⁻¹) := by
    rw [← hr t]
    exact csInf_le (rad_bdd p t) (prop_gauge_radius_root h hn ha)
  calc p t ^ n ≤ (a ^ ((n : ℝ)⁻¹)) ^ n := pow_le_pow_left₀ (h.nonneg t) h5 n
    _ = a := Real.rpow_inv_natCast_pow ha.1.le (by omega)

/-- Proof of Proposition prop:gauge: "Let f satisfy p(f) > 0 and let p_f(t) = inf p(tfⁿ)/p(f)ⁿ; the sequence is nonincreasing.
It is again such a gauge: p_f(1) = 1, submultiplicativity follows from p(stf^(a+b)) ≤ p(sfᵃ)p(tfᵇ), and the two other
properties pass to the limit." Here p(fⁿ) = p(f)ⁿ is a hypothesis. The statement says of q = p_f what is used: it is a gauge
below p, it keeps what p keeps, and it keeps (1, f, 1/p(f)), that is, p(f)·p_f(t) ≤ p_f(tf). -/
theorem prop_gauge_localize (h : IsPre D p) {f : M} (hf : 0 < p f) (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : M → ℝ, IsPre D q ∧ (∀ t, q t ≤ p t) ∧ Keeps q 1 f (p f)⁻¹ ∧
      ∀ x y c, 0 ≤ c → Keeps p x y c → Keeps q x y c := by
  set P : ℕ → M → ℝ := fun n t => p (t * f ^ n) / p f ^ n with hP
  have anti : Antitone P := by
    refine antitone_nat_of_succ_le fun n t => ?_
    simp only [hP]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc p (t * f ^ (n + 1)) * p f ^ n ≤ (p (t * f ^ n) * p f) * p f ^ n := by
          gcongr
          rw [pow_succ, ← mul_assoc]
          exact h.mul_le _ _
      _ = p (t * f ^ n) * p f ^ (n + 1) := by ring
  have nonneg : ∀ n t, 0 ≤ P n t := fun n t => div_nonneg (h.nonneg _) (by positivity)
  have hle : ∀ n t, ⨅ j, P j t ≤ P n t := fun n t =>
    ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩ n
  refine ⟨fun t => ⨅ n, P n t, isPre_iInf anti.directed_ge nonneg ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hP, one_mul, hpow]
    exact div_self (by positivity)
  · intro n s t
    refine ⟨n + n, ?_⟩
    simp only [hP]
    rw [div_mul_div_comm, ← pow_add]
    gcongr
    have : s * t * f ^ (n + n) = (s * f ^ n) * (t * f ^ n) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact h.mul_le _ _
  · intro n κ _ t b hb
    have h1 := h.le_sum _ _ (D.mul (f ^ n) hb)
    simp only [hP]
    rw [← Finset.sum_div]
    gcongr
  · intro t
    simpa [hP] using hle 0 t
  · intro t
    rw [mul_one, Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun n => (hle (n + 1) t).trans (le_of_eq ?_)
    simp only [hP]
    rw [pow_succ' f n, ← mul_assoc, pow_succ]
    field_simp
  · intro x y c hc hk
    refine keeps_iInf nonneg hc fun n t => ?_
    simp only [hP]
    rw [mul_div_assoc']
    gcongr
    have := hk (t * f ^ n)
    rwa [mul_right_comm, mul_right_comm t y]

/-- Proposition prop:gauge for a commutative monoid with a covering relation: below every gauge p₀ there is a gauge that is
multiplicative and keeps every triple which p₀ keeps. -/
theorem prop_gauge_monoid {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ F : M → ℝ, IsPre D F ∧ (∀ s t, F (s * t) = F s * F t) ∧ (∀ t, F t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps F x y c := by
  obtain ⟨p, hp, hle, hkeep, hmin⟩ := prop_gauge_minimal h₀
  -- "By minimality r = p, that is, p(tⁿ) = p(t)ⁿ."
  have hrad : ∀ t, sInf (rad p t) = p t :=
    hmin _ (prop_gauge_radius hp) (fun x y c hc hk => prop_gauge_radius_keeps hp hc (hkeep x y c hc hk))
      (prop_gauge_radius_le hp)
  refine ⟨p, hp, fun s f => le_antisymm (hp.mul_le s f) ?_, hle, hkeep⟩
  rcases (hp.nonneg f).eq_or_lt with hf | hf
  · -- "If p(f) = 0, then p(tf) = 0 as well."
    rw [← hf, mul_zero]
    exact hp.nonneg _
  · -- "By minimality p_f = p, hence p(tf) = p(t)p(f)."
    obtain ⟨q, hq, hqle, hqk, hqkeep⟩ := prop_gauge_localize hp hf (prop_gauge_radius_pow hp hrad f)
    have hqp := hmin q hq (fun x y c hc hk => hqkeep x y c hc (hkeep x y c hc hk)) hqle
    have h1 := hqk s
    rw [hqp, hqp, mul_one, inv_mul_eq_div, le_div_iff₀ hf] at h1
    exact h1

end Monoid

/-- **Paper: Proposition prop:gauge.** "Below every gauge there is a spectral point that keeps every triple which the
gauge keeps." A gauge is an Ov.PreSpec; it keeps (x, y, c) if p(tx) ≤ c p(ty) for all t. This is prop_gauge_monoid for the
classes of tensors. -/
theorem prop_gauge (p : PreSpec K I) :
    ∃ φ : Spec K I, (∀ t, φ.F t ≤ p.p t) ∧
      ∀ (x y : Ten K I) (c : ℝ), 0 ≤ c → (∀ t, p.p (t * x) ≤ c * p.p (t * y)) →
        ∀ t, φ.F (t * x) ≤ c * φ.F (t * y) := by
  obtain ⟨F, hF, hmul, hle, hk⟩ := prop_gauge_monoid (isPre_onCls p)
  refine ⟨⟨fun t => F (cls t), fun _ => hF.nonneg _, hF.one, fun s t => by rw [cls_mul, hmul],
    fun s b hb => hF.le_sum _ _ (tenCover_cov.2 hb)⟩, fun t => ?_, fun x y c hc h t => ?_⟩
  · exact (hle (cls t)).trans (onCls_cls p t).le
  · have h1 := hk (cls x) (cls y) c hc (keeps_onCls h) (cls t)
    rwa [← cls_mul, ← cls_mul] at h1

section Certificates

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- Proof of Theorem thm:duality, first half: "Let p(t) be the infimum of the weights of all certificates for t. Certificates
can be multiplied, and can be raised to a common level and added along covers. As the trivial certificate of level 0 gives
p(1) ≤ 1, and copies of 1 give every t a certificate of level 0, the function p is a gauge if p(1) ≥ 1. … Multiplying a
certificate for tC by A_β gives one for tA_β of one level higher and η times the weight; so p keeps (A_β, C, η)." -/
theorem thm_duality_gauge {C : M} {A : B → M} {η : ℝ} (hη : 0 < η)
    (hone : ∀ t : M, ∃ r : ℕ, D.cov t (fun _ : Fin r => (1 : M)))
    (h : ∀ k W, Cert D C A η 1 k W → 1 ≤ W) :
    IsPre D (fun t => sInf {W | ∃ k, Cert D C A η t k W}) ∧
      ∀ β, Keeps (fun t => sInf {W | ∃ k, Cert D C A η t k W}) (A β) C η := by
  set S : M → Set ℝ := fun t => {W | ∃ k, Cert D C A η t k W} with hS
  have hne : ∀ t, (S t).Nonempty := by
    intro t
    obtain ⟨r, hr⟩ := hone t
    exact ⟨_, 0, Cert.cover hr fun _ => Cert.one 0⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := fun t w ⟨k, hk⟩ => hk.nonneg hη
  refine ⟨isPre_sInf hne h0 ⟨0, Cert.one 0⟩ (fun w ⟨k, hk⟩ => h k w hk)
    (fun s t a ⟨k, hk⟩ b ⟨l, hl⟩ => ⟨k + l, hk.mul hη hl⟩) ?_, fun β => ?_⟩
  · intro κ _ t b hb w hw
    choose k hk using hw
    exact ⟨_, ⟨∑ j, k j, Cert.cover hb fun j => (hk j).raise hη
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩, le_rfl⟩
  · exact keeps_sInf hne h0 hη fun t w ⟨k, hk⟩ => ⟨k + 1, hk.mul_gen hη β⟩

/-- Proof of Theorem thm:duality: "So p(1) < 1, and 1 has a certificate of some level k and weight below 1. Then k ≥ 1, and
every term has v_j ≠ 0, as it would weigh 1 otherwise: this is a cover of C^k by terms in which at least one C was
exchanged." (The certificate of level k₀ is raised to the level k = k₀ + 1.) -/
theorem thm_duality_exchange {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k₀ : ℕ} {W : ℝ}
    (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) :
    ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k₀ + 1) ∧
      (∀ j, u j < k₀ + 1) ∧ D.cov (C ^ (k₀ + 1)) (fun j => C ^ u j * mon A (v j)) ∧
      ∑ j, η ^ (∑ β, v j β) ≤ 1 := by
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h.raise hη (Nat.le_succ k₀)
  rw [one_mul] at hc
  have hlt : ∑ j, η ^ (∑ β, v j β) < 1 := hW.trans_lt hW1
  refine ⟨κ, inferInstance, u, v, hu, fun j => ?_, hc, hlt.le⟩
  by_contra hge
  have h1 := hu j
  have h2 : ∑ β, v j β = 0 := by omega
  have h3 := Finset.single_le_sum (f := fun j => η ^ (∑ β, v j β))
    (fun j _ => by positivity) (Finset.mem_univ j)
  simp only [h2, pow_zero] at h3
  linarith

/-- Proof of Theorem thm:duality: "In C^N replace C^k by this cover as long as some term contains it. The total weight never
increases, so it stays at most 1, and each final term has fewer than k factors C." -/
theorem thm_duality_replace {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k : ℕ} {κ : Type} [Fintype κ] {u : κ → ℕ}
    {v : κ → B → ℕ} (hu : ∀ j, u j + ∑ β, v j β = k) (huk : ∀ j, u j < k)
    (hc : D.cov (C ^ k) (fun j => C ^ u j * mon A (v j))) (hw : ∑ j, η ^ (∑ β, v j β) ≤ 1) (N : ℕ) :
    ∃ (κ' : Type) (_ : Fintype κ') (u' : κ' → ℕ) (v' : κ' → B → ℕ),
      (∀ j, u' j < k) ∧ (∀ j, u' j + ∑ β, v' j β = N) ∧
      D.cov (C ^ N) (fun j => C ^ u' j * mon A (v' j)) ∧ ∑ j, η ^ (∑ β, v' j β) ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N k with hN | hN
    · exact ⟨Unit, inferInstance, fun _ => N, fun _ _ => 0, fun _ => by simpa using hN,
        by simp, by simpa [mon_zero] using D.refl (C ^ N), by simp⟩
    · have hN' : ∀ j, N - k + u j < N := fun j => by have := huk j; omega
      choose μ i u' v' hu' hs' hc' hw' using fun j => ih _ (hN' j)
      refine ⟨Σ j, μ j, inferInstance, fun x => u' x.1 x.2, fun x β => v x.1 β + v' x.1 x.2 β,
        fun x => hu' _ _, fun x => ?_, ?_, ?_⟩
      · have h1 := hs' x.1 x.2
        have h2 := hu x.1
        rw [Finset.sum_add_distrib]
        dsimp only
        omega
      · have h1 : D.cov (C ^ N) (fun j => C ^ (N - k + u j) * mon A (v j)) := by
          have h2 := D.mul (C ^ (N - k)) hc
          rw [← pow_add, Nat.add_sub_cancel' hN] at h2
          convert h2 using 2 with j
          rw [pow_add]
          ac_rfl
        refine D.bind (c := fun j (x : μ j) =>
          C ^ u' j x * mon A (fun β => v j β + v' j x β)) h1 fun j => ?_
        have h2 := D.mul (mon A (v j)) (hc' j)
        convert h2 using 2 with x
        rw [mon_add]
        ac_rfl
      · rw [Fintype.sum_sigma]
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) hw
        calc ∑ x, η ^ (∑ β, (v j β + v' j x β)) =
            η ^ (∑ β, v j β) * ∑ x, η ^ (∑ β, v' j x β) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, Finset.sum_add_distrib]
          _ ≤ η ^ (∑ β, v j β) * 1 := by gcongr; exact hw' j
          _ = _ := mul_one _

omit [Fintype B] in
/-- Proof of Theorem thm:duality: "Replacing each remaining factor C by a fixed number c of copies of a nonzero A_β": if C is
covered by c copies of a, then Cⁿ is covered by cⁿ copies of aⁿ. -/
theorem thm_duality_copies {C a : M} {c : ℕ} (hc : D.cov C (fun _ : Fin c => a)) (n : ℕ) :
    ∃ (μ : Type) (_ : Fintype μ), Fintype.card μ = c ^ n ∧ D.cov (C ^ n) (fun _ : μ => a ^ n) := by
  induction n with
  | zero => exact ⟨Unit, inferInstance, by simp, by simpa using D.refl (1 : M)⟩
  | succ n ih =>
    obtain ⟨μ, _, hμ, hcov⟩ := ih
    refine ⟨Σ _ : μ, Fin c, inferInstance, ?_, ?_⟩
    · rw [Fintype.card_sigma]
      simp [hμ, pow_succ]
    · have := D.mul_mul hcov hc
      simpa only [pow_succ] using this

/-- Proof of Theorem thm:duality, second half: from a certificate for 1 of level k₀ and weight below 1, and a cover of C by c
copies of some A_β, a cover of C^N by products of N factors. "Hence there are at most η^(-N) terms. Replacing each remaining
factor C by a fixed number c of copies of a nonzero A_β gives at most c^k η^(-N)" terms; the Lean bound has c + 1 for c, and
k = k₀ + 1. -/
theorem thm_duality_cover {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {β₀ : B} {c : ℕ}
    (hcA : D.cov C (fun _ : Fin c => A β₀)) {k₀ : ℕ} {W : ℝ} (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) (N : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → B → ℕ),
      (Fintype.card κ : ℝ) ≤ ((c : ℝ) + 1) ^ (k₀ + 1) * (η⁻¹) ^ N ∧ (∀ j, ∑ β, v j β = N) ∧
      D.cov (C ^ N) (fun j => mon A (v j)) := by
  classical
  obtain ⟨κ, _, u, v, hu, huk, hc, hw⟩ := thm_duality_exchange hη h hW1
  obtain ⟨κ', _, u', v', hu', hs', hc', hw'⟩ := thm_duality_replace hη hu huk hc hw N
  choose μ i hμ hcov using fun j : κ' => thm_duality_copies hcA (u' j)
  set E : ℝ := ((c : ℝ) + 1) ^ (k₀ + 1) with hE
  refine ⟨Σ j, μ j, inferInstance, fun x β => v' x.1 β + if β = β₀ then u' x.1 else 0,
    ?_, fun x => ?_, ?_⟩
  · rw [Fintype.card_sigma]
    push_cast
    have h1 : ∀ j, (Fintype.card (μ j) : ℝ) ≤ E := fun j => by
      rw [hμ j]
      push_cast
      calc (c : ℝ) ^ u' j ≤ ((c : ℝ) + 1) ^ u' j := by gcongr; linarith
        _ ≤ E := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) c]) (hu' j).le
    have h2 : (Fintype.card κ' : ℝ) * η ^ N ≤ 1 := by
      refine le_trans ?_ hw'
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hη.le hη1.le ?_
      have := hs' j
      omega
    calc ∑ j, (Fintype.card (μ j) : ℝ) ≤ ∑ _j : κ', E := Finset.sum_le_sum fun j _ => h1 j
      _ = Fintype.card κ' * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card κ' * η ^ N) * (E * (η⁻¹) ^ N) := by
        rw [inv_pow]
        field_simp
      _ ≤ 1 * (E * (η⁻¹) ^ N) := by gcongr
      _ = _ := one_mul _
  · have := hs' x.1
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  · refine D.bind (b := fun j => C ^ u' j * mon A (v' j))
      (c := fun j (_ : μ j) => mon A (fun β => v' j β + if β = β₀ then u' j else 0)) hc' fun j => ?_
    have h1 := D.mul (mon A (v' j)) (hcov j)
    convert h1 using 2 with x
    rw [mon_add, mon_single]
    exact mul_comm _ _

end Certificates

/-- **Paper: Theorem thm:duality.** "Let C ≠ 0 and A_1, …, A_r be tensors on I, not all A_β zero, and suppose that
every spectral point satisfies φ(C) ≤ max φ(A_β). Then for every ε > 0 and all large N, the power C^N is covered by at
most 2^(εN) products of N factors from A_1, …, A_r." The family is indexed by any finite type B. -/
theorem thm_duality [Nonempty I] {B : Type} [Fintype B] [DecidableEq B] {C : Ten K I} {A : B → Ten K I}
    (hC : ∃ x, C.val x ≠ 0) (hA : ∃ β x, (A β).val x ≠ 0) (h : ∀ φ : Spec K I, ∃ β, φ.F C ≤ φ.F (A β)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (m : ℕ) (v : Fin m → B → ℕ), (m : ℝ) ≤ 2 ^ (ε * N) ∧
      (∀ i, ∑ β, v i β = N) ∧
      SumRestr (Ten.kpow C N) fun i => Ten.prod fun β => Ten.kpow (A β) (v i β) := by
  -- η = 2^(-ε/2)
  have hη : (0 : ℝ) < 2 ^ (-(ε / 2)) := by positivity
  have hη1 : (2 : ℝ) ^ (-(ε / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hinv : ((2 : ℝ) ^ (-(ε / 2)))⁻¹ = 2 ^ (ε / 2) := by rw [← Real.rpow_neg (by norm_num), neg_neg]
  have hsq : ∀ N : ℕ, ((2 : ℝ) ^ (ε / 2)) ^ N * ((2 : ℝ) ^ (ε / 2)) ^ N = 2 ^ (ε * N) := by
    intro N
    rw [← mul_pow, ← Real.rpow_add (by norm_num), add_halves, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  -- copies of 1, and so of any nonzero tensor, cover every tensor
  have hcov : ∀ (t : Ten K I) {s : Ten K I}, Restr 1 s →
      ∃ r : ℕ, (tenCover K I).cov (cls t) (fun _ : Fin r => cls s) := fun t s hs => by
    obtain ⟨r, hr⟩ := tensor_covered_by_ones t
    exact ⟨r, tenCover_cov.2 (hr.mono fun _ => hs)⟩
  have hone : ∀ t : Cls K I, ∃ r : ℕ, (tenCover K I).cov t (fun _ : Fin r => (1 : Cls K I)) := by
    intro t
    obtain ⟨r, hr⟩ := hcov (rep t) (Restr.refl 1)
    rw [cls_rep] at hr
    exact ⟨r, hr⟩
  obtain ⟨β₀, hβ₀⟩ := hA
  by_cases hcert : ∃ k W, Cert (tenCover K I) (cls C) (fun β => cls (A β)) (2 ^ (-(ε / 2))) 1 k W ∧ W < 1
  · -- 1 has a certificate of weight below 1
    obtain ⟨k, W, hc, hW⟩ := hcert
    obtain ⟨c, hcA⟩ := hcov C (tensor_one_restr hβ₀)
    have hbase : (1 : ℝ) < 2 ^ (ε / 2) := Real.one_lt_rpow one_lt_two (by linarith)
    -- c^k η^(-N) ≤ 2^(εN) for large N
    obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (((c : ℝ) + 1) ^ (k + 1)) hbase
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨κ, _, v, hcard, hv, hc⟩ := thm_duality_cover hη hη1 (β₀ := β₀) hcA hc hW N
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun i => v (e.symm i), ?_, fun i => hv _, ?_⟩
    · rw [hinv] at hcard
      refine hcard.trans (le_trans ?_ (hsq N).le)
      gcongr
      exact hN₀.le.trans (pow_le_pow_right₀ hbase.le hN)
    simp only [cls_mon, ← cls_kpow] at hc
    exact (tenCover_cov.1 hc).reindex e.symm
  · -- otherwise the weights of certificates are a gauge, and Proposition prop:gauge contradicts the hypothesis
    exfalso
    push Not at hcert
    obtain ⟨hp, hA⟩ := thm_duality_gauge (D := tenCover K I) (C := cls C) (A := fun β => cls (A β)) hη hone hcert
    obtain ⟨φ, -, hk⟩ := prop_gauge (ofCls hp)
    obtain ⟨β, hβ⟩ := h φ
    have h2 := hk (A β) C _ hη.le (fun t => by
      have h5 := hA β (cls t)
      rw [← cls_mul, ← cls_mul] at h5
      exact h5) 1
    rw [(def_spectral_congr φ).2 (Equi.one_mul _), (def_spectral_congr φ).2 (Equi.one_mul _)] at h2
    have h3 : 1 ≤ φ.F C := (def_spectral_values φ C).1 hC
    nlinarith

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": extension

The subsection "Extension": Proposition prop:extend, with the steps of its proof.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

variable {I' : Type} [Fintype I'] [DecidableEq I'] {L : Type} [Fintype L]

/-- The product on the right in Proposition prop:extend: "Call the product on the right f(t)". -/
noncomputable def extendProduct (π : L → I' → I) (θ : L → ℝ) (φ : Spec K I) (t : Ten K I') : ℝ :=
  ∏ l, φ.F (Ten.push (π l) t) ^ θ l

/-- Proof of Proposition prop:extend: "Call the product on the right f(t); it is multiplicative and monotone." Also f ≥ 0 and
f(1) = 1. -/
theorem prop_extend_product (π : L → I' → I) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l) (φ : Spec K I) :
    (∀ t, 0 ≤ extendProduct π θ φ t) ∧ extendProduct π θ φ 1 = 1 ∧
    (∀ s t, extendProduct π θ φ (s * t) = extendProduct π θ φ s * extendProduct π θ φ t) ∧
    ∀ {s t}, Restr s t → extendProduct π θ φ s ≤ extendProduct π θ φ t := by
  refine ⟨fun t => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (φ.nonneg _) _, ?_, fun s t => ?_, fun {s t} h => ?_⟩
  · refine Finset.prod_eq_one fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_one _), φ.one, Real.one_rpow]
  · rw [extendProduct, extendProduct, extendProduct, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_mul _ s t), φ.mul, Real.mul_rpow (φ.nonneg _) (φ.nonneg _)]
  · exact Finset.prod_le_prod (fun l _ => Real.rpow_nonneg (φ.nonneg _) _) fun l _ =>
      Real.rpow_le_rpow (φ.nonneg _) ((def_spectral_congr φ).1 ((tensor_push_cover _).2 h)) (hθ l)

/-- Proof of Proposition prop:extend: "Suppose that ιA = ∑ s_j, each s_j a restriction of b_j. As ιA has trivial index sets
outside ι(I), so has every s_j; so s_j = ιa_j with ∑ a_j = A. Push-forwards preserve restrictions, so a_j = π_l s_j is a
restriction of π_l b_j for every l." -/
theorem prop_extend_cover (ι : I → I') {A : Ten K I} {κ : Type} [Fintype κ] {b : κ → Ten K I'}
    (h : Ten.SumRestr (Ten.push ι A) b) :
    ∃ c : κ → Ten K I, Ten.SumRestr A c ∧
      ∀ k, ∀ π : I' → I, (∀ i, π (ι i) = i) → Ten.Restr (c k) (Ten.push π (b k)) := by
  obtain ⟨v, hv, hr⟩ := Ten.sumRestr_iff.1 h
  let emb : (∀ i, A.ι i) → ∀ q, (Ten.push ι A).ι q := fun x q j => x j.1
  refine ⟨fun k => A.withVal fun x => v k (emb x), Ten.SumRestr.of_withVal A _ fun x => ?_,
    fun k π hπ => ?_⟩
  · exact hv (emb x)
  · have h1 : Ten.Restr (Ten.push ι (A.withVal fun x => v k (emb x)))
        ((Ten.push ι A).withVal (v k)) := by
      refine Ten.Restr.of_map' (fun q x => x) fun x => ?_
      rw [Ten.push_val]
      change v k _ = v k _
      congr 1
      funext q j
      obtain ⟨j, rfl⟩ := j
      rfl
    have h2 := (tensor_push_cover π).2 (h1.trans (hr k))
    have h3 : π ∘ ι = id := funext hπ
    have h4 := tensor_push_comp π ι (A.withVal fun x => v k (emb x))
    rw [h3] at h4
    exact (h4.trans (tensor_push_id _)).2.trans h2

/-- Proof of Proposition prop:extend: "So φ(A) ≤ ∑ φ(a_j) ≤ ∑ f(b_j)", for every cover (b_j) of ιA. -/
theorem prop_extend_lower (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) {κ : Type} [Fintype κ] (b : κ → Ten K I')
    (hb : SumRestr (Ten.push ι A) b) : φ.F A ≤ ∑ k, extendProduct π θ φ (b k) := by
  obtain ⟨a, ha, hr⟩ := prop_extend_cover ι hb
  refine (φ.le_sum A a ha).trans (Finset.sum_le_sum fun k _ => ?_)
  -- φ(a_j) is at most every factor φ(π_l b_j), so at most their weighted geometric mean
  rcases (φ.nonneg (a k)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact (prop_extend_product π θ hθ φ).1 _
  · calc φ.F (a k) = φ.F (a k) ^ (∑ l, θ l) := by rw [hθ1, Real.rpow_one]
      _ = ∏ l, φ.F (a k) ^ θ l := Real.rpow_sum_of_pos h0 _ _
      _ ≤ extendProduct π θ φ (b k) := Finset.prod_le_prod (fun l _ => Real.rpow_nonneg h0.le _) fun l _ =>
        Real.rpow_le_rpow h0.le ((def_spectral_congr φ).1 (hr k _ (hπ l))) (hθ l)

/-- Proof of Proposition prop:extend: "f(ιA) = φ(A), as π_l ι = id." -/
theorem prop_extend_upper (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) : extendProduct π θ φ (Ten.push ι A) = φ.F A := by
  have retr : ∀ l, Equi (Ten.push (π l) (Ten.push ι A)) A := by
    intro l
    have h := tensor_push_comp (π l) ι A
    rw [show π l ∘ ι = id from funext (hπ l)] at h
    exact h.trans (tensor_push_id _)
  have h1 : extendProduct π θ φ (Ten.push ι A) = ∏ l, φ.F A ^ θ l :=
    Finset.prod_congr rfl fun l _ => by rw [(def_spectral_congr φ).2 (retr l)]
  rw [h1]
  rcases (φ.nonneg A).eq_or_lt with h0 | h0
  · obtain ⟨l, hl⟩ : ∃ l, θ l ≠ 0 := by
      by_contra hne
      push Not at hne
      simp [hne] at hθ1
    rw [← h0]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Real.zero_rpow hl)
  · rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]

/-- Proof of Proposition prop:extend: there is "a gauge with p ≤ f and p(ιA) = φ(A) for all A". In the proof it is the printed
one: "Let p(t) be the infimum of ∑ f(b_j) over the covers (b_j) of t. … With A = 1 this shows p(1) = 1". -/
theorem prop_extend_gauge (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) :
    ∃ p : PreSpec K I', (∀ t, p.p t ≤ extendProduct π θ φ t) ∧ ∀ A : Ten K I, p.p (Ten.push ι A) = φ.F A := by
  classical
  obtain ⟨f0, f1, fmul, fmono⟩ := prop_extend_product π θ hθ φ
  set f : Ten K I' → ℝ := extendProduct π θ φ with hf
  have hcongr : ∀ {s t : Ten K I'}, Equi s t → f s = f t := fun h => le_antisymm (fmono h.1) (fmono h.2)
  -- the sums ∑ f(b_j) over the covers of a class of tensors
  set S : Cls K I' → Set ℝ := fun m => {W | ∃ (κ : Type) (_ : Fintype κ) (b : κ → Cls K I'),
    (tenCover K I').cov m b ∧ ∑ k, f (rep (b k)) = W} with hS
  have hne : ∀ t, (S t).Nonempty := fun t =>
    ⟨_, Unit, inferInstance, fun _ => t, (tenCover K I').refl t, rfl⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := by
    rintro t w ⟨κ, _, b, -, rfl⟩
    exact Finset.sum_nonneg fun k _ => f0 _
  have hlow : ∀ A : Ten K I, ∀ w ∈ S (cls (Ten.push ι A)), φ.F A ≤ w := by
    rintro A w ⟨κ, _, b, hb, rfl⟩
    exact prop_extend_lower ι π hπ θ hθ hθ1 φ A _ ((rep_cls _).2.trans_sum hb)
  have hup : ∀ t : Ten K I', f t ∈ S (cls t) := fun t =>
    ⟨Unit, inferInstance, fun _ => cls t, (tenCover K I').refl _, by
      simpa using hcongr (rep_cls t)⟩
  have hpre : IsPre (tenCover K I') (fun t => sInf (S t)) := by
    refine isPre_sInf hne h0 ?_ ?_ ?_ ?_
    · have h := hup 1
      rwa [f1, cls_one] at h
    · intro w hw
      rw [← cls_one, ← cls_eq.2 (tensor_push_one ι)] at hw
      have h := hlow 1 w hw
      rwa [φ.one] at h
    · rintro s t a ⟨κ, _, b, hb, rfl⟩ a' ⟨κ', _, b', hb', rfl⟩
      refine ⟨Σ _ : κ, κ', inferInstance, _, (tenCover K I').mul_mul hb hb', ?_⟩
      rw [Fintype.sum_sigma, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      rw [← fmul]
      exact hcongr (rep_cls _)
    · intro κ _ t b hb w hw
      choose μ i c hc hw using hw
      refine ⟨_, ⟨Σ k, μ k, inferInstance, _, (tenCover K I').bind hb hc, rfl⟩, ?_⟩
      rw [Fintype.sum_sigma]
      exact (Finset.sum_congr rfl fun k _ => hw k).le
  have Pf : ∀ t, (ofCls hpre).p t ≤ f t := fun t => csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (hup t)
  exact ⟨ofCls hpre, Pf, fun A => le_antisymm ((Pf _).trans (prop_extend_upper ι π hπ θ hθ1 φ A).le)
    (le_csInf (hne _) (hlow A))⟩

/-- Proof of Proposition prop:extend: "let c = φ(C) and q(t) = inf p(t ιCⁿ)/cⁿ. As p(ιCⁿ) = cⁿ, this is a gauge below p that
keeps (1, ιC, 1/c)." Stated for any gauge p and any tensor f with p(f) > 0 and p(fⁿ) = p(f)ⁿ: some gauge q below p keeps
(1, f, 1/p(f)). It is the one of prop_gauge_localize, for the classes of tensors. -/
theorem prop_extend_localize (p : PreSpec K I) (f : Ten K I) (hf : 0 < p.p f)
    (hpow : ∀ n, p.p (Ten.kpow f n) = p.p f ^ n) :
    ∃ q : PreSpec K I, (∀ t, q.p t ≤ p.p t) ∧ ∀ t, q.p (t * 1) ≤ (p.p f)⁻¹ * q.p (t * f) := by
  obtain ⟨q, hq, hle, hk, -⟩ := prop_gauge_localize (isPre_onCls p) (f := cls f) (by simpa using hf)
    (fun n => by rw [← cls_kpow, onCls_cls, onCls_cls, hpow])
  refine ⟨ofCls hq, fun t => (hle _).trans (onCls_cls p t).le, fun t => ?_⟩
  have := hk (cls t)
  rw [onCls_cls] at this
  change q (cls (t * 1)) ≤ _ * q (cls (t * f))
  rwa [cls_mul, cls_mul]

/-- **Paper: Proposition prop:extend.** "Let ι : I → I′ and π_l : I′ → I, l ≤ L, be maps with π_l ι = id, let θ_l ≥ 0
add up to 1, let φ be a spectral point on I, and let C be a tensor on I. There is a spectral point φ′ on I′ with
φ′(t) ≤ ∏ φ(π_l t)^θ_l for all t, and φ′(ιC) = φ(C)." The maps are indexed by any finite type L. -/
theorem prop_extend (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (C : Ten K I) :
    ∃ φ' : Spec K I', (∀ t, φ'.F t ≤ ∏ l, φ.F (Ten.push (π l) t) ^ θ l) ∧ φ'.F (Ten.push ι C) = φ.F C := by
  obtain ⟨p, pf, pA⟩ := prop_extend_gauge ι π hπ θ hθ hθ1 φ
  rcases (φ.nonneg C).eq_or_lt with hC | hC
  · -- φ(C) = 0 (the printed case C = 0)
    obtain ⟨φ', hφ', -⟩ := prop_gauge p
    exact ⟨φ', fun t => (hφ' t).trans (pf t),
      le_antisymm ((hφ' _).trans (pA C).le) (by rw [← hC]; exact φ'.nonneg _)⟩
  · obtain ⟨q, hq, hqk⟩ := prop_extend_localize p (Ten.push ι C) (by rwa [pA]) (fun n => by
      rw [← p.congr (Equi.push_kpow ι C n), pA, pA, φ.kpow])
    -- "A spectral point φ′ ≤ q that keeps this triple has c ≤ φ′(ιC) ≤ f(ιC) = c."
    obtain ⟨φ', hφ', hk⟩ := prop_gauge q
    refine ⟨φ', fun t => (hφ' t).trans ((hq t).trans (pf t)),
      le_antisymm ((hφ' _).trans ((hq _).trans (pA C).le)) ?_⟩
    have h1 := hk 1 (Ten.push ι C) _ (by rw [pA]; positivity) hqk 1
    rw [(def_spectral_congr φ').2 (Equi.one_mul _), (def_spectral_congr φ').2 (Equi.one_mul _), φ'.one, pA,
      inv_mul_eq_div, le_div_iff₀ hC, one_mul] at h1
    exact h1

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The values of a spectral point at wires

The parts of Lemma lem:exponents (`Paper/Tensors.lean`) in the form in which the development cites them, and what follows
at once for tensors whose legs are moved.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- φ(⟨n⟩_P) = n^g with g = log₂ φ(⟨2⟩_P), wherever the legs are. -/
theorem unit_eq [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    F.F (Ten.push π (unit K J n)) = (n : ℝ) ^ Real.logb 2 (F.F (Ten.push π (unit K J 2))) :=
  (Paper.lem_exponents_power F π).2 n hn

/-- φ(⟨n⟩_pq) = n^(d_φ(p,q)). -/
theorem wire_eq (p q : I) {n : ℕ} (hn : 1 ≤ n) : F.F (wire K n p q) = (n : ℝ) ^ F.e p q :=
  Paper.lem_exponents_wire F p q hn

/-- φ(⟨2⟩_pq) = 2^(d_φ(p,q)). -/
theorem wire_two (p q : I) : F.F (wire K 2 p q) = 2 ^ F.e p q := Paper.lem_exponents_wire_two F p q

/-- φ(⟨n⟩_pq) ≤ n^(d_φ(p,q)), also for n = 0. -/
theorem wire_le (p q : I) (n : ℕ) : F.F (wire K n p q) ≤ (n : ℝ) ^ F.e p q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : F.F (wire K 0 p q) ≤ (0 : ℕ) := F.unit_le ![p, q] 0
    exact this.trans (by exact_mod_cast Real.rpow_nonneg le_rfl _)
  · exact (F.wire_eq p q hn).le

/-- Distances are not negative. -/
theorem e_nonneg (p q : I) : 0 ≤ F.e p q := (Paper.lem_exponents_unit_interval F p q).1

/-- Distances are at most 1. -/
theorem e_le_one (p q : I) : F.e p q ≤ 1 := (Paper.lem_exponents_unit_interval F p q).2

/-- The distance from a party to itself is 0. -/
theorem e_self (p : I) : F.e p p = 0 := Paper.lem_exponents_self F p

/-- Distances are symmetric. -/
theorem e_comm (p q : I) : F.e p q = F.e q p := Paper.lem_exponents_symm F p q

/-- A tensor with all its legs at one party costs at most 1. -/
theorem push_const_le (q : I) (t : Ten K J) : F.F (Ten.push (fun _ => q) t) ≤ 1 := by
  rw [← F.one]
  exact F.mono (Restr.push_const q t)

/-- Moving legs: if the leg j moves from π' j to π j, the value grows at most by the values of wires
between π j and π' j that have the dimensions of the legs. -/
theorem push_le_move (π π' : J → I) (t : Ten K J) :
    F.F (Ten.push π t) ≤
      (∏ j, (Fintype.card (t.ι j) : ℝ) ^ F.e (π j) (π' j)) * F.F (Ten.push π' t) := by
  refine (F.le_mul (Restr.move π π' t)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (F.nonneg _)
  rw [F.prod]
  exact Finset.prod_le_prod (fun _ _ => F.nonneg _) fun j _ => F.wire_le _ _ _

/-- The distances of a pull-back. -/
theorem pull_e (π : J → I) (p q : J) : (F.pull π).e p q = F.e (π p) (π q) := by
  rw [e, e, pull_F]
  congr 1
  refine F.congr ((Equi.push_push π ![p, q] (unit K (Fin 2) 2)).trans ?_)
  have : π ∘ ![p, q] = ![π p, π q] := by funext i; fin_cases i <;> rfl
  rw [this]
  exact Equi.refl _

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Prices of wires: the definition

For a field K and a finite set V of parties, `Prices K V` is the closure (for pointwise limits) of the
multiples c·d_F, c ≥ 0, of the metrics d_F(u,v) = F.e u v of the spectral points F over V. A function w
on pairs of any set Y is a price (`IsPrice K w`) if its pull-backs to finite sets are in `Prices`.
That prices are pseudometrics, closed under pull-backs, multiples and limits, and compact below a bound is
in `Paper/Prices.lean`. At the end there are two lemmas on the entries of a wire, for the files that compute with them.
-/

namespace Nc.Price

open Ov Finset

section Finite

variable (K : Type) [Field K]

variable {K} {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem specCone_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ specCone K V) :
    (fun a b => d (f a) (f b)) ∈ specCone K U := by
  obtain ⟨F, c, hc, rfl⟩ := h
  exact ⟨F.pull f, c, hc, by funext a b; rw [F.pull_e]⟩

theorem continuous_comp {X Y : Type*} (f : X → Y) :
    Continuous fun (d : Y → Y → ℝ) (a b : X) => d (f a) (f b) := by
  fun_prop

theorem prices_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ Prices K V) :
    (fun a b => d (f a) (f b)) ∈ Prices K U :=
  map_mem_closure (continuous_comp f) h fun _ hd => specCone_comp f hd

theorem specCone_smul {d : V → V → ℝ} (h : d ∈ specCone K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ specCone K V := by
  obtain ⟨F, c', hc', rfl⟩ := h
  exact ⟨F, c * c', mul_nonneg hc hc', by funext a b; ring⟩

theorem prices_smul {d : V → V → ℝ} (h : d ∈ Prices K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ Prices K V :=
  map_mem_closure (f := fun (d : V → V → ℝ) a b => c * d a b) (by fun_prop) h
    fun _ hd => specCone_smul hd hc

/-- A closed property of the metrics of spectral points that is kept by multiples holds for
prices. -/
theorem prices_induction {d : V → V → ℝ} (h : d ∈ Prices K V) {S : Set (V → V → ℝ)}
    (hS : IsClosed S) (hF : ∀ (F : Spec K V) (c : ℝ), 0 ≤ c → (fun u v => c * F.e u v) ∈ S) :
    d ∈ S := by
  refine closure_minimal ?_ hS h
  rintro _ ⟨F, c, hc, rfl⟩
  exact hF F c hc

end Finite

section General

variable (K : Type) [Field K]

variable {K}

theorem IsPrice.mem {Y : Type*} {w : Y → Y → ℝ} (h : IsPrice K w) {V : Type} [Fintype V]
    [DecidableEq V] (g : V → Y) : (fun a b => w (g a) (g b)) ∈ Prices K V := by
  have h1 := prices_comp (Fintype.equivFin V) (h _ fun i => g ((Fintype.equivFin V).symm i))
  simpa using h1

theorem isPrice_of_mem {V : Type} [Fintype V] [DecidableEq V] {d : V → V → ℝ}
    (h : d ∈ Prices K V) : IsPrice K d := fun _ f => prices_comp f h

/-- The metric of a spectral point is a price. -/
theorem isPrice_spec {V : Type} [Fintype V] [DecidableEq V] (F : Spec K V) :
    IsPrice K F.e :=
  isPrice_of_mem (subset_closure ⟨F, 1, zero_le_one, by simp⟩)

/-- A function is a price if its restrictions to finite subsets are. -/
theorem isPrice_of_finset {Y : Type*} {w : Y → Y → ℝ}
    (h : ∀ S : Finset Y, IsPrice K fun a b : S => w a b) : IsPrice K w := by
  classical
  intro n f
  exact h (Finset.univ.image f) n fun i => ⟨f i, by simp⟩

variable {Y : Type*} {w : Y → Y → ℝ}

/-- Approximation by the metric of a spectral point. -/
theorem IsPrice.exists_spec (h : IsPrice K w) {V : Type} [Fintype V] [DecidableEq V] (g : V → Y)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Spec K V) (c : ℝ), 0 ≤ c ∧ ∀ a b, |w (g a) (g b) - c * F.e a b| < δ := by
  obtain ⟨d, ⟨F, c, hc, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (h.mem g) δ hδ
  refine ⟨F, c, hc, fun a b => ?_⟩
  have := (dist_pi_lt_iff hδ).1 ((dist_pi_lt_iff hδ).1 hd a) b
  rwa [Real.dist_eq] at this

/-- 0 is a price. -/
theorem isPrice_zero : IsPrice K fun _ _ : Y => 0 := fun n _ =>
  subset_closure ⟨Paper.trivialPoint K (Fin n), 0, le_rfl, by simp⟩

end General

section Unit

open Ov.Ten

variable {K : Type} [Field K]

/-- The entries of the unit tensor with two legs (a wire before it is placed). -/
theorem unit_two_val {n : ℕ} (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if y 0 = y 1 then 1 else 0 := by
  rw [unit_val]
  simp [Fin.forall_fin_two, eq_comm]

theorem unit_two_val' {n : ℕ} {β : Type} [DecidableEq β] (ε : Fin n ≃ β) (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if ε (y 0) = ε (y 1) then 1 else 0 := by
  rw [unit_two_val]
  simp only [ε.injective.eq_iff]

end Unit

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": prices

The subsection "Prices". The definitions are in Nc/Price/Basic.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- **Paper: Definition def:price.** "A price on a finite set V is a limit of multiples s·d_φ, s ≥ 0, φ a spectral
point on V. A function on the pairs of an arbitrary set Y is a price if all its pull-backs to finite sets are prices." -/
theorem def_price :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ), IsPrice K d ↔
      ∀ δ : ℝ, 0 < δ → ∃ (φ : Spec K V) (s : ℝ), 0 ≤ s ∧ ∀ u v, |d u v - s * φ.e u v| < δ) ∧
    ∀ (Y : Type) (w : Y → Y → ℝ), IsPrice K w ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (g : V → Y), IsPrice K fun u v => w (g u) (g v) := by
  refine ⟨fun V _ _ d => ⟨fun h δ hδ => h.exists_spec id hδ, fun h => isPrice_of_mem ?_⟩,
    fun Y w => ⟨fun h V _ _ g n f => h n fun i => g (f i), fun h n f => (h (Fin n) f).mem id⟩⟩
  rw [Prices, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨φ, s, hs, hd⟩ := h δ hδ
  refine ⟨_, ⟨φ, s, hs, rfl⟩, (dist_pi_lt_iff hδ).2 fun u => (dist_pi_lt_iff hδ).2 fun v => ?_⟩
  rw [Real.dist_eq]
  exact hd u v

section Facts

variable {Y : Type*} {w : Y → Y → ℝ}

/-- "Prices are pseudometrics." By Lemma lem:exponents the d_φ are; the conditions are closed and kept by multiples. -/
theorem def_price_pseudometric (h : IsPrice K w) :
    (∀ a b, 0 ≤ w a b) ∧ (∀ a, w a a = 0) ∧ (∀ a b, w a b = w b a) ∧ ∀ a b c, w a c ≤ w a b + w b c := by
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | 0 ≤ d 0 1} :=
      prices_induction (h 2 ![a, b]) (isClosed_le continuous_const (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, -, hI, -⟩ := lem_exponents φ
        exact mul_nonneg hc (hI 0 1).1
    exact h2
  · have h2 : (fun i j : Fin 1 => w (![a] i) (![a] j)) ∈ {d : Fin 1 → Fin 1 → ℝ | d 0 0 = 0} :=
      prices_induction (h 1 ![a]) (isClosed_eq (by fun_prop) continuous_const) fun φ c hc => by
        obtain ⟨-, -, -, h0, -⟩ := lem_exponents φ
        show c * φ.e 0 0 = 0
        rw [h0, mul_zero]
    exact h2
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | d 0 1 = d 1 0} :=
      prices_induction (h 2 ![a, b]) (isClosed_eq (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, hs, -⟩ := lem_exponents φ
        show c * φ.e 0 1 = c * φ.e 1 0
        rw [hs]
    exact h2
  · have h2 : (fun i j : Fin 3 => w (![a, b, c] i) (![a, b, c] j)) ∈
        {d : Fin 3 → Fin 3 → ℝ | d 0 2 ≤ d 0 1 + d 1 2} :=
      prices_induction (h 3 ![a, b, c]) (isClosed_le (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, ht, -⟩ := lem_exponents φ
        show c * φ.e 0 2 ≤ c * φ.e 0 1 + c * φ.e 1 2
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (ht _ _ _) hc
    exact h2

/-- "Pull-backs … of prices are prices; for g : V → W one uses t ↦ φ(gt)." (The latter is Nc.Price.specCone_comp, which
makes the two parts of Definition def:price consistent.) -/
theorem def_price_pullback {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  fun n f => h n fun i => g (f i)

/-- "Nonnegative multiples … of prices are prices". -/
theorem def_price_multiple (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  fun n f => prices_smul (h n f) hc

/-- The set of prices is closed under pointwise convergence. -/
theorem def_price_closed : IsClosed {w : Y → Y → ℝ | IsPrice K w} := by
  have : {w : Y → Y → ℝ | IsPrice K w} = ⋂ (n : ℕ) (f : Fin n → Y),
      (fun (w : Y → Y → ℝ) i j => w (f i) (f j)) ⁻¹' Prices K (Fin n) := by
    ext w
    simp [IsPrice]
  rw [this]
  exact isClosed_iInter fun n => isClosed_iInter fun f =>
    isClosed_closure.preimage (continuous_comp f)

/-- "Pointwise limits of prices are prices". -/
theorem def_price_limit {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w := by
  refine def_price_closed.mem_of_tendsto ?_ hd
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  exact h a

/-- "The prices below a given function form a compact set, by Tychonoff's theorem." -/
theorem def_price_compact (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} := by
  have h1 : IsCompact {w : Y → Y → ℝ | ∀ a, w a ∈ {v : Y → ℝ | ∀ b, v b ∈ Set.Icc 0 (C a b)}} :=
    isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  have h2 : IsClosed {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} := by
    have : {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} = ⋂ (a : Y) (b : Y), {w | w a b ≤ C a b} := by
      ext w; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) continuous_const
  refine h1.of_isClosed_subset (def_price_closed.inter h2) ?_
  rintro w ⟨hw, hC⟩ a b
  exact ⟨(def_price_pseudometric hw).1 a b, hC a b⟩

end Facts

end Paper

/-! The same facts in the form in which the development cites them. -/

namespace Nc.Price

variable {K : Type} [Field K] {Y : Type*} {w : Y → Y → ℝ}

theorem IsPrice.nonneg (h : IsPrice K w) (a b : Y) : 0 ≤ w a b := (Paper.def_price_pseudometric h).1 a b

theorem IsPrice.self (h : IsPrice K w) (a : Y) : w a a = 0 := (Paper.def_price_pseudometric h).2.1 a

theorem IsPrice.symm (h : IsPrice K w) (a b : Y) : w a b = w b a := (Paper.def_price_pseudometric h).2.2.1 a b

theorem IsPrice.triangle (h : IsPrice K w) (a b c : Y) : w a c ≤ w a b + w b c :=
  (Paper.def_price_pseudometric h).2.2.2 a b c

theorem IsPrice.comp {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  Paper.def_price_pullback h g

theorem IsPrice.smul (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  Paper.def_price_multiple h hc

theorem isPrice_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Filter.Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w :=
  Paper.def_price_limit h hd

theorem isCompact_isPrice_le (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} :=
  Paper.def_price_compact C

end Nc.Price

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

section Spectral

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Proof of Proposition prop:random, the finite case for w = d_φ: "Let C be the product of all wires ⟨2⟩_uv with u, v ∈ Y, and
apply Proposition prop:extend. For every pair e of Y ∪ Q we obtain d_φ′(e) ≤ ∑ θ_l d_φ(π_l e). On Y we have d_φ′ ≤ d_φ with
equality for the sum over all pairs, hence equality for each." -/
theorem prop_random_spectral (F : Spec K P) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ F' : Spec K (P ⊕ Q), (∀ p p', F'.e (Sum.inl p) (Sum.inl p') = F.e p p') ∧
      ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  classical
  obtain ⟨F', hle, hC⟩ := prop_extend (K := K) (Sum.inl : P → P ⊕ Q)
    (fun l => Sum.elim id (σ l)) (fun l i => rfl) θ hθ hθ1 F
    (Ten.prod fun e : P × P => Ten.wire K 2 e.1 e.2)
  have hb : ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
    intro a b
    have h1 := hle (Ten.wire K 2 a b)
    have h2 : ∀ l, F.F (Ten.push (Sum.elim id (σ l)) (Ten.wire K 2 a b)) =
        2 ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      intro l
      rw [← F.pull_F, (F.pull _).wire_two, F.pull_e]
    simp only [h2] at h1
    rw [F'.wire_two] at h1
    have h3 : ∏ l, ((2 : ℝ) ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) ^ θ l =
        2 ^ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      rw [Real.rpow_sum_of_pos (by norm_num)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Real.rpow_mul (by norm_num), mul_comm]
    rw [h3] at h1
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h1
  refine ⟨F', ?_, hb⟩
  have hle' : ∀ p p', F'.e (Sum.inl p) (Sum.inl p') ≤ F.e p p' := by
    intro p p'
    refine (hb (Sum.inl p) (Sum.inl p')).trans (le_of_eq ?_)
    simp only [Sum.elim_inl, id]
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hsum : ∑ e : P × P, F'.e (Sum.inl e.1) (Sum.inl e.2) = ∑ e : P × P, F.e e.1 e.2 := by
    rw [← F'.pull_F, (F'.pull _).prod, F.prod] at hC
    simp only [Spec.wire_two, Spec.pull_e] at hC
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num)] at hC
    have h2 := congrArg (Real.logb 2) hC
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at h2
  intro p p'
  have h1 := (Finset.sum_eq_sum_iff_of_le
    (fun (e : P × P) _ => hle' e.1 e.2)).1 hsum (p, p') (Finset.mem_univ _)
  exact h1

end Spectral

section Random

/-- Proof of Proposition prop:random, the reduction to finite sets: "It is enough to find, for all finite Y₀ ⊆ Y and Q₀ ⊆ Q
such that σ maps Q₀ into Y₀, a price on Y₀ ∪ Q₀ with the two properties: these prices form compact sets, so then there is
one that works for all of them at once." Here Z is Y ∪ Q, the two properties are bounds A ≤ |oo′| ≤ B, and the compact
sets are those of def_price_compact. -/
theorem prop_random_compact {Z : Type*} (A B : Z → Z → ℝ)
    (h : ∀ S : Finset Z, ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ B a b) :
    ∃ w' : Z → Z → ℝ, IsPrice K w' ∧ ∀ a b, A a b ≤ w' a b ∧ w' a b ≤ B a b := by
  classical
  choose d hd hAB using h
  -- the price on T, as a function on all pairs
  let D : Finset Z → Z → Z → ℝ := fun T a b => if h : a ∈ T ∧ b ∈ T then d T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hD : ∀ {S T : Finset Z} (hT : S ⊆ T) (a b : S), D T a b = d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ :=
    fun hT a b => dif_pos ⟨hT a.2, hT b.2⟩
  let U : Ultrafilter (Finset Z) := Ultrafilter.of atTop
  have hmem : ∀ S : Finset Z, ∀ᶠ T in (U : Filter (Finset Z)), S ⊆ T := fun S =>
    Ultrafilter.of_le _ (eventually_ge_atTop S)
  -- on every finite set S the restrictions have a limit, in the compact set of the prices on S below B
  have key : ∀ S : Finset Z, ∃ v : S → S → ℝ, (IsPrice K v ∧ ∀ a b : S, v a b ≤ B a b) ∧
      ∀ a b : S, Tendsto (fun T => D T a b) U (nhds (v a b)) := by
    intro S
    obtain ⟨v, hv, hlim⟩ := (def_price_compact (K := K) fun a b : S => B a b).ultrafilter_le_nhds
      (U.map fun T (a b : S) => D T a b) (by
        rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
        filter_upwards [hmem S] with T hT
        have e : (fun a b : S => D T a b) = fun a b : S => d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ := by
          funext a b
          exact hD hT a b
        refine ⟨?_, fun a b => (hD hT a b).le.trans (hAB T _ _).2⟩
        show IsPrice K fun a b : S => D T a b
        rw [e]
        exact def_price_pullback (hd T) fun a : S => (⟨a, hT a.2⟩ : T))
    have h1 : Tendsto (fun T (a b : S) => D T a b) U (nhds v) := hlim
    exact ⟨v, hv, fun a b => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h1 a) b⟩
  choose v hv hlim using key
  have ha : ∀ a b : Z, a ∈ ({a, b} : Finset Z) := fun a b => by simp
  have hb : ∀ a b : Z, b ∈ ({a, b} : Finset Z) := fun a b => by simp
  -- the limits fit together
  have hfit : ∀ (S : Finset Z) (a b : S), v S a b = v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩ := fun S a b =>
    tendsto_nhds_unique (hlim S a b) (hlim {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩)
  refine ⟨fun a b => v {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩, isPrice_of_finset fun S => ?_, fun a b => ⟨?_, ?_⟩⟩
  · have e : (fun a b : S => v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) = v S := by
      funext a b
      exact (hfit S a b).symm
    rw [e]
    exact (hv S).1
  · refine ge_of_tendsto (hlim {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) ?_
    filter_upwards [hmem {a, b}] with T hT
    exact ((hAB T _ _).1.trans (hD hT ⟨a, ha _ _⟩ ⟨b, hb _ _⟩).ge :)
  · exact (hv {a, b}).2 ⟨a, ha _ _⟩ ⟨b, hb _ _⟩

/-- Proof of Proposition prop:random, the finite case: "So let Y and Q be finite, and let σ take the values π_l with
probabilities θ_l. By a limit we may assume w = s·d_φ, and then s = 1 by homogeneity." The prices that
prop_random_spectral gives for approximations s·d_φ of w have a limit, since they lie in a compact set (def_price_compact). -/
theorem prop_random_limit {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {w : P → P → ℝ}
    (hw : IsPrice K w) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ w' : P ⊕ Q → P ⊕ Q → ℝ, IsPrice K w' ∧ (∀ p p', w' (Sum.inl p) (Sum.inl p') = w p p') ∧
      ∀ a b, w' a b ≤ ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  -- w is s·d_φ up to 1/(n+1)
  choose φ s hs hφ using fun n : ℕ => hw.exists_spec (id : P → P) (hpos n)
  choose φ' h1 h2 using fun n => prop_random_spectral (φ n) θ hθ hθ1 σ
  let B : P ⊕ Q → P ⊕ Q → ℝ := fun a b => ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)
  let d : ℕ → P ⊕ Q → P ⊕ Q → ℝ := fun n a b => s n * (φ' n).e a b
  have hd : ∀ n, IsPrice K (d n) := fun n => def_price_multiple (isPrice_spec (φ' n)) (hs n)
  have hdB : ∀ n a b, d n a b ≤ B a b + 1 / (n + 1) := by
    intro n a b
    calc s n * (φ' n).e a b
        ≤ s n * ∑ l, θ l * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) :=
          mul_le_mul_of_nonneg_left (h2 n a b) (hs n)
      _ = ∑ l, θ l * (s n * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ ∑ l, θ l * (w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) + 1 / (n + 1)) := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hθ l)
        have h3 := (abs_lt.1 (hφ n (Sum.elim id (σ l) a) (Sum.elim id (σ l) b))).1
        simp only [id] at h3
        linarith
      _ = B a b + 1 / (n + 1) := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ1, one_mul]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨w', ⟨hw', -⟩, hlim⟩ := (def_price_compact (K := K) fun a b => B a b + 1).ultrafilter_le_nhds (U.map d) (by
    rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact univ_mem' fun n => ⟨hd n, fun a b => (hdB n a b).trans (by linarith [hle1 n])⟩)
  have hlim' : ∀ a b, Tendsto (fun n => d n a b) U (nhds (w' a b)) := by
    intro a b
    have h3 : Tendsto d U (nhds w') := hlim
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h3 a) b
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) U (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  refine ⟨w', hw', fun p p' => ?_, fun a b => ?_⟩
  · have h3 : Tendsto (fun n => d n (Sum.inl p) (Sum.inl p') - w p p') U (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_) hzero
      have h4 := hφ n p p'
      simp only [id] at h4
      rw [Real.norm_eq_abs, abs_sub_comm]
      show |w p p' - s n * (φ' n).e (Sum.inl p) (Sum.inl p')| ≤ _
      rw [h1]
      exact h4.le
    have h4 := tendsto_nhds_unique h3 ((hlim' (Sum.inl p) (Sum.inl p')).sub_const (w p p'))
    linarith
  · exact le_of_tendsto_of_tendsto (hlim' a b) ((hzero.const_add (B a b)).trans (by rw [add_zero]))
      (Eventually.of_forall fun n => hdB n a b)

/-- Proof of Proposition prop:random: "let σ take the values π_l with probabilities θ_l". On a finite set T of new points a
random map, each σ(o) having finitely many values, takes finitely many values π_l; with their probabilities θ_l, the
expectation of any function of the map is a finite mean. -/
theorem prop_random_values {Y Q Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Q → Ω → Y)
    (hfin : ∀ κ, (Set.range (σ κ)).Finite) (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) (T : Finset Q) :
    ∃ (m : ℕ) (θ : Fin m → ℝ) (π : Fin m → T → Y), (∀ l, 0 ≤ θ l) ∧ ∑ l, θ l = 1 ∧
      ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ = ∑ l, θ l * f (π l) := by
  classical
  have hfin' : (Set.range fun ω (κ : T) => σ κ ω).Finite := by
    refine (Set.Finite.pi' fun κ : T => hfin κ).subset ?_
    rintro _ ⟨ω, rfl⟩ κ
    exact ⟨ω, rfl⟩
  let V : Finset (T → Y) := hfin'.toFinset
  have hV : ∀ ω, (fun κ : T => σ κ ω) ∈ V := fun ω => by simp [V]
  have hmeas' : ∀ f : T → Y, MeasurableSet {ω | (fun κ : T => σ κ ω) = f} := by
    intro f
    have : {ω | (fun κ : T => σ κ ω) = f} = ⋂ κ : T, σ κ ⁻¹' {f κ} := by
      ext ω
      simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun κ => hmeas _ _
  let e : Fin V.card ≃ V := V.equivFin.symm
  have hmean : ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ =
      ∑ l : Fin V.card, μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)} * f (e l) := by
    intro f
    have h1 : ∀ ω, f (fun κ : T => σ κ ω) = ∑ g ∈ V,
        ({ω | (fun κ : T => σ κ ω) = g}).indicator (fun _ => f g) ω := by
      intro ω
      rw [Finset.sum_eq_single (fun κ : T => σ κ ω)]
      · rw [Set.indicator_of_mem]; rfl
      · intro g _ hg
        rw [Set.indicator_of_notMem]
        exact fun h => hg h.symm
      · intro h
        exact absurd (hV ω) h
    simp only [h1]
    rw [integral_finsetSum]
    · rw [← Finset.sum_coe_sort V]
      refine (Fintype.sum_equiv e _ _ fun l => ?_).symm
      rw [integral_indicator (hmeas' _), setIntegral_const, smul_eq_mul]
    · intro g _
      exact (integrable_const _).indicator (hmeas' g)
  refine ⟨V.card, fun l => μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)}, fun l => e l,
    fun l => measureReal_nonneg, ?_, hmean⟩
  have := hmean fun _ => 1
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at this
  exact this.symm

end Random

/-- **Paper: Proposition prop:random.** "Let w be a price on Y, let Q be a set disjoint from Y, and let σ be a random
map Y ∪ Q → Y that is the identity on Y, each σ(o) having finitely many values. Then a price on Y ∪ Q extends w and
satisfies |oo′| ≤ E |σ(o)σ(o′)| for all o, o′." -/
theorem prop_random {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Q → Ω → Y) (hfin : ∀ κ, (Set.range (σ κ)).Finite)
    (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤
        ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ := by
  classical
  -- the two properties: at least w on Y, and at most the expectation
  let A : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' => match o, o' with
    | Sum.inl y, Sum.inl y' => w y y'
    | _, _ => 0
  let E : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' =>
    ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ
  suffices hS : ∀ S : Finset (Y ⊕ Q), ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ E a b by
    obtain ⟨w', hw', h⟩ := prop_random_compact A E hS
    refine ⟨w', hw', fun y y' => le_antisymm ?_ (h (Sum.inl y) (Sum.inl y')).1, fun o o' => (h o o').2⟩
    simpa [E] using (h (Sum.inl y) (Sum.inl y')).2
  intro S
  -- Q₀: the new points of S; Y₀: the old points of S and all values of σ on Q₀
  let T : Finset Q := S.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨m, θ, π, hθ, hθ1, hmean⟩ := prop_random_values μ σ hfin hmeas T
  let R : Finset Y := S.preimage Sum.inl Sum.inl_injective.injOn ∪
    Finset.univ.biUnion fun κ : T => Finset.univ.image fun l => π l κ
  have hR : ∀ l κ, π l κ ∈ R := fun l κ => Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨κ, Finset.mem_univ κ, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩)
  obtain ⟨v, hv, hv1, hv2⟩ := prop_random_limit (def_price_pullback hw (Subtype.val : R → Y)) θ hθ hθ1
    fun l κ => (⟨π l κ, hR l κ⟩ : R)
  -- the points of S among those of Y₀ ∪ Q₀, and their places under a map Q₀ → Y
  let g : S → R ⊕ T := fun a => match a with
    | ⟨Sum.inl y, hy⟩ => Sum.inl ⟨y, Finset.mem_union_left _ (Finset.mem_preimage.2 hy)⟩
    | ⟨Sum.inr κ, hκ⟩ => Sum.inr ⟨κ, Finset.mem_preimage.2 hκ⟩
  let place : (T → Y) → S → Y := fun f a => match a with
    | ⟨Sum.inl y, _⟩ => y
    | ⟨Sum.inr κ, hκ⟩ => f ⟨κ, Finset.mem_preimage.2 hκ⟩
  have hg : ∀ l (a : S), ((Sum.elim id (fun κ => (⟨π l κ, hR l κ⟩ : R)) (g a) : R) : Y) = place (π l) a := by
    rintro l ⟨y | κ, ha⟩ <;> rfl
  have hσ : ∀ ω (a : S), Sum.elim id (fun κ => σ κ ω) a.1 = place (fun κ : T => σ κ ω) a := by
    rintro ω ⟨y | κ, ha⟩ <;> rfl
  refine ⟨fun a b => v (g a) (g b), def_price_pullback hv g, fun a b => ⟨?_, ?_⟩⟩
  · obtain ⟨y | κ, ha⟩ := a <;> obtain ⟨y' | κ', hb⟩ := b
    · exact (hv1 ⟨y, _⟩ ⟨y', _⟩).ge
    all_goals exact hv.nonneg _ _
  · refine (hv2 (g a) (g b)).trans (le_of_eq ?_)
    show _ = ∫ ω, w (Sum.elim id (fun κ => σ κ ω) a.1) (Sum.elim id (fun κ => σ κ ω) b.1) ∂μ
    simp only [hg, hσ]
    exact (hmean fun f => w (place f a) (place f b)).symm

/-- Proposition prop:random for a random map with finitely many values σ_l, taken with probabilities θ_l. -/
theorem prop_random_finite {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Λ : Type} [Fintype Λ] (θ : Λ → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Λ → Q → Y) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤ ∑ l, θ l * w (Sum.elim id (σ l) o) (Sum.elim id (σ l) o') := by
  classical
  let _ : MeasurableSpace Λ := ⊤
  have : MeasurableSingletonClass Λ := ⟨fun _ => trivial⟩
  let p : PMF Λ := PMF.ofFintype (fun l => ENNReal.ofReal (θ l))
    (by rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hθ l, hθ1, ENNReal.ofReal_one])
  obtain ⟨w', h1, h2, h3⟩ := prop_random hw p.toMeasure (fun κ l => σ l κ) (fun κ => Set.toFinite _)
    fun κ y => trivial
  refine ⟨w', h1, h2, fun o o' => (h3 o o').trans (le_of_eq ?_)⟩
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hθ l), smul_eq_mul]

/-- **Paper: Lemma lem:hubs.** "Let I = I₁ ⊔ I₂, let a tensor t on I be a sum of r products of a tensor on I₁ and one
on I₂, and let n_p be its index sizes. For two further parties o₁, o₂ it is a restriction of
∏_{p ∈ I₁} ⟨n_p⟩_{p o₁} · ⟨r⟩_{o₁ o₂} · ∏_{p ∈ I₂} ⟨n_p⟩_{p o₂}, and this remains true when o₁, o₂ are identified with given
parties." In Lean the paper's I is A, its part I₁ is given by the predicate S, and α j, β j are the factors of the j-th
product, functions of the indices in I₁ and in I₂. The map π places the parties of A among those of a set I that also
contains o₁ and o₂, in any way; lem_hubs_further is the case of two further parties. -/
theorem lem_hubs {A : Type} [Fintype A] [DecidableEq A] (π : A → I) (t : Ten K A) (S : A → Prop) [DecidablePred S]
    {r : ℕ} (α β : Fin r → (∀ a, t.ι a) → K)
    (hα : ∀ j x x', (∀ a, S a → x a = x' a) → α j x = α j x')
    (hβ : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → β j x = β j x')
    (hs : ∀ x, t.val x = ∑ j, α j x * β j x) (o₁ o₂ : I) :
    Restr (Ten.push π t)
      (Ten.prod (fun a => Ten.wire K (Fintype.card (t.ι a)) (π a) (if S a then o₁ else o₂)) * Ten.wire K r o₁ o₂) := by
  classical
  let Λ : Option A → Type := fun o => match o with
    | none => Fin r
    | some a => t.ι a
  let iΛ : ∀ o, Fintype (Λ o) := fun o => match o with
    | none => inferInstanceAs (Fintype (Fin r))
    | some a => t.fin a
  let ξ : A ⊕ Bool → I := Sum.elim π fun b => if b then o₁ else o₂
  let src : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr true) Sum.inl
  let tgt : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr false) fun a => Sum.inr (decide (S a))
  let tab : A ⊕ Bool → (∀ a, t.ι a) → (∀ o, Λ o) → K := fun v x l => match v with
    | Sum.inl a => if x a = l (some a) then 1 else 0
    | Sum.inr true => α (l none) fun a => l (some a)
    | Sum.inr false => β (l none) fun a => l (some a)
  have key := Restr.of_edges π ξ t Λ src tgt tab (by
    rintro (a | b) x x' l l' hx hl
    · have h1 := hx a rfl
      have h2 : l (some a) = l' (some a) := hl (some a) (Or.inl rfl)
      show (if x a = l (some a) then (1 : K) else 0) = if x' a = l' (some a) then 1 else 0
      rw [h1, h2]
    · cases b
      · have h1 : l none = l' none := hl none (Or.inr rfl)
        show β (l none) _ = β (l' none) _
        rw [h1]
        refine hβ _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]
      · have h1 : l none = l' none := hl none (Or.inl rfl)
        show α (l none) _ = α (l' none) _
        rw [h1]
        refine hα _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]) (by
    intro x
    have e1 : ∀ l : ∀ o, Λ o, ∏ v, tab v x l =
        (∏ a, if x a = l (some a) then (1 : K) else 0) *
          (α (l none) (fun a => l (some a)) * β (l none) fun a => l (some a)) := by
      intro l
      rw [Fintype.prod_sum_type]
      congr 1
      rw [Fintype.prod_bool]
    simp only [e1]
    rw [hs]
    symm
    refine (Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Λ)) _
      (fun z : Λ none × (∀ a, Λ (some a)) => (∏ a, if x a = z.2 a then (1 : K) else 0) *
          (α z.1 z.2 * β z.1 z.2)) fun l => rfl).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hy
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg fun hxy => ha hxy.symm), zero_mul]
    · simp)
  refine key.trans ((Equi.prod_reindex _ (Equiv.optionEquivSumPUnit A).symm).1.trans
    ((Equi.prod_sum _).1.trans (Restr.mul (Restr.prod fun a => ?_) ((Equi.prod_unique _).1.trans ?_))))
  · show Restr (Ten.wire K (Fintype.card (t.ι a)) (π a) (if decide (S a) then o₁ else o₂)) _
    simp only [decide_eq_true_eq]
    exact Restr.refl _
  · show Restr (Ten.wire K (Fintype.card (Fin r)) o₁ o₂) _
    rw [Fintype.card_fin]
    exact Restr.refl _

/-- Lemma lem:hubs as printed, "for two further parties o₁, o₂": the parties are I₁ ⊔ I₂ and the two hubs. -/
theorem lem_hubs_further {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (t : Ten K (I₁ ⊕ I₂)) {r : ℕ} (α : Fin r → (∀ p, t.ι (Sum.inl p)) → K) (β : Fin r → (∀ p, t.ι (Sum.inr p)) → K)
    (hs : ∀ x, t.val x = ∑ j, α j (fun p => x (Sum.inl p)) * β j fun p => x (Sum.inr p)) :
    Restr (Ten.push (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t)
      (Ten.prod (fun p : I₁ => Ten.wire K (Fintype.card (t.ι (Sum.inl p))) (Sum.inl (Sum.inl p)) (Sum.inr true)) *
        Ten.wire K r (Sum.inr true) (Sum.inr false) *
        Ten.prod fun p : I₂ => Ten.wire K (Fintype.card (t.ι (Sum.inr p))) (Sum.inl (Sum.inr p)) (Sum.inr false)) := by
  have key := lem_hubs (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t (fun a => a.isLeft = true)
    (fun j x => α j fun p => x (Sum.inl p)) (fun j x => β j fun p => x (Sum.inr p))
    (fun j x x' h => congrArg (α j) (funext fun p => h (Sum.inl p) rfl))
    (fun j x x' h => congrArg (β j) (funext fun p => h (Sum.inr p) (by simp))) hs (Sum.inr true) (Sum.inr false)
  refine key.trans ((Restr.mul (Equi.prod_sum _).1 (Restr.refl _)).trans ?_)
  exact ((Equi.mul_assoc _ _ _).trans (((Equi.refl _).mul (Equi.mul_comm _ _)).trans (Equi.mul_assoc _ _ _).symm)).1

end Paper
end


namespace Paper
private theorem thm_cn {K : Type} [Field K] {Y : Type} {w : Y → Y → ℝ}
    (hw : Nc.Price.IsPrice K w) (x v m z : Y) {D : ℝ}
    (h1 : w x m ≤ D) (h2 : w v m ≤ D) (h3 : w x v = 2 * D) :
    w z m ^ 2 ≤ 1 / 2 * w z x ^ 2 + 1 / 2 * w z v ^ 2 - D ^ 2 :=
  ValiantBorder.priceMidpointCN hw x v m z h1 h2 h3
end Paper
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Complete CAT(0) spaces: definitions

`Cat.CN X`: `X` is complete and any two points have a midpoint with the CN inequality.
What follows from the defining inequalities of barycentres (`IsBary`) and of points at
fraction `t` (`IsPt`) in any metric space. The facts on CAT(0) spaces are Lemma lem:toolkit, in Paper/Toolkit.lean.
-/

open Filter Topology

namespace Cat

/-- Complete CAT(0) spaces: complete, and every two points have a midpoint with the
inequality of Bruhat and Tits. -/
class CN (X : Type*) [MetricSpace X] : Prop extends CompleteSpace X where
  exists_mid : ∀ x v : X, ∃ m : X, ∀ z : X,
    dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4

variable {X : Type*} [MetricSpace X]

section min
variable [CN X]

/-- The midpoint. -/
noncomputable def mid (x v : X) : X := Classical.choose (CN.exists_mid x v)

theorem cn (x v z : X) :
    dist z (mid x v) ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 :=
  Classical.choose_spec (CN.exists_mid x v) z

theorem dist_mid_left (x v : X) : dist x (mid x v) = dist x v / 2 := by
  have h1 := cn x v x
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_self] at h1 h2
  rw [dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3
  have ha : dist x (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

theorem dist_mid_right (x v : X) : dist (mid x v) v = dist x v / 2 := by
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_mid_left] at h3
  rw [dist_self, dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3 ⊢
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

end min

/-! ### Barycentres -/

section bary
variable {ι : Type*} [Fintype ι]

/-- `b` is the barycentre of the points `x i` with weights `w i` (of any total weight):
the inequality of variances. -/
def IsBary (w : ι → ℝ) (x : ι → X) (b : X) : Prop :=
  ∀ y, ∑ i, w i * dist b (x i) ^ 2 + (∑ i, w i) * dist y b ^ 2 ≤ ∑ i, w i * dist y (x i) ^ 2

theorem IsBary.unique {w : ι → ℝ} {x : ι → X} {b b' : X} (hw : 0 < ∑ i, w i)
    (h : IsBary w x b) (h' : IsBary w x b') : b = b' := by
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm] at h1
  have h3 : (∑ i, w i) * dist b b' ^ 2 ≤ 0 := by linarith
  have h4 : dist b b' ^ 2 ≤ 0 := by
    by_contra h5
    push Not at h5
    exact absurd h3 (not_le.2 (mul_pos hw h5))
  have h5 : dist b b' = 0 := by
    have := sq_nonneg (dist b b')
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 this)
  exact dist_eq_zero.1 h5

/-- A barycentre is mapped to a barycentre by a surjective isometry. -/
theorem IsBary.map {Y : Type*} [MetricSpace Y] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) {f : X → Y} (hf : Isometry f) (hs : Function.Surjective f) :
    IsBary w (fun i => f (x i)) (f b) := by
  intro y
  obtain ⟨y, rfl⟩ := hs y
  simpa only [hf.dist_eq] using h y

/-- Barycentres don't depend on the names of the points. -/
theorem IsBary.comp_equiv {κ : Type*} [Fintype κ] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) (e : κ ≃ ι) : IsBary (w ∘ e) (x ∘ e) b := by
  intro y
  have h1 := h y
  rw [← e.sum_comp fun i => w i * dist b (x i) ^ 2, ← e.sum_comp w,
    ← e.sum_comp fun i => w i * dist y (x i) ^ 2] at h1
  exact h1

end bary

/-! ### Points at fraction `t` -/

/-- `b` is the point at fraction `t` between `x` and `v`. -/
def IsPt (x v : X) (t : ℝ) (b : X) : Prop :=
  ∀ z, dist z b ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2

theorem IsPt.dist_left {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist x b = t * dist x v := by
  have h2 := h x
  have h3 := h v
  have h4 := dist_triangle x b v
  rw [dist_self] at h2 h3
  rw [dist_comm v x] at h3
  rw [dist_comm b v] at h4
  have ha : dist x b ≤ t * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg h0 dist_nonneg) |>.2
    nlinarith
  have hb : dist v b ≤ (1 - t) * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg (by linarith) dist_nonneg) |>.2
    nlinarith
  linarith

theorem IsPt.symm {x v b : X} {t : ℝ} (h : IsPt x v t b) : IsPt v x (1 - t) b := by
  intro z
  have := h z
  rw [dist_comm v x]
  linarith

theorem IsPt.dist_right {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist b v = (1 - t) * dist x v := by
  have := h.symm.dist_left (by linarith) (by linarith)
  rw [dist_comm b v, this, dist_comm v x]

/-- A point with the distances of the point at fraction `t` is the point at fraction `t`. -/
theorem IsPt.eq_of_dist {x v b b' : X} {t : ℝ} (h : IsPt x v t b)
    (h2 : dist x b' = t * dist x v) (h3 : dist b' v = (1 - t) * dist x v) : b' = b := by
  have h4 := h b'
  rw [dist_comm b' x, h2, h3] at h4
  have h5 : dist b' b ^ 2 ≤ 0 := by nlinarith
  exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h5 (sq_nonneg _)))

theorem le_two_mul_of_forall {S a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ τ : ℝ, 0 < τ → S ≤ τ * b ^ 2 + a ^ 2 / τ) : S ≤ 2 * a * b := by
  rcases ha.eq_or_lt with rfl | ha
  · by_contra hS
    push Not at hS
    simp only [mul_zero, zero_mul] at hS
    have h1 := h (S / (2 * (b ^ 2 + 1))) (by positivity)
    have h2 : S / (2 * (b ^ 2 + 1)) * b ^ 2 ≤ S / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    simp at h1
    linarith
  rcases hb.eq_or_lt with rfl | hb
  · by_contra hS
    push Not at hS
    rw [mul_zero] at hS
    have h1 := h (2 * (a ^ 2 + 1) / S) (by positivity)
    have h2 : a ^ 2 / (2 * (a ^ 2 + 1) / S) ≤ S / 2 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : 2 * (a ^ 2 + 1) / S * (0 : ℝ) ^ 2 = 0 := by ring
    linarith
  · have h1 := h (a / b) (by positivity)
    have h2 : a / b * b ^ 2 + a ^ 2 / (a / b) = 2 * a * b := by
      field_simp
      ring
    linarith

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The metric of a finite ℓ²-product
-/

namespace Cat

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)]

theorem piLp_dist_sq (f g : PiLp 2 X) : dist f g ^ 2 = ∑ i, dist (f i) (g i) ^ 2 := by
  rw [PiLp.dist_eq_sum (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Prices are nonpositively curved": CAT(0) spaces

The definition of CAT(0) spaces and Lemma lem:toolkit, part by part. All of it rests on the inequality (CN) alone, which is
the class Cat.CN. Two predicates of the library are used in the proofs: Cat.IsPt x v t b says that b satisfies the inequality
of part (a), and Cat.IsBary w x b that b satisfies the inequality of part (c), for weights w.
-/

namespace Paper

open Finset Filter Topology Cat

/-- The paper's definition: "A complete metric space is CAT(0) if any two points x, v have a midpoint and (CN) holds
for it." -/
theorem cat0_iff (X : Type) [MetricSpace X] : Cat.CN X ↔ CompleteSpace X ∧ ∀ x v : X, ∃ m,
    dist x m = dist x v / 2 ∧ dist m v = dist x v / 2 ∧
      ∀ z, dist z m ^ 2 ≤ 1 / 2 * dist z x ^ 2 + 1 / 2 * dist z v ^ 2 - (dist x v / 2) ^ 2 := by
  constructor
  · intro h
    refine ⟨h.toCompleteSpace, fun x v => ⟨Cat.mid x v, Cat.dist_mid_left x v, Cat.dist_mid_right x v, fun z => ?_⟩⟩
    linarith [Cat.cn x v z]
  · rintro ⟨hc, h⟩
    refine { hc with exists_mid := fun x v => ?_ }
    obtain ⟨m, -, -, hm⟩ := h x v
    exact ⟨m, fun z => by linarith [hm z]⟩

section Toolkit

variable {Y : Type*} [MetricSpace Y] [CN Y]

/-- The minimization behind parts (a), (c) and (d): "Strict convexity of the functions to be minimized, from (CN), makes
minimizing sequences converge; comparing the minimum with points close to it on [b,y], respectively [Py,q], gives the
inequalities." Let C be nonempty, closed and convex, and let Θ ≥ 0 be continuous with
Θ(m) ≤ ½Θ(x) + ½Θ(v) − (c/4)|xv|² for the midpoint m of x, v ∈ C, where c > 0. Then some b ∈ C has Θ(y) ≥ Θ(b) + c|yb|² for all
y ∈ C. -/
theorem lem_toolkit_minimization (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty)
    (hmem : ∀ x ∈ C, ∀ v ∈ C, mid x v ∈ C) (Θ : Y → ℝ) (hF : Continuous Θ)
    (hF0 : ∀ x, 0 ≤ Θ x) {c : ℝ} (hc : 0 < c)
    (hconv : ∀ x ∈ C, ∀ v ∈ C, Θ (mid x v) ≤ (Θ x + Θ v) / 2 - c / 4 * dist x v ^ 2) :
    ∃ b ∈ C, ∀ y ∈ C, Θ b + c * dist y b ^ 2 ≤ Θ y := by
  set I := sInf (Θ '' C) with hI
  have hbdd : BddBelow (Θ '' C) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hF0 x⟩
  have hle : ∀ y ∈ C, I ≤ Θ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hseq : ∀ n : ℕ, ∃ y ∈ C, Θ y < I + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Real.lt_sInf_add_pos (hne.image Θ)
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    exact ⟨y, hy, h⟩
  choose u huC hu using hseq
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < c / 4 * ε ^ 2 by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hconv _ (huC m) _ (huC n)
    have h2 := hle _ (hmem _ (huC m) _ (huC n))
    have hmono : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      intro k hk
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h3 := hu m
    have h4 := hu n
    have h5 := hmono m hm
    have h6 := hmono n hn
    have h7 : c / 4 * dist (u m) (u n) ^ 2 < c / 4 * ε ^ 2 := by linarith
    have h8 : dist (u m) (u n) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h7 (by positivity)
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h8
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hbC : b ∈ C := hC.mem_of_tendsto hb (Eventually.of_forall huC)
  have hFb : Θ b ≤ I := by
    have h1 : Tendsto (fun n => Θ (u n)) atTop (𝓝 (Θ b)) := (hF.tendsto b).comp hb
    have h2 : Tendsto (fun n : ℕ => I + 1 / ((n : ℝ) + 1)) atTop (𝓝 (I + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => (hu n).le
  refine ⟨b, hbC, ?_⟩
  have key : ∀ k : ℕ, ∀ y ∈ C, Θ b + c * (1 - (1 / 2) ^ k) * dist y b ^ 2 ≤ Θ y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hFb.trans (hle y hy)
    | succ k ih =>
      intro y hy
      have h1 := ih _ (hmem b hbC y hy)
      have h2 := hconv b hbC y hy
      rw [dist_comm _ b, dist_mid_left] at h1
      rw [dist_comm y b, pow_succ]
      nlinarith
  intro y hy
  have h1 : Tendsto (fun k : ℕ => Θ b + c * (1 - (1 / 2 : ℝ) ^ k) * dist y b ^ 2) atTop
      (𝓝 (Θ b + c * (1 - 0) * dist y b ^ 2)) := by
    apply Tendsto.const_add
    apply Tendsto.mul_const
    apply Tendsto.const_mul
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_sub 1
  rw [sub_zero, mul_one] at h1
  exact le_of_tendsto' h1 fun k => key k y hy

/-- The first half of part (c) with weights: points x_i with weights w_i ≥ 0 have a barycenter b, with
∑ w_i|yx_i|² ≥ (∑ w_i)|yb|² + ∑ w_i|bx_i|² for all y. It is the minimizer of y ↦ ∑ w_i|yx_i|² given by lem_toolkit_minimization. -/
theorem lem_toolkit_c_exists {ι : Type*} [Fintype ι] [Nonempty Y] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ι → Y) :
    ∃ b, IsBary w x b := by
  rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i).eq_or_lt with h0 | h0
  · have h : ∀ i, w i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => hw i).1 h0.symm
      exact this i (Finset.mem_univ i)
    exact ⟨Classical.arbitrary Y, fun y => by simp [h]⟩
  · obtain ⟨b, -, hb⟩ := lem_toolkit_minimization (Y := Y) Set.univ isClosed_univ Set.univ_nonempty
      (fun _ _ _ _ => Set.mem_univ _) (fun y => ∑ i, w i * dist y (x i) ^ 2) (by fun_prop)
      (fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) h0
      (by
        intro y _ y' _
        have h : ∀ i, w i * dist (mid y y') (x i) ^ 2 ≤
            w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4) := by
          intro i
          have h1 := mul_le_mul_of_nonneg_left (cn y y' (x i)) (hw i)
          rw [dist_comm (x i), dist_comm (x i), dist_comm (x i)] at h1
          linarith
        calc ∑ i, w i * dist (mid y y') (x i) ^ 2
            ≤ ∑ i, (w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4)) := Finset.sum_le_sum fun i _ => h i
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
              ← Finset.sum_div, ← Finset.sum_mul]
            ring)
    exact ⟨b, fun y => hb y (Set.mem_univ y)⟩

/-- **Paper: Lemma lem:toolkit (a).** "For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|, (1−t)|xv| from
them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|²." The point is the barycenter of x and v with the weights 1−t and t. -/
theorem lem_toolkit_a (x v : Y) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ γ : Y,
    (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
    (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
    ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2 := by
  have : Nonempty Y := ⟨x⟩
  obtain ⟨b, hb⟩ := lem_toolkit_c_exists (Y := Y) (ι := Bool) (fun i => cond i t (1 - t))
    (by intro i; cases i <;> simp <;> linarith) (fun i => cond i v x)
  have hpt : IsPt x v t b := by
    intro z
    have h := hb z
    simp only [Fintype.sum_bool, cond_true, cond_false] at h
    have h2 := dist_triangle x b v
    rw [dist_comm x b] at h2
    have h3 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist b x + dist b v) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h0 (by linarith))
      exact pow_le_pow_left₀ dist_nonneg h2 2
    have h4 : 0 ≤ ((1 - t) * dist b x - t * dist b v) ^ 2 := sq_nonneg _
    nlinarith
  exact ⟨b, ⟨hpt.dist_left h0 h1, hpt.dist_right h0 h1⟩, fun _ e1 e2 => hpt.eq_of_dist e1 e2, hpt⟩

/-- Part (a) in the words of the library. -/
theorem lem_toolkit_a_isPt (x v : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ b, IsPt x v t b := by
  obtain ⟨γ, -, -, h⟩ := lem_toolkit_a x v t h0 h1
  exact ⟨γ, h⟩

/-- A point with the distances of part (a) satisfies its inequality. -/
theorem lem_toolkit_a_of_dist {x v c : Y} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (e1 : dist x c = t * dist x v)
    (e2 : dist c v = (1 - t) * dist x v) : IsPt x v t c := by
  obtain ⟨γ, -, hu, h⟩ := lem_toolkit_a x v t h0 h1
  rw [hu c e1 e2]
  exact h

/-- The first step of the proof of part (b): for the point q at s on [p,p′], insert (a) twice into
t(1−t)|xv|² ≤ (1−t)|xq|² + t|qv|². -/
theorem lem_toolkit_b_box (x v p p' : Y) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) * dist x v ^ 2 + s * (1 - s) * dist p p' ^ 2 ≤
      (1 - t) * (1 - s) * dist x p ^ 2 + (1 - t) * s * dist x p' ^ 2
        + t * (1 - s) * dist v p ^ 2 + t * s * dist v p' ^ 2 := by
  obtain ⟨q, -, -, hq⟩ := lem_toolkit_a p p' s hs0 hs1
  have h1 := mul_le_mul_of_nonneg_left (hq x) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hq v) ht0
  have h3 := dist_triangle x q v
  rw [dist_comm q v] at h3
  have h4 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist x q + dist v q) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg h3 2)
      (mul_nonneg ht0 (by linarith))
  have h5 : 0 ≤ ((1 - t) * dist x q - t * dist v q) ^ 2 := sq_nonneg _
  nlinarith

/-- The second step of the proof of part (b), the choice of the parameter: it gives the first inequality of (b), here as
|x₁x₃|² + |x₂x₄|² ≤ |x₁x₂|² + |x₃x₄|² + 2|x₂x₃||x₁x₄|. -/
theorem lem_toolkit_b_first (x₁ x₂ x₃ x₄ : Y) :
    dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 ≤
      dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + 2 * dist x₂ x₃ * dist x₁ x₄ := by
  have key : dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 - dist x₁ x₂ ^ 2 - dist x₃ x₄ ^ 2 ≤
      2 * dist x₁ x₄ * dist x₂ x₃ := by
    apply le_two_mul_of_forall dist_nonneg dist_nonneg
    intro τ hτ
    have hs0 : 0 ≤ τ / (1 + τ) := by positivity
    have hs1 : τ / (1 + τ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h := lem_toolkit_b_box x₁ x₃ x₄ x₂ hs0 hs1 hs0 hs1
    have e1 : 1 - τ / (1 + τ) = 1 / (1 + τ) := by field_simp; ring
    rw [e1] at h
    have hpos : 0 < (1 + τ) ^ 2 / τ := by positivity
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have e2 : (1 + τ) ^ 2 / τ * (τ / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₃ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₄ x₂ ^ 2) =
        dist x₁ x₃ ^ 2 + dist x₄ x₂ ^ 2 := by field_simp
    have e3 : (1 + τ) ^ 2 / τ * (1 / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₄ ^ 2 +
        1 / (1 + τ) * (τ / (1 + τ)) * dist x₁ x₂ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₃ x₄ ^ 2 +
        τ / (1 + τ) * (τ / (1 + τ)) * dist x₃ x₂ ^ 2) =
        dist x₁ x₄ ^ 2 / τ + dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + τ * dist x₃ x₂ ^ 2 := by
      field_simp
    rw [e2, e3, dist_comm x₄ x₂, dist_comm x₃ x₂] at h2
    linarith
  linarith

/-- **Paper: Lemma lem:toolkit (b).** "|xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in particular the squared diagonals of a
quadrangle add up to at most its squared sides, and if there is equality, opposite sides are equal." -/
theorem lem_toolkit_b (x v y u : Y) :
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
    (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
      dist x y = dist v u ∧ dist y v = dist x u) := by
  have h1 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v := by
    have h := lem_toolkit_b_first x u v y
    rw [dist_comm u y, dist_comm v y] at h
    linarith
  have h2 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist v u ^ 2 + 2 * dist y v * dist x u :=
    lem_toolkit_b_first x y v u
  refine ⟨h1, by nlinarith [sq_nonneg (dist y v - dist x u)], fun he => ⟨?_, ?_⟩⟩
  · have h3 : (dist x y - dist v u) ^ 2 ≤ 0 := by
      rw [dist_comm u v] at h1
      nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  · have h3 : (dist y v - dist x u) ^ 2 ≤ 0 := by nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith

/-- The second half of part (c) with weights: (∑ w_i)|bb′| ≤ ∑ w_i|x_ix′_i|. "Adding the inequality of (c) for (b,x) at b′
and for (b′,x′) at b, and applying (b) to every b, b′, x_i, x′_i". -/
theorem lem_toolkit_c_contract {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {x x' : ι → Y} {b b' : Y}
    (h : IsBary w x b) (h' : IsBary w x' b') :
    (∑ i, w i) * dist b b' ≤ ∑ i, w i * dist (x i) (x' i) := by
  rcases (dist_nonneg (x := b) (y := b')).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) dist_nonneg
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm b' b] at h1
  have h3 : ∀ i, w i * dist b' (x i) ^ 2 + w i * dist b (x' i) ^ 2 ≤
      w i * dist b (x i) ^ 2 + w i * dist b' (x' i) ^ 2
        + 2 * dist b b' * (w i * dist (x i) (x' i)) := by
    intro i
    have h4 := mul_le_mul_of_nonneg_left (lem_toolkit_b b' (x i) b (x' i)).1 (hw i)
    rw [dist_comm (x' i) (x i), dist_comm b' b] at h4
    linarith
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  simp only [Finset.sum_add_distrib] at h5
  rw [← Finset.mul_sum] at h5
  have h6 : dist b b' * ((∑ i, w i) * dist b b') ≤
      dist b b' * ∑ i, w i * dist (x i) (x' i) := by nlinarith
  exact le_of_mul_le_mul_left h6 h0

/-- **Paper: Lemma lem:toolkit (c).** "Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|." Here a barycenter is a
point with the displayed inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly
one. -/
theorem lem_toolkit_c :
    (∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
      (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
      (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
      (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i) := by
  constructor
  · intro n x hn
    have : Nonempty Y := ⟨x ⟨0, hn⟩⟩
    obtain ⟨b, hb⟩ := lem_toolkit_c_exists (fun _ : Fin n => (1 : ℝ)) (fun _ => zero_le_one) x
    refine ⟨b, fun y => ?_⟩
    have := hb y
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    linarith
  · intro n x x' b b' hb hb'
    have conv : ∀ (x : Fin n → Y) (b : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
          IsBary (fun _ => (1 : ℝ)) x b := by
      intro x b h y
      simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      linarith [h y]
    simpa using lem_toolkit_c_contract (fun _ => zero_le_one) (conv x b hb) (conv x' b' hb')

/-- Part (c): the barycenter is "the minimizer of y ↦ ∑|yx_i|²". For n ≥ 1 there is exactly one minimizer, and a point is the
minimizer if and only if it satisfies the inequality of (c), by which lem_toolkit_c describes the barycenter. -/
theorem lem_toolkit_c_minimizer {n : ℕ} (hn : 0 < n) (x : Fin n → Y) :
    (∃! b, ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ↔
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨b₀, h₀⟩ := lem_toolkit_c.1 n x hn
  have hmin : ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := fun b h y => by
    nlinarith [h y, sq_nonneg (dist y b)]
  have huniq : ∀ b, (∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) → b = b₀ := fun b h => by
    have h1 : (n : ℝ) * dist b b₀ ^ 2 ≤ 0 := by linarith [h₀ b, h b₀]
    have h2 : dist b b₀ ^ 2 ≤ 0 := by nlinarith
    exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))
  exact ⟨⟨b₀, hmin b₀ h₀, huniq⟩, fun b => ⟨hmin b, fun h => (huniq b h).symm ▸ h₀⟩⟩

/-- **Paper: Lemma lem:toolkit (d).** "A nonempty closed convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for
q ∈ F." A set is convex if it contains the midpoints of its points. -/
theorem lem_toolkit_d (F : Set Y) (hF : IsClosed F) (hne : F.Nonempty)
    (hconv : ∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) (y : Y) :
    ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := by
  obtain ⟨P, hP, h⟩ := lem_toolkit_minimization F hF hne
    (fun x hx v hv => hconv x hx v hv _ (dist_mid_left x v) (dist_mid_right x v))
    (fun q => dist y q ^ 2) (by fun_prop) (fun _ => sq_nonneg _) one_pos
    (fun x _ v _ => by linarith [cn x v y])
  have h' : ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := fun q hq => by
    have := h q hq
    rw [dist_comm P q]
    linarith
  exact ⟨P, hP, fun q hq => (abs_le_of_sq_le_sq' (by nlinarith [h' q hq]) dist_nonneg).2, h'⟩

/-- Part (e) for factors that may differ. -/
theorem lem_toolkit_e_general {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)] [∀ i, CN (X i)] :
    CN (PiLp 2 X) where
  exists_mid x v := by
    refine ⟨WithLp.toLp 2 fun i => mid (x i) (v i), fun z => ?_⟩
    simp only [piLp_dist_sq]
    calc ∑ i, dist (z i) (mid (x i) (v i)) ^ 2
        ≤ ∑ i, ((dist (z i) (x i) ^ 2 + dist (z i) (v i) ^ 2) / 2
          - dist (x i) (v i) ^ 2 / 4) := Finset.sum_le_sum fun i _ => cn _ _ _
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib]

/-- **Paper: Lemma lem:toolkit (e).** "Finite L² products of copies of Y are CAT(0)." -/
theorem lem_toolkit_e (ι : Type) [Fintype ι] : CN (PiLp 2 fun _ : ι => Y) := lem_toolkit_e_general

/-! Part (f). The letters are those of the paper: |xy| = |uv| = δ, |xu| = |yv| = h, a is the point at s on [x,u] and b the
point at t on [y,v]. The steps before the last one ask only that the squared diagonals add up to at least 2h² + 2δ² (a flat
parallelogram). The form Φ(p,p′;r,r′) = |pr′|² + |p′r|² − |pr|² − |p′r′|² is at most 2|pp′||rr′| by (b), and it is additive when
[p,p′] and [r,r′] are cut; so equality for the whole is inherited by the parts. -/

/-- Φ(p,p′;r,r′) ≤ 2|pp′||rr′|, by part (b). -/
theorem lem_toolkit_f_form (p p' r r' : Y) :
    dist p r' ^ 2 + dist p' r ^ 2 - dist p r ^ 2 - dist p' r' ^ 2 ≤ 2 * dist p p' * dist r r' := by
  linarith [(lem_toolkit_b p r' p' r).1]

/-- The form is additive, Φ(x,u;y,v) = Φ(x,a;y,b) + Φ(x,a;b,v) + Φ(a,u;y,b) + Φ(a,u;b,v), and the four bounds of
lem_toolkit_f_form add up to 2h², which is at most Φ(x,u;y,v) by hypothesis. So all four are equalities; the first one says
|xb|² + |ay|² − δ² − |ab|² = 2sth². -/
theorem lem_toolkit_f_parts {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist x b ^ 2 + dist a y ^ 2 - δ ^ 2 - dist a b ^ 2 = 2 * s * t * h ^ 2 := by
  have e1 := ha.dist_left hs0 hs1
  have e2 := ha.dist_right hs0 hs1
  have e3 := hb.dist_left ht0 ht1
  have e4 := hb.dist_right ht0 ht1
  rw [hp] at e1 e2
  rw [hp'] at e3 e4
  have f1 := lem_toolkit_f_form x a y b
  have f2 := lem_toolkit_f_form x a b v
  have f3 := lem_toolkit_f_form a u y b
  have f4 := lem_toolkit_f_form a u b v
  rw [e1, e3, hq'] at f1
  rw [e1, e4] at f2
  rw [e2, e3] at f3
  rw [e2, e4, hq] at f4
  nlinarith

/-- The case s = t: then |ab| = δ, and |xb|² and |ay|² have the values that the inequality of (a) allows at most. -/
theorem lem_toolkit_f_same {x u v y a b : Y} {h δ s : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : IsPt x u s a) (hb : IsPt y v s b) :
    dist a b = δ ∧ dist x b ^ 2 = (1 - s) * δ ^ 2 + s * dist x v ^ 2 - s * (1 - s) * h ^ 2 ∧
      dist a y ^ 2 = (1 - s) * δ ^ 2 + s * dist u y ^ 2 - s * (1 - s) * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 hs0 hs1 ha hb
  have h2 := lem_toolkit_b_first x a b y
  have e1 := ha.dist_left hs0 hs1
  have e3 := hb.dist_left hs0 hs1
  rw [hp] at e1
  rw [hp'] at e3
  rw [dist_comm b y, e1, e3, hq'] at h2
  have h3 : (dist a b - δ) ^ 2 ≤ 0 := by nlinarith
  have h4 : dist a b = δ := by
    have : dist a b - δ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  have h5 := hb x
  have h6 := ha y
  rw [hp', hq'] at h5
  rw [hp, dist_comm y a, dist_comm y x, dist_comm y u, hq'] at h6
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  rw [h4] at h1
  have h8 : dist x v ^ 2 + dist u y ^ 2 = 2 * h ^ 2 + 2 * δ ^ 2 := le_antisymm (by linarith) hd
  have h9 : s * dist x v ^ 2 + s * dist u y ^ 2 = s * (2 * h ^ 2 + 2 * δ ^ 2) := by
    rw [← mul_add, h8]
  refine ⟨h4, ?_, ?_⟩ <;> nlinarith

/-- The values of |xb|² and |ay|² from lem_toolkit_f_same, inserted into lem_toolkit_f_parts: the formula for |ab|², still in
terms of the two diagonals. -/
theorem lem_toolkit_f_parallelogram {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = (1 - s - t) * δ ^ 2 + t * dist x v ^ 2 + s * dist u y ^ 2
      - s * (1 - s) * h ^ 2 - t * (1 - t) * h ^ 2 - 2 * s * t * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 ht0 ht1 ha hb
  obtain ⟨a', ha'⟩ := lem_toolkit_a_isPt x u ht0 ht1
  obtain ⟨b', hb'⟩ := lem_toolkit_a_isPt y v hs0 hs1
  have h2 := (lem_toolkit_f_same hp hp' hq hq' hd ht0 ht1 ha' hb).2.1
  have h3 := (lem_toolkit_f_same hp hp' hq hq' hd hs0 hs1 ha hb').2.2
  rw [h2, h3] at h1
  linarith

/-- Part (f), with a ∈ [x,u] and b ∈ [y,v] given by the inequality of (a) (Cat.IsPt), and with lower bounds for the diagonals. -/
theorem lem_toolkit_f_isPt {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : h ^ 2 + δ ^ 2 ≤ dist x v ^ 2) (hd' : h ^ 2 + δ ^ 2 ≤ dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = δ ^ 2 + (s - t) ^ 2 * h ^ 2 := by
  have hab := lem_toolkit_f_parallelogram hp hp' hq hq' (by linarith) hs0 hs1 ht0 ht1 ha hb
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  have h8 : dist x v ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  have h9 : dist u y ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  rw [hab, h8, h9]
  ring

/-- **Paper: Lemma lem:toolkit (f).** "Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared
length δ² + h², and a ∈ [x,u], b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." -/
theorem lem_toolkit_f (x y u v a b : Y) (δ h s t : ℝ) (hxy : dist x y = δ) (huv : dist u v = δ) (hxu : dist x u = h)
    (hyv : dist y v = h) (d1 : dist x v ^ 2 = δ ^ 2 + h ^ 2) (d2 : dist y u ^ 2 = δ ^ 2 + h ^ 2) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a1 : dist x a = s * dist x u) (a2 : dist a u = (1 - s) * dist x u)
    (b1 : dist y b = t * dist y v) (b2 : dist b v = (1 - t) * dist y v) :
    dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 := by
  have := lem_toolkit_f_isPt (x := x) (u := u) (y := y) (v := v) (a := a) (b := b) hxu hyv huv hxy
    (by linarith) (by rw [dist_comm u y]; linarith) hs0 hs1 ht0 ht1 (lem_toolkit_a_of_dist hs0 hs1 a1 a2)
    (lem_toolkit_a_of_dist ht0 ht1 b1 b2)
  linarith

end Toolkit

open Cat in
/-- **Paper: Lemma lem:toolkit.** "Let Y be CAT(0). (a) For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|,
(1−t)|xv| from them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|². (b) |xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in
particular the squared diagonals of a quadrangle add up to at most its squared sides, and if there is equality, opposite sides
are equal. (c) Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|. (d) A nonempty closed
convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for q ∈ F. (e) Finite L² products of copies of Y are CAT(0).
(f) Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared length δ² + h², and a ∈ [x,u],
b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." In (c) a barycenter is a point with the displayed
inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly one. -/
theorem lem_toolkit {Y : Type} [MetricSpace Y] [CN Y] :
    (∀ (x v : Y) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ γ : Y,
      (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
      (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
      ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2) ∧
    (∀ x v y u : Y,
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
      (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
        dist x y = dist v u ∧ dist y v = dist x u)) ∧
    ((∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
        (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
      ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
        (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
        (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i)) ∧
    (∀ F : Set Y, IsClosed F → F.Nonempty →
      (∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) →
      ∀ y, ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2) ∧
    (∀ (ι : Type) [Fintype ι], CN (PiLp 2 fun _ : ι => Y)) ∧
    ∀ (x y u v a b : Y) (δ h s t : ℝ), dist x y = δ → dist u v = δ → dist x u = h → dist y v = h →
      dist x v ^ 2 = δ ^ 2 + h ^ 2 → dist y u ^ 2 = δ ^ 2 + h ^ 2 → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      dist x a = s * dist x u → dist a u = (1 - s) * dist x u →
      dist y b = t * dist y v → dist b v = (1 - t) * dist y v →
      dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 :=
  ⟨lem_toolkit_a, lem_toolkit_b, lem_toolkit_c, lem_toolkit_d, fun ι _ => lem_toolkit_e ι, lem_toolkit_f⟩

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Formal midpoints

A helper for Proposition prop:space (Paper/Curvature.lean): the terms that name the iterated midpoints.
-/

open Filter Topology Finset

namespace Cat

/-- Formal midpoints. -/
inductive Term (V : Type) : Type
  | of : V → Term V
  | mid : Term V → Term V → Term V

namespace Term

variable {V : Type}

/-- The depth of a term. -/
def depth : Term V → ℕ
  | of _ => 0
  | mid s t => max s.depth t.depth + 1

/-- The first letter of a term. -/
def base : Term V → V
  | of v => v
  | mid s _ => s.base

/-- Where the terms of depth at most `n+1` stand when a new point is added for every pair of terms of depth at most `n`. -/
def place (n : ℕ) (s : Term V) : Term V ⊕ (Term V × Term V) :=
  if s.depth ≤ n then Sum.inl s else
    match s with
    | of v => Sum.inl (of v)
    | Term.mid a b => Sum.inr (a, b)

end Term

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Prices are nonpositively curved"

The subsection "Means" is in Paper/Means.lean, Theorem thm:cn and its proof are in Paper/Fan.lean, the definition of CAT(0)
spaces and Lemma lem:toolkit in Paper/Toolkit.lean; this file has Proposition prop:space.
-/

namespace Paper

open Finset Filter Topology Nc.Price

variable {K : Type} [Field K]

section Space

open Cat Cat.Term

variable {V : Type} {w : V → V → ℝ}

/-- One step of the proof of Proposition prop:space: "let V_{l+1} be V_l with a new point for each pair of its points; define
prices by placing each new point at either end with probability ½ (Proposition prop:random)." The points are named by terms;
V_n consists of the terms of depth at most n. -/
theorem prop_space_step {d : Term V → Term V → ℝ} (hd : IsPrice K d) (n : ℕ) :
    ∃ d' : Term V → Term V → ℝ, IsPrice K d' ∧
      (∀ s t, s.depth ≤ n → t.depth ≤ n → d' s t = d s t) ∧
      ∀ s t, max s.depth t.depth = n →
        d' s (Term.mid s t) ≤ d s t / 2 ∧ d' t (Term.mid s t) ≤ d s t / 2 := by
  obtain ⟨w', h1, h2, h3⟩ := prop_random_finite hd (Q := Term V × Term V) (Λ := Fin 2) (fun _ => 1 / 2)
    (fun _ => by norm_num) (by simp) (fun l κ => if l = 0 then κ.1 else κ.2)
  refine ⟨fun s t => w' (Term.place n s) (Term.place n t), h1.comp _, ?_, ?_⟩
  · intro s t hs ht
    simp only [Term.place, if_pos hs, if_pos ht]
    exact h2 s t
  · intro s t hst
    have hs : s.depth ≤ n := hst ▸ le_max_left _ _
    have ht : t.depth ≤ n := hst ▸ le_max_right _ _
    have hm : ¬ (Term.mid s t).depth ≤ n := by
      simp only [depth, hst]
      omega
    simp only [Term.place, if_pos hs, if_pos ht, if_neg hm]
    have g1 := h3 (Sum.inl s) (Sum.inr (s, t))
    have g2 := h3 (Sum.inl t) (Sum.inr (s, t))
    simp only [Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, id, if_true, Fin.isValue, one_ne_zero, if_false] at g1 g2
    rw [hd.self] at g1 g2
    rw [hd.symm t s] at g2
    constructor <;> linarith

/-- "Each step extends the one before, so together they form a price; in it each new point is a midpoint of its pair". -/
theorem prop_space_midpoints (hw : IsPrice K w) : ∃ d : Term V → Term V → ℝ, IsPrice K d ∧
    (∀ a b, d (of a) (of b) = w a b) ∧
    ∀ s t, d s (Term.mid s t) ≤ d s t / 2 ∧ d t (Term.mid s t) ≤ d s t / 2 := by
  choose! f hf1 hf2 hf3 using fun (n : ℕ) (d : Term V → Term V → ℝ) (hd : IsPrice K d) => prop_space_step hd n
  let D : ℕ → Term V → Term V → ℝ := fun n => Nat.rec (fun s t => w s.base t.base) (fun n d => f n d) n
  have hDs : ∀ n, D (n + 1) = f n (D n) := fun _ => rfl
  have hP : ∀ n, IsPrice K (D n) := by
    intro n
    induction n with
    | zero => exact hw.comp _
    | succ n ih => rw [hDs]; exact hf1 n _ ih
  have hst : ∀ n k s t, s.depth ≤ n → t.depth ≤ n → D (n + k) s t = D n s t := by
    intro n k s t hs ht
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← add_assoc, hDs, hf2 _ _ (hP _) s t (by omega) (by omega), ih]
  refine ⟨fun s t => D (max s.depth t.depth) s t, ?_, ?_, ?_⟩
  · refine isPrice_of_tendsto (l := atTop) (d := D) (fun s t => ?_) (Eventually.of_forall hP)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max s.depth t.depth)] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hst _ k s t (le_max_left _ _) (le_max_right _ _)).symm
  · intro a b
    rfl
  · intro s t
    have h := hf3 (max s.depth t.depth) (D (max s.depth t.depth)) (hP _) s t rfl
    have e1 : max s.depth (Term.mid s t).depth = max s.depth t.depth + 1 := by
      simp only [depth]
      omega
    have e2 : max t.depth (Term.mid s t).depth = max s.depth t.depth + 1 := by
      simp only [depth]
      omega
    simp only [e1, e2, hDs]
    exact h

/-- "Midpoints of Cauchy sequences are Cauchy by (CN) itself": if a n → x and b n → v, and m n satisfies (CN) for a n and b n,
then (m n) is a Cauchy sequence. -/
theorem prop_space_cauchy {X : Type*} [MetricSpace X] {a b m : ℕ → X} {x v : X} (ha : Tendsto a atTop (𝓝 x))
    (hb : Tendsto b atTop (𝓝 v))
    (hm : ∀ n z, dist z (m n) ^ 2 ≤ (dist z (a n) ^ 2 + dist z (b n) ^ 2) / 2 - dist (a n) (b n) ^ 2 / 4) :
    CauchySeq m := by
  have hR : Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 (dist x v)) := ha.dist hb
  have hmid : ∀ n, dist (a n) (m n) ≤ dist (a n) (b n) / 2 ∧
      dist (b n) (m n) ≤ dist (a n) (b n) / 2 := by
    intro n
    have h1 := hm n (a n)
    have h2 := hm n (b n)
    rw [dist_self] at h1 h2
    rw [dist_comm (b n) (a n)] at h2
    constructor
    · apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
      nlinarith
    · apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
      nlinarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set R := dist x v + 1 with hRdef
  have hR0 : 0 < R := by positivity
  set δ := min 1 (ε ^ 2 / (2 * (2 * R + 4))) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 ha.cauchySeq (δ / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hb.cauchySeq (δ / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hR.eventually (gt_mem_nhds (show dist x v < R by linarith)))
  refine ⟨max N₁ (max N₂ N₃), fun l hl k hk => ?_⟩
  have l1 := (le_max_left _ _).trans hl
  have l2 := ((le_max_left _ _).trans (le_max_right _ _)).trans hl
  have k1 := (le_max_left _ _).trans hk
  have k2 := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have k3 := ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have e1 := hN₁ l l1 k k1
  have e2 := hN₂ l l2 k k2
  have e3 := hN₃ k k3
  set e := dist (a l) (a k) + dist (b l) (b k) with he
  have he0 : 0 ≤ e := by positivity
  have hed : e < δ := by linarith
  have d1 : dist (m l) (a k) ≤ dist (a k) (b k) / 2 + 2 * e := by
    have t1 := dist_triangle (m l) (a l) (a k)
    have t2 := dist_triangle4 (a l) (a k) (b k) (b l)
    rw [dist_comm (m l) (a l)] at t1
    rw [dist_comm (b k) (b l)] at t2
    have := (hmid l).1
    have := dist_nonneg (x := b l) (y := b k)
    linarith
  have d2 : dist (m l) (b k) ≤ dist (a k) (b k) / 2 + 2 * e := by
    have t1 := dist_triangle (m l) (b l) (b k)
    have t2 := dist_triangle4 (a l) (a k) (b k) (b l)
    rw [dist_comm (m l) (b l)] at t1
    rw [dist_comm (b k) (b l)] at t2
    have := (hmid l).2
    have := dist_nonneg (x := a l) (y := a k)
    linarith
  have d3 := hm k (m l)
  have d4 := pow_le_pow_left₀ dist_nonneg d1 2
  have d5 := pow_le_pow_left₀ dist_nonneg d2 2
  have d6 : dist (m l) (m k) ^ 2 ≤ (2 * R + 4) * e := by
    have e4 : e ≤ 1 := hed.le.trans (min_le_left _ _)
    have e5 : dist (a k) (b k) * e ≤ R * e := mul_le_mul_of_nonneg_right e3.le he0
    nlinarith
  have d7 : (2 * R + 4) * e < ε ^ 2 := by
    have e4 : e < ε ^ 2 / (2 * (2 * R + 4)) := hed.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at e4
    have : 0 < ε ^ 2 := by positivity
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (d6.trans_lt d7)

/-- "The completion satisfies (CN)": a complete metric space is CAT(0) if any two points x, v of a dense subset S have a
point m for which (CN) holds at all z in S. -/
theorem prop_space_completion {X : Type*} [MetricSpace X] [CompleteSpace X] {S : Set X} (hS : Dense S)
    (h : ∀ x ∈ S, ∀ v ∈ S, ∃ m, ∀ z ∈ S,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4) : CN X := by
  have h' : ∀ x ∈ S, ∀ v ∈ S, ∃ m, ∀ z,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 := by
    intro x hx v hv
    obtain ⟨m, hm⟩ := h x hx v hv
    refine ⟨m, fun z => ?_⟩
    have hc : IsClosed {z | dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h3 : S ⊆ {z | dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4} := hm
    exact hc.closure_subset_iff.2 h3 (hS z)
  refine ⟨fun x v => ?_⟩
  obtain ⟨a, haS, ha⟩ := mem_closure_iff_seq_limit.1 (hS x)
  obtain ⟨b, hbS, hb⟩ := mem_closure_iff_seq_limit.1 (hS v)
  choose m hm using fun n => h' (a n) (haS n) (b n) (hbS n)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (prop_space_cauchy ha hb hm)
  refine ⟨p, fun z => ?_⟩
  have hl : Tendsto (fun n => dist z (m n) ^ 2) atTop (𝓝 (dist z p ^ 2)) :=
    (tendsto_const_nhds.dist hp).pow 2
  have hr : Tendsto (fun n => (dist z (a n) ^ 2 + dist z (b n) ^ 2) / 2 - dist (a n) (b n) ^ 2 / 4)
      atTop (𝓝 ((dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4)) :=
    ((((tendsto_const_nhds.dist ha).pow 2).add ((tendsto_const_nhds.dist hb).pow 2)).div_const 2).sub
      (((ha.dist hb).pow 2).div_const 4)
  exact le_of_tendsto_of_tendsto' hl hr fun n => hm n z

/-- "Its metric is a price as a limit": if the distance of a pseudometric space is a price, so is the metric of its
completion. -/
theorem prop_space_limit {T : Type} [PseudoMetricSpace T] (hd : IsPrice K fun s t : T => dist s t) :
    IsPrice K fun a b : UniformSpace.Completion T => dist a b := by
  have hseq : ∀ a : UniformSpace.Completion T, ∃ u : ℕ → T,
      Tendsto (fun n => ((u n : T) : UniformSpace.Completion T)) atTop (𝓝 a) := by
    intro a
    obtain ⟨u, hu, ha⟩ := mem_closure_iff_seq_limit.1 (UniformSpace.Completion.denseRange_coe (α := T) a)
    choose u' hu' using hu
    exact ⟨u', by simpa only [hu'] using ha⟩
  choose u hu using hseq
  refine isPrice_of_tendsto (l := atTop) (d := fun n a b => dist (u a n) (u b n)) ?_
    (Eventually.of_forall fun n => hd.comp fun a => u a n)
  intro a b
  have h := (hu a).dist (hu b)
  simpa only [UniformSpace.Completion.dist_eq] using h

/-- **Paper: Proposition prop:space.** "Every price on a set V is the pull-back of the metric of a price space." A price
space is a complete CAT(0) space whose metric is a price. -/
theorem prop_space {V : Type} {w : V → V → ℝ} (hw : IsPrice K w) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : Cat.CN X) (f : V → X),
      IsPrice K (fun a b : X => dist a b) ∧ ∀ a b, dist (f a) (f b) = w a b := by
  obtain ⟨d, hd, hof, hmid⟩ := prop_space_midpoints hw
  let _ : PseudoMetricSpace (Term V) :=
    { dist := d
      dist_self := hd.self
      dist_comm := hd.symm
      dist_triangle := hd.triangle }
  have hdd : ∀ s t : Term V, dist s t = d s t := fun _ _ => rfl
  -- "identify points at distance 0. The completion satisfies (CN), its metric is a price as a limit"
  refine ⟨UniformSpace.Completion (Term V), inferInstance,
    prop_space_completion UniformSpace.Completion.denseRange_coe ?_,
    fun v => ((of v : Term V) : UniformSpace.Completion (Term V)), prop_space_limit hd, ?_⟩
  · -- "each new point is a midpoint of its pair, so (CN) holds", by Theorem thm:cn
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    refine ⟨((Term.mid s t : Term V) : UniformSpace.Completion (Term V)), ?_⟩
    rintro _ ⟨z, rfl⟩
    simp only [UniformSpace.Completion.dist_eq, hdd]
    have h := thm_cn hd s t (Term.mid s t) z (D := d s t / 2) (hmid s t).1 (hmid s t).2 (by ring)
    refine h.trans (le_of_eq ?_)
    ring
  · intro a b
    simp only [UniformSpace.Completion.dist_eq, hdd]
    exact hof a b

end Space

end Paper
end


theorem solution {K : Type} [Field K] {V : Type} {w : V → V → ℝ}
    (hw : Nc.Price.IsPrice K w) :
    ∃ (X : Type) (_ : MetricSpace X) (f : V → X), CompleteSpace X ∧
      (∀ x v : X, ∃ m : X, dist x m = dist x v / 2 ∧ dist m v = dist x v / 2 ∧
        ∀ z : X, dist z m ^ 2 ≤ 1 / 2 * dist z x ^ 2 + 1 / 2 * dist z v ^ 2 - (dist x v / 2) ^ 2) ∧
      Nc.Price.IsPrice K (fun a b : X => dist a b) ∧ ∀ a b, dist (f a) (f b) = w a b := by
  obtain ⟨X, hX, hCN, f, hprice, hiso⟩ := Paper.prop_space hw
  letI := hX
  obtain ⟨hc, hmid⟩ := (Paper.cat0_iff X).mp hCN
  exact ⟨X, hX, f, hc, hmid, hprice, hiso⟩
