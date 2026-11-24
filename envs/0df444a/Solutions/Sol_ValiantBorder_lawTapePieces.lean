-- Prove2me | solution 1 for ValiantBorder.lawTapePieces
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:18:14.58984+00:00
-- url     : https://prove2.me/submissions/6ecad19a-cace-4611-9cd4-2061dcae5a42

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_lawThinTrees
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
/- Source module Nc.Tape.Rep. -/
section
namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}


abbrev Series (F Ω : Type*) := List Ω → F

namespace Series


def mul (f g : Series F Ω) : Series F Ω := fun o =>
  ∑ k ∈ range (o.length + 1), f (o.take k) * g (o.drop k)


def one : Series F Ω := fun o => if o = [] then 1 else 0


def kstar (f : Series F Ω) : Series F Ω
  | [] => 1
  | a :: o => ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k)
  termination_by o => o.length
  decreasing_by simp

theorem kstar_nil (f : Series F Ω) : kstar f [] = 1 := by rw [kstar]

theorem kstar_cons (f : Series F Ω) (a : Ω) (o : List Ω) : kstar f (a :: o) =
    ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k) := by rw [kstar]

end Series

theorem elim_dot {α β : Type*} [Fintype α] [Fintype β] (a c : α → F) (b d : β → F) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by simp [dotProduct]


structure Rep (F Ω Q : Type*) where
  
  lam : Q → F
  
  mu : Ω → Matrix Q Q F
  
  gam : Q → F

namespace Rep

variable {Q Q₁ Q₂ : Type*} [Fintype Q] [Fintype Q₁] [Fintype Q₂]


def tail (r : Rep F Ω Q) : List Ω → Q → F
  | [] => r.gam
  | a :: o => r.mu a *ᵥ tail r o


def series (r : Rep F Ω Q) : Series F Ω := fun o => r.lam ⬝ᵥ r.tail o


def add (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam r₂.lam
  mu a := Matrix.fromBlocks (r₁.mu a) 0 0 (r₂.mu a)
  gam := Sum.elim r₁.gam r₂.gam

theorem add_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).tail o = Sum.elim (r₁.tail o) (r₂.tail o) := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    simp only [tail, ih]
    simp [add, Matrix.fromBlocks_mulVec]

theorem add_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).series o = r₁.series o + r₂.series o := by
  rw [series, add_tail]
  simp [series, add]


def mul (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam)
  mu a := Matrix.fromBlocks (r₁.mu a) (Matrix.vecMulVec (r₁.mu a *ᵥ r₁.gam) r₂.lam) 0 (r₂.mu a)
  gam := Sum.elim 0 r₂.gam

theorem mul_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).tail o = Sum.elim
      (∑ k ∈ range o.length, (r₂.series (o.drop (k + 1))) • r₁.tail (o.take (k + 1))) (r₂.tail o) := by
  induction o with
  | nil => simp [tail, mul]
  | cons a o ih =>
    rw [tail, ih]
    simp only [mul, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    congr 1
    rw [List.length_cons, Finset.sum_range_succ']
    congr 1
    · rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [tail, Matrix.mulVec_smul]
    · ext i
      simp [tail, series, Matrix.vecMulVec_mulVec, mul_comm]

theorem mul_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).series o = Series.mul r₁.series r₂.series o := by
  rw [series, mul_tail, Series.mul, Finset.sum_range_succ']
  have e : (r₁.mul r₂).lam = Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam) := rfl
  rw [e, elim_dot, dotProduct_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [series, mul_comm]
  · simp [series, tail]


def star (r : Rep F Ω Q) : Rep F Ω (Unit ⊕ Q) where
  lam := Sum.elim 1 0
  mu a := Matrix.fromBlocks
    (Matrix.of fun _ _ => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)) (Matrix.of fun _ q => (r.lam ᵥ* r.mu a) q)
    (Matrix.of fun q _ => (r.mu a *ᵥ r.gam) q) (r.mu a)
  gam := Sum.elim 1 0

theorem star_tail (r : Rep F Ω Q) (o : List Ω) :
    r.star.tail o = Sum.elim (fun _ => Series.kstar r.series o)
      (∑ k ∈ range o.length, (Series.kstar r.series (o.drop (k + 1))) • r.tail (o.take (k + 1))) := by
  induction o with
  | nil => ext q; rcases q with q | q <;> simp [tail, star, Series.kstar_nil]
  | cons a o ih =>
    rw [tail, ih]
    have h2 : ∑ k ∈ range (a :: o).length, (Series.kstar r.series ((a :: o).drop (k + 1))) •
        r.tail ((a :: o).take (k + 1)) = r.mu a *ᵥ (∑ k ∈ range o.length,
          (Series.kstar r.series (o.drop (k + 1))) • r.tail (o.take (k + 1))) +
          (Series.kstar r.series o) • (r.mu a *ᵥ r.gam) := by
      rw [List.length_cons, Finset.sum_range_succ']
      congr 1
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [tail, Matrix.mulVec_smul]
    simp only [star, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · ext _
      rw [Series.kstar_cons, Finset.sum_range_succ']
      simp only [Pi.add_apply]
      rw [add_comm]
      congr 1
      · have : ∀ v : Q → F, ((Matrix.of fun (_ : Unit) q => (r.lam ᵥ* r.mu a) q) *ᵥ v) () =
            r.lam ⬝ᵥ (r.mu a *ᵥ v) := by
          intro v
          rw [Matrix.dotProduct_mulVec]
          simp [Matrix.mulVec, dotProduct]
        rw [this, Matrix.mulVec_sum, dotProduct_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [series, tail, Matrix.mulVec_smul, mul_comm]
      · simp [series, tail, Matrix.mulVec, dotProduct]
    · rw [h2, add_comm]
      congr 1
      ext q
      simp [Matrix.mulVec, dotProduct, mul_comm]

theorem star_series (r : Rep F Ω Q) (o : List Ω) : r.star.series o = Series.kstar r.series o := by
  rw [series, star_tail]
  have e : r.star.lam = Sum.elim (1 : Unit → F) (0 : Q → F) := rfl
  rw [e, elim_dot]
  simp [dotProduct]

end Rep

end Nc
end
/- Source module Nc.Tape.Rat. -/
section
set_option linter.unusedSimpArgs false

namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}


def RatLe (n : ℕ) (f : Series F Ω) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (r : Rep F Ω Q), Fintype.card Q ≤ n ∧ r.series = f

namespace RatLe

theorem mono {n m : ℕ} {f : Series F Ω} (h : RatLe n f) (hm : n ≤ m) : RatLe m f := by
  obtain ⟨Q, _, r, h1, h2⟩ := h
  exact ⟨Q, _, r, h1.trans hm, h2⟩

theorem zero : RatLe 0 (0 : Series F Ω) :=
  ⟨Empty, inferInstance, ⟨0, 0, 0⟩, by simp, by ext o; simp [Rep.series]⟩

theorem add {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) : RatLe (n + m) (f + g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.add r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.add_series r₁ r₂ o

theorem mul {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (Series.mul f g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.mul r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.mul_series r₁ r₂ o

theorem kstar {n : ℕ} {f : Series F Ω} (hf : RatLe n f) : RatLe (n + 1) (Series.kstar f) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  refine ⟨Unit ⊕ Q₁, inferInstance, r₁.star, by simp; omega, ?_⟩
  ext o
  exact Rep.star_series r₁ o

theorem smul {n : ℕ} {f : Series F Ω} (c : F) (hf : RatLe n f) : RatLe n (c • f) := by
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  refine ⟨Q, _, ⟨c • r.lam, r.mu, r.gam⟩, h1, ?_⟩
  ext o
  have : ∀ o, (⟨c • r.lam, r.mu, r.gam⟩ : Rep F Ω Q).tail o = r.tail o := by
    intro o
    induction o with
    | nil => rfl
    | cons a o ih => simp [Rep.tail, ih]
  simp [Rep.series, this]

theorem one : RatLe 1 (Series.one : Series F Ω) := by
  refine ⟨Unit, inferInstance, ⟨1, 0, 1⟩, by simp, ?_⟩
  ext o
  cases o with
  | nil => simp [Rep.series, Rep.tail, Series.one, dotProduct]
  | cons a o => simp [Rep.series, Rep.tail, Series.one]

theorem sum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → Series F Ω) (h : ∀ i ∈ s, RatLe (n i) (f i)) :
    RatLe (∑ i ∈ s, n i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end RatLe


def Series.letter [DecidableEq Ω] (a : Ω) : Series F Ω := fun o => if o = [a] then 1 else 0

theorem RatLe.letter [DecidableEq Ω] (a : Ω) : RatLe 2 (Series.letter a : Series F Ω) := by
  refine ⟨Bool, inferInstance, ⟨fun q => if q then 0 else 1,
    fun b => Matrix.of fun q q' => if b = a ∧ q = false ∧ q' = true then 1 else 0,
    fun q => if q then 1 else 0⟩, by simp, ?_⟩
  ext o
  match o with
  | [] => simp [Rep.series, Rep.tail, Series.letter, dotProduct]
  | [b] =>
    by_cases h : b = a <;> simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec, h]
  | b :: c :: o =>
    simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec]


theorem RatLe.normal {n : ℕ} {f : Series F Ω} (hf : RatLe n f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Ω → Matrix Q Q F) (i e : Q),
      Fintype.card Q ≤ n + 2 ∧ ∀ o : List Ω, o ≠ [] → (o.map mu).prod i e = f o := by
  classical
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  let mu : Ω → Matrix (Option (Option Q)) (Option (Option Q)) F := fun a => Matrix.of fun q q' =>
    match q, q' with
    | none, none => 0
    | none, some none => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)
    | none, some (some q') => (r.lam ᵥ* r.mu a) q'
    | some none, _ => 0
    | some (some _), none => 0
    | some (some q), some none => (r.mu a *ᵥ r.gam) q
    | some (some q), some (some q') => r.mu a q q'
  refine ⟨Option (Option Q), inferInstance, inferInstance, mu, none, some none, by simp; omega, ?_⟩
  have key : ∀ o : List Ω, ∀ q, o ≠ [] → (o.map mu).prod (some (some q)) (some none) = r.tail o q := by
    intro o
    induction o with
    | nil => simp
    | cons a o ih =>
      intro q _
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
      by_cases ho : o = []
      · subst ho
        simp [mu, Rep.tail, Matrix.one_apply]
      · have h0 : (o.map mu).prod (some none) (some none) = 0 := by
          obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
          rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
          simp [mu]
        simp only [mu, Matrix.of_apply, zero_mul, zero_add] at *
        rw [h0, mul_zero, zero_add, Rep.tail, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun q' _ => by rw [ih q' ho]
  intro o ho
  obtain ⟨a, o, rfl⟩ := List.exists_cons_of_ne_nil ho
  rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
  by_cases ho : o = []
  · subst ho
    simp [mu, Rep.series, Rep.tail, Matrix.one_apply]
  · have h0 : (o.map mu).prod (some none) (some none) = 0 := by
      obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
      simp [mu]
    rw [Finset.sum_congr rfl fun q' _ => by rw [key o q' ho]]
    simp only [mu, Matrix.of_apply, zero_mul, zero_add] at *
    rw [h0, mul_zero, zero_add, Rep.series, Rep.tail, Matrix.dotProduct_mulVec]
    rfl

end Nc
end
/- Source module Nc.Tape.Hat. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

@[simp] theorem proj_nil : proj ([] : List (Z × Γ)) = fun _ => [] := rfl

theorem proj_append (o₁ o₂ : List (Z × Γ)) (z : Z) : proj (o₁ ++ o₂) z = proj o₁ z ++ proj o₂ z := by
  simp [proj]

theorem proj_cons (a : Z × Γ) (o : List (Z × Γ)) (z : Z) :
    proj (a :: o) z = if a.1 = z then a.2 :: proj o z else proj o z := by
  by_cases h : a.1 = z <;> simp [proj, h]

theorem sum_length_proj (o : List (Z × Γ)) : ∑ z, (proj o z).length = o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    have : ∀ z, (proj (a :: o) z).length = (proj o z).length + if a.1 = z then 1 else 0 := by
      intro z
      rw [proj_cons]
      by_cases h : a.1 = z <;> simp [h]
    simp only [this, Finset.sum_add_distrib, ih]
    simp


noncomputable def fib (v : Z → List Γ) : Finset (List (Z × Γ)) :=
  (show {o : List (Z × Γ) | proj o = v}.Finite from
    (List.finite_length_eq (Z × Γ) (∑ z, (v z).length)).subset (by
      rintro o rfl
      exact (sum_length_proj o).symm)).toFinset

theorem mem_fib {v : Z → List Γ} {o : List (Z × Γ)} : o ∈ fib v ↔ proj o = v := by
  simp [fib]


noncomputable def hat (f : Series F (Z × Γ)) (v : Z → List Γ) : F := ∑ o ∈ fib v, f o


def anti (v : Z → List Γ) : Finset ((Z → List Γ) × (Z → List Γ)) :=
  (Fintype.piFinset fun z => range ((v z).length + 1)).image fun k =>
    (fun z => (v z).take (k z), fun z => (v z).drop (k z))

theorem mem_anti {v : Z → List Γ} {p : (Z → List Γ) × (Z → List Γ)} :
    p ∈ anti v ↔ ∀ z, p.1 z ++ p.2 z = v z := by
  simp only [anti, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨k, -, rfl⟩ z
    simp
  · intro h
    refine ⟨fun z => (p.1 z).length, fun z => ?_, ?_⟩
    · rw [← h z]; simp
    · ext1
      · funext z; simp only; rw [← h z]; simp
      · funext z; simp only; rw [← h z]; simp

theorem hat_add (f g : Series F (Z × Γ)) (v : Z → List Γ) : hat (f + g) v = hat f v + hat g v := by
  simp [hat, Finset.sum_add_distrib]

theorem hat_smul (c : F) (f : Series F (Z × Γ)) (v : Z → List Γ) : hat (c • f) v = c * hat f v := by
  simp [hat, Finset.mul_sum]

theorem hat_sum {ι : Type*} (s : Finset ι) (f : ι → Series F (Z × Γ)) (v : Z → List Γ) :
    hat (∑ i ∈ s, f i) v = ∑ i ∈ s, hat (f i) v := by
  simp only [hat, Finset.sum_apply]
  rw [Finset.sum_comm]

theorem hat_one (v : Z → List Γ) :
    hat (Series.one : Series F (Z × Γ)) v = if v = fun _ => [] then 1 else 0 := by
  simp only [hat, Series.one, Finset.sum_ite_eq', mem_fib, proj_nil]
  by_cases h : v = fun _ => []
  · simp [h]
  · simp [h, Ne.symm h]

theorem hat_mul (f g : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.mul f g) v = ∑ p ∈ anti v, hat f p.1 * hat g p.2 := by
  simp only [hat, Series.mul, Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun x _ => ⟨⟨proj (x.1.take x.2), proj (x.1.drop x.2)⟩, x.1.take x.2, x.1.drop x.2⟩)
    (j := fun y _ => ⟨y.2.1 ++ y.2.2, y.2.1.length⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨o, k⟩ h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range] at h
    simp only [Finset.mem_sigma, mem_anti, mem_fib, and_true]
    intro z
    rw [← proj_append, List.take_append_drop, h.1]
  · rintro ⟨⟨v₁, v₂⟩, a, b⟩ h
    simp only [Finset.mem_sigma, mem_anti, mem_fib] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range, List.length_append]
    refine ⟨?_, by omega⟩
    funext z
    rw [proj_append, h2, h3]
    exact h1 z
  · rintro ⟨o, k⟩ h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range] at h
    simp only [List.take_append_drop, List.length_take, Sigma.mk.injEq, heq_eq_eq, true_and]
    omega
  · rintro ⟨⟨v₁, v₂⟩, a, b⟩ h
    simp only [Finset.mem_sigma, mem_anti, mem_fib] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h2, h3]
  · rintro ⟨o, k⟩ h
    rfl


def Series.ne (f : Series F (Z × Γ)) : Series F (Z × Γ) := fun o => if o = [] then 0 else f o

theorem kstar_eq (f : Series F (Z × Γ)) :
    Series.kstar f = Series.one + Series.mul (Series.ne f) (Series.kstar f) := by
  funext o
  cases o with
  | nil => simp [Series.kstar_nil, Series.one, Series.mul, Series.ne]
  | cons a o =>
    rw [Series.kstar_cons, Pi.add_apply, Series.mul]
    conv_rhs => rw [Finset.sum_range_succ']
    simp [Series.one, Series.ne]

theorem hat_ne (f : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.ne f) v = if v = fun _ => [] then 0 else hat f v := by
  by_cases h : v = fun _ => []
  · rw [if_pos h, hat]
    refine Finset.sum_eq_zero fun o ho => ?_
    rw [mem_fib, h] at ho
    have : o = [] := by
      have := sum_length_proj o
      rw [ho] at this
      simpa using this.symm
    simp [Series.ne, this]
  · rw [if_neg h, hat, hat]
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [mem_fib] at ho
    have : o ≠ [] := by rintro rfl; exact h (by rw [← ho]; rfl)
    simp [Series.ne, this]


theorem hat_kstar (f : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.kstar f) v = (if v = fun _ => [] then 1 else 0) +
      ∑ p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []), hat f p.1 * hat (Series.kstar f) p.2 := by
  conv_lhs => rw [kstar_eq]
  rw [hat_add, hat_one, hat_mul, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hat_ne]
  by_cases h : p.1 = fun _ => [] <;> simp [h]

end Nc
end
/- Source module Nc.Tape.Loop. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]


def Series.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) : Series F Ω := fun o => if o = w then 1 else 0

theorem RatLe.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) :
    RatLe (2 * w.length + 1) (Series.word w : Series F Ω) := by
  induction w with
  | nil => exact RatLe.one
  | cons a w ih =>
    have h := (RatLe.letter (F := F) a).mul ih
    have e : Series.mul (Series.letter a) (Series.word w) = (Series.word (a :: w) : Series F Ω) := by
      funext o
      cases o with
      | nil => simp [Series.mul, Series.letter, Series.word]
      | cons b o =>
        rw [Series.mul, List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ']
        have : ∀ k, Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) = if k + 1 ≤ o.length then 0 else
            Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) := by
          intro k
          split_ifs with hk
          · obtain ⟨c, o, rfl⟩ : ∃ c o', o = c :: o' := by
              cases o with
              | nil => simp at hk
              | cons c o => exact ⟨c, o, rfl⟩
            simp [Series.letter]
          · rfl
        rw [Finset.sum_congr rfl fun k _ => this k]
        rw [Finset.sum_congr rfl (g := fun _ => (0 : F)) (fun k hk => by
          rw [if_pos (by have := Finset.mem_range.1 hk; omega)])]
        simp only [Finset.sum_const_zero, zero_add]
        by_cases hb : b = a
        · subst hb
          by_cases ho : o = w <;> simp [Series.letter, Series.word, ho]
        · simp [Series.letter, Series.word, hb]
    rw [e] at h
    exact h.mono (by simp; omega)

theorem hat_word (w : List (Z × Γ)) (v : Z → List Γ) :
    hat (Series.word w : Series F (Z × Γ)) v = if v = proj w then 1 else 0 := by
  simp only [hat, Series.word, Finset.sum_ite_eq', mem_fib]
  by_cases h : v = proj w
  · simp [h]
  · simp [h, Ne.symm h]

section Loop

variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def Series.body (wd : κ → List (Z × Γ)) (c : κ → F) : Series F (Z × Γ) :=
  ∑ k, c k • Series.word (wd k)

theorem RatLe.body (wd : κ → List (Z × Γ)) (c : κ → F) :
    RatLe (∑ k, (2 * (wd k).length + 1)) (Series.body wd c) :=
  RatLe.sum _ _ _ fun k _ => (RatLe.word (wd k)).smul (c k)

theorem hat_body (wd : κ → List (Z × Γ)) (c : κ → F) (v : Z → List Γ) :
    hat (Series.body wd c) v = ∑ k, if v = proj (wd k) then c k else 0 := by
  rw [Series.body, hat_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hat_smul, hat_word]
  simp

end Loop

section Phases

end Phases

end Nc
end
/- Source module Nc.Tape.Task. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]


def tup (W : S → List Γ) (u : J → List Γ) : Ch S J → List Γ
  | .tp s _ => W s
  | .inp j => u j


noncomputable def contents (S Γ : Type*) [Fintype S] [DecidableEq S] [Fintype Γ] (t : ℕ) :
    Finset (S → List Γ) :=
  open Classical in
  (Fintype.piFinset fun _ => (List.finite_length_le Γ t).toFinset).filter fun W => ∑ s, (W s).length ≤ t

theorem mem_contents {t : ℕ} {W : S → List Γ} : W ∈ contents S Γ t ↔ ∑ s, (W s).length ≤ t := by
  classical
  simp only [contents, Finset.mem_filter, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun s => ?_, h⟩
    exact (Finset.single_le_sum (f := fun s => (W s).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s)).trans h


noncomputable def val (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : F :=
  ∑ W ∈ contents S Γ t, hat P (tup W u)


def Bdd (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : Prop :=
  ∀ W, hat P (tup W u) ≠ 0 → ∑ s, (W s).length ≤ t

theorem val_eq_of_bdd {t t' : ℕ} {P : Series F (Ch S J × Γ)} {u : J → List Γ} (h : Bdd t P u)
    (ht : t ≤ t') : val t' P u = val t P u := by
  classical
  symm
  apply Finset.sum_subset
  · intro W hW
    rw [mem_contents] at hW ⊢
    exact hW.trans ht
  · intro W _ hW
    by_contra hne
    exact hW (mem_contents.2 (h W hne))

end Nc
end
/- Source module Nc.Tape.Refine. -/
section
namespace Nc

variable {Γ : Type*} {K : ℕ}




theorem cat_succ (A : Fin (K + 1) → List Γ) : cat A = A 0 ++ cat fun i => A i.succ := by
  simp [cat, List.ofFn_succ]

theorem cat_eq_nil {A : Fin K → List Γ} : cat A = [] ↔ ∀ i, A i = [] := by
  induction K with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ, List.append_eq_nil_iff, ih, Fin.forall_fin_succ]

theorem cat_eq_cons {A : Fin K → List Γ} {a : Γ} {W : List Γ} (h : cat A = a :: W) :
    ∃ i l, (∀ j < i, A j = []) ∧ A i = a :: l ∧ cat (Function.update A i l) = W := by
  induction K with
  | zero => simp [cat] at h
  | succ K ih =>
    rw [cat_succ] at h
    rcases hA : A 0 with _ | ⟨b, l⟩
    · rw [hA, List.nil_append] at h
      obtain ⟨i, l, h1, h2, h3⟩ := ih h
      refine ⟨i.succ, l, ?_, h2, ?_⟩
      · intro j hj
        refine Fin.cases (fun _ => hA) (fun j hj => h1 j (by simpa using hj)) j hj
      · rw [cat_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm, hA, List.nil_append, ← h3]
        congr 1
        funext j
        by_cases e : j = i
        · subst e; simp
        · rw [Function.update_of_ne e, Function.update_of_ne (fun h => e (Fin.succ_injective _ h))]
    · rw [hA, List.cons_append, List.cons.injEq] at h
      refine ⟨0, l, fun j hj => absurd hj (Fin.not_lt_zero j), by rw [hA, h.1], ?_⟩
      rw [cat_succ, Function.update_self, ← h.2]
      congr 2

theorem cat_of_cons {A : Fin K → List Γ} {a : Γ} {i : Fin K} {l : List Γ} (h1 : ∀ j < i, A j = [])
    (h2 : A i = a :: l) : cat A = a :: cat (Function.update A i l) := by
  induction K with
  | zero => exact i.elim0
  | succ K ih =>
    rw [cat_succ, cat_succ]
    by_cases e : i = 0
    · subst e
      rw [h2, Function.update_self, List.cons_append]
      congr 3
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 e
      rw [Function.update_of_ne (Ne.symm e), h1 0 (Fin.succ_pos i'), List.nil_append, List.nil_append]
      rw [ih (A := fun j => A j.succ) (i := i') (fun j hj => h1 _ (by simpa using hj)) h2]
      congr 2
      funext j
      by_cases e' : j = i'
      · subst e'; simp
      · rw [Function.update_of_ne e', Function.update_of_ne (fun h => e' (Fin.succ_injective _ h))]


def Stair (X : Fin K → Fin K → List Γ) : Prop :=
  ∀ a a' b b', X a b ≠ [] → X a' b' ≠ [] → a < a' → b ≤ b'


structure IsRef (A B : Fin K → List Γ) (X : Fin K → Fin K → List Γ) : Prop where
  stair : Stair X
  row : ∀ a, cat (X a) = A a
  col : ∀ b, cat (fun a => X a b) = B b


def upd (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) : Fin K → Fin K → List Γ :=
  fun a' b' => if a' = a ∧ b' = b then l else X a' b'

theorem upd_row (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    upd X a b l a = Function.update (X a) b l := by
  funext b'
  by_cases e : b' = b
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_row_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {a' : Fin K} (h : a' ≠ a) :
    upd X a b l a' = X a' := by
  funext b'; simp [upd, h]

theorem upd_col (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    (fun a' => upd X a b l a' b) = Function.update (fun a' => X a' b) a l := by
  funext a'
  by_cases e : a' = a
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_col_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {b' : Fin K} (h : b' ≠ b) :
    (fun a' => upd X a b l a' b') = fun a' => X a' b' := by
  funext a'; simp [upd, h]


theorem IsRef.first {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) {a : Fin K}
    {c : Γ} {l : List Γ} (h1 : ∀ j < a, A j = []) (h2 : A a = c :: l) :
    ∃ b x m, X a b = c :: x ∧ (∀ j < b, B j = []) ∧ B b = c :: m ∧
      IsRef (Function.update A a l) (Function.update B b m) (upd X a b x) := by
  obtain ⟨b, x, hx1, hx2, hx3⟩ := cat_eq_cons ((h.row a).trans h2)
  have hrow : ∀ j < a, ∀ b', X j b' = [] := fun j hj b' => cat_eq_nil.1 ((h.row j).trans (h1 j hj)) b'
  have hcol : ∀ j < b, ∀ a', X a' j = [] := by
    intro j hj a'
    rcases lt_trichotomy a' a with h' | h' | h'
    · exact hrow a' h' j
    · subst h'; exact hx1 j hj
    · by_contra hne
      exact absurd (h.stair a a' b j (by simp [hx2]) hne h') (not_le.2 hj)
  have hB := cat_of_cons (A := fun a' => X a' b) (i := a) (l := x) (fun j hj => hrow j hj b) hx2
  rw [h.col b] at hB
  refine ⟨b, x, _, hx2, fun j hj => ?_, hB, ?_, ?_, ?_⟩
  · rw [← h.col j]; exact cat_eq_nil.2 fun a' => hcol j hj a'
  · intro a₁ a₂ b₁ b₂ n1 n2 hlt
    have key : ∀ a' b', upd X a b x a' b' ≠ [] → X a' b' ≠ [] := by
      intro a' b' hn
      by_cases e : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := e; simp [hx2]
      · simpa [upd, e] using hn
    exact h.stair _ _ _ _ (key _ _ n1) (key _ _ n2) hlt
  · intro a'
    by_cases e : a' = a
    · subst e; rw [upd_row, Function.update_self, hx3]
    · rw [upd_row_ne _ _ _ _ e, Function.update_of_ne e, h.row]
  · intro b'
    by_cases e : b' = b
    · subst e; rw [upd_col, Function.update_self]
    · rw [upd_col_ne _ _ _ _ e, Function.update_of_ne e, h.col]

theorem IsRef.cat_eq {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) :
    cat A = cat B := by
  generalize hW : cat A = W
  induction W generalizing A B X with
  | nil =>
    symm
    rw [cat_eq_nil] at hW ⊢
    intro b
    rw [← h.col b, cat_eq_nil]
    intro a
    exact cat_eq_nil.1 ((h.row a).trans (hW a)) b
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, -, hb, hB, href⟩ := h.first h1 h2
    rw [cat_of_cons hb hB, ← ih href h3]

theorem IsRef.unique {A B : Fin K → List Γ} {X Y : Fin K → Fin K → List Γ} (h : IsRef A B X)
    (h' : IsRef A B Y) : X = Y := by
  generalize hW : cat A = W
  induction W generalizing A B X Y with
  | nil =>
    rw [cat_eq_nil] at hW
    funext a b
    rw [cat_eq_nil.1 ((h.row a).trans (hW a)) b, cat_eq_nil.1 ((h'.row a).trans (hW a)) b]
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, hx, hb, hB, href⟩ := h.first h1 h2
    obtain ⟨b', y, m', hy, hb', hB', href'⟩ := h'.first h1 h2
    have eb : b = b' := by
      rcases lt_trichotomy b b' with e | e | e
      · rw [hb' b e] at hB; simp at hB
      · exact e
      · rw [hb b' e] at hB'; simp at hB'
    subst eb
    rw [hB] at hB'
    obtain rfl : m = m' := by simpa using hB'
    have := ih href href' h3
    funext a' b'
    by_cases e : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      have h4 := congrFun (congrFun this a') b'
      simp only [upd, and_self, if_true] at h4
      rw [hx, hy, h4]
    · have h4 := congrFun (congrFun this a') b'
      simpa [upd, e] using h4

theorem IsRef.exists {A B : Fin K → List Γ} (h : cat A = cat B) : ∃ X, IsRef A B X := by
  generalize hW : cat A = W
  induction W generalizing A B with
  | nil =>
    have hB : cat B = [] := h ▸ hW
    rw [cat_eq_nil] at hW hB
    refine ⟨fun _ _ => [], fun _ _ _ _ h => absurd rfl h, fun a => ?_, fun b => ?_⟩
    · rw [hW, cat_eq_nil]; exact fun _ => rfl
    · rw [hB, cat_eq_nil]; exact fun _ => rfl
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, m, g1, g2, g3⟩ := cat_eq_cons (h ▸ hW)
    obtain ⟨X, hX⟩ := ih (h3.trans g3.symm) h3
    have hrow : ∀ j < a, ∀ b', X j b' = [] := fun j hj b' =>
      cat_eq_nil.1 ((hX.row j).trans (by rw [Function.update_of_ne hj.ne, h1 j hj])) b'
    have hcol : ∀ j < b, ∀ a', X a' j = [] := fun j hj a' =>
      cat_eq_nil.1 ((hX.col j).trans (by rw [Function.update_of_ne hj.ne, g1 j hj])) a'
    refine ⟨upd X a b (c :: X a b), ?_, ?_, ?_⟩
    · have key : ∀ a' b', upd X a b (c :: X a b) a' b' ≠ [] → (a' = a ∧ b' = b) ∨ X a' b' ≠ [] := by
        intro a' b' hn
        by_cases e : a' = a ∧ b' = b
        · exact Or.inl e
        · exact Or.inr (by simpa [upd, e] using hn)
      have key2 : ∀ a' b', upd X a b (c :: X a b) a' b' ≠ [] → a ≤ a' ∧ b ≤ b' := by
        intro a' b' hn
        rcases key a' b' hn with ⟨rfl, rfl⟩ | hne
        · exact ⟨le_rfl, le_rfl⟩
        · exact ⟨not_lt.1 fun h => hne (hrow _ h _), not_lt.1 fun h => hne (hcol _ h _)⟩
      intro a₁ a₂ b₁ b₂ n1 n2 hlt
      rcases key a₁ b₁ n1 with ⟨rfl, rfl⟩ | m1
      · exact (key2 _ _ n2).2
      · rcases key a₂ b₂ n2 with ⟨rfl, rfl⟩ | m2
        · exact absurd (key2 _ _ n1).1 (not_le.2 hlt)
        · exact hX.stair _ _ _ _ m1 m2 hlt
    · intro a'
      by_cases e : a' = a
      · subst e
        rw [upd_row, cat_of_cons (a := c) (i := b) (l := X a' b), Function.update_idem,
          Function.update_eq_self, hX.row, Function.update_self, h2]
        · intro j hj; rw [Function.update_of_ne hj.ne]; exact hcol j hj a'
        · simp
      · rw [upd_row_ne _ _ _ _ e, hX.row, Function.update_of_ne e]
    · intro b'
      by_cases e : b' = b
      · subst e
        rw [upd_col, cat_of_cons (i := a) (l := X a b') (a := c), Function.update_idem]
        · rw [Function.update_eq_self (f := fun a' => X a' b') a, hX.col, Function.update_self, g2]
        · intro j hj; rw [Function.update_of_ne hj.ne]; exact hrow j hj b'
        · simp
      · rw [upd_col_ne _ _ _ _ e, hX.col, Function.update_of_ne e]

end Nc
end
/- Source module Nc.Cut.Blocks. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]


theorem prod_path {K : ℕ} (M : Fin K → Matrix Q Q F) (a b : Q) :
    (List.ofFn M).prod a b = ∑ q : Fin (K + 1) → Q,
      if q 0 = a ∧ q (Fin.last K) = b then ∏ k, M k (q k.castSucc) (q k.succ) else 0 := by
  induction K generalizing a with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
    rw [Matrix.one_apply]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl, Finset.sum_eq_single fun _ => a]
      · simp
      · intro q _ hne
        rw [if_neg]
        rintro ⟨h0, -⟩
        apply hne
        funext k
        have : k = 0 := Fin.ext (by omega)
        rw [this, h0]
      · simp
    · rw [if_neg h, Finset.sum_eq_zero]
      intro q _
      rw [if_neg]
      rintro ⟨h0, h1⟩
      apply h
      rw [← h0, ← h1]
      congr 1
  | succ K ih =>
    have hR : (∑ q : Fin (K + 1 + 1) → Q, if q 0 = a ∧ q (Fin.last (K + 1)) = b then
        ∏ k, M k (q k.castSucc) (q k.succ) else 0) = ∑ q : Fin (K + 1) → Q,
        if q (Fin.last K) = b then M 0 a (q 0) * ∏ k : Fin K, M k.succ (q k.castSucc) (q k.succ) else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (K + 2) => Q).sum_comp, Fintype.sum_prod_type,
        Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun q _ => ?_
        have e1 : (Fin.consEquiv fun _ : Fin (K + 2) => Q) (a, q) = (Fin.cons a q : Fin (K + 2) → Q) := rfl
        simp only [e1]
        have e2 : (Fin.cons a q : Fin (K + 2) → Q) (Fin.last (K + 1)) = q (Fin.last K) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have e3 : (Fin.cons a q : Fin (K + 2) → Q) 0 = a := rfl
        rw [e2, e3]
        simp only [true_and]
        split_ifs
        · rw [Fin.prod_univ_succ]
          rfl
        · rfl
      · intro a' _ ha'
        refine Finset.sum_eq_zero fun q _ => if_neg ?_
        rintro ⟨h0, -⟩
        exact ha' h0
      · simp
    rw [hR, List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp only [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q 0)]
    · by_cases h : q (Fin.last K) = b <;> simp [h]
    · intro c _ hc
      rw [if_neg (fun hh => hc hh.1.symm), mul_zero]
    · simp

theorem emit_append (o₁ o₂ : List (Letter S J Γ)) (z : Ch S J) : emit (o₁ ++ o₂) z = emit o₁ z ++ emit o₂ z := by
  simp [emit, List.reduceOption_append, proj_append]

theorem emit_flatten {K : ℕ} (o : Fin K → List (Letter S J Γ)) (z : Ch S J) :
    emit (List.ofFn o).flatten z = cat fun k => emit (o k) z := by
  induction K with
  | zero => simp [emit, cat]
  | succ K ih => rw [List.ofFn_succ, List.flatten_cons, emit_append, ih, cat_succ]

theorem length_emit_le (o : List (Letter S J Γ)) (z : Ch S J) : (emit o z).length ≤ o.length := by
  have h1 := sum_length_proj o.reduceOption
  have h2 := List.reduceOption_length_le o
  exact (Finset.single_le_sum (f := fun z => (proj o.reduceOption z).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ z)).trans (h1.le.trans h2)







theorem mem_wordsLe {T : ℕ} {w : List Γ} : w ∈ wordsLe Γ T ↔ w.length ≤ T := by simp [wordsLe]


theorem blockW_ne_zero {mu : Letter S J Γ → Matrix Q Q F} {T : ℕ} {q q' : Q} {v : Ch S J → List Γ}
    (h : blockW mu T q q' v ≠ 0) (z : Ch S J) : v z ∈ wordsLe Γ T := by
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at ho with he
  · rw [mem_wordsLe, ← he]
    simpa using length_emit_le (List.ofFn o) z
  · exact absurd rfl ho


theorem runVal_blocks (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (K T : ℕ) (u : J → List Γ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J => wordsLe Γ T,
        if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
          ∀ j, cat (fun k => v k (.inp j)) = u j then
          ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) else 0
      else 0 := by
  classical
  -- runs as families of blocks
  have h1 : runVal mu i e (K * T) u = ∑ o : Fin K → Fin T → Letter S J Γ,
      if (∀ s, cat (fun k => emit (List.ofFn (o k)) (.tp s false)) =
          cat fun k => emit (List.ofFn (o k)) (.tp s true)) ∧
        ∀ j, cat (fun k => emit (List.ofFn (o k)) (.inp j)) = u j then
      ((List.ofFn fun k => ((List.ofFn (o k)).map mu).prod)).prod i e else 0 := by
    rw [runVal]
    let eq : (Fin K → Fin T → Letter S J Γ) ≃ (Fin (K * T) → Letter S J Γ) :=
      (Equiv.curry (Fin K) (Fin T) (Letter S J Γ)).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl _))
    rw [← eq.sum_comp]
    refine Finset.sum_congr rfl fun o _ => ?_
    have e1 : List.ofFn (eq o) = (List.ofFn fun k => List.ofFn (o k)).flatten := by
      rw [List.ofFn_mul]
      congr 1
      congr 1
      funext k
      congr 1
      funext l
      have : finProdFinEquiv.symm ⟨k.1 * T + l.1, by
          calc k.1 * T + l.1 < (k.1 + 1) * T := by nlinarith [l.2]
            _ ≤ K * T := Nat.mul_le_mul_right _ k.2⟩ = (k, l) := by
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
      simp only [eq, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
        Equiv.curry_symm_apply, Function.uncurry, this]
    rw [e1]
    simp only [Matched, emit_flatten]
    congr 1
    rw [List.map_flatten, List.prod_flatten]
    congr 2
    simp [List.map_ofFn, Function.comp_def]
  rw [h1]
  simp only [prod_path]
  have h2 : ∀ (o : Fin K → Fin T → Letter S J Γ) (c : Prop) [Decidable c],
      (if c then ∑ q : Fin (K + 1) → Q, (if q 0 = i ∧ q (Fin.last K) = e then
        ∏ k, ((List.ofFn (o k)).map mu).prod (q k.castSucc) (q k.succ) else 0) else 0) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        (if c then ∏ k, ((List.ofFn (o k)).map mu).prod (q k.castSucc) (q k.succ) else 0) else 0 := by
    intro o c _
    by_cases hc : c
    · simp only [if_pos hc]
    · simp [hc]
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q 0 = i ∧ q (Fin.last K) = e
  swap
  · simp [hq]
  simp only [if_pos hq]
  -- group the families of blocks by what they emit
  have h3 : ∀ o : Fin K → Fin T → Letter S J Γ, (fun k => emit (List.ofFn (o k))) ∈
      Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J => wordsLe Γ T := by
    intro o
    simp only [Fintype.mem_piFinset, mem_wordsLe]
    intro k z
    simpa using length_emit_le (List.ofFn (o k)) z
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun o : Fin K → Fin T → Letter S J Γ =>
    fun k => emit (List.ofFn (o k))) (fun o _ => h3 o)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_filter]
  by_cases hv : (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
      ∀ j, cat (fun k => v k (.inp j)) = u j
  · rw [if_pos hv]
    simp only [blockW]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : (fun k => emit (List.ofFn (o k))) = v
    · have ho' : ∀ k, emit (List.ofFn (o k)) = v k := fun k => congrFun ho k
      rw [if_pos ho, if_pos (by simpa only [ho'] using hv)]
      exact Finset.prod_congr rfl fun k _ => by rw [if_pos (ho' k)]
    · rw [if_neg ho]
      symm
      have : ∃ k, emit (List.ofFn (o k)) ≠ v k := by
        by_contra hc
        push Not at hc
        exact ho (funext hc)
      obtain ⟨k, hk⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
  · rw [if_neg hv, Finset.sum_eq_zero]
    intro o _
    split_ifs with ho hc
    · exfalso
      have ho' : ∀ k, emit (List.ofFn (o k)) = v k := fun k => congrFun ho k
      simp only [ho'] at hc
      exact hv hc
    · rfl
    · rfl

end Nc
end
/- Source module Nc.Cut.Units. -/
section
set_option linter.unusedSectionVars false

namespace Nc

variable (ub : ℕ)













variable {ub}

theorem unitsOf_inj (hub : 0 < ub) {L L' : List Bool} (h : ∀ k, unitsOf ub L k = unitsOf ub L' k) : L = L' := by
  have hc : ucount ub L = ucount ub L' := by
    rcases lt_trichotomy (ucount ub L) (ucount ub L') with hlt | heq | hlt
    · have := h (ucount ub L)
      simp [unitsOf, hlt] at this
    · exact heq
    · have := h (ucount ub L')
      simp [unitsOf, hlt] at this
  have hp : ∀ i, i < ucount ub L * ub → (L ++ [true]).getD i false = (L' ++ [true]).getD i false := by
    intro i hi
    have hk : i / ub < ucount ub L := (Nat.div_lt_iff_lt_mul hub).2 hi
    have := h (i / ub)
    simp only [unitsOf, if_pos hk, if_pos (hc ▸ hk), Option.some.injEq] at this
    have h2 := congrFun this ⟨i % ub, Nat.mod_lt _ hub⟩
    simp only [uword, Nat.div_add_mod'] at h2
    exact h2
  have hl : ∀ L : List Bool, L.length < ucount ub L * ub := by
    intro L
    have := Nat.div_add_mod L.length ub
    have h3 := Nat.mod_lt L.length hub
    simp only [ucount, add_mul, one_mul]
    rw [mul_comm] at this
    omega
  have hlen : L.length = L'.length := by
    rcases lt_trichotomy L.length L'.length with hlt | heq | hlt
    · exfalso
      have := hp L'.length (hc ▸ hl L')
      rw [List.getD_eq_default _ _ (by simp; omega)] at this
      simp at this
    · exact heq
    · exfalso
      have := hp L.length (hl L)
      rw [List.getD_eq_default (L' ++ [true]) _ (by simp; omega)] at this
      simp at this
  apply List.ext_getElem hlen
  intro i h1 h2
  have := hp i (h1.trans (hl L))
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)] at this
  rwa [List.getElem_append_left h1, List.getElem_append_left h2] at this

theorem unitsOf_eq_none {L : List Bool} {k : ℕ} : unitsOf ub L k = none ↔ ucount ub L ≤ k := by
  simp [unitsOf]

section Segments

variable {Γ : Type*} {c : ℕ}




theorem length_bitsOf (cb : Γ → Fin c → Bool) (X : List Γ) : (bitsOf cb X).length = X.length * c := by
  induction X with
  | nil => simp [bitsOf]
  | cons a X ih =>
    simp only [bitsOf, List.flatMap_cons, List.length_append, List.length_ofFn, List.length_cons] at *
    rw [ih]; ring

theorem bitsOf_inj {cb : Γ → Fin c → Bool} (hcb : Function.Injective cb) (hc : 0 < c) {X X' : List Γ}
    (h : bitsOf cb X = bitsOf cb X') : X = X' := by
  induction X generalizing X' with
  | nil =>
    cases X' with
    | nil => rfl
    | cons a X' =>
      have := congrArg List.length h
      rw [length_bitsOf, length_bitsOf] at this
      simp only [List.length_nil, List.length_cons, zero_mul] at this
      have : 0 < (X'.length + 1) * c := Nat.mul_pos (by omega) hc
      omega
  | cons a X ih =>
    cases X' with
    | nil =>
      have := congrArg List.length h
      rw [length_bitsOf, length_bitsOf] at this
      simp only [List.length_nil, List.length_cons, zero_mul] at this
      have : 0 < (X.length + 1) * c := Nat.mul_pos (by omega) hc
      omega
    | cons a' X' =>
      simp only [bitsOf, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      have e1 : a = a' := hcb (List.ofFn_injective h1)
      rw [e1, ih h2]

end Segments

end Nc
end
/- Source module Nc.Cut.Play. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W O : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype O]







def Contents (h0 h1 : U → A) (e : W) (Seen : Finset U) : Finset (A → U → W) :=
  univ.filter fun y => ∀ a id, ¬ (id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e


def Agree (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Prop :=
  ∀ id ∈ Cur, y (h0 id) id = y (h1 id) id

instance (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Decidable (Agree h0 h1 Cur y) := by
  unfold Agree; infer_instance


def posVal (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (E : (A → U → W) → F) : F :=
  ∑ y ∈ Contents h0 h1 e Seen, if Agree h0 h1 Cur y then E y else 0


def ext (h0 h1 : U → A) (New : Finset U) (y : A → U → W) (z : U → W) : A → U → W := fun a id =>
  if id ∈ New ∧ Holds h0 h1 a id then z id else y a id

theorem ext_self {h0 h1 : U → A} {New : Finset U} {y : A → U → W} {z : U → W} {a : A} {id : U}
    (h : id ∈ New) (ha : Holds h0 h1 a id) : ext h0 h1 New y z a id = z id := by simp [ext, h, ha]

theorem ext_of_not {h0 h1 : U → A} {New : Finset U} {y : A → U → W} {z : U → W} {a : A} {id : U}
    (h : id ∉ New) : ext h0 h1 New y z a id = y a id := by simp [ext, h]


theorem sum_contents_union (h0 h1 : U → A) (e : W) (Seen New : Finset U) (hd : Disjoint Seen New)
    (f : (A → U → W) → F) :
    (∑ y ∈ Contents h0 h1 e (Seen ∪ New), if Agree h0 h1 New y then f y else 0) =
      ∑ y ∈ Contents h0 h1 e Seen, ∑ z ∈ Common e New, f (ext h0 h1 New y z) := by
  rw [← Finset.sum_filter, ← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun y _ => (fun a id => if id ∈ New then e else y a id, fun id => if id ∈ New then y (h0 id) id else e))
    (j := fun p _ => ext h0 h1 New p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union] at hy ⊢
    refine ⟨fun a id hn => ?_, fun id hn => by simp [hn]⟩
    by_cases h : id ∈ New
    · simp [h]
    · simp only [h, if_false]
      apply hy.1
      rintro ⟨h1 | h1, h2⟩
      · exact hn ⟨h1, h2⟩
      · exact h h1
  · rintro ⟨y, z⟩ hp
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union] at hp ⊢
    refine ⟨fun a id hn => ?_, fun id hid => ?_⟩
    · have h1 : ¬ (id ∈ New ∧ Holds h0 h1 a id) := fun h => hn ⟨Or.inr h.1, h.2⟩
      simp only [ext, h1, if_false]
      exact hp.1 a id fun h => hn ⟨Or.inl h.1, h.2⟩
    · rw [ext_self hid (Or.inl rfl), ext_self hid (Or.inr rfl)]
  · intro y hy
    simp only [Contents, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy
    funext a id
    by_cases h : id ∈ New
    · by_cases ha : Holds h0 h1 a id
      · rw [ext_self h ha]
        simp only [h, if_true]
        rcases ha with rfl | rfl
        · rfl
        · exact hy.2 id h
      · simp only [ext, h, ha, and_false, if_false, if_true]
        exact (hy.1 a id fun hh => ha hh.2).symm
    · simp [ext, h]
  · rintro ⟨y, z⟩ hp
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    ext1
    · funext a id
      by_cases h : id ∈ New
      · simp only [h, if_true]
        exact (hp.1 a id fun hh => Finset.disjoint_left.1 hd hh.1 h).symm
      · simp [ext, h]
    · funext id
      by_cases h : id ∈ New
      · simp only [h, if_true]
        exact ext_self h (Or.inl rfl)
      · simp only [h, if_false]
        exact (hp.2 id h).symm
  · intro y hy
    simp only [Contents, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy
    congr 1
    funext a id
    by_cases h : id ∈ New
    · by_cases ha : Holds h0 h1 a id
      · rw [ext_self h ha]
        simp only [h, if_true]
        rcases ha with rfl | rfl
        · rfl
        · exact (hy.2 id h).symm
      · simp only [ext, h, ha, and_false, if_false, if_true]
        exact hy.1 a id fun hh => ha hh.2
    · simp [ext, h]

end Nc
end
/- Source module Nc.LowDegree. -/
section
namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}


def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)


def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

section Proof


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
/- Source module Nc.Cut.Rows. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Rows

variable {Γ : Type} {A : ℕ}


def ValidRow (ρ : Fin A → RowData A) (p : Fin A) : Prop :=
  if (ρ p).1 then (ρ p).2.1.1 = prevHi ρ p ∧ (ρ p).2.2.1 = prevHi ρ p
  else prevHi ρ p ≤ (ρ p).2.1.1 ∧ (ρ p).2.1 ≤ (ρ p).2.2

theorem ValidRow.prev_le {ρ : Fin A → RowData A} {p : Fin A} (h : ValidRow ρ p) : prevHi ρ p ≤ (ρ p).2.2.1 := by
  unfold ValidRow at h
  split_ifs at h with hc
  · exact h.2.ge
  · exact h.1.trans h.2

theorem hi_le_prevHi {ρ : Fin A → RowData A} (h : ∀ p, ValidRow ρ p) {p p' : Fin A} (hp : p < p') :
    (ρ p).2.2.1 ≤ prevHi ρ p' := by
  obtain ⟨p', hp'⟩ := p'
  have hlt : p.1 < p' := hp
  clear hp
  induction p' with
  | zero => omega
  | succ q ih =>
    have e : prevHi ρ ⟨q + 1, hp'⟩ = (ρ ⟨q, Nat.lt_of_succ_lt hp'⟩).2.2.1 := by
      rw [prevHi, dif_neg (Nat.succ_ne_zero q)]
      rfl
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h1 | h1
    · exact (ih (Nat.lt_of_succ_lt hp') h1).trans (h _).prev_le
    · have : p = ⟨q, Nat.lt_of_succ_lt hp'⟩ := Fin.ext h1
      rw [this]

theorem RowOk.flag {d : RowData A} {X : Fin A → List Γ} (h : RowOk d X) {b : Fin A} (hb : X b ≠ []) :
    d.1 = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [RowOk, if_pos hc] at h
  exact hb (h b)


theorem stair_of_rows {ρ : Fin A → RowData A} (h : ∀ p, ValidRow ρ p) {X : Fin A → Fin A → List Γ}
    (hX : ∀ p, RowOk (ρ p) (X p)) : Stair X := by
  intro a a' b b' hb hb' hlt
  have f := (hX a).flag hb
  have f' := (hX a').flag hb'
  have r := hX a
  have r' := hX a'
  have v' := h a'
  rw [RowOk, if_neg (by simp [f])] at r
  rw [RowOk, if_neg (by simp [f'])] at r'
  rw [ValidRow, if_neg (by simp [f'])] at v'
  have h1 := (r.2.2 b hb).2
  have h2 := hi_le_prevHi h hlt
  have h3 := (r'.2.2 b' hb').1
  rw [Fin.le_def] at *
  omega


noncomputable def hiBefore (X : Fin A → Fin A → List Γ) (q : ℕ) : ℕ :=
  open Classical in (univ.filter fun z : Fin A × Fin A => z.1.1 < q ∧ X z.1 z.2 ≠ []).sup fun z => z.2.1

theorem le_hiBefore {X : Fin A → Fin A → List Γ} {q : ℕ} {p b : Fin A} (hp : p.1 < q) (hb : X p b ≠ []) :
    b.1 ≤ hiBefore X q := by
  classical
  exact Finset.le_sup (f := fun z : Fin A × Fin A => z.2.1) (b := (p, b))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp, hb⟩)

theorem hiBefore_le {X : Fin A → Fin A → List Γ} {q c : ℕ} (h : ∀ p b : Fin A, p.1 < q → X p b ≠ [] → b.1 ≤ c) :
    hiBefore X q ≤ c := by
  classical
  refine Finset.sup_le fun z hz => ?_
  have := (Finset.mem_filter.1 hz).2
  exact h _ _ this.1 this.2

theorem exists_rows {X : Fin A → Fin A → List Γ} (hX : Stair X) :
    ∃ ρ : Fin A → RowData A, (∀ p, ValidRow ρ p) ∧ ∀ p, RowOk (ρ p) (X p) := by
  classical
  have hlt : ∀ (p : Fin A) q, hiBefore X q < A := by
    intro p q
    have : hiBefore X q ≤ A - 1 := hiBefore_le fun p b _ _ => by omega
    have := p.2
    omega
  have hrow : ∀ p : Fin A, ∃ d : RowData A, RowOk d (X p) ∧ d.2.2.1 = hiBefore X (p.1 + 1) ∧
      (if d.1 then d.2.1.1 = hiBefore X p.1 ∧ d.2.2.1 = hiBefore X p.1
        else hiBefore X p.1 ≤ d.2.1.1 ∧ d.2.1 ≤ d.2.2) := by
    intro p
    by_cases he : ∀ b, X p b = []
    · refine ⟨(true, ⟨hiBefore X p.1, hlt p _⟩, ⟨hiBefore X p.1, hlt p _⟩), ?_, ?_, ?_⟩
      · simpa [RowOk] using he
      · apply le_antisymm
        · exact hiBefore_le fun p' b hp' hb => le_hiBefore (Nat.lt_succ_of_lt hp') hb
        · refine hiBefore_le fun p' b hp' hb => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp' with h1 | h1
          · exact le_hiBefore h1 hb
          · have : p' = p := Fin.ext h1
            subst this
            exact absurd (he b) hb
      · simp
    · push Not at he
      obtain ⟨b0, hb0⟩ := he
      have hne : (univ.filter fun b => X p b ≠ []).Nonempty := ⟨b0, by simpa using hb0⟩
      have hmin := Finset.min'_mem _ hne
      have hmax := Finset.max'_mem _ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmin hmax
      refine ⟨(false, Finset.min' _ hne, Finset.max' _ hne), ?_, ?_, ?_⟩
      · simp only [RowOk, Bool.false_eq_true, if_false]
        refine ⟨hmin, hmax, fun b hb => ⟨Finset.min'_le _ _ (by simpa using hb), Finset.le_max' _ _ (by simpa using hb)⟩⟩
      · apply le_antisymm
        · exact le_hiBefore (Nat.lt_succ_self _) hmax
        · refine hiBefore_le fun p' b hp' hb => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp' with h1 | h1
          · exact hX p' p b _ hb hmax h1
          · have : p' = p := Fin.ext h1
            subst this
            have hm : b ∈ univ.filter fun b => X p' b ≠ [] := by simpa using hb
            exact Finset.le_max' _ _ hm
      · simp only [Bool.false_eq_true, if_false]
        exact ⟨hiBefore_le fun p' b hp' hb => hX p' p b _ hb hmin hp', Finset.min'_le _ _ (by simpa using hmax)⟩
  choose ρ h1 h2 h3 using hrow
  have hprev : ∀ p, prevHi ρ p = hiBefore X p.1 := by
    intro p
    rw [prevHi]
    split_ifs with h
    · rw [h]
      symm
      apply Nat.le_zero.1
      exact hiBefore_le fun p' b hp' _ => by omega
    · rw [h2]
      congr 1
      show p.1 - 1 + 1 = p.1
      omega
  refine ⟨ρ, fun p => ?_, h1⟩
  rw [ValidRow, hprev]
  exact h3 p

theorem rows_unique {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
    (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, RowOk (ρ p) (X p)) (hX' : ∀ p, RowOk (ρ' p) (X p)) : ρ = ρ' := by
  have key : ∀ (q : ℕ) (hq : q < A), ρ ⟨q, hq⟩ = ρ' ⟨q, hq⟩ := by
    intro q
    induction q with
    | zero =>
      intro hq
      exact row_eq h h' hX hX' rfl
    | succ q ih =>
      intro hq
      apply row_eq h h' hX hX'
      rw [prevHi, prevHi, dif_neg (Nat.succ_ne_zero q), dif_neg (Nat.succ_ne_zero q)]
      have := ih (Nat.lt_of_succ_lt hq)
      show (ρ ⟨q, _⟩).2.2.1 = (ρ' ⟨q, _⟩).2.2.1
      rw [this]
  exact funext fun p => key p.1 p.2
where
  row_eq {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
      (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, RowOk (ρ p) (X p)) (hX' : ∀ p, RowOk (ρ' p) (X p)) {p : Fin A}
      (hp : prevHi ρ p = prevHi ρ' p) : ρ p = ρ' p := by
    have v := h p
    have v' := h' p
    have r := hX p
    have r' := hX' p
    rw [ValidRow] at v v'
    by_cases he : ∀ b, X p b = []
    · have f : (ρ p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r
        exact r.1 (he _)
      have f' : (ρ' p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r'
        exact r'.1 (he _)
      rw [if_pos f] at v
      rw [if_pos f'] at v'
      refine Prod.ext (f.trans f'.symm) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · rw [v.1, v'.1, hp]
      · rw [v.2, v'.2, hp]
    · push Not at he
      obtain ⟨b, hb⟩ := he
      have f := r.flag hb
      have f' := r'.flag hb
      rw [RowOk, if_neg (by simp [f])] at r
      rw [RowOk, if_neg (by simp [f'])] at r'
      refine Prod.ext (f.trans f'.symm) (Prod.ext ?_ ?_)
      · exact le_antisymm (r.2.2 _ r'.1).1 (r'.2.2 _ r.1).1
      · exact le_antisymm (r'.2.2 _ r.2.1).2 (r.2.2 _ r'.2.1).2

end Rows

section Strings

variable {Γ S : Type} [Fintype S] [DecidableEq S]

theorem flatMap_sep_inj {σ : Type} (l : List σ) {X X' : σ → List Γ}
    (h : (l.flatMap fun s => (X s).map some ++ [none]) = l.flatMap fun s => (X' s).map some ++ [none]) :
    ∀ s ∈ l, X s = X' s := by
  have sep : ∀ (w w' : List Γ) (r r' : List (Option Γ)), w.map some ++ (none :: r) = w'.map some ++ (none :: r') →
      w = w' ∧ r = r' := by
    intro w
    induction w with
    | nil =>
      intro w' r r' h
      cases w' with
      | nil => simpa using h
      | cons a w' => simp at h
    | cons a w ih =>
      intro w' r r' h
      cases w' with
      | nil => simp at h
      | cons a' w' =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
        obtain ⟨e1, e2⟩ := ih w' r r' h.2
        exact ⟨by rw [h.1, e1], e2⟩
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append] at h
    obtain ⟨e1, e2⟩ := sep _ _ _ _ h
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact e1
    · exact ih e2 s' hs'

theorem joinSeg_inj {X X' : Option S → List Γ} (h : joinSeg X = joinSeg X') : X = X' :=
  funext fun s => flatMap_sep_inj _ h s (Finset.mem_toList.2 (Finset.mem_univ s))

theorem length_joinSeg (X : Option S → List Γ) :
    (joinSeg X).length = ∑ s, (X s).length + (Fintype.card S + 1) := by
  have : ∀ l : List (Option S), (l.flatMap fun s => (X s).map some ++ [none]).length =
      (l.map fun s => (X s).length).sum + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_nil,
        List.map_cons, List.sum_cons, List.length_cons]
      omega
  rw [joinSeg, this, Finset.length_toList, Finset.card_univ, Fintype.card_option]
  congr 1
  exact Finset.sum_map_toList _ _

variable {c : ℕ} {cb : Option Γ → Fin c → Bool}

theorem strOf_inj (hcb : Function.Injective cb) (hc : 0 < c) {X X' : Option S → List Γ}
    (h : strOf cb X = strOf cb X') : X = X' :=
  joinSeg_inj (bitsOf_inj hcb hc h)

theorem length_strOf (X : Option S → List Γ) :
    (strOf cb X).length = (∑ s, (X s).length + (Fintype.card S + 1)) * c := by
  rw [strOf, length_bitsOf, length_joinSeg]

end Strings

end Nc.Cut
end
/- Source module Nc.Cut.StartA. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Cat

variable {Γ : Type}

theorem cat_add {K K' : ℕ} (X : Fin (K + K') → List Γ) :
    cat X = (cat fun κ : Fin K => X (Fin.castAdd K' κ)) ++ cat fun κ : Fin K' => X (Fin.natAdd K κ) := by
  simp only [cat]
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem length_le_cat {K : ℕ} (X : Fin K → List Γ) (b : Fin K) : (X b).length ≤ (cat X).length := by
  rw [cat, List.length_flatten]
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  rw [List.mem_map]
  exact ⟨X b, List.mem_ofFn.2 ⟨b, rfl⟩, rfl⟩

theorem cat_nil_of {K : ℕ} {X : Fin K → List Γ} (h : ∀ b, X b = []) : cat X = [] := cat_eq_nil.2 h

theorem cat_parts {K : ℕ} (ℓ : ℕ) (u : List Γ) : cat (parts ℓ u : Fin K → List Γ) = u.take (K * ℓ) := by
  induction K generalizing u with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ]
    have e1 : (fun i : Fin K => (parts ℓ u : Fin (K + 1) → List Γ) i.succ) = parts ℓ (u.drop ℓ) := by
      funext i
      simp only [parts, Fin.val_succ, List.drop_drop]
      congr 2
      ring
    rw [e1, ih]
    simp only [parts, Fin.val_zero, Nat.zero_mul, List.drop_zero]
    rw [← List.take_add]
    congr 1
    ring

theorem length_parts_le {K : ℕ} (ℓ : ℕ) (u : List Γ) (κ : Fin K) : (parts ℓ u κ).length ≤ ℓ := by
  simp [parts]

end Cat

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ)


theorem blockW_sum_le {J : Type} [Fintype J] [DecidableEq J] {mu : Letter S J Γ → Matrix Q Q F} {T : ℕ} {q q' : Q}
    {v : Ch S J → List Γ} (h : blockW mu T q q' v ≠ 0) : ∑ z, (v z).length ≤ T := by
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at ho with he
  · have h1 := sum_length_proj (List.ofFn o).reduceOption
    have h2 := List.reduceOption_length_le (List.ofFn o)
    rw [← he]
    calc ∑ z, (emit (List.ofFn o) z).length = (List.ofFn o).reduceOption.length := h1
      _ ≤ T := by simpa using h2
  · exact absurd rfl ho

section Party

variable {T} {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}

open Classical in
theorem partyW_block (κ : Fin K) : partyW mu T q x (Fin.castAdd K κ) R C =
    if ∀ b, R none b = [] then blockW mu T (q κ.castSucc) (q κ.succ) (vec R C) else 0 := by
  rw [partyW, Fin.addCases_left]

open Classical in
theorem partyW_input (κ : Fin K) : partyW mu T q x (Fin.natAdd K κ) R C =
    if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0 := by
  rw [partyW, Fin.addCases_right]

variable {mu}


theorem partyW_sum_le (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)} (h : partyW mu T q x p R C ≠ 0) :
    ∑ s, (cat (R s)).length ≤ T := by
  classical
  refine Fin.addCases (motive := fun p => partyW mu T q x p R C ≠ 0 → ∑ s, (cat (R s)).length ≤ T) ?_ ?_ p h
  · intro κ h
    rw [partyW_block] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans ?_ (blockW_sum_le h)
    rw [Fintype.sum_option, cat_nil_of hc, List.length_nil, zero_add]
    have : ∑ s, (cat (R (some s))).length = ∑ s : S, ((vec R C (.tp s false)).length) := by
      simp [vec]
    rw [this]
    rw [← Finset.sum_image (f := fun z : Ch S Unit => (vec R C z).length) (s := univ) (g := fun s : S => .tp s false)]
    · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · intro s _ s' _ e
      simpa using e
  · intro κ h
    rw [partyW_input] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    rw [Fintype.sum_option, hc.2.2]
    have : ∑ s, (cat (R (some s))).length = 0 := by
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [cat_nil_of (hc.1 s), List.length_nil]
    rw [this]
    exact hx κ

end Party


noncomputable def segW (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p)


noncomputable def segs (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T

theorem mem_segs {K T : ℕ} {X : Option S → Fin (K + K) → Fin (K + K) → List Γ} :
    X ∈ segs Γ S K T ↔ ∀ s a b, (X s a b).length ≤ T := by
  simp [segs, mem_wordsLe]

variable {mu T}


theorem segW_ne_zero {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {X : Option S → Fin (K + K) → Fin (K + K) → List Γ} (h : segW mu T q x X ≠ 0) :
    (∀ κ b, X none (Fin.castAdd K κ) b = []) ∧
    (∀ s κ b, X (some s) (Fin.natAdd K κ) b = []) ∧ (∀ s κ b, X s b (Fin.natAdd K κ) = []) ∧
    (∀ κ, cat (X none (Fin.natAdd K κ)) = x κ) ∧
    segW mu T q x X = ∏ κ : Fin K, blockW mu T (q κ.castSucc) (q κ.succ)
      (vec (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) := by
  classical
  have h0 : ∀ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p) ≠ 0 := fun p hp =>
    h (Finset.prod_eq_zero (Finset.mem_univ p) hp)
  have h1 : ∀ κ b, X none (Fin.castAdd K κ) b = [] := by
    intro κ
    have := h0 (Fin.castAdd K κ)
    rw [partyW_block] at this
    by_contra hc
    rw [if_neg hc] at this
    exact this rfl
  have h2 : ∀ κ, (∀ s b, X (some s) (Fin.natAdd K κ) b = []) ∧ (∀ s b, X s b (Fin.natAdd K κ) = []) ∧
      cat (X none (Fin.natAdd K κ)) = x κ := by
    intro κ
    have := h0 (Fin.natAdd K κ)
    rw [partyW_input] at this
    by_contra hc
    rw [if_neg hc] at this
    exact this rfl
  refine ⟨h1, fun s κ => (h2 κ).1 s, fun s κ => (h2 κ).2.1 s, fun κ => (h2 κ).2.2, ?_⟩
  rw [segW, Fin.prod_univ_add]
  have e1 : (∏ κ : Fin K, partyW mu T q x (Fin.natAdd K κ) (fun s b => X s (Fin.natAdd K κ) b)
      fun s b => X s b (Fin.natAdd K κ)) = 1 := by
    refine Finset.prod_eq_one fun κ _ => ?_
    rw [partyW_input, if_pos (h2 κ)]
  rw [e1, mul_one]
  refine Finset.prod_congr rfl fun κ _ => ?_
  rw [partyW_block, if_pos (h1 κ)]

open Classical in

theorem sum_segs (q : Fin (K + 1) → Q) {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T) (u : Unit → List Γ)
    (hu : cat x = u ()) :
    (∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S Unit => wordsLe Γ T,
      if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j then
      ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) else 0) =
    ∑ X ∈ segs Γ S K T, if ∀ s, Stair (X s) then segW mu T q x X else 0 := by
  symm
  refine Finset.sum_bij_ne_zero (fun X _ _ => fun κ =>
    vec (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) ?_ ?_ ?_ ?_
  · intro X _ hne
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hst] at hne
    obtain ⟨-, -, -, -, e⟩ := segW_ne_zero hne
    rw [e] at hne
    rw [Fintype.mem_piFinset]
    intro κ
    rw [Fintype.mem_piFinset]
    exact blockW_ne_zero fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ κ) h0)
  · intro X _ hX X' _ hX' heq
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hX
      exact hX rfl
    have hst' : ∀ s, Stair (X' s) := by
      by_contra hc
      rw [if_neg hc] at hX'
      exact hX' rfl
    rw [if_pos hst] at hX
    rw [if_pos hst'] at hX'
    obtain ⟨a1, a2, a3, a4, -⟩ := segW_ne_zero hX
    obtain ⟨b1, b2, b3, b4, -⟩ := segW_ne_zero hX'
    funext s
    have hrow : ∀ p, cat (X s p) = cat (X' s p) := by
      intro p
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
      · cases s with
        | none => rw [cat_nil_of (a1 κ), cat_nil_of (b1 κ)]
        | some s => exact congrFun (congrFun heq κ) (.tp s false)
      · cases s with
        | none => rw [a4, b4]
        | some s => rw [cat_nil_of (a2 s κ), cat_nil_of (b2 s κ)]
    have hcol : ∀ p, cat (fun a => X s a p) = cat fun a => X' s a p := by
      intro p
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
      · cases s with
        | none => exact congrFun (congrFun heq κ) (.inp ())
        | some s => exact congrFun (congrFun heq κ) (.tp s true)
      · rw [cat_nil_of (a3 s κ), cat_nil_of (b3 s κ)]
    have r1 : IsRef (fun p => cat (X s p)) (fun p => cat fun a => X s a p) (X s) :=
      ⟨hst s, fun _ => rfl, fun _ => rfl⟩
    have r2 : IsRef (fun p => cat (X s p)) (fun p => cat fun a => X s a p) (X' s) :=
      ⟨hst' s, fun p => (hrow p).symm, fun p => (hcol p).symm⟩
    exact r1.unique r2
  · intro v hv hne
    have hm : (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hm] at hne
    have hvT : ∀ κ z, (v κ z).length ≤ T := by
      intro κ z
      have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hv κ) z
      exact mem_wordsLe.1 this
    -- what the parties write and read
    let W : Option S → Fin (K + K) → List Γ := fun s => match s with
      | none => Fin.addCases (motive := fun _ => List Γ) (fun _ => []) x
      | some s => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.tp s false)) fun _ => []
    let Rd : Option S → Fin (K + K) → List Γ := fun s => match s with
      | none => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.inp ())) fun _ => []
      | some s => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.tp s true)) fun _ => []
    have hW1 : ∀ κ, W none (Fin.castAdd K κ) = [] := fun κ => by simp only [W, Fin.addCases_left]
    have hW2 : ∀ κ, W none (Fin.natAdd K κ) = x κ := fun κ => by simp only [W, Fin.addCases_right]
    have hW3 : ∀ s κ, W (some s) (Fin.castAdd K κ) = v κ (.tp s false) := fun s κ => by
      simp only [W, Fin.addCases_left]
    have hW4 : ∀ s κ, W (some s) (Fin.natAdd K κ) = [] := fun s κ => by simp only [W, Fin.addCases_right]
    have hR1 : ∀ κ, Rd none (Fin.castAdd K κ) = v κ (.inp ()) := fun κ => by simp only [Rd, Fin.addCases_left]
    have hR2 : ∀ s κ, Rd s (Fin.natAdd K κ) = [] := by
      intro s κ
      cases s <;> simp only [Rd, Fin.addCases_right]
    have hR3 : ∀ s κ, Rd (some s) (Fin.castAdd K κ) = v κ (.tp s true) := fun s κ => by
      simp only [Rd, Fin.addCases_left]
    have hcat : ∀ s, cat (W s) = cat (Rd s) := by
      intro s
      rw [cat_add, cat_add]
      cases s with
      | none =>
        simp only [hW1, hW2, hR1, hR2]
        rw [cat_nil_of fun _ => rfl, hm.2 (), ← hu]
        simp
      | some s =>
        simp only [hW3, hW4, hR3, hR2]
        rw [hm.1 s]
    choose X hX using fun s => IsRef.exists (hcat s)
    have row : ∀ s p, cat (X s p) = W s p := fun s p => (hX s).row p
    have col : ∀ s p, cat (fun a => X s a p) = Rd s p := fun s p => (hX s).col p
    have c1 : ∀ κ b, X none (Fin.castAdd K κ) b = [] := fun κ => cat_eq_nil.1 ((row _ _).trans (hW1 κ))
    have c2 : ∀ s κ b, X (some s) (Fin.natAdd K κ) b = [] := fun s κ => cat_eq_nil.1 ((row _ _).trans (hW4 s κ))
    have c3 : ∀ s κ b, X s b (Fin.natAdd K κ) = [] := fun s κ => cat_eq_nil.1 ((col _ _).trans (hR2 s κ))
    have c4 : ∀ κ, cat (X none (Fin.natAdd K κ)) = x κ := fun κ => (row _ _).trans (hW2 κ)
    have hvec : ∀ κ, vec (fun s b => X s (Fin.castAdd K κ) b) (fun s b => X s b (Fin.castAdd K κ)) = v κ := by
      intro κ
      funext z
      cases z with
      | tp s b =>
        cases b with
        | false => exact (row (some s) _).trans (hW3 s κ)
        | true => exact (col (some s) _).trans (hR3 s κ)
      | inp j => exact (col none _).trans (hR1 κ)
    have hWX : segW mu T q x X = ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) := by
      rw [segW, Fin.prod_univ_add]
      have e1 : (∏ κ : Fin K, partyW mu T q x (Fin.natAdd K κ) (fun s b => X s (Fin.natAdd K κ) b)
          fun s b => X s b (Fin.natAdd K κ)) = 1 := by
        refine Finset.prod_eq_one fun κ _ => ?_
        rw [partyW_input, if_pos ⟨fun s => c2 s κ, fun s => c3 s κ, c4 κ⟩]
      rw [e1, mul_one]
      refine Finset.prod_congr rfl fun κ _ => ?_
      rw [partyW_block, if_pos (c1 κ), hvec]
    refine ⟨X, ?_, ?_, ?_⟩
    · rw [mem_segs]
      intro s a b
      refine (length_le_cat (X s a) b).trans ?_
      rw [row]
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) a
      · cases s with
        | none => rw [hW1]; exact Nat.zero_le _
        | some s => rw [hW3]; exact hvT _ _
      · cases s with
        | none => rw [hW2]; exact hx κ
        | some s => rw [hW4]; exact Nat.zero_le _
    · rw [if_pos fun s => (hX s).stair, hWX]
      exact hne
    · funext κ
      exact hvec κ
  · intro X _ hne
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hst] at hne ⊢
    obtain ⟨a1, a2, a3, a4, e⟩ := segW_ne_zero hne
    rw [if_pos, e]
    have hcat : ∀ s, cat (fun p => cat (X s p)) = cat fun p => cat fun a => X s a p := fun s =>
      IsRef.cat_eq ⟨hst s, fun _ => rfl, fun _ => rfl⟩
    constructor
    · intro s
      have := hcat (some s)
      rw [cat_add, cat_add] at this
      simp only [fun κ => cat_nil_of (a2 s κ), fun κ => cat_nil_of (a3 (some s) κ)] at this
      exact List.append_cancel_right this
    · intro j
      have := hcat none
      rw [cat_add, cat_add] at this
      simp only [fun κ => cat_nil_of (a1 κ), fun κ => cat_nil_of (a3 none κ), a4] at this
      rw [cat_nil_of (K := K) (X := fun _ => ([] : List Γ)) fun _ => rfl, List.nil_append, List.append_nil] at this
      rw [hu] at this
      exact this.symm

end Nc.Cut
end
/- Source module Nc.Cut.Codes. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Codes

variable {F : Type*} [CommRing F] {I : Type*} [Fintype I] {A B : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] {Zg Zh : Type*} [Fintype Zg] [DecidableEq Zg] [Fintype Zh]
  [DecidableEq Zh] (ca : (i : I) → A i → Zg) (cb : (i : I) → B i → Zh)

variable {ca cb} (hca : Function.Injective fun p : Σ i, A i => ca p.1 p.2)
  (hcb : Function.Injective fun p : Σ i, B i => cb p.1 p.2)

include hca hcb

end Codes

section Strings

variable {I : Type} {lam : ℕ} (lab : I → Fin lam → Bool)

theorem sideString_succ {B : ℕ} (len : I → ℕ) (i : Fin (B + 1) → I) (g : ∀ k, Fin (len (i k)) → Bool) :
    sideString lab len i g = List.ofFn (lab (i 0)) ++ (List.ofFn (g 0) ++
      sideString lab len (fun k => i k.succ) fun k => g k.succ) := by
  simp [sideString, List.ofFn_succ]

theorem length_sideString {B : ℕ} (len : I → ℕ) (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) :
    (sideString lab len i g).length = ∑ k, (lam + len (i k)) := by
  induction B with
  | zero => simp [sideString]
  | succ B ih =>
    rw [sideString_succ, List.length_append, List.length_append, ih, Fin.sum_univ_succ]
    simp [add_assoc]

variable {lab}

theorem sideString_inj (hlab : Function.Injective lab) {B : ℕ} (len : I → ℕ) {i i' : Fin B → I}
    {g : ∀ k, Fin (len (i k)) → Bool} {g' : ∀ k, Fin (len (i' k)) → Bool}
    (h : sideString lab len i g = sideString lab len i' g') : ∀ k, i k = i' k ∧ HEq (g k) (g' k) := by
  induction B with
  | zero => exact fun k => k.elim0
  | succ B ih =>
    rw [sideString_succ, sideString_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have e0 : i 0 = i' 0 := hlab (List.ofFn_injective h1)
    obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp [e0])
    have key : ∀ (a a' : I) (_ : a = a') (f : Fin (len a) → Bool) (f' : Fin (len a') → Bool),
        List.ofFn f = List.ofFn f' → HEq f f' := by
      rintro a _ rfl f f' hf
      exact heq_of_eq (List.ofFn_injective hf)
    intro k
    refine Fin.cases ⟨e0, key _ _ e0 _ _ h3⟩ (fun k => ih h4 k) k

theorem sideString_injective (hlab : Function.Injective lab) {B : ℕ} (len : I → ℕ) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, Fin (len (i k)) → Bool =>
      sideString lab len p.1 p.2 := by
  rintro ⟨i, g⟩ ⟨i', g'⟩ h
  have h := sideString_inj hlab len h
  have e : i = i' := funext fun k => (h k).1
  subst e
  have : g = g' := funext fun k => eq_of_heq (h k).2
  rw [this]

theorem ucount_sideString_le {m B U ub : ℕ} {len : I → ℕ} (hlen : ∀ i, len i ≤ m) (hB : B * (m + lam) / ub + 1 ≤ U)
    (i : Fin B → I) (g : ∀ k, Fin (len (i k)) → Bool) : ucount ub (sideString lab len i g) ≤ U := by
  refine le_trans ?_ hB
  rw [ucount, length_sideString]
  refine Nat.add_le_add_right (Nat.div_le_div_right ?_) _
  calc ∑ k, (lam + len (i k)) ≤ ∑ _k : Fin B, (m + lam) :=
        Finset.sum_le_sum fun k _ => by have := hlen (i k); omega
    _ = B * (m + lam) := by simp


def codeWord (lab : I → Fin lam → Bool) (len : I → ℕ) (ub U : ℕ) {B : ℕ} (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : Fin U → UW ub := fun k => unitsOf ub (sideString lab len i g) k

theorem codeWord_injective (hlab : Function.Injective lab) {m B U ub : ℕ} (hub : 0 < ub) {len : I → ℕ}
    (hlen : ∀ i, len i ≤ m) (hB : B * (m + lam) / ub + 1 ≤ U) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, Fin (len (i k)) → Bool =>
      codeWord lab len ub U p.1 p.2 := by
  intro p p' h
  apply sideString_injective hlab len
  apply unitsOf_inj hub
  intro k
  by_cases hk : k < U
  · exact congrFun h ⟨k, hk⟩
  · rw [unitsOf_eq_none.2, unitsOf_eq_none.2]
    · exact (ucount_sideString_le hlen hB _ _).trans (not_lt.1 hk)
    · exact (ucount_sideString_le hlen hB _ _).trans (not_lt.1 hk)

end Strings

end Nc.Cut
end
/- Source module Nc.Cut.Groups. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W G : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]











theorem mem_contents_iff {h0 h1 : U → A} {e : W} {Seen : Finset U} {y : A → U → W} :
    y ∈ Contents h0 h1 e Seen ↔ ∀ a id, ¬ (id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e := by
  simp [Contents]

theorem mem_common_iff {e : W} {New : Finset U} {z : U → W} :
    z ∈ Common e New ↔ ∀ id, id ∉ New → z id = e := by simp [Common]

theorem mem_gcontents_iff {h0 h1 : U → A} {e : W} {Seen : Finset U} {grp : A → G} {g : G} {y : A → U → W} :
    y ∈ GContents h0 h1 e Seen grp g ↔
      ∀ a id, ¬ (grp a = g ∧ id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e := by
  simp [GContents]

open Classical in




theorem posVal_groups (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (grp : A → G) (φ : A → (U → W) → F) :
    posVal h0 h1 e Seen Cur (fun y => ∏ a, φ a (y a)) =
      ∑ b ∈ Common e (cutUnits h0 h1 grp Cur), ∏ g, groupVal h0 h1 e Seen Cur grp φ g b := by
  classical
  have hR : ∀ b, (∏ g, groupVal h0 h1 e Seen Cur grp φ g b) =
      ∑ p ∈ Fintype.piFinset fun g => GContents h0 h1 e Seen grp g,
        if ∀ g, GAgree h0 h1 grp g Cur b (p g) then ∏ a, φ a (p (grp a) a) else 0 := by
    intro b
    simp only [groupVal]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff]
    congr 1
    rw [← Finset.prod_fiberwise univ grp]
    refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  simp only [hR]
  rw [← Finset.sum_product', ← Finset.sum_filter, posVal, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun y _ => (fun id => if id ∈ cutUnits h0 h1 grp Cur then y (h0 id) id else e,
      fun g a id => if grp a = g then y a id else e))
    (j := fun q _ => fun a id => q.2 (grp a) a id) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_contents_iff, mem_common_iff,
      mem_gcontents_iff] at hy ⊢
    refine ⟨⟨fun id hid => by simp [hid], fun g a id hn => ?_⟩, fun g => ⟨?_, ?_, ?_⟩⟩
    · by_cases h : grp a = g
      · simp only [h, if_true]
        exact hy.1 a id fun hh => hn ⟨h, hh⟩
      · simp [h]
    · intro id hid g1 g2
      simp [g1, g2, hy.2 id hid]
    · intro id hid g1 g2
      have : id ∈ cutUnits h0 h1 grp Cur := by
        simp only [cutUnits, Finset.mem_filter]
        exact ⟨hid, fun hh => g2 (hh ▸ g1)⟩
      simp [g1, this]
    · intro id hid g1 g2
      have : id ∈ cutUnits h0 h1 grp Cur := by
        simp only [cutUnits, Finset.mem_filter]
        exact ⟨hid, fun hh => g1 (hh ▸ g2)⟩
      simp [g2, this, hy.2 id hid]
  · rintro ⟨b, p⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_contents_iff, mem_common_iff,
      mem_gcontents_iff] at hq ⊢
    refine ⟨fun a id hn => hq.1.2 _ _ _ fun hh => hn hh.2, fun id hid => ?_⟩
    show p (grp (h0 id)) (h0 id) id = p (grp (h1 id)) (h1 id) id
    by_cases h : grp (h0 id) = grp (h1 id)
    · rw [h]
      exact (hq.2 (grp (h1 id))).both id hid h rfl
    · rw [(hq.2 _).fst id hid rfl (Ne.symm h), (hq.2 _).snd id hid h rfl]
  · intro y hy
    funext a id
    simp
  · rintro ⟨b, p⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_common_iff,
      mem_gcontents_iff] at hq ⊢
    ext1
    · funext id
      by_cases h : id ∈ cutUnits h0 h1 grp Cur
      · simp only [h, if_true]
        simp only [cutUnits, Finset.mem_filter] at h
        exact (hq.2 _).fst id h.1 rfl (Ne.symm h.2)
      · simp only [h, if_false]
        exact (hq.1.1 id h).symm
    · funext g a id
      by_cases h : grp a = g
      · subst h; simp
      · simp only [h, if_false]
        exact (hq.1.2 g a id fun hh => h hh.1).symm
  · intro y hy
    refine Finset.prod_congr rfl fun a _ => ?_
    simp


theorem posVal_move' {O : Type*} [Fintype O] (h0 h1 : U → A) (e : W) (Seen Cur Out : Finset U) (hOut : Out ⊆ Cur)
    (hCur : Cur ⊆ Seen) (New : O → Finset U) (hNew : ∀ o, Disjoint Seen (New o)) (E : (A → U → W) → F)
    (hE : ∀ o y z, E (ext h0 h1 (New o) y z) = E y) (C : O → (A → U → W) → F)
    (hC : ∀ y ∈ Contents h0 h1 e Seen, E y ≠ 0 → (if Agree h0 h1 Out y then (1 : F) else 0) =
      ∑ o, ∑ z ∈ Common e (New o), C o (ext h0 h1 (New o) y z)) :
    posVal h0 h1 e Seen Cur E =
      ∑ o, posVal h0 h1 e (Seen ∪ New o) ((Cur \ Out) ∪ New o) fun y => E y * C o y := by
  classical
  have h1' : ∀ o, posVal h0 h1 e (Seen ∪ New o) ((Cur \ Out) ∪ New o) (fun y => E y * C o y) =
      ∑ y ∈ Contents h0 h1 e Seen, if Agree h0 h1 (Cur \ Out) y then
        E y * ∑ z ∈ Common e (New o), C o (ext h0 h1 (New o) y z) else 0 := by
    intro o
    have e1 : ∀ y : A → U → W, (if Agree h0 h1 ((Cur \ Out) ∪ New o) y then E y * C o y else 0) =
        if Agree h0 h1 (New o) y then (if Agree h0 h1 (Cur \ Out) y then E y * C o y else 0) else 0 := by
      intro y
      have : Agree h0 h1 ((Cur \ Out) ∪ New o) y ↔ Agree h0 h1 (New o) y ∧ Agree h0 h1 (Cur \ Out) y := by
        simp only [Agree, Finset.mem_union]
        constructor
        · exact fun h => ⟨fun id hid => h id (Or.inr hid), fun id hid => h id (Or.inl hid)⟩
        · rintro ⟨ha, hb⟩ id (hid | hid)
          · exact hb id hid
          · exact ha id hid
      by_cases ha : Agree h0 h1 (New o) y <;> by_cases hb : Agree h0 h1 (Cur \ Out) y <;>
        simp [this, ha, hb]
    rw [posVal, Finset.sum_congr rfl fun y _ => e1 y, sum_contents_union h0 h1 e Seen (New o) (hNew o)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hne : ∀ id, id ∈ Seen → id ∉ New o := fun id h => Finset.disjoint_left.1 (hNew o) h
    have e2 : ∀ z, Agree h0 h1 (Cur \ Out) (ext h0 h1 (New o) y z) ↔ Agree h0 h1 (Cur \ Out) y := by
      intro z
      simp only [Agree]
      refine forall₂_congr fun id hid => ?_
      have := hne id (hCur (Finset.mem_sdiff.1 hid).1)
      rw [ext_of_not this, ext_of_not this]
    have e3 : ∀ z, E (ext h0 h1 (New o) y z) = E y := fun z => hE o y z
    simp only [e2, e3]
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  simp only [h1']
  rw [Finset.sum_comm, posVal]
  refine Finset.sum_congr rfl fun y hy => ?_
  by_cases hE0 : E y = 0
  · simp [hE0]
  by_cases hb : Agree h0 h1 (Cur \ Out) y
  · simp only [hb, if_true]
    rw [← Finset.mul_sum, ← hC y hy hE0]
    have : Agree h0 h1 Cur y ↔ Agree h0 h1 Out y := by
      constructor
      · exact fun h id hid => h id (hOut hid)
      · intro h id hid
        by_cases ho : id ∈ Out
        · exact h id ho
        · exact hb id (Finset.mem_sdiff.2 ⟨hid, ho⟩)
    by_cases ho : Agree h0 h1 Out y <;> simp [this, ho]
  · have : ¬ Agree h0 h1 Cur y := fun h => hb fun id hid => h id (Finset.mem_sdiff.1 hid).1
    simp [hb, this]

end Nc
end
/- Source module Nc.Cut.StartB. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

theorem ite_sum {ι M : Type*} [AddCommMonoid M] (c : Prop) [Decidable c] (s : Finset ι) (f : ι → M) :
    (if c then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if c then f i else 0 := by
  split_ifs <;> simp

theorem ite_ite_zero {M : Type*} [Zero M] (c d : Prop) [Decidable c] [Decidable d] (a : M) :
    (if c then (if d then a else 0) else 0) = if c ∧ d then a else 0 := by
  by_cases hc : c <;> simp [hc]

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

end Nc.Cut
end
/- Source module Nc.G.Contract. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

section Contract

variable {F : Type} [CommRing F] {Ro Cn ι : Type} [Fintype Ro] [DecidableEq Ro] [Fintype Cn] [DecidableEq Cn]
  [Fintype ι] {S : ι → Cn → Type} [∀ i ν, Fintype (S i ν)] {Z : Type} [Fintype Z] (c d : Cn → Ro)
  (code : (ν : Cn) → (i : ι) → S i ν → Z)

open Classical in

noncomputable def codeTab (p : Ro) (G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) (z : Cn → Z) : F :=
  ∑ i, ∑ g : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν then G i g else 0


theorem codeTab_congr {p : Ro} {G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F} {z z' : Cn → Z}
    (h : ∀ ν, c ν = p ∨ d ν = p → z ν = z' ν) : codeTab c d code p G z = codeTab c d code p G z' := by
  classical
  unfold codeTab
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  have : (∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν) ↔
      ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z' ν :=
    forall_congr' fun ν => by rw [h ν.1 ν.2]
  by_cases h1 : ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν
  · rw [if_pos h1, if_pos (this.1 h1)]
  · rw [if_neg h1, if_neg fun h2 => h1 (this.2 h2)]

variable {c d code}

open Classical in


theorem contract [Nonempty Ro]
    (hcode : ∀ ν, Function.Injective fun q : Σ i, S i ν => code ν q.1 q.2)
    (conn : ∀ f : Ro → ι, (∀ ν, f (c ν) = f (d ν)) → ∀ p p', f p = f p')
    (G : (p : Ro) → (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) :
    (∑ z : Cn → Z, ∏ p, codeTab c d code p (G p) z) = ∑ i, ∑ g : ∀ ν, S i ν, ∏ p, G p i fun ν => g ν := by
  have p0 : Ro := Classical.arbitrary Ro
  have hL : ∀ z : Cn → Z, (∏ p, codeTab c d code p (G p) z) =
      ∑ f : (p : Ro) → Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν,
        if ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν (f p).1 ((f p).2 ν) = z ν then ∏ p, G p (f p).1 (f p).2 else 0 := by
    intro z
    have e1 : ∀ p, codeTab c d code p (G p) z = ∑ q : Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν,
        if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν q.1 (q.2 ν) = z ν then G p q.1 q.2 else 0 := by
      intro p
      rw [codeTab, Fintype.sum_sigma]
    simp only [e1]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff]
  simp only [hL]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_sigma (fun q : Σ i, ∀ ν, S i ν => ∏ p, G p q.1 fun ν => q.2 ν)]
  symm
  refine Finset.sum_bij_ne_zero (fun q _ _ => (fun ν => code ν q.1 (q.2 ν), fun p => ⟨q.1, fun ν => q.2 ν⟩)) ?_ ?_ ?_ ?_
  · exact fun _ _ _ => Finset.mem_univ _
  · rintro ⟨i, g⟩ - - ⟨i', g'⟩ - - heq
    have h2 := congrArg Prod.snd heq
    have hi : i = i' := congrArg Sigma.fst (congrFun h2 p0)
    subst hi
    congr 1
    funext ν
    have h4 := congrFun h2 (c ν)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h4
    exact congrFun h4 ⟨ν, Or.inl rfl⟩
  · rintro ⟨z, f⟩ - hne
    have hcond : ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν (f p).1 ((f p).2 ν) = z ν := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hcond] at hne
    have hpair : ∀ ν, (⟨(f (c ν)).1, (f (c ν)).2 ⟨ν, Or.inl rfl⟩⟩ : Σ i, S i ν) =
        ⟨(f (d ν)).1, (f (d ν)).2 ⟨ν, Or.inr rfl⟩⟩ := by
      intro ν
      apply hcode ν
      simp only
      rw [hcond (c ν) ⟨ν, Or.inl rfl⟩, hcond (d ν) ⟨ν, Or.inr rfl⟩]
    have hall : ∀ p, (f p).1 = (f p0).1 := fun p =>
      conn (fun p => (f p).1) (fun ν => by
        have := congrArg Sigma.fst (hpair ν)
        exact this) p p0
    obtain ⟨i, hi⟩ : ∃ i, i = (f p0).1 := ⟨_, rfl⟩
    have hex : ∀ p, ∃ gp : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, f p = ⟨i, gp⟩ := by
      intro p
      have h := (hall p).trans hi.symm
      generalize f p = q at h ⊢
      obtain ⟨i', g'⟩ := q
      have h : i' = i := h
      subst h
      exact ⟨g', rfl⟩
    choose gp hgp using hex
    have hcond' : ∀ p, ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (gp p ν) = z ν := by
      intro p
      have := hcond p
      rw [hgp p] at this
      exact this
    let g : ∀ ν, S i ν := fun ν => gp (c ν) ⟨ν, Or.inl rfl⟩
    have hg : ∀ p, (fun ν : {ν // c ν = p ∨ d ν = p} => g ν) = gp p := by
      intro p
      funext ν
      obtain ⟨ν, hν⟩ := ν
      rcases hν with rfl | rfl
      · rfl
      · have := hpair ν
        rw [hgp (c ν), hgp (d ν)] at this
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
        exact this
    have hprod : (∏ p, G p i fun ν => g ν) = ∏ p, G p (f p).1 (f p).2 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [hgp p, hg p]
    refine ⟨⟨i, g⟩, Finset.mem_univ _, ?_, ?_⟩
    · rw [hprod]
      exact hne
    · ext1
      · funext ν
        exact hcond' (c ν) ⟨ν, Or.inl rfl⟩
      · funext p
        show (⟨i, fun ν => g ν⟩ : Σ i, (ν : {ν // c ν = p ∨ d ν = p}) → S i ν) = f p
        rw [hgp p, hg p]
  · rintro ⟨i, g⟩ - -
    simp only
    rw [if_pos]
    exact fun p ν => trivial

end Contract

section Pow

variable {F : Type} [CommRing F] (L : Law F)


theorem Law.pow (B : ℕ) (X : L.Ro → Fin B → L.Sl → Bool) :
    (if ∀ e k, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k := by
  have h1 : (if ∀ e k, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∏ k, if ∀ e, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0 := by
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff, Finset.prod_const_one]
    exact if_congr forall_comm rfl rfl
  rw [h1]
  have h2 : ∀ k, (if ∀ e, X (L.a e) k e = X (L.b e) k e then (1 : F) else 0) =
      ∑ i, ∑ g : (ν : L.Cn) → Fin (L.len i ν) → Bool, ∏ p, L.tab p i (fun e => X p k e) fun ν => g ν := fun k =>
    L.law fun p => X p k
  rw [Finset.prod_congr rfl fun k _ => h2 k]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.piComm fun (k : Fin B) (ν : L.Cn) => Fin (L.len (i k) ν) → Bool) _ _ fun g => ?_
  rw [Finset.prod_comm]
  rfl

theorem Law.conn_pow (B : ℕ) (f : L.Ro → Fin B → L.I) (h : ∀ ν, f (L.c ν) = f (L.d ν)) : ∀ p p', f p = f p' := by
  intro p p'
  funext k
  exact L.conn (fun p => f p k) (fun ν => congrFun (h ν) k) p p'

end Pow

end Nc.G
end
/- Source module Nc.G.Move. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

section Slots

variable {N : Type} [Fintype N] [DecidableEq N]

theorem length_uwBits {w : UW ub} (h : w ≠ none) : (uwBits w).length = ub := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  simp [uwBits]

theorem uwBits_inj {w w' : UW ub} (h : w ≠ none) (h' : w' ≠ none) (e : uwBits w = uwBits w') : w = w' := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨v', rfl⟩ := Option.ne_none_iff_exists'.1 h'
  rw [List.ofFn_injective e]

theorem length_uwList {ids : List (Uid A U0 N U1)} {y : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none) :
    (ids.flatMap fun id => uwBits (y id)).length = ids.length * ub := by
  induction ids with
  | nil => simp
  | cons id ids ih =>
    rw [List.flatMap_cons, List.length_append, length_uwBits (h id List.mem_cons_self),
      ih fun i hi => h i (List.mem_cons_of_mem _ hi), List.length_cons]
    ring

theorem length_slotBits {t : ℕ} {ids : List (Uid A U0 N U1)} {y : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none)
    (ht : ids.length ≤ t) : (slotBits t ids y).length = t * ub := by
  rw [slotBits, List.length_append, length_uwList h, List.length_replicate, ← add_mul, Nat.add_sub_cancel' ht]

theorem uwList_inj {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none)
    (h' : ∀ id ∈ ids, y' id ≠ none)
    (e : (ids.flatMap fun id => uwBits (y id)) = ids.flatMap fun id => uwBits (y' id)) : ∀ id ∈ ids, y id = y' id := by
  induction ids with
  | nil => simp
  | cons id ids ih =>
    rw [List.flatMap_cons, List.flatMap_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (by
      rw [length_uwBits (h id List.mem_cons_self), length_uwBits (h' id List.mem_cons_self)])
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact uwBits_inj (h _ List.mem_cons_self) (h' _ List.mem_cons_self) e1
    · exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) (fun i hi => h' i (List.mem_cons_of_mem _ hi)) e2 i hi


theorem slotBits_eq_iff {t : ℕ} {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub}
    (h : ∀ id ∈ ids, y id ≠ none) (h' : ∀ id ∈ ids, y' id ≠ none) (ht : ids.length ≤ t) :
    (∀ k : Fin (t * ub), (slotBits t ids y).getD k false = (slotBits t ids y').getD k false) ↔
      ∀ id ∈ ids, y id = y' id := by
  constructor
  · intro hk
    have e : slotBits t ids y = slotBits t ids y' := by
      apply List.ext_getElem
      · rw [length_slotBits h ht, length_slotBits h' ht]
      · intro k h1 h2
        have := hk ⟨k, by rwa [length_slotBits h ht] at h1⟩
        rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    unfold slotBits at e
    exact uwList_inj h h' (List.append_inj e (by rw [length_uwList h, length_uwList h'])).1
  · intro hk k
    have : slotBits t ids y = slotBits t ids y' := by
      unfold slotBits
      congr 1
      exact List.flatMap_congr fun id hid => by rw [hk id hid]
    rw [this]

theorem slotBits_congr {t : ℕ} {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub}
    (h : ∀ id ∈ ids, y id = y' id) : slotBits t ids y = slotBits t ids y' := by
  unfold slotBits
  congr 1
  exact List.flatMap_congr fun id hid => by rw [h id hid]

end Slots

section Role


theorem role_congr {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o o' : M.N → Fin U1} {y y' : Uid A U0 M.N U1 → UW ub} (ho : ∀ ν, o ⟨x, ν⟩ = o' ⟨x, ν⟩)
    (h1 : ∀ e, ∀ id ∈ ids e, y id = y' id)
    (h2 : ∀ ν : (M.kind x).CnAt p, ∀ k, y (.new ⟨x, ν.1⟩ k) = y' (.new ⟨x, ν.1⟩ k)) :
    role M x p t ids o y = role M x p t ids o' y' := by
  classical
  unfold role
  refine if_congr (forall_congr' fun e => forall₂_congr fun id hid => by rw [h1 e id hid]) ?_ rfl
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  refine if_congr (forall_congr' fun ν => ?_) ?_ rfl
  · unfold ChOk
    rw [ho]
    exact and_congr_right fun _ => forall_congr' fun k => by rw [h2 ν k]
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext e
    rw [slotBits_congr (h1 e)]

theorem role_ne_zero {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) :
    (∀ e, ∀ id ∈ ids e, y id ≠ none) ∧ ∃ (i : Fin (t * ub) → (M.kind x).I)
      (g : ∀ k, ∀ ν : (M.kind x).CnAt p, Fin ((M.kind x).len (i k) ν) → Bool),
      (∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
        (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y) ∧
      ∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) ≠ 0 := by
  classical
  rw [role] at h
  split_ifs at h with hy
  swap
  · exact absurd rfl h
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨g, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  · exact ⟨hy, i, g, hc, h⟩
  · exact absurd rfl h

theorem ChOk.ne_none {N : Type} {ν : N} {J : ℕ} {str : List Bool} {y : Uid A U0 N U1 → UW ub} (h : ChOk ν J str y)
    {k : Fin U1} (hk : k.1 ≤ J) : y (.new ν k) ≠ none := by
  rw [h.2 k, Ne, unitsOf_eq_none, h.1]
  omega


theorem role_new_ne_none {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) {k : Fin U1} (hk : k ≤ o ⟨x, ν⟩) : y (.new ⟨x, ν⟩ k) ≠ none := by
  obtain ⟨-, i, g, hg, -⟩ := role_ne_zero h
  exact (hg ⟨ν, hν⟩).ne_none hk

end Role

section Law

variable (L : Law F)


def chCode (ub U1 B : ℕ) (ν : L.Cn) (i : Fin B → L.I) (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool) : Fin U1 → UW ub :=
  fun k => unitsOf ub (chString L.lab (fun j => L.len j ν) i g) k

theorem length_chString {I : Type} {lam B : ℕ} (lb : I → Fin lam → Bool) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : (chString lb len i g).length = ∑ k, (lam + len (i k)) :=
  length_sideString lb len i g


structure Law.Le (L : Law F) (m : ℕ) : Prop where
  len_le : ∀ i ν, L.len i ν ≤ m

variable {L}

theorem chCode_injective (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1) (ν : L.Cn) :
    Function.Injective fun q : Σ i : Fin B → L.I, (k : Fin B) → Fin (L.len (i k) ν) → Bool =>
      chCode L ub U1 B ν q.1 q.2 :=
  codeWord_injective (len := fun i => L.len i ν) L.lab_inj hub (fun i => hm.len_le i ν) hB

open Classical in
variable (L) in

noncomputable def outTab (ub : ℕ) {U1 B : ℕ} (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1) (p : L.Ro)
    (i : Fin B → L.I) (g : (ν : L.CnAt p) → (k : Fin B) → Fin (L.len (i k) ν) → Bool) : F :=
  if ∀ ν : L.CnAt p, ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1 then
    ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k else 0


theorem sum_outTab (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1)
    (X : L.Ro → Fin B → L.Sl → Bool) :
    (∑ o : L.Cn → Fin U1, ∑ z : L.Cn → Fin U1 → UW ub, ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) =
      if ∀ e k, X (L.a e) k e = X (L.b e) k e then 1 else 0 := by
  classical
  rcases isEmpty_or_nonempty L.Ro with hRo | hRo
  · have hCn : IsEmpty L.Cn := ⟨fun ν => hRo.elim (L.c ν)⟩
    have hSl : IsEmpty L.Sl := ⟨fun e => hRo.elim (L.a e)⟩
    rw [if_pos fun e => hSl.elim e]
    simp
  have e1 : ∀ o : L.Cn → Fin U1, (∑ z : L.Cn → Fin U1 → UW ub,
      ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, outTab L ub X o p i fun ν => g ν := fun o =>
    contract (fun ν => chCode_injective hub hm hB ν) (L.conn_pow B) (outTab L ub X o)
  simp only [e1]
  let cnt : (Fin B → L.I) → L.Cn → ℕ := fun i ν => (∑ k, (L.lam + L.len (i k) ν)) / ub
  have hcnt : ∀ (i : Fin B → L.I) ν (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool),
      ucount ub (chString L.lab (fun j => L.len j ν) i g) = cnt i ν + 1 := by
    intro i ν g
    rw [ucount, length_chString]
  have hlt : ∀ i ν, cnt i ν < U1 := by
    intro i ν
    refine lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.div_le_div_right ?_)) hB
    calc ∑ k, (L.lam + L.len (i k) ν) ≤ ∑ _k : Fin B, (m + L.lam) :=
          Finset.sum_le_sum fun k _ => by have := hm.len_le (i k) ν; omega
      _ = B * (m + L.lam) := by simp
  have e2 : ∀ (o : L.Cn → Fin U1) i (g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool),
      (∏ p, outTab L ub X o p i fun ν => g ν) = if o = fun ν => ⟨cnt i ν, hlt i ν⟩ then
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) else 0 := by
    intro o i g
    unfold outTab
    rw [Finset.prod_ite_zero]
    have key : (∀ p ∈ (univ : Finset L.Ro), ∀ ν : L.CnAt p,
        ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1) ↔
        o = fun ν => (⟨cnt i ν, hlt i ν⟩ : Fin U1) := by
      simp only [Finset.mem_univ, true_imp_iff, hcnt]
      constructor
      · intro h
        funext ν
        have := h (L.c ν) ⟨ν, Or.inl rfl⟩
        exact Fin.ext (by simpa using this.symm)
      · rintro rfl p ν
        rfl
    by_cases h : o = fun ν => (⟨cnt i ν, hlt i ν⟩ : Fin U1)
    · rw [if_pos h, if_pos (key.2 h)]
    · rw [if_neg h, if_neg fun h' => h (key.1 h')]
  simp only [e2]
  have swap : (∑ o : L.Cn → Fin U1, ∑ i : Fin B → L.I,
      ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
      if o = fun ν => ⟨cnt i ν, hlt i ν⟩ then
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) else 0) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  rw [swap, ← L.pow B X]


theorem sum_codeTab_zero (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1)
    (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1)
    (h : ¬ ∃ i : Fin B → L.I, ∀ ν, (o ν).1 = (∑ k, (L.lam + L.len (i k) ν)) / ub) :
    (∑ z : L.Cn → Fin U1 → UW ub, ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) = 0 := by
  classical
  rcases isEmpty_or_nonempty L.Ro with hRo | hRo
  · have hCn : IsEmpty L.Cn := ⟨fun ν => hRo.elim (L.c ν)⟩
    have hSl : IsEmpty L.Sl := ⟨fun e => hRo.elim (L.a e)⟩
    have hI : IsEmpty (Fin B → L.I) := ⟨fun i => h ⟨i, fun ν => hCn.elim ν⟩⟩
    have := L.pow B X
    rw [if_pos fun e => hSl.elim e, Fintype.sum_empty] at this
    have h0 : ∀ a : F, a = 0 := fun a => by rw [← mul_one a, this, mul_zero]
    exact h0 _
  rw [contract (fun ν => chCode_injective hub hm hB ν) (L.conn_pow B) (outTab L ub X o)]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun g _ => ?_
  by_contra hne
  refine h ⟨i, fun ν => ?_⟩
  have h1 : outTab L ub X o (L.c ν) i (fun ν => g ν) ≠ 0 := fun h0 =>
    hne (Finset.prod_eq_zero (Finset.mem_univ (L.c ν)) h0)
  rw [outTab] at h1
  split_ifs at h1 with h2
  swap
  · exact absurd rfl h1
  have h3 := h2 ⟨ν, Or.inl rfl⟩
  rw [ucount, length_chString, Nat.add_right_cancel_iff] at h3
  exact h3.symm

end Law

section Identity


theorem role_eq_codeTab {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (hy : ∀ e, ∀ id ∈ ids e, y id ≠ none)
    {X : (M.kind x).Ro → Fin (t * ub) → (M.kind x).Sl → Bool}
    (hX : ∀ k (e : (M.kind x).SlAt p), X p k e = (slotBits t (ids e) y).getD k false) :
    role M x p t ids o y = codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
      (outTab (M.kind x) ub X (fun ν => o ⟨x, ν⟩) p) (fun ν k => y (.new ⟨x, ν⟩ k)) := by
  classical
  rw [role, if_pos hy, codeTab]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.piComm fun (k : Fin (t * ub)) (ν : (M.kind x).CnAt p) =>
    Fin ((M.kind x).len (i k) ν) → Bool) _ _ fun g => ?_
  have e1 : ∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
      (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y ↔
      chCode (M.kind x) ub U1 (t * ub) ν i (fun k => g k ν) = (fun k => y (.new ⟨x, ν.1⟩ k)) ∧
      ucount ub (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) = (o ⟨x, ν.1⟩).1 + 1 := by
    intro ν
    rw [ChOk, and_comm]
    refine and_congr_left fun _ => ?_
    rw [funext_iff]
    exact forall_congr' fun k => eq_comm
  have e2 : (∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k)) =
      ∏ k, (M.kind x).tab p (i k) (fun e => X p k e) (fun ν => g k ν) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext e
    exact (hX k e).symm
  rw [e2]
  by_cases h1 : ∀ ν : (M.kind x).CnAt p, chCode (M.kind x) ub U1 (t * ub) ν i (fun k => g k ν) =
    (fun k => y (.new ⟨x, ν.1⟩ k))
  · by_cases h2 : ∀ ν : (M.kind x).CnAt p, ucount ub (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i
        fun k => g k ν) = (o ⟨x, ν.1⟩).1 + 1
    · refine (if_pos fun ν => (e1 ν).2 ⟨h1 ν, h2 ν⟩).trans (Eq.trans ?_ (if_pos h1).symm)
      exact (if_pos h2).symm
    · refine (if_neg fun h => h2 fun ν => ((e1 ν).1 (h ν)).2).trans (Eq.trans ?_ (if_pos h1).symm)
      exact (if_neg h2).symm
  · exact (if_neg fun h => h1 fun ν => ((e1 ν).1 (h ν)).1).trans (if_neg h1).symm

theorem new_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

theorem init_not_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∉ newUnits M x o := by
  simp [newUnits]

theorem holds_new {x : Fin E} {p : (M.kind x).Ro} {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) (k : Fin U1) :
    Holds (hold0 M.np) (hold1 M.np) (M.part x p) (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) := by
  rcases hν with h | h
  · left
    show M.part x p = M.part x ((M.kind x).c ν)
    rw [h]
  · right
    show M.part x p = M.part x ((M.kind x).d ν)
    rw [h]


def upd (M : Sys F (A + A') E) (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) : M.N → Fin U1 := fun ν =>
  if h : x = ν.1 then (h ▸ oo : (M.kind ν.1).Cn → Fin U1) ν.2 else o ν

theorem upd_self (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) (ν : (M.kind x).Cn) :
    upd M o x oo ⟨x, ν⟩ = oo ν := by simp [upd]

theorem upd_ne (o : M.N → Fin U1) {x : Fin E} (oo : (M.kind x).Cn → Fin U1) {ν : M.N} (h : ν.1 ≠ x) :
    upd M o x oo ν = o ν := by
  rw [upd, dif_neg (Ne.symm h)]


theorem move_outcome (x : Fin E) {t : ℕ} (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none)
    (oo : (M.kind x).Cn → Fin U1) :
    (∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) =
      ∑ z : (M.kind x).Cn → Fin U1 → UW ub, ∏ p, codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
        (outTab (M.kind x) ub (fun p k e => (slotBits t (ids e) (y (M.part x p))).getD k false) oo p) z := by
  classical
  set X : (M.kind x).Ro → Fin (t * ub) → (M.kind x).Sl → Bool := fun p k e =>
    (slotBits t (ids e) (y (M.part x p))).getD k false with hX
  set New : Finset (Uid A U0 M.N U1) := newUnits M x (upd M o x oo) with hNew
  have hnew : ∀ id, id ∈ Seen → id ∉ New := by
    intro id hs hn
    cases id with
    | init a b k => exact init_not_mem_newUnits hn
    | new ν k =>
      obtain ⟨x', ν⟩ := ν
      obtain ⟨h, -⟩ := new_mem_newUnits.1 hn
      simp only at h
      subst h
      exact hSeen ν k hs
  rw [mem_contents_iff] at hy
  have key : ∀ z ∈ Common (none : UW ub) New, ∀ (a : Fin (A + A')) (ν : (M.kind x).Cn) k,
      Holds (hold0 M.np) (hold1 M.np) a (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) →
      ext (hold0 M.np) (hold1 M.np) New y z a (.new ⟨x, ν⟩ k) = z (.new ⟨x, ν⟩ k) := by
    intro z hz a ν k ha
    rw [mem_common_iff] at hz
    by_cases hn : (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) ∈ New
    · exact ext_self hn ha
    · rw [ext_of_not hn, hz _ hn]
      exact hy _ _ fun hh => hSeen _ _ hh.1
  have hext : ∀ (z : Uid A U0 M.N U1 → UW ub) p, ∀ e, ∀ id ∈ ids e,
      ext (hold0 M.np) (hold1 M.np) New y z (M.part x p) id = y (M.part x p) id := fun z p e id hid =>
    ext_of_not (hnew id (hids e id hid))
  have e1 : ∀ z ∈ Common (none : UW ub) New, ∀ p,
      role M x p t (fun e => ids e.1) (upd M o x oo) (ext (hold0 M.np) (hold1 M.np) New y z (M.part x p)) =
      codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p (outTab (M.kind x) ub X oo p)
        (fun ν k => z (.new ⟨x, ν⟩ k)) := by
    intro z hz p
    have hoo : (fun ν => upd M o x oo ⟨x, ν⟩) = oo := funext fun ν => upd_self o x oo ν
    rw [role_eq_codeTab (X := X), hoo]
    · exact codeTab_congr _ _ _ fun ν hν => funext fun k => key z hz _ _ _ (holds_new hν k)
    · intro e id hid
      rw [hext z p e.1 id hid]
      obtain ⟨e, he⟩ := e
      rcases he with he | he
      · rw [← he]; exact (hne e id hid).1
      · rw [← he]; exact (hne e id hid).2
    · intro k e
      rw [hX]
      simp only
      rw [slotBits_congr (hext z p e.1)]
  rw [Finset.sum_congr rfl fun z hz => Finset.prod_congr rfl fun p _ => e1 z hz p]
  refine Finset.sum_bij_ne_zero (fun z _ _ => fun ν k => z (.new ⟨x, ν⟩ k)) ?_ ?_ ?_ ?_
  · exact fun _ _ _ => Finset.mem_univ _
  · intro z1 h1 _ z2 h2 _ heq
    rw [mem_common_iff] at h1 h2
    funext id
    by_cases hn : id ∈ New
    · cases id with
      | init a b k => exact absurd hn init_not_mem_newUnits
      | new ν k =>
        obtain ⟨x', ν⟩ := ν
        obtain ⟨h, -⟩ := new_mem_newUnits.1 hn
        simp only at h
        subst h
        exact congrFun (congrFun heq ν) k
    · rw [h1 _ hn, h2 _ hn]
  · intro ζ _ hζ
    have hζ' : ∀ p, codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
        (outTab (M.kind x) ub X oo p) ζ ≠ 0 := fun p h0 => hζ (Finset.prod_eq_zero (Finset.mem_univ p) h0)
    let z : Uid A U0 M.N U1 → UW ub := fun id => match id with
      | .init _ _ _ => none
      | .new ν k => if h : x = ν.1 then (h ▸ ζ : (M.kind ν.1).Cn → Fin U1 → UW ub) ν.2 k else none
    have hz : ∀ ν k, z (.new ⟨x, ν⟩ k) = ζ ν k := fun ν k => by simp [z]
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [mem_common_iff]
      intro id hn
      cases id with
      | init a b k => rfl
      | new ν k =>
        obtain ⟨x', ν⟩ := ν
        by_cases hx : x = x'
        · subst hx
          rw [hz]
          rw [hNew, new_mem_newUnits] at hn
          simp only [true_and, not_le, upd_self] at hn
          obtain ⟨i, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hζ' ((M.kind x).c ν))
          obtain ⟨g, -, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
          split_ifs at h2 with h3
          swap
          · exact absurd rfl h2
          have h4 := h3 ⟨ν, Or.inl rfl⟩
          rw [outTab] at h2
          split_ifs at h2 with h5
          swap
          · exact absurd rfl h2
          have h6 := h5 ⟨ν, Or.inl rfl⟩
          rw [← h4]
          show unitsOf ub _ _ = none
          rw [unitsOf_eq_none, h6]
          exact hn
        · simp only [z]
          rw [dif_neg hx]
    · simpa only [hz] using hζ
    · funext ν k
      exact hz ν k
  · intro z _ _
    rfl


theorem move_identity (hub : 0 < ub) (x : Fin E) {m t : ℕ} (hm : (M.kind x).Le m)
    (hB : t * ub * (m + (M.kind x).lam) / ub + 1 ≤ U1) (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none) :
    (∑ oo : (M.kind x).Cn → Fin U1, ∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) =
      if ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id = y (M.part x ((M.kind x).b e)) id then 1 else 0 := by
  classical
  rw [Finset.sum_congr rfl fun oo _ => move_outcome x o Seen hSeen hy ids hids ht hne oo, sum_outTab hub hm hB]
  by_cases hall : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id = y (M.part x ((M.kind x).b e)) id
  · rw [if_pos hall, if_pos]
    exact fun e => (slotBits_eq_iff (fun id hid => (hne e id hid).1) (fun id hid => (hne e id hid).2) (ht e)).2 (hall e)
  · rw [if_neg hall, if_neg]
    exact fun h => hall fun e =>
      (slotBits_eq_iff (fun id hid => (hne e id hid).1) (fun id hid => (hne e id hid).2) (ht e)).1 (h e)


theorem move_zero (hub : 0 < ub) (x : Fin E) {m t : ℕ} (hm : (M.kind x).Le m)
    (hB : t * ub * (m + (M.kind x).lam) / ub + 1 ≤ U1) (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none)
    (oo : (M.kind x).Cn → Fin U1)
    (hoo : ¬ ∃ i : Fin (t * ub) → (M.kind x).I, ∀ ν, (oo ν).1 = (∑ k, ((M.kind x).lam + (M.kind x).len (i k) ν)) / ub) :
    (∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) = 0 := by
  rw [move_outcome x o Seen hSeen hy ids hids ht hne oo]
  exact sum_codeTab_zero hub hm hB _ oo hoo

end Identity

end Nc.G
end
/- Source module Nc.G.PlayThm. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

theorem init_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {a b : Fin A}
    {k : Fin U0} : (Uid.init a b k : Uid A U0 N U1) ∈ seen0 n ↔ k.1 < (n a b).1 := by
  simp [seen0]

theorem new_not_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {ν : N}
    {k : Fin U1} : (Uid.new ν k : Uid A U0 N U1) ∉ seen0 n := by
  simp [seen0]

namespace Plan

variable {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}

theorem mem_seenAt {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ seenAt n o x ↔
    id ∈ seen0 n ∨ ∃ x' : Fin E, x'.1 < x ∧ id ∈ newUnits M x' o := by
  simp [seenAt]

theorem new_mem_seenAt {x : ℕ} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ ν.1.1 < x ∧ k ≤ o ν := by
  rw [mem_seenAt]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact absurd h new_not_mem_seen0
    · obtain ⟨rfl, h2⟩ := new_mem_newUnits.1 h
      exact ⟨hx', h2⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨ν.1, h1, new_mem_newUnits.2 ⟨rfl, h2⟩⟩

theorem init_mem_seenAt {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ k.1 < (n a b).1 := by
  rw [mem_seenAt, init_mem_seen0]
  refine or_iff_left ?_
  rintro ⟨x', -, h⟩
  exact init_not_mem_newUnits h


theorem mem_seenAt_end {id : Uid A U0 M.N U1} : id ∈ seenAt n o E ↔ unum id < ucnt n o id := by
  cases id with
  | init a b k => exact init_mem_seenAt
  | new ν k =>
    rw [new_mem_seenAt]
    simp only [unum, ucnt, Nat.lt_succ_iff, ν.1.2, true_and]
    exact Iff.rfl

theorem mem_used {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.used n o x ↔ ∃ z : M.Z, z.1.1 < x ∧ id ∈ P.cons n o z := by
  simp [used]

theorem mem_cur {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.cur n o x ↔ id ∈ seenAt n o x ∧
    ∀ z : M.Z, z.1.1 < x → id ∉ P.cons n o z := by
  rw [cur, Finset.mem_sdiff, mem_used]
  push Not
  exact Iff.rfl

theorem mem_ids {z : M.Z} {id : Uid A U0 M.N U1} : id ∈ P.ids n o z ↔ id ∈ P.cons n o z := by
  simp [ids, allIds]

theorem length_ids {z : M.Z} : (P.ids n o z).length = (P.cons n o z).card := by
  rw [← List.toFinset_card_of_nodup]
  · congr 1
    ext id
    rw [List.mem_toFinset, mem_ids]
  · exact (Finset.nodup_toList _).filter _

theorem ids_congr {z : M.Z} (h : P.cons n o z = P.cons n o' z) : P.ids n o z = P.ids n o' z := by
  simp only [ids, h]

end Plan

section Lemmas

variable {P : Plan M U0 U1} {cap : ℕ} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}

theorem holds_cons (hP : P.Ok cap) {x : Fin E} {p : (M.kind x).Ro} {e : (M.kind x).Sl}
    (he : (M.kind x).a e = p ∨ (M.kind x).b e = p) {id : Uid A U0 M.N U1} (h : id ∈ P.cons n o ⟨x, e⟩) :
    Holds (hold0 M.np) (hold1 M.np) (M.part x p) id := by
  have h1 : (hold0 M.np id = M.part x ((M.kind x).a e) ∧ hold1 M.np id = M.part x ((M.kind x).b e)) ∨
      (hold1 M.np id = M.part x ((M.kind x).a e) ∧ hold0 M.np id = M.part x ((M.kind x).b e)) :=
    hP.hold n o ⟨x, e⟩ id h
  rcases he with rfl | rfl <;> rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr h1.symm
  · exact Or.inr h2.symm
  · exact Or.inl h2.symm

theorem seenAt_congr {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) :
    (Plan.seenAt n o x : Finset (Uid A U0 M.N U1)) = Plan.seenAt n o' x := by
  ext id
  cases id with
  | init a b k => rw [Plan.init_mem_seenAt, Plan.init_mem_seenAt]
  | new ν k =>
    rw [Plan.new_mem_seenAt, Plan.new_mem_seenAt]
    exact and_congr_right fun hx => by rw [h ν hx]

theorem cons_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) (z : M.Z) (hz : z.1.1 ≤ x) :
    P.cons n o z = P.cons n o' z :=
  hP.causal n o o' z fun ν hν => h ν (lt_of_lt_of_le hν hz)

theorem num_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) (x' : Fin E) (hx' : x'.1 ≤ x) :
    P.num n o x' = P.num n o' x' :=
  hP.causal' n o o' x' fun ν hν => h ν (lt_of_lt_of_le hν hx')

theorem cur_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) : P.cur n o x = P.cur n o' x := by
  ext id
  rw [Plan.mem_cur, Plan.mem_cur, seenAt_congr h]
  exact and_congr_right fun _ => forall_congr' fun z => imp_congr_right fun hz => by
    rw [cons_congr hP h z hz.le]

theorem roleAt_congr_o (hP : P.Ok cap) {x : Fin E} (h : ∀ ν : M.N, ν.1.1 < x.1 → o ν = o' ν)
    (ho : ∀ ν, o ⟨x, ν⟩ = o' ⟨x, ν⟩) (p : (M.kind x).Ro) (y : Uid A U0 M.N U1 → UW ub) :
    roleAt P n o ⟨x, p⟩ y = roleAt P n o' ⟨x, p⟩ y := by
  unfold roleAt
  have e1 : P.num n o x = P.num n o' x := num_congr hP h x le_rfl
  have e2 : (fun e : (M.kind x).SlAt p => P.ids n o ⟨x, e.1⟩) = fun e => P.ids n o' ⟨x, e.1⟩ :=
    funext fun e => Plan.ids_congr (cons_congr hP h ⟨x, e.1⟩ le_rfl)
  simp only [e1, e2]
  exact role_congr ho (fun _ _ _ => rfl) fun _ _ => rfl


noncomputable def tabUpTo (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F) (x : ℕ) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : F :=
  (∏ a, init a (y a)) * ∏ x' ∈ univ.filter (fun x' : Fin E => x'.1 < x), ∏ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p))

variable {init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F}


theorem tabUpTo_ne_none {x : ℕ} {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub}
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id →
      y id ≠ none) (h : tabUpTo P n o init x y ≠ 0) {a : Fin (A + A')} {id : Uid A U0 M.N U1}
    (hid : id ∈ Plan.seenAt n o x) (ha : Holds (hold0 M.np) (hold1 M.np) a id) : y a id ≠ none := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  cases id with
  | init b c k =>
    have h3 : init a (y a) ≠ 0 := fun h0 => h1 (Finset.prod_eq_zero (Finset.mem_univ a) h0)
    exact hinit a _ h3 _ (init_mem_seen0.2 (Plan.init_mem_seenAt.1 hid)) ha
  | new ν k =>
    obtain ⟨hx, hk⟩ := Plan.new_mem_seenAt.1 hid
    obtain ⟨x', ν⟩ := ν
    have h3 : ∀ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p)) ≠ 0 := by
      intro p h0
      exact h2 (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ x', hx⟩)
        (Finset.prod_eq_zero (Finset.mem_univ p) h0))
    rcases ha with ha | ha
    · have : a = M.part x' ((M.kind x').c ν) := ha
      rw [this]
      exact role_new_ne_none (h3 ((M.kind x').c ν)) (Or.inl rfl) hk
    · have : a = M.part x' ((M.kind x').d ν) := ha
      rw [this]
      exact role_new_ne_none (h3 ((M.kind x').d ν)) (Or.inr rfl) hk


theorem tabUpTo_congr (hP : P.Ok cap)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y') {x : ℕ}
    {y y' : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (h1 : ∀ a b c k, y a (.init b c k) = y' a (.init b c k))
    (h2 : ∀ a (ν : M.N) k, ν.1.1 < x → y a (.new ν k) = y' a (.new ν k)) :
    tabUpTo P n o init x y = tabUpTo P n o init x y' := by
  unfold tabUpTo
  congr 1
  · exact Finset.prod_congr rfl fun a _ => hloc a _ _ (h1 a)
  · refine Finset.prod_congr rfl fun x' hx' => Finset.prod_congr rfl fun p _ => ?_
    have hx := (Finset.mem_filter.1 hx').2
    refine role_congr (fun _ => rfl) (fun e id hid => ?_) fun ν k => h2 _ _ _ hx
    have hs := (Plan.mem_cur.1 (hP.sub n o _ (Plan.mem_ids.1 hid))).1
    cases id with
    | init a b k => exact h1 _ _ _ _
    | new ν k => exact h2 _ _ _ ((Plan.new_mem_seenAt.1 hs).1.trans hx)

theorem tabUpTo_congr_o (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν)
    (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : tabUpTo P n o init x y = tabUpTo P n o' init x y := by
  unfold tabUpTo
  congr 1
  refine Finset.prod_congr rfl fun x' hx' => Finset.prod_congr rfl fun p _ => ?_
  have hx := (Finset.mem_filter.1 hx').2
  exact roleAt_congr_o hP (fun ν hν => h ν (hν.trans hx)) (fun ν => h ⟨x', ν⟩ hx) p _

theorem filter_lt_succ (x : Fin E) : univ.filter (fun x' : Fin E => x'.1 < x.1 + 1) =
    insert x (univ.filter fun x' : Fin E => x'.1 < x.1) := by
  ext x'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem tabUpTo_succ (x : Fin E) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) :
    tabUpTo P n o init (x.1 + 1) y = tabUpTo P n o init x.1 y * ∏ p, roleAt P n o ⟨x, p⟩ (y (M.part x p)) := by
  unfold tabUpTo
  rw [filter_lt_succ, Finset.prod_insert (by simp)]
  ring

theorem seenAt_succ (x : Fin E) :
    (Plan.seenAt n o (x.1 + 1) : Finset (Uid A U0 M.N U1)) = Plan.seenAt n o x.1 ∪ newUnits M x o := by
  ext id
  rw [Finset.mem_union]
  cases id with
  | init a b k =>
    rw [Plan.init_mem_seenAt, Plan.init_mem_seenAt]
    exact (or_iff_left init_not_mem_newUnits).symm
  | new ν k =>
    rw [Plan.new_mem_seenAt, Plan.new_mem_seenAt, new_mem_newUnits, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
      · exact ⟨by omega, h2⟩


def outSet (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (x : Fin E) :
    Finset (Uid A U0 M.N U1) := univ.biUnion fun e : (M.kind x).Sl => P.cons n o ⟨x, e⟩

theorem mem_outSet {x : Fin E} {id : Uid A U0 M.N U1} : id ∈ outSet P n o x ↔ ∃ e, id ∈ P.cons n o ⟨x, e⟩ := by
  simp [outSet]

theorem cur_succ (hP : P.Ok cap) (x : Fin E) :
    P.cur n o (x.1 + 1) = (P.cur n o x.1 \ outSet P n o x) ∪ newUnits M x o := by
  ext id
  rw [Finset.mem_union, Finset.mem_sdiff, Plan.mem_cur, Plan.mem_cur, seenAt_succ, Finset.mem_union, mem_outSet]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · refine Or.inl ⟨⟨h1, fun z hz => h2 z (Nat.lt_succ_of_lt hz)⟩, ?_⟩
      rintro ⟨e, he⟩
      exact h2 ⟨x, e⟩ (Nat.lt_succ_self _) he
    · exact Or.inr h1
  · rintro (⟨⟨h1, h2⟩, h3⟩ | h)
    · refine ⟨Or.inl h1, fun z hz hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hz with h4 | h4
      · exact h2 z h4 hc
      · obtain ⟨x', e⟩ := z
        have : x' = x := Fin.ext h4
        subst this
        exact h3 ⟨e, hc⟩
    · refine ⟨Or.inr h, fun z hz hc => ?_⟩
      have hs := (Plan.mem_cur.1 (hP.sub n o z hc)).1
      cases id with
      | init a b k => exact init_not_mem_newUnits h
      | new ν k =>
        have h1 := (new_mem_newUnits.1 h).1
        have h2 := (Plan.new_mem_seenAt.1 hs).1
        rw [h1] at h2
        omega

end Lemmas

open Classical in


theorem _root_.Paper.thm_tree_move {P : Plan M U0 U1} {cap : ℕ} (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Poss n o ub x → P.good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.kind x).Le (m x)) (hU1 : ∀ x, cap * (m x + (M.kind x).lam) + 1 ≤ U1)
    {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1} (x : Fin E) {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub}
    (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x.1))
    (hne : ∀ a id, id ∈ Plan.seenAt n o x.1 → Holds (hold0 M.np) (hold1 M.np) a id → y a id ≠ none) :
    (if Agree (hold0 M.np) (hold1 M.np) (outSet P n o x) y then (1 : F) else 0) =
      ∑ oo : (M.kind x).Cn → Fin U1, ∑ z ∈ Common none (newUnits M x (upd M o x oo)),
        if P.good n (upd M o x oo) x then ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) else 0 := by
  have hnumo : ∀ oo : (M.kind x).Cn → Fin U1, P.num n (upd M o x oo) x = P.num n o x := fun oo =>
    hP.causal' n _ o x fun ν hν => upd_ne _ _ (ne_of_lt hν)
  have hB : P.num n o x * ub * (m x + (M.kind x).lam) / ub + 1 ≤ U1 := by
    refine le_trans ?_ (hU1 x)
    rw [mul_assoc, mul_comm ub, ← mul_assoc, Nat.mul_div_cancel _ hub]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hP.cap n o x)) 1
  have hseen : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, id ∈ Plan.seenAt n o x.1 := fun e id hid =>
    (Plan.mem_cur.1 (hP.sub n o ⟨x, e⟩ (Plan.mem_ids.1 hid))).1
  have hSeen : ∀ (ν : (M.kind x).Cn) (k : Fin U1), (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) ∉ Plan.seenAt n o x.1 :=
    fun ν k h => lt_irrefl _ (Plan.new_mem_seenAt.1 h).1
  have hlen : ∀ e, (P.ids n o ⟨x, e⟩).length ≤ P.num n o x := fun e => by
    rw [Plan.length_ids]
    exact hP.card n o ⟨x, e⟩
  have hne' : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, y (M.part x ((M.kind x).a e)) id ≠ none ∧
      y (M.part x ((M.kind x).b e)) id ≠ none := fun e id hid =>
    ⟨hne _ _ (hseen e id hid) (holds_cons hP (Or.inl rfl) (Plan.mem_ids.1 hid)),
      hne _ _ (hseen e id hid) (holds_cons hP (Or.inr rfl) (Plan.mem_ids.1 hid))⟩
  have hz : ∀ oo : (M.kind x).Cn → Fin U1, (∑ z ∈ Common none (newUnits M x (upd M o x oo)),
      if P.good n (upd M o x oo) x then ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) else (0 : F)) =
      ∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) := by
    intro oo
    by_cases hg : P.good n (upd M o x oo) x
    · simp only [hg, if_true]
    · simp only [hg, if_false, Finset.sum_const_zero]
      symm
      refine move_zero hub x (hm x) hB o (Plan.seenAt n o x.1) hSeen hy (fun e => P.ids n o ⟨x, e⟩) hseen hlen hne' oo ?_
      rintro ⟨i, hi⟩
      refine hg (hgood n _ x ?_)
      have e1 := hnumo oo
      unfold Plan.Poss
      rw [e1]
      exact ⟨i, fun ν => by rw [upd_self]; exact hi ν⟩
  rw [Finset.sum_congr rfl fun oo _ => hz oo]
  rw [move_identity hub x (hm x) (t := P.num n o x) hB o (Plan.seenAt n o x.1) hSeen hy
    (fun e => P.ids n o ⟨x, e⟩) hseen hlen hne']
  · refine if_congr ⟨fun h e id hid => ?_, fun h id hid => ?_⟩ rfl rfl
    · have hid' := Plan.mem_ids.1 hid
      have ha := h id (mem_outSet.2 ⟨e, hid'⟩)
      rcases hP.hold n o ⟨x, e⟩ id hid' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at ha; exact ha
      · rw [h1, h2] at ha; exact ha.symm
    · obtain ⟨e, he⟩ := mem_outSet.1 hid
      have := h e id (Plan.mem_ids.2 he)
      rcases hP.hold n o ⟨x, e⟩ id he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact this
      · rw [h1, h2]; exact this.symm

theorem upd_upd (o : M.N → Fin U1) (x : Fin E) (oo oo' : (M.kind x).Cn → Fin U1) :
    upd M (upd M o x oo) x oo' = upd M o x oo' := by
  funext ν
  obtain ⟨x', ν⟩ := ν
  by_cases h : x' = x
  · subst h
    rw [upd_self, upd_self]
  · rw [upd_ne _ _ h, upd_ne _ _ h, upd_ne _ _ h]

theorem upd_eq_self (o : M.N → Fin U1) (x : Fin E) : upd M o x (fun ν => o ⟨x, ν⟩) = o := by
  funext ν
  obtain ⟨x', ν⟩ := ν
  by_cases h : x' = x
  · subst h
    rw [upd_self]
  · rw [upd_ne _ _ h]

open Classical in


theorem _root_.Paper.thm_tree_moves {P : Plan M U0 U1} {cap : ℕ} (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Poss n o ub x → P.good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.kind x).Le (m x)) (hU : 0 < U1) (hU1 : ∀ x, cap * (m x + (M.kind x).lam) + 1 ≤ U1)
    (n : Fin A → Fin A → Fin (U0 + 1)) (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id →
      y id ≠ none) :
    posVal (hold0 M.np) (hold1 M.np) (none : UW ub) (seen0 n) (seen0 n) (fun y => ∏ a, init a (y a)) =
      ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
        posVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o E) (P.cur n o E) fun y =>
          ∏ a, partyTab P n o (init a) a (y a) else 0 := by
  let d : Fin U1 := ⟨0, hU⟩
  let pre : ℕ → Finset (M.N → Fin U1) := fun x => univ.filter fun o => ∀ ν : M.N, x ≤ ν.1.1 → o ν = d
  have claim : ∀ x, x ≤ E → posVal (hold0 M.np) (hold1 M.np) (none : UW ub) (seen0 n) (seen0 n)
      (fun y => ∏ a, init a (y a)) = ∑ o ∈ pre x, if ∀ x' : Fin E, x'.1 < x → P.good n o x' then
        posVal (hold0 M.np) (hold1 M.np) none
        (Plan.seenAt n o x) (P.cur n o x) (tabUpTo P n o init x) else 0 := by
    intro x
    induction x with
    | zero =>
      intro _
      have e1 : pre 0 = {fun _ => d} := by
        ext o
        simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · exact fun h => funext fun ν => h ν (Nat.zero_le _)
        · rintro rfl ν _; rfl
      rw [e1, Finset.sum_singleton]
      have e2 : (Plan.seenAt n (fun _ : M.N => d) 0 : Finset (Uid A U0 M.N U1)) = seen0 n := by
        ext id; simp [Plan.mem_seenAt]
      have e3 : P.cur n (fun _ : M.N => d) 0 = seen0 n := by
        ext id; simp [Plan.mem_cur, e2]
      have e4 : tabUpTo P n (fun _ => d) init 0 = fun y => ∏ a, init a (y a) := by
        funext y
        simp [tabUpTo]
      rw [e2, e3, e4, if_pos fun x' hx' => absurd hx' (Nat.not_lt_zero _)]
    | succ x ih =>
      intro hx
      rw [ih (Nat.le_of_succ_le hx)]
      let xE : Fin E := ⟨x, hx⟩
      have step : ∀ o ∈ pre x, (if ∀ x' : Fin E, x'.1 < x → P.good n o x' then
          posVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x) (P.cur n o x)
          (tabUpTo P n o init x) else 0) = ∑ oo : (M.kind xE).Cn → Fin U1,
          if ∀ x' : Fin E, x'.1 < x + 1 → P.good n (upd M o xE oo) x' then posVal (hold0 M.np) (hold1 M.np) none
          (Plan.seenAt n (upd M o xE oo) (x + 1)) (P.cur n (upd M o xE oo) (x + 1))
          (tabUpTo P n (upd M o xE oo) init (x + 1)) else 0 := by
        intro o _
        have hgx : ∀ (oo : (M.kind xE).Cn → Fin U1), (∀ x' : Fin E, x'.1 < x + 1 → P.good n (upd M o xE oo) x') ↔
            (∀ x' : Fin E, x'.1 < x → P.good n o x') ∧ P.good n (upd M o xE oo) xE := by
          intro oo
          have hc : ∀ x' : Fin E, x'.1 < x → (P.good n (upd M o xE oo) x' ↔ P.good n o x') := fun x' hx' =>
            hP.causal'' n _ o x' fun ν hν => upd_ne _ _ (by
              rintro h
              rw [h] at hν
              have : x ≤ x'.1 := hν
              omega)
          constructor
          · intro h
            exact ⟨fun x' hx' => (hc x' hx').1 (h x' (Nat.lt_succ_of_lt hx')), h xE (Nat.lt_succ_self _)⟩
          · rintro ⟨h1, h2⟩ x' hx'
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx' with h3 | h3
            · exact (hc x' h3).2 (h1 x' h3)
            · have : x' = xE := Fin.ext h3
              rw [this]
              exact h2
        by_cases hall : ∀ x' : Fin E, x'.1 < x → P.good n o x'
        swap
        · rw [if_neg hall]
          symm
          refine Finset.sum_eq_zero fun oo _ => if_neg fun h => hall ((hgx oo).1 h).1
        rw [if_pos hall]
        rw [posVal_move' (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x) (P.cur n o x)
          (outSet P n o xE) (fun id h => ?_)
          (fun id h => (Plan.mem_cur.1 h).1) (fun oo : (M.kind xE).Cn → Fin U1 => newUnits M xE (upd M o xE oo))
          (fun oo => ?_) (tabUpTo P n o init x) (fun oo y z => ?_)
          (fun oo y => if P.good n (upd M o xE oo) xE then
            ∏ p, role M xE p (P.num n o xE) (fun e => P.ids n o ⟨xE, e.1⟩) (upd M o xE oo)
            (y (M.part xE p)) else 0) (fun y hy h0 => ?_)]
        · refine Finset.sum_congr rfl fun oo _ => ?_
          by_cases hgo : P.good n (upd M o xE oo) xE
          swap
          · rw [if_neg fun h => hgo ((hgx oo).1 h).2]
            simp only [hgo, if_false, mul_zero, posVal, ite_self, Finset.sum_const_zero]
          rw [if_pos ((hgx oo).2 ⟨hall, hgo⟩)]
          simp only [hgo, if_true]
          set o' := upd M o xE oo with ho'
          have hlt : ∀ ν : M.N, ν.1.1 < xE.1 → o ν = o' ν := by
            intro ν hν
            rw [ho', upd_ne]
            rintro h
            rw [h] at hν
            exact lt_irrefl _ hν
          have f1 : Plan.seenAt n o' (x + 1) = Plan.seenAt n o x ∪ newUnits M xE o' := by
            rw [show x + 1 = xE.1 + 1 from rfl, seenAt_succ xE, seenAt_congr hlt]
          have f0 : outSet P n o xE = outSet P n o' xE := by
            unfold outSet
            congr 1
            funext e
            exact cons_congr hP hlt ⟨xE, e⟩ le_rfl
          have f2 : P.cur n o' (x + 1) = (P.cur n o x \ outSet P n o xE) ∪ newUnits M xE o' := by
            rw [show x + 1 = xE.1 + 1 from rfl, cur_succ hP xE, ← cur_congr hP hlt, f0]
          have f3 : tabUpTo P n o' init (x + 1) = fun y => tabUpTo P n o init x y *
              ∏ p, role M xE p (P.num n o xE) (fun e => P.ids n o ⟨xE, e.1⟩) o' (y (M.part xE p)) := by
            funext y
            rw [show x + 1 = xE.1 + 1 from rfl, tabUpTo_succ, ← tabUpTo_congr_o hP hlt]
            congr 1
            refine Finset.prod_congr rfl fun p _ => ?_
            have e1 : P.num n o xE = P.num n o' xE := num_congr hP hlt xE le_rfl
            have e2 : (fun e : (M.kind xE).SlAt p => P.ids n o ⟨xE, e.1⟩) = fun e => P.ids n o' ⟨xE, e.1⟩ :=
              funext fun e => Plan.ids_congr (cons_congr hP hlt ⟨xE, e.1⟩ le_rfl)
            rw [roleAt, e1, e2]
          rw [f1, f2, f3]
        · obtain ⟨e, he⟩ := mem_outSet.1 h
          exact hP.sub n o ⟨xE, e⟩ he
        · rw [Finset.disjoint_left]
          intro id h1 h2
          cases id with
          | init a b k => exact init_not_mem_newUnits h2
          | new ν k =>
            have a1 := (new_mem_newUnits.1 h2).1
            have a2 := (Plan.new_mem_seenAt.1 h1).1
            rw [a1] at a2
            exact lt_irrefl _ a2
        · refine tabUpTo_congr hP hloc (fun a b c k => ?_) fun a ν k hν => ?_
          · exact ext_of_not init_not_mem_newUnits
          · refine ext_of_not fun h => ?_
            have a1 := (new_mem_newUnits.1 h).1
            rw [a1] at hν
            exact lt_irrefl _ hν
        · exact Paper.thm_tree_move hP hub hgood hm hU1 xE hy fun a id hid ha => tabUpTo_ne_none hinit h0 hid ha
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_bij' (i := fun q _ => upd M q.1 xE q.2)
        (j := fun o _ => (upd M o xE fun _ => d, fun ν => o ⟨xE, ν⟩)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨o, oo⟩ h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h ⊢
        intro ν hν
        rw [upd_ne]
        · exact h ν (Nat.le_of_succ_le hν)
        · rintro h'
          rw [h'] at hν
          exact absurd hν (Nat.not_succ_le_self x)
      · intro o h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h ⊢
        intro ν hν
        obtain ⟨x', ν⟩ := ν
        by_cases e : x' = xE
        · subst e
          rw [upd_self]
        · rw [upd_ne _ _ e]
          exact h _ (lt_of_le_of_ne hν fun h => e (Fin.ext h.symm))
      · rintro ⟨o, oo⟩ h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h
        ext1
        · simp only [upd_upd]
          have : (fun _ : (M.kind xE).Cn => d) = fun ν => o ⟨xE, ν⟩ := funext fun ν => (h ⟨xE, ν⟩ le_rfl).symm
          rw [this, upd_eq_self]
        · funext ν
          exact upd_self _ _ _ ν
      · intro o _
        simp only [upd_upd]
        exact upd_eq_self o xE
      · rintro ⟨o, oo⟩ _
        rfl
  rw [claim E le_rfl]
  have e1 : pre E = univ := by
    ext o
    simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact fun ν hν => absurd ν.1.2 (not_lt.2 hν)
  rw [e1]
  refine Finset.sum_congr rfl fun o _ => if_congr ⟨fun h x => h x x.2, fun h x _ => h x⟩ ?_ rfl
  congr 1
  funext y
  unfold tabUpTo partyTab
  rw [Finset.prod_mul_distrib]
  congr 1
  have e2 : univ.filter (fun x' : Fin E => x'.1 < E) = univ := by
    ext x'; simp
  rw [e2, ← Fintype.prod_sigma' (f := fun x' p => roleAt P n o ⟨x', p⟩ (y (M.part x' p)))]
  symm
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Finset.prod_ite_eq, if_pos (Finset.mem_univ _)]
  rfl

end Nc.G
end
/- Source module Nc.G.Start. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}


def InitOk (ub : ℕ) {c : ℕ} (cb : Option Γ → Fin c → Bool) {A : ℕ} (ρ : Option S → RowData A)
    (n : Fin A → Fin A → ℕ) (p : Fin A) (y : Uid A U0 N U1 → UW ub) (R C : Option S → Fin A → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b ∧
      ∀ k : Fin U0, y (.init p b k) = unitsOf ub (strOf cb fun s => R s b) k) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p ∧
      ∀ k : Fin U0, y (.init b p k) = unitsOf ub (strOf cb fun s => C s b) k)

open Classical in
theorem tabInit_eq (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (y : Uid (K + K) U0 N U1 → UW ub) :
    tabInit mu T cb q x ρ n p y =
      ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
      ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
        if InitOk ub cb ρ n p y R C then partyW mu T q x p R C else 0 := by
  unfold tabInit
  exact Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr Iff.rfl rfl rfl


theorem tabInit_ne_none {np : N → Bool → Fin (K + K + A')} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K)}
    {y : Uid (K + K) U0 N U1 → UW ub} (h : tabInit mu T cb q x ρ (fun a b => (n a b).1) p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 np) (hold1 np) (Fin.castAdd A' p) id → y id ≠ none := by
  classical
  rw [tabInit_eq] at h
  obtain ⟨R, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  obtain ⟨-, h1, h2⟩ := hc
  intro id hid hh
  cases id with
  | new ν k => exact absurd hid new_not_mem_seen0
  | init a b k =>
    rw [init_mem_seen0] at hid
    rcases hh with hh | hh
    · have hh : p = a := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h1 b).2, Ne, unitsOf_eq_none, (h1 b).1]
      exact not_le.2 hid
    · have hh : p = b := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h2 a).2, Ne, unitsOf_eq_none, (h2 a).1]
      exact not_le.2 hid


theorem tabInit_congr {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)} {y y' : Uid (K + K) U0 N U1 → UW ub}
    (h : ∀ a b k, y (.init a b k) = y' (.init a b k)) :
    tabInit mu T cb q x ρ n p y = tabInit mu T cb q x ρ n p y' := by
  classical
  rw [tabInit_eq, tabInit_eq]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr ?_ rfl rfl
  simp only [InitOk, h]


noncomputable def sides (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Fin (K + K) → Option S → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T

theorem mem_sides {K T : ℕ} {R : Fin (K + K) → Option S → Fin (K + K) → List Γ} :
    R ∈ sides Γ S K T ↔ ∀ p s b, (R p s b).length ≤ T := by
  simp [sides, mem_wordsLe]

open Classical in
theorem prod_tabInit (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (y : Fin (K + K) → Uid (K + K) U0 N U1 → UW ub) :
    (∏ p, tabInit mu T cb q x (fun s => ρ s p) n p (y p)) =
      ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T, if ∀ p, InitOk ub cb (fun s => ρ s p) n p (y p) (R p) (C p) then
        ∏ p, partyW mu T q x p (R p) (C p) else 0 := by
  simp only [tabInit_eq]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_imp_iff]

open Classical in

theorem sum_pos (hcb : Function.Injective cb) (hc : 0 < c) (hub : 0 < ub)
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A'))
    (q : Fin (K + 1) → Q) {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T) :
    (∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
      ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 (N := N) (U1 := U1) n) (seen0 n) fun y =>
          ∏ p : Fin (K + K), tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p (y (Fin.castAdd A' p))
      else 0) =
    ∑ X ∈ segs Γ S K T, if ∀ s, Stair (X s) then segW mu T q x X else 0 := by
  have hpos : ∀ (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (f : (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) → F),
      posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 n) (seen0 n) f = ∑ y, if
        y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) ∧ Agree (hold0 np) (hold1 np) (seen0 n) y then
          f y else 0 := by
    intro n f
    rw [posVal, ← Finset.univ_inter (Contents (hold0 np) (hold1 np) none (seen0 n)), ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h1 : y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) <;>
      by_cases h2 : Agree (hold0 np) (hold1 np) (seen0 n) y <;> simp [h1, h2]
  have hprod : ∀ (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → ℕ)
      (y : Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub),
      (∏ p : Fin (K + K), tabInit mu T cb q x (fun s => ρ s p) n p (y (Fin.castAdd A' p))) =
      ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T,
        if ∀ p, InitOk ub cb (fun s => ρ s p) n p (y (Fin.castAdd A' p)) (R p) (C p) then
          ∏ p, partyW mu T q x p (R p) (C p) else 0 := fun ρ n y =>
    prod_tabInit q x ρ n fun p => y (Fin.castAdd A' p)
  simp only [hpos, hprod, ite_sum, ite_ite_zero]
  -- one sum over all data
  let Cnd : (Option S → Fin (K + K) → RowData (K + K)) × (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) ×
      (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) × (Fin (K + K) → Option S → Fin (K + K) → List Γ) ×
      (Fin (K + K) → Option S → Fin (K + K) → List Γ) → Prop := fun ω =>
    ValidRows ω.1 ∧ (ω.2.2.1 ∈ Contents (hold0 np) (hold1 np) none (seen0 ω.2.1) ∧
      Agree (hold0 np) (hold1 np) (seen0 ω.2.1) ω.2.2.1) ∧
      ∀ p, InitOk ub cb (fun s => ω.1 s p) (fun a b => (ω.2.1 a b).1) p (ω.2.2.1 (Fin.castAdd A' p)) (ω.2.2.2.1 p) (ω.2.2.2.2 p)
  have big : (∑ ω ∈ (univ ×ˢ (univ ×ˢ (univ ×ˢ (sides Γ S K T ×ˢ sides Γ S K T))) :
      Finset ((Option S → Fin (K + K) → RowData (K + K)) × (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) ×
      (Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub) × (Fin (K + K) → Option S → Fin (K + K) → List Γ) ×
      (Fin (K + K) → Option S → Fin (K + K) → List Γ))),
      if Cnd ω then ∏ p, partyW mu T q x p (ω.2.2.2.1 p) (ω.2.2.2.2 p) else 0) =
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        ∑ y : Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub, ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T,
        if ValidRows ρ ∧ (y ∈ Contents (hold0 np) (hold1 np) none (seen0 n) ∧
          Agree (hold0 np) (hold1 np) (seen0 n) y) ∧ ∀ p, InitOk ub cb (fun s => ρ s p)
          (fun a b => (n a b).1) p (y (Fin.castAdd A' p)) (R p) (C p) then ∏ p, partyW mu T q x p (R p) (C p) else 0 := by
    simp only [Finset.sum_product, Cnd]
  refine big.symm.trans ?_
  symm
  -- the data of given segments
  let nX : (Option S → Fin (K + K) → Fin (K + K) → List Γ) → Fin (K + K) → Fin (K + K) → Fin (U0 + 1) :=
    fun X a b => ⟨min (ucount ub (strOf cb fun s => X s a b)) U0, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let yX : (Option S → Fin (K + K) → Fin (K + K) → List Γ) → Fin (K + K + A') → Uid (K + K) U0 N U1 → UW ub :=
    fun X p id => match id with
      | .init a b k => if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then unitsOf ub (strOf cb fun s => X s a b) k
          else none
      | .new _ _ => none
  have hst : ∀ X, (if ∀ s, Stair (X s) then segW mu T q x X else 0) ≠ 0 →
      (∀ s, Stair (X s)) ∧ segW mu T q x X ≠ 0 := by
    intro X h
    by_cases hs : ∀ s, Stair (X s)
    · rw [if_pos hs] at h
      exact ⟨hs, h⟩
    · rw [if_neg hs] at h
      exact absurd rfl h
  have hrows : ∀ X : Option S → Fin (K + K) → Fin (K + K) → List Γ, (∀ s, Stair (X s)) →
      ∃ ρ : Option S → Fin (K + K) → RowData (K + K), ValidRows ρ ∧ ∀ s p, RowOk (ρ s p) (X s p) := by
    intro X h
    choose ρ h1 h2 using fun s => exists_rows (h s)
    exact ⟨ρ, h1, h2⟩
  choose ρX hρ1 hρ2 using hrows
  have hcount : ∀ X, segW mu T q x X ≠ 0 → ∀ a b, ucount ub (strOf cb fun s => X s a b) ≤ U0 := by
    intro X h a b
    refine le_trans ?_ hU
    rw [ucount, length_strOf]
    refine Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right ?_ _))) _
    have ha : partyW mu T q x a (fun s b => X s a b) (fun s b => X s b a) ≠ 0 := fun h0 =>
      h (Finset.prod_eq_zero (Finset.mem_univ a) h0)
    exact (Finset.sum_le_sum fun s _ => length_le_cat (X s a) b).trans (partyW_sum_le hx ha)
  refine Finset.sum_bij_ne_zero (fun X _ h => (ρX X (hst X h).1, nX X, yX X, fun p s b => X s p b,
    fun p s b => X s b p)) ?_ ?_ ?_ ?_
  · intro X hX h
    rw [mem_segs] at hX
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_sides]
    exact ⟨fun p s b => hX s p b, fun p s b => hX s b p⟩
  · intro X _ h X' _ h' heq
    have := congrArg (fun ω => ω.2.2.2.1) heq
    funext s a b
    exact congrFun (congrFun (congrFun this a) s) b
  · rintro ⟨ρ, n, y, R, C⟩ hω h
    have hC : Cnd (ρ, n, y, R, C) := by
      by_contra hc
      rw [if_neg hc] at h
      exact h rfl
    rw [if_pos hC] at h
    obtain ⟨v, ⟨hy, hag⟩, hI⟩ := hC
    simp only at v hy hag hI h
    rw [mem_contents_iff] at hy
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_sides] at hω
    -- rows and columns agree
    have hRC : ∀ a b, (fun s => R a s b) = fun s => C b s a := by
      intro a b
      apply strOf_inj hcb hc
      apply unitsOf_inj hub
      intro k
      have r := (hI a).2.1 b
      have r' := (hI b).2.2 a
      by_cases hk : k < (n a b).1
      · have hkU : k < U0 := lt_of_lt_of_le hk (Nat.le_of_lt_succ (n a b).2)
        rw [← r.2 ⟨k, hkU⟩, ← r'.2 ⟨k, hkU⟩]
        exact hag (.init a b ⟨k, hkU⟩) (init_mem_seen0.2 hk)
      · rw [unitsOf_eq_none.2 (r.1.trans_le (not_lt.1 hk)), unitsOf_eq_none.2 (r'.1.trans_le (not_lt.1 hk))]
    let X : Option S → Fin (K + K) → Fin (K + K) → List Γ := fun s a b => R a s b
    have hCX : ∀ p s b, C p s b = X s b p := fun p s b => (congrFun (hRC b p) s).symm
    have hC' : C = fun p s b => X s b p := by
      funext p s b
      exact hCX p s b
    have hrow : ∀ s p, RowOk (ρ s p) (X s p) := fun s p => (hI p).1 s
    have hstX : ∀ s, Stair (X s) := fun s => stair_of_rows (v s) (hrow s)
    have hW : segW mu T q x X = ∏ p, partyW mu T q x p (R p) (C p) := by
      rw [hC']
      rfl
    have hne : (if ∀ s, Stair (X s) then segW mu T q x X else 0) ≠ 0 := by
      rw [if_pos hstX, hW]
      exact h
    refine ⟨X, mem_segs.2 fun s a b => hω.1 a s b, hne, ?_⟩
    have e1 : ρX X (hst X hne).1 = ρ := by
      funext s
      exact rows_unique (hρ1 X _ s) (v s) (hρ2 X _ s) (hrow s)
    have e2 : nX X = n := by
      funext a b
      apply Fin.ext
      have := ((hI a).2.1 b).1
      show min (ucount ub (strOf cb fun s => R a s b)) U0 = (n a b).1
      rw [this]
      exact Nat.min_eq_left (Nat.le_of_lt_succ (n a b).2)
    have e3 : yX X = y := by
      funext p id
      cases id with
      | new ν k =>
        symm
        exact hy _ _ fun hh => new_not_mem_seen0 hh.1
      | init a b k =>
        show (if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then unitsOf ub (strOf cb fun s => R a s b) k else none) =
          y p (.init a b k)
        by_cases hp : p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b
        · rw [if_pos hp]
          rcases hp with rfl | rfl
          · exact (((hI a).2.1 b).2 k).symm
          · rw [((hI b).2.2 a).2 k, hRC]
        · rw [if_neg hp]
          symm
          exact hy _ _ fun hh => hp hh.2
    rw [e1, e2, e3, hC']
  · intro X _ h
    obtain ⟨hs, hne⟩ := hst X h
    have hcnt := hcount X hne
    have hn : ∀ a b, (nX X a b).1 = ucount ub (strOf cb fun s => X s a b) := fun a b =>
      Nat.min_eq_left (hcnt a b)
    have hy : ∀ p a b k, p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b → yX X p (.init a b k) = unitsOf ub (strOf cb fun s => X s a b) k := by
      intro p a b k hp
      exact if_pos hp
    rw [if_pos hs, if_pos]
    · rfl
    refine ⟨hρ1 X hs, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_contents_iff]
      intro p id hn'
      cases id with
      | new ν k => rfl
      | init a b k =>
        by_cases hp : p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b
        · have h1 : yX X p (.init a b k) = unitsOf ub (strOf cb fun s => X s a b) k := hy p a b k hp
          refine h1.trans (unitsOf_eq_none.2 ?_)
          rw [← hn]
          exact not_lt.1 fun hk => hn' ⟨init_mem_seen0.2 hk, hp⟩
        · exact if_neg hp
    · intro id hid
      cases id with
      | new ν k => exact absurd hid new_not_mem_seen0
      | init a b k => exact (hy _ a b k (Or.inl rfl)).trans (hy _ a b k (Or.inr rfl)).symm
    · intro p
      refine ⟨fun s => hρ2 X hs s p, fun b => ⟨(hn p b).symm, fun k => hy _ p b k (Or.inl rfl)⟩,
        fun b => ⟨(hn b p).symm, fun k => hy _ b p k (Or.inr rfl)⟩⟩

open Classical in


theorem start (hcb : Function.Injective cb) (hc : 0 < c) (hub : 0 < ub)
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A')) (i e : Q)
    (u : Unit → List Γ) {ℓ : ℕ} (hℓ : ℓ ≤ T) (hu : (u ()).length ≤ K * ℓ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
          posVal (hold0 np) (hold1 np) (none : UW ub) (seen0 (N := N) (U1 := U1) n) (seen0 n) fun y =>
            ∏ p : Fin (K + K), tabInit mu T cb q (parts ℓ (u ())) (fun s => ρ s p) (fun a b => (n a b).1) p
              (y (Fin.castAdd A' p))
      else 0
    else 0 := by
  rw [runVal_blocks]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hx : ∀ κ : Fin K, (parts ℓ (u ()) κ).length ≤ T := fun κ => (length_parts_le _ _ _).trans hℓ
  have hcat : cat (parts ℓ (u ()) : Fin K → List Γ) = u () := by
    rw [cat_parts, List.take_of_length_le hu]
  rw [sum_pos hcb hc hub hU np q hx, ← sum_segs q hx u hcat]

end Nc.G
end
/- Source module Nc.Cut.Exact. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Groups

variable {AA UU W G : Type*} [Fintype AA] [DecidableEq AA] [Fintype UU] [DecidableEq UU]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]


theorem groupVal_ne_none {h0 h1 : UU → AA} {e : W} {Seen Cur : Finset UU} (hCur : Cur ⊆ Seen) {grp : AA → G}
    {φ : AA → (UU → W) → F} {g : G} {b : UU → W}
    (hφ : ∀ a y, φ a y ≠ 0 → ∀ id ∈ Seen, Holds h0 h1 a id → y id ≠ e)
    (h : groupVal h0 h1 e Seen Cur grp φ g b ≠ 0) {id : UU} (hid : id ∈ Cur)
    (hg : (grp (h0 id) = g ∧ grp (h1 id) ≠ g) ∨ (grp (h0 id) ≠ g ∧ grp (h1 id) = g)) : b id ≠ e := by
  classical
  rw [groupVal] at h
  obtain ⟨y, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  have h2 : ∀ a, grp a = g → φ a (y a) ≠ 0 := fun a ha h0 =>
    h (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h0)
  rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
  · rw [← hc.fst id hid g1 g2]
    exact hφ _ _ (h2 _ g1) id (hCur hid) (Or.inl rfl)
  · rw [← hc.snd id hid g1 g2]
    exact hφ _ _ (h2 _ g2) id (hCur hid) (Or.inr rfl)

end Groups

end Nc.Cut
end
/- Source module Nc.G.Exact. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A A' K E U0 U1 ub c : ℕ}

section Play

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}


theorem partyTab_ne_none {init : (Uid A U0 M.N U1 → UW ub) → F} {a : Fin (A + A')} {y : Uid A U0 M.N U1 → UW ub}
    (hinit : init y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id → y id ≠ none)
    (h : partyTab P n o init a y ≠ 0) {id : Uid A U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) a id) : y id ≠ none := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  cases id with
  | init b c k => exact hinit h1 _ (init_mem_seen0.2 (Plan.init_mem_seenAt.1 hid)) ha
  | new ν k =>
    obtain ⟨-, hk⟩ := Plan.new_mem_seenAt.1 hid
    obtain ⟨x, ν⟩ := ν
    have h3 : ∀ p, M.part x p = a → roleAt P n o ⟨x, p⟩ y ≠ 0 := by
      intro p hp h0
      refine h2 (Finset.prod_eq_zero (Finset.mem_univ (⟨x, p⟩ : M.R)) ?_)
      have : M.rp ⟨x, p⟩ = a := hp
      rw [if_pos this]
      exact h0
    rcases ha with ha | ha
    · have : a = M.part x ((M.kind x).c ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inl rfl) hk
    · have : a = M.part x ((M.kind x).d ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inr rfl) hk

end Play

section Exact

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E}


noncomputable def initAll (A' : ℕ) {N : Type} [Fintype N] [DecidableEq N] {U0 U1 ub : ℕ} (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (p : Fin (K + K + A')) : (Uid (K + K) U0 N U1 → UW ub) → F :=
  Fin.addCases (motive := fun _ => (Uid (K + K) U0 N U1 → UW ub) → F)
    (fun p => tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p) (fun _ _ => 1) p

variable {mu T cb}

theorem tabFinal_eq {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} (p : Fin (K + K + A')) :
    (tabFinal mu T cb P q x ρ n o p : (Uid (K + K) U0 M.N U1 → UW ub) → F) =
      partyTab P n o (initAll mu T cb A' q x ρ n p) p := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · rw [tabFinal, initAll, Fin.addCases_left, Fin.addCases_left]
  · rw [tabFinal, initAll, Fin.addCases_right, Fin.addCases_right]

theorem initAll_ne_none {N : Type} [Fintype N] [DecidableEq N] {f : N → Bool → Fin (K + K + A')}
    {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K + A')} {y : Uid (K + K) U0 N U1 → UW ub}
    (h : initAll mu T cb A' q x ρ n p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 f) (hold1 f) p id → y id ≠ none := by
  revert h
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · intro h
    rw [initAll, Fin.addCases_left] at h
    exact tabInit_ne_none h
  · intro _ id hid hh
    cases id with
    | new ν k => exact absurd hid new_not_mem_seen0
    | init a b k =>
      exfalso
      have hne : ∀ a : Fin (K + K), Fin.natAdd (K + K) p ≠ Fin.castAdd A' a := by
        intro a h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      rcases hh with hh | hh
      · exact hne a hh
      · exact hne b hh

theorem tabFinal_ne_none {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} {p : Fin (K + K + A')} {y : Uid (K + K) U0 M.N U1 → UW ub}
    (h : tabFinal mu T cb P q x ρ n o p y ≠ 0) {id : Uid (K + K) U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) p id) : y id ≠ none := by
  rw [tabFinal_eq] at h
  exact partyTab_ne_none (fun h0 => initAll_ne_none h0) h hid ha


theorem grpVal_ne_none {G : Type} [Fintype G] [DecidableEq G] {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
    {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.N → Fin U1} {grp : Fin (K + K + A') → G}
    {g : G} {b : Uid (K + K) U0 M.N U1 → UW ub} (h : grpVal mu T cb P q x ρ n o grp g b ≠ 0)
    {id : Uid (K + K) U0 M.N U1} (hid : id ∈ P.cur n o E)
    (hg : (grp (hold0 M.np id) = g ∧ grp (hold1 M.np id) ≠ g) ∨
      (grp (hold0 M.np id) ≠ g ∧ grp (hold1 M.np id) = g)) : b id ≠ none :=
  Cut.groupVal_ne_none (fun _ hi => (Plan.mem_cur.1 hi).1)
    (fun _ _ h0 _ hi ha => tabFinal_ne_none h0 hi ha) h hid hg

end Exact

end Nc.G
end
/- Source module Nc.SlpCalc. -/
section
namespace Unc

open Finset Nc.Cut

variable {Inp ι : Type} {D : ℕ}


variable {inp : ι → Inp → Fin D}

lemma SlpN.mono {p : ℕ} {H H' : Set (Inp → ℕ)} (h : SlpN inp p H) (hs : H' ⊆ H) : SlpN inp p H' := by
  obtain ⟨fn, h1, h2⟩ := h
  exact ⟨fn, h1, fun f hf => h2 f (hs hf)⟩

lemma SlpN.empty (hD : 0 < D) : SlpN inp 0 ∅ :=
  ⟨fun _ _ => ⟨0, hD⟩, fun k hk => absurd hk (Nat.not_lt_zero k), fun f hf => absurd hf (Set.notMem_empty f)⟩


lemma SlpN.snoc {p : ℕ} {H : Set (Inp → ℕ)} (h : SlpN inp p H) (f : Inp → Fin D)
    (hf : (∃ i, f = inp i) ∨ (∃ c, f = fun _ => c) ∨ ∃ h1 ∈ H, ∃ h2 ∈ H, ∃ φ : Fin D → Fin D → Fin D,
      ∀ (x : Inp) (a b : Fin D), (a : ℕ) = h1 x → (b : ℕ) = h2 x → f x = φ a b) :
    SlpN inp (p + 1) (insert (fun x => (f x : ℕ)) H) := by
  classical
  obtain ⟨fn, hs, hH⟩ := h
  have hne : ∀ k < p, Function.update fn p f k = fn k := fun k hk =>
    Function.update_of_ne (by omega) _ _
  have heq : Function.update fn p f p = f := Function.update_self _ _ _
  refine ⟨Function.update fn p f, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · rcases hs k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, φ, h1⟩
      · exact Or.inl ⟨i, by rw [hne k hk, h1]⟩
      · exact Or.inr (Or.inl ⟨c, by rw [hne k hk, h1]⟩)
      · refine Or.inr (Or.inr ⟨i, hi, j, hj, φ, fun x => ?_⟩)
        rw [hne k hk, hne i (by omega), hne j (by omega), h1]
    · subst hk
      rcases hf with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨h1, hh1, h2, hh2, φ, h3⟩
      · exact Or.inl ⟨i, by rw [heq, h1]⟩
      · exact Or.inr (Or.inl ⟨c, by rw [heq, h1]⟩)
      · obtain ⟨i, hi, e1⟩ := hH h1 hh1
        obtain ⟨j, hj, e2⟩ := hH h2 hh2
        refine Or.inr (Or.inr ⟨i, hi, j, hj, φ, fun x => ?_⟩)
        rw [heq, hne i hi, hne j hj]
        exact h3 x _ _ (e1 x) (e2 x)
  · intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · exact ⟨p, Nat.lt_succ_self p, fun x => by rw [heq, hg]⟩
    · obtain ⟨k, hk, e1⟩ := hH g hg
      exact ⟨k, by omega, fun x => by rw [hne k hk]; exact e1 x⟩


lemma SlpN.le (hD : 0 < D) {p q : ℕ} (hpq : p ≤ q) {H : Set (Inp → ℕ)} (h : SlpN inp p H) :
    SlpN inp q H := by
  induction q, hpq using Nat.le_induction with
  | base => exact h
  | succ q _ ih =>
    exact (ih.snoc (fun _ => ⟨0, hD⟩) (Or.inr (Or.inl ⟨_, rfl⟩))).mono (Set.subset_insert _ _)


lemma SlpN.inputs [Fintype ι] (hD : 0 < D) (inp : ι → Inp → Fin D) :
    SlpN inp (Fintype.card ι) (Set.range fun i x => (inp i x : ℕ)) := by
  classical
  have : ∀ s : Finset ι, SlpN inp s.card ((fun i x => (inp i x : ℕ)) '' (s : Set ι)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using SlpN.empty hD
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi]
      refine (ih.snoc (inp i) (Or.inl ⟨i, rfl⟩)).mono ?_
      intro f hf
      obtain ⟨j, hj, rfl⟩ := hf
      rcases mem_insert.mp (mem_coe.mp hj) with h | h
      · subst h; exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨j, mem_coe.mpr h, rfl⟩
  have h := this univ
  rw [coe_univ, Set.image_univ, card_univ] at h
  exact h


inductive Cost (D : ℕ) (A : Set (Inp → ℕ)) : ℕ → (Inp → ℕ) → Prop
  
  | base {h : Inp → ℕ} : h ∈ A → Cost D A 0 h
  
  | const (c : ℕ) : c < D → Cost D A 1 fun _ => c
  
  | op {p q : ℕ} {h1 h2 : Inp → ℕ} (φ : ℕ → ℕ → ℕ) : Cost D A p h1 → Cost D A q h2 →
      (∀ x, φ (h1 x) (h2 x) < D) → Cost D A (p + q + 1) fun x => φ (h1 x) (h2 x)
  
  | mono {p q : ℕ} {h : Inp → ℕ} : Cost D A p h → p ≤ q → Cost D A q h

variable {A : Set (Inp → ℕ)}


theorem Cost.run (hD : 0 < D) {c : ℕ} {h : Inp → ℕ} (hc : Cost D A c h) :
    ∀ {p : ℕ} {H : Set (Inp → ℕ)}, A ⊆ H → SlpN inp p H → SlpN inp (p + c) (insert h H) := by
  induction hc with
  | base hA =>
    intro p H hs hH
    rw [Set.insert_eq_of_mem (hs hA)]
    exact hH
  | const c hc =>
    intro p H _ hH
    exact hH.snoc (fun _ => ⟨c, hc⟩) (Or.inr (Or.inl ⟨_, rfl⟩))
  | @op p q h1 h2 φ _ _ hφ ih1 ih2 =>
    intro p' H hs hH
    have a1 := ih1 hs hH
    have a2 := ih2 (hs.trans (Set.subset_insert h1 H)) a1
    have a3 := a2.snoc (fun x => ⟨φ (h1 x) (h2 x), hφ x⟩) (Or.inr (Or.inr ⟨h1,
      Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2, Set.mem_insert _ _,
      fun a b => if hlt : φ a b < D then ⟨φ a b, hlt⟩ else ⟨0, hD⟩, by
        intro x a b ha hb
        simp only [ha, hb, dif_pos (hφ x)]⟩))
    have e : p' + (p + q + 1) = p' + p + q + 1 := by ring
    rw [e]
    refine a3.mono ?_
    intro f hf
    rcases Set.mem_insert_iff.mp hf with hf | hf
    · rw [hf]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
  | mono _ hpq ih =>
    intro p' H hs hH
    exact (ih hs hH).le hD (by omega)


theorem SlpN.stage (hD : 0 < D) {κ : Type*} [Fintype κ] {p : ℕ} {H : Set (Inp → ℕ)} (h : SlpN inp p H)
    (f : κ → Inp → ℕ) (c : ℕ) (hf : ∀ i, Cost D H c (f i)) :
    SlpN inp (p + Fintype.card κ * c) (H ∪ Set.range f) := by
  classical
  have : ∀ s : Finset κ, SlpN inp (p + s.card * c) (H ∪ f '' (s : Set κ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi]
      have e : p + (s.card + 1) * c = p + s.card * c + c := by ring
      rw [e]
      refine ((hf i).run hD Set.subset_union_left ih).mono ?_
      intro g hg
      rcases hg with hg | ⟨j, hj, rfl⟩
      · exact Set.mem_insert_of_mem _ (Or.inl hg)
      · rcases mem_insert.mp (mem_coe.mp hj) with h | h
        · subst h; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Or.inr ⟨j, mem_coe.mpr h, rfl⟩)
  have h2 := this univ
  rw [coe_univ, Set.image_univ, card_univ] at h2
  exact h2

namespace Cost

lemma congr {c : ℕ} {h h' : Inp → ℕ} (hc : Cost D A c h) (e : ∀ x, h x = h' x) : Cost D A c h' := by
  have : h = h' := funext e
  rwa [← this]

lemma weaken {A' : Set (Inp → ℕ)} (hA : A ⊆ A') {c : ℕ} {h : Inp → ℕ} (hc : Cost D A c h) :
    Cost D A' c h := by
  induction hc with
  | base hh => exact base (hA hh)
  | const c hc => exact const c hc
  | op φ _ _ hφ ih1 ih2 => exact op φ ih1 ih2 hφ
  | mono _ hpq ih => exact mono ih hpq


lemma op1 (hD : 0 < D) {p : ℕ} {h : Inp → ℕ} (φ : ℕ → ℕ) (hc : Cost D A p h) (hφ : ∀ x, φ (h x) < D) :
    Cost D A (p + 2) fun x => φ (h x) :=
  op (fun a _ => φ a) hc (const 0 hD) hφ


lemma sum (hD : 0 < D) {κ : Type*} (s : Finset κ) {c : ℕ} {h : κ → Inp → ℕ} (hc : ∀ i ∈ s, Cost D A c (h i))
    (hb : ∀ x, ∑ i ∈ s, h i x < D) : Cost D A (s.card * (c + 1) + 1) fun x => ∑ i ∈ s, h i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (A := A) 0 hD
  | insert i s hi ih =>
    have hb' : ∀ x, ∑ i ∈ s, h i x < D := fun x => by
      have := hb x
      rw [sum_insert hi] at this
      omega
    have h1 := ih (fun j hj => hc j (mem_insert_of_mem hj)) hb'
    have h2 := op (fun a b => a + b) (hc i (mem_insert_self _ _)) h1 (fun x => by
      have := hb x
      rw [sum_insert hi] at this
      exact this)
    refine (h2.congr fun x => by rw [sum_insert hi]).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

end Cost

lemma ind_true {P : Inp → Prop} {x : Inp} (h : P x) : ind P x = 1 := by unfold ind; simp [h]

lemma ind_false {P : Inp → Prop} {x : Inp} (h : ¬ P x) : ind P x = 0 := by unfold ind; simp [h]

lemma ind_le (P : Inp → Prop) (x : Inp) : ind P x ≤ 1 := by
  by_cases h : P x
  · rw [ind_true h]
  · rw [ind_false h]; omega


def CostP (D : ℕ) (A : Set (Inp → ℕ)) (c : ℕ) (P : Inp → Prop) : Prop := Cost D A c (ind P)

namespace CostP

lemma congr {c : ℕ} {P Q : Inp → Prop} (hc : CostP D A c P) (h : ∀ x, P x ↔ Q x) : CostP D A c Q := by
  have : P = Q := funext fun x => propext (h x)
  rwa [← this]

lemma mono {p q : ℕ} {P : Inp → Prop} (hc : CostP D A p P) (h : p ≤ q) : CostP D A q P := Cost.mono hc h


lemma rel (hD : 1 < D) {p q : ℕ} {h1 h2 : Inp → ℕ} (r : ℕ → ℕ → Prop) (c1 : Cost D A p h1) (c2 : Cost D A q h2) :
    CostP D A (p + q + 1) fun x => r (h1 x) (h2 x) := by
  classical
  have := Cost.op (fun a b => if r a b then 1 else 0) c1 c2 (fun x => by split_ifs <;> omega)
  refine this.congr fun x => ?_
  by_cases h : r (h1 x) (h2 x)
  · rw [ind_true (P := fun x => r (h1 x) (h2 x)) h, if_pos h]
  · rw [ind_false (P := fun x => r (h1 x) (h2 x)) h, if_neg h]


lemma rel1 (hD : 1 < D) {p : ℕ} {h : Inp → ℕ} (r : ℕ → Prop) (c1 : Cost D A p h) :
    CostP D A (p + 2) fun x => r (h x) :=
  rel hD (fun a _ => r a) c1 (Cost.const 0 (by omega))

lemma true' (hD : 1 < D) : CostP D A 1 fun _ => True := by
  refine (Cost.const 1 hD).congr fun x => ?_
  rw [ind_true (P := fun _ => True) (x := x) trivial]

lemma false' (hD : 1 < D) : CostP D A 1 fun _ => False := by
  refine (Cost.const 0 (by omega)).congr fun x => ?_
  rw [ind_false (P := fun _ => False) (x := x) (fun h => h)]


lemma const (hD : 1 < D) (P : Prop) : CostP D A 1 fun _ => P := by
  by_cases h : P
  · exact (true' hD).congr fun _ => by simp [h]
  · exact (false' hD).congr fun _ => by simp [h]

lemma and (hD : 1 < D) {p q : ℕ} {P Q : Inp → Prop} (c1 : CostP D A p P) (c2 : CostP D A q Q) :
    CostP D A (p + q + 1) fun x => P x ∧ Q x := by
  refine (rel hD (fun a b => a = 1 ∧ b = 1) c1 c2).congr fun x => ?_
  by_cases h1 : P x <;> by_cases h2 : Q x <;> simp [ind, h1, h2]

lemma or (hD : 1 < D) {p q : ℕ} {P Q : Inp → Prop} (c1 : CostP D A p P) (c2 : CostP D A q Q) :
    CostP D A (p + q + 1) fun x => P x ∨ Q x := by
  refine (rel hD (fun a b => a = 1 ∨ b = 1) c1 c2).congr fun x => ?_
  by_cases h1 : P x <;> by_cases h2 : Q x <;> simp [ind, h1, h2]

lemma not (hD : 1 < D) {p : ℕ} {P : Inp → Prop} (c1 : CostP D A p P) :
    CostP D A (p + 2) fun x => ¬ P x := by
  refine (rel1 hD (fun a => a = 0) c1).congr fun x => ?_
  by_cases h1 : P x <;> simp [ind, h1]

lemma exists_mem (hD : 1 < D) {κ : Type*} (s : Finset κ) {c : ℕ} {P : κ → Inp → Prop}
    (hc : ∀ i ∈ s, CostP D A c (P i)) : CostP D A (s.card * (c + 1) + 1) fun x => ∃ i ∈ s, P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((false' hD).congr fun x => by simp).mono (by simp)
  | insert i s hi ih =>
    have h1 := ih fun j hj => hc j (mem_insert_of_mem hj)
    refine ((hc i (mem_insert_self _ _)).or hD h1 |>.congr fun x => by simp).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

lemma forall_mem (hD : 1 < D) {κ : Type*} (s : Finset κ) {c : ℕ} {P : κ → Inp → Prop}
    (hc : ∀ i ∈ s, CostP D A c (P i)) : CostP D A (s.card * (c + 1) + 1) fun x => ∀ i ∈ s, P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((true' hD).congr fun x => by simp).mono (by simp)
  | insert i s hi ih =>
    have h1 := ih fun j hj => hc j (mem_insert_of_mem hj)
    refine ((hc i (mem_insert_self _ _)).and hD h1 |>.congr fun x => by simp).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

end CostP


lemma Cost.ite {c p q : ℕ} {P : Inp → Prop} [DecidablePred P] {h1 h2 : Inp → ℕ}
    (c0 : CostP D A c P) (c1 : Cost D A p h1) (c2 : Cost D A q h2) (b1 : ∀ x, h1 x < D) (b2 : ∀ x, h2 x < D) :
    Cost D A (2 * c + p + q + 3) fun x => if P x then h1 x else h2 x := by
  have a1 := Cost.op (fun a b => a * b) c0 c1 (fun x => by
    have := ind_le P x
    have := b1 x
    nlinarith)
  have a2 := Cost.op (fun a b => (1 - a) * b) c0 c2 (fun x => by
    have := ind_le P x
    have := b2 x
    have : 1 - ind P x ≤ 1 := by omega
    nlinarith)
  have a3 := Cost.op (fun a b => a + b) a1 a2 (fun x => by
    have := b1 x
    have := b2 x
    by_cases h : P x
    · simp only [ind_true h]; omega
    · simp only [ind_false h]; omega)
  refine (a3.congr fun x => ?_).mono (by ring_nf; omega)
  by_cases h : P x
  · simp only [ind_true h, if_pos h]; omega
  · simp only [ind_false h, if_neg h]; omega

end Unc
end
/- Source module Paper.Tree. -/
section
namespace Paper
open Finset Nc Nc.G Nc.Tow Unc
open NS1 (lg)
section Start
variable {R : Type} [CommRing R] {AA A' E N U1 ℓ : ℕ} {S : Sys R (AA + A') E} {n : Fin AA → Fin AA → Fin (N + 1)}

theorem startTab_congr (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    {y y' : Uid AA N S.N U1 → UW ℓ} (h : ∀ b c k, y (.init b c k) = y' (.init b c k)) :
    startTab S U1 n tab p y = startTab S U1 n tab p y' := by
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · simp only [startTab, Fin.addCases_left, h]
  · simp only [startTab, Fin.addCases_right]

theorem startTab_ne_none (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    (y : Uid AA N S.N U1 → UW ℓ) (h : startTab S U1 n tab p y ≠ 0) :
    ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, Holds (hold0 S.np) (hold1 S.np) p id → y id ≠ none := by
  intro id hid hh
  rcases id with ⟨b, c, k⟩ | ⟨ν, k⟩
  swap
  · simp [seen0] at hid
  have hk : k.1 < (n b c).1 := by simpa [seen0] using hid
  revert h hh
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · intro h hh
    simp only [startTab, Fin.addCases_left] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    have ha : b = a ∨ c = a := by
      rcases hh with hh | hh
      · exact Or.inl (Fin.castAdd_injective _ _ hh).symm
      · exact Or.inr (Fin.castAdd_injective _ _ hh).symm
    exact hc ⟨⟨b, c, ⟨k.1, hk⟩⟩, ha⟩
  · intro h hh
    rcases hh with hh | hh <;> exact absurd (congrArg Fin.val hh) (by simp [hold0, hold1, cparty]; omega)

open Classical in
/-- The position with which the moves start has the value of the network. -/
theorem posVal_start (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) :
    posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = netValue tab := by
  have e0 : posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = ∑ z ∈ Common (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n),
        ∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p) := by
    have h1 := sum_contents_union (hold0 S.np) (hold1 S.np) (none : UW ℓ) ∅ (seen0 (N := S.N) (U1 := U1) n)
      (disjoint_empty_left _) (fun y => ∏ p, startTab S U1 n tab p (y p))
    rw [empty_union] at h1
    rw [posVal, h1]
    have h2 : Contents (hold0 S.np) (hold1 S.np) (none : UW ℓ) (∅ : Finset (Uid AA N S.N U1)) = {fun _ _ => none} := by
      ext y
      simp [Contents, funext_iff]
    rw [h2, Finset.sum_singleton]
  rw [e0]
  have hne : ∀ z, (∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p)) ≠ 0 →
      ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none := by
    intro z hz id hid
    have h1 : startTab S U1 n tab (hold0 S.np id) (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z
        (hold0 S.np id)) ≠ 0 := fun h => hz (Finset.prod_eq_zero (mem_univ _) h)
    have h2 := startTab_ne_none tab _ _ h1 id hid (Or.inl rfl)
    rwa [ext_self hid (Or.inl rfl)] at h2
  let un : NetUnit (fun a c => (n a c).1) → Uid AA N S.N U1 := fun u =>
    .init u.1 u.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1 u.2.1).2) u.2.2)
  have hun : ∀ u, un u ∈ seen0 (N := S.N) (U1 := U1) n := fun u => by
    simp [un, seen0]
  let W : (NetUnit (fun a c => (n a c).1) → Fin ℓ → Bool) → Uid AA N S.N U1 → UW ℓ := fun w id => match id with
    | .init a c k => if hk : k.1 < (n a c).1 then some (w ⟨a, c, ⟨k.1, hk⟩⟩) else none
    | .new _ _ => none
  have hW : ∀ w u, W w (un u) = some (w u) := by
    rintro w ⟨a, c, k⟩
    simp [W, un]
  rw [← Finset.sum_filter_of_ne (p := fun z => ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none) fun z _ hz => hne z hz]
  symm
  unfold netValue
  refine Finset.sum_bij' (fun w _ => W w) (fun z _ u => (z (un u)).getD fun _ => false) ?_ ?_ ?_ ?_ ?_
  · intro w _
    simp only [Finset.mem_filter, mem_common_iff]
    constructor
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dif_neg]
        simpa [seen0] using hid
      · rfl
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dif_pos (by simpa [seen0] using hid)]
        exact Option.some_ne_none _
      · simp [seen0] at hid
  · intro z _
    exact mem_univ _
  · intro w _
    funext u
    simp [hW]
  · intro z hz
    simp only [Finset.mem_filter, mem_common_iff] at hz
    funext id
    rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp only [W]
      split_ifs with hk
      · have h1 := hz.2 (.init a c k) (by simp [seen0, hk])
        have e : un ⟨a, c, ⟨k.1, hk⟩⟩ = .init a c k := rfl
        rw [e]
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h1
        rw [hv]
        rfl
      · exact (hz.1 _ (by simp [seen0, hk])).symm
    · exact (hz.1 _ (by simp [seen0])).symm
  · intro w _
    rw [Fin.prod_univ_add]
    have e2 : ∀ e : Fin A', startTab S U1 n tab (Fin.natAdd AA e)
        (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.natAdd AA e)) = 1 := fun e => by
      simp only [startTab, Fin.addCases_right]
    rw [Finset.prod_congr rfl (fun e _ => e2 e), Finset.prod_const_one, mul_one]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e3 : ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.castAdd A' a) (un u.1) = some (w u.1) := by
      rintro ⟨u, hu⟩
      rw [ext_self (hun u), hW]
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    simp only [startTab, Fin.addCases_left, un] at e3 ⊢
    simp [e3]

end Start
theorem lg_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ lg M := by
  unfold lg
  have := Nat.log_pos (b := 2) (n := M) (by norm_num) hM
  omega

/-- A constant times a power is a higher power. -/
theorem const_mul_pow_le {L : ℕ} (hL : 2 ≤ L) {k e C : ℕ} (h : k + e ≤ C) : k * L ^ e ≤ L ^ C := by
  calc k * L ^ e ≤ L ^ k * L ^ e :=
        Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hL k))
    _ = L ^ (k + e) := (pow_add _ _ _).symm
    _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) h

end Paper
end
/- Source module Nc.Dl.Facts. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open Finset Nc.Cut Nc.G

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

theorem sum_div_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℕ) : ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Nat.add_le_add_left ih _).trans Nat.div_add_div_le_add_div

theorem sum_length_cat {A : ℕ} (X : Fin A → List Γ) : ∑ b, (X b).length = (cat X).length := by
  rw [cat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rfl


theorem partyW_read_le {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}
    {p : Fin (K + K)} (h : partyW mu T q x p R C ≠ 0) : ∑ s, (cat (C s)).length ≤ T := by
  classical
  refine Fin.addCases (motive := fun p => partyW mu T q x p R C ≠ 0 → ∑ s, (cat (C s)).length ≤ T) ?_ ?_ p h
  · intro κ h
    rw [partyW_block] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans ?_ (blockW_sum_le h)
    let f : Option S → Ch S Unit := fun s => s.elim (.inp ()) fun s => .tp s true
    have hf : ∑ s, (cat (C s)).length = ∑ s, (vec R C (f s)).length := by
      refine Finset.sum_congr rfl fun s _ => ?_
      cases s <;> simp [f, vec]
    have inj : Function.Injective f := by
      intro s s' e
      cases s <;> cases s' <;> simp [f] at e ⊢
      exact e
    rw [hf, ← Finset.sum_image (f := fun z : Ch S Unit => (vec R C z).length) (s := univ) (g := f)
      fun s _ s' _ e => inj e]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro κ h
    rw [partyW_input] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [cat_nil_of (hc.2.1 s), List.length_nil]


theorem sum_ucount_le {A : ℕ} {X : Option S → Fin A → List Γ} (h : ∑ s, (cat (X s)).length ≤ T) :
    ∑ b, ucount ub (strOf cb fun s => X s b) ≤ (T + A * (Fintype.card S + 1)) * c / ub + A := by
  have e1 : ∀ b, ucount ub (strOf cb fun s => X s b) =
      (∑ s, (X s b).length + (Fintype.card S + 1)) * c / ub + 1 := by
    intro b
    rw [ucount, length_strOf]
  simp only [e1]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine Nat.add_le_add_right ((sum_div_le _ _ _).trans (Nat.div_le_div_right ?_)) _
  rw [← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [sum_length_cat, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_le_add_right h _


theorem init_count {N : Type} [Fintype N] [DecidableEq N] {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    (hx : ∀ κ, (x κ).length ≤ T) {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)}
    {y : G.Uid (K + K) U0 N U1 → UW ub} {R C : Option S → Fin (K + K) → List Γ} (h : G.InitOk ub cb ρ n p y R C)
    (hW : partyW mu T q x p R C ≠ 0) :
    ∑ b, (n p b + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  have h1 : ∑ b, n p b ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => ((h.2.1 b).1).symm]
    exact sum_ucount_le (partyW_sum_le hx hW)
  have h2 : ∑ b, n b p ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => ((h.2.2 b).1).symm]
    exact sum_ucount_le (partyW_read_le hW)
  rw [Finset.sum_add_distrib]
  omega

end Nc.Dl
end
/- Source module Paper.Runnet. -/
section
set_option linter.unusedSectionVars false

namespace Paper

open Finset













theorem lem_runnet {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (mu : Nc.Letter S Unit Γ → Matrix Q Q F) {T c ub K A' U0 U1 : ℕ}
    (cb : Option Γ → Fin c → Bool) {N : Type} [Fintype N] [DecidableEq N] (hcb : Function.Injective cb) (hc : 0 < c)
    (hub : 0 < ub) (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A')) (i e : Q)
    (u : Unit → List Γ) {ℓ : ℕ} (hℓ : ℓ ≤ T) (hu : (u ()).length ≤ K * ℓ) :
    open Classical in
    (Nc.runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K), if Nc.Cut.ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
          Nc.posVal (Nc.G.hold0 np) (Nc.G.hold1 np) (none : Nc.UW ub) (Nc.G.seen0 (N := N) (U1 := U1) n) (Nc.G.seen0 n)
            fun y => ∏ p : Fin (K + K), Nc.G.tabInit mu T cb q (Nc.Cut.parts ℓ (u ())) (fun s => ρ s p)
              (fun a b => (n a b).1) p (y (Fin.castAdd A' p))
      else 0
    else 0) ∧
    ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Nc.Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (p : Fin (K + K)) (y : Nc.G.Uid (K + K) U0 N U1 → Nc.UW ub),
      Nc.G.tabInit mu T cb q (Nc.Cut.parts ℓ (u ())) ρ (fun a b => (n a b).1) p y ≠ 0 →
        ∑ b, ((n p b).val + (n b p).val) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  classical
  refine ⟨Nc.G.start hcb hc hub hU np i e u hℓ hu, fun q ρ n p y h => ?_⟩
  rw [Nc.G.tabInit_eq] at h
  obtain ⟨R, -, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h4⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  split_ifs at h4 with h5
  · exact Nc.Dl.init_count (fun κ => (Nc.Cut.length_parts_le _ _ _).trans hℓ) h5 h4
  · exact absurd rfl h4

end Paper
end
/- Source module Nc.Tow.Slp0. -/
section
namespace Nc.Tow

open Finset Unc

variable {Inp ι : Type} {D Y : ℕ} {H H' : Set (Inp → ℕ)}


def CY (D : ℕ) (H : Set (Inp → ℕ)) (Y a : ℕ) (f : Inp → ℕ) : Prop := Cost D H (Y ^ a) f


def PY (D : ℕ) (H : Set (Inp → ℕ)) (Y a : ℕ) (P : Inp → Prop) : Prop := CostP D H (Y ^ a) P


structure Alph (D Y : ℕ) : Prop where
  three : 3 ≤ Y
  pow : Y ^ 4 ≤ D

namespace Alph

variable (h : Alph D Y)
include h

theorem pos : 0 < Y := by have := h.three; omega

theorem lt_of_le {n : ℕ} (hn : n ≤ Y) : n < D := by
  have h3 := h.three
  have h4 : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by omega)
  have := h.pow
  omega

theorem lt_of_le3 {n : ℕ} (hn : n ≤ 2 * Y ^ 3) : n < D := by
  have h3 := h.three
  have h4 : 2 * Y ^ 3 < Y ^ 4 := by
    have e : Y ^ 4 = Y * Y ^ 3 := by ring
    have hp : 0 < Y ^ 3 := Nat.pow_pos (by omega)
    rw [e]
    nlinarith
  have := h.pow
  omega

theorem one_lt : 1 < D := h.lt_of_le (by have := h.three; omega)

theorem zero_lt : 0 < D := by have := h.one_lt; omega

theorem pow_pos (a : ℕ) : 1 ≤ Y ^ a := Nat.one_le_pow _ _ h.pos

theorem step (a : ℕ) : 3 * Y ^ a ≤ Y ^ (a + 1) := by
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ h.three

theorem step2 (a : ℕ) : 9 * Y ^ a ≤ Y ^ (a + 2) := by
  have h1 := h.step a
  have h2 : 3 * Y ^ (a + 1) ≤ Y ^ (a + 2) := h.step (a + 1)
  omega

theorem sum_step {s a : ℕ} (hs : s ≤ Y) : s * (Y ^ a + 1) + 1 ≤ Y ^ (a + 2) := by
  have h1 := h.pow_pos a
  have h2 : 3 * Y ^ (a + 1) ≤ Y ^ (a + 2) := h.step (a + 1)
  have h3 : Y * Y ^ a = Y ^ (a + 1) := by ring
  have h4 : Y ≤ Y ^ (a + 1) := by
    rw [← h3]
    exact Nat.le_mul_of_pos_right Y (by omega)
  have h5 := h.pos
  have h6 : s * (Y ^ a + 1) ≤ Y * (Y ^ a + 1) := Nat.mul_le_mul_right _ hs
  have e1 : Y * (Y ^ a + 1) = Y ^ (a + 1) + Y := by ring
  rw [e1] at h6
  omega

end Alph

namespace CY

theorem base {f : Inp → ℕ} (hf : f ∈ H) (_hY : 0 < Y) : CY D H Y 0 f :=
  Cost.mono (Cost.base hf) (Nat.zero_le _)

theorem const (c : ℕ) (hc : c < D) : CY D H Y 0 fun _ => c := by
  unfold CY
  rw [pow_zero]
  exact Cost.const c hc

theorem mono {a b : ℕ} {f : Inp → ℕ} (hY : 0 < Y) (hf : CY D H Y a f) (hab : a ≤ b) : CY D H Y b f :=
  Cost.mono hf (Nat.pow_le_pow_right hY hab)

theorem congr {a : ℕ} {f g : Inp → ℕ} (hf : CY D H Y a f) (e : ∀ x, f x = g x) : CY D H Y a g := Cost.congr hf e

theorem weaken {a : ℕ} {f : Inp → ℕ} (hf : CY D H Y a f) (hH : H ⊆ H') : CY D H' Y a f := Cost.weaken hH hf

variable (hA : Alph D Y)
include hA

theorem op {a : ℕ} {f g : Inp → ℕ} (φ : ℕ → ℕ → ℕ) (hf : CY D H Y a f) (hg : CY D H Y a g)
    (hb : ∀ x, φ (f x) (g x) < D) : CY D H Y (a + 1) fun x => φ (f x) (g x) :=
  Cost.mono (Cost.op φ hf hg hb) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem op1 {a : ℕ} {f : Inp → ℕ} (φ : ℕ → ℕ) (hf : CY D H Y a f) (hb : ∀ x, φ (f x) < D) :
    CY D H Y (a + 1) fun x => φ (f x) :=
  Cost.mono (Cost.op1 hA.zero_lt φ hf hb) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem sum {κ : Type*} (s : Finset κ) {a : ℕ} {f : κ → Inp → ℕ} (hs : s.card ≤ Y)
    (hf : ∀ i ∈ s, CY D H Y a (f i)) (hb : ∀ x, ∑ i ∈ s, f i x < D) :
    CY D H Y (a + 2) fun x => ∑ i ∈ s, f i x :=
  Cost.mono (Cost.sum hA.zero_lt s hf hb) (hA.sum_step hs)

theorem ite {a : ℕ} {P : Inp → Prop} [DecidablePred P] {f g : Inp → ℕ} (hP : PY D H Y a P)
    (hf : CY D H Y a f) (hg : CY D H Y a g) (b1 : ∀ x, f x < D) (b2 : ∀ x, g x < D) :
    CY D H Y (a + 2) fun x => if P x then f x else g x :=
  Cost.mono (Cost.ite hP hf hg b1 b2) (by
    have := hA.step2 a
    have := hA.pow_pos a
    omega)

end CY

namespace PY

theorem base {P : Inp → Prop} (hP : ind P ∈ H) (hY : 0 < Y) : PY D H Y 0 P := CY.base hP hY

theorem mono {a b : ℕ} {P : Inp → Prop} (hY : 0 < Y) (hP : PY D H Y a P) (hab : a ≤ b) : PY D H Y b P :=
  CY.mono hY hP hab

theorem congr {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (e : ∀ x, P x ↔ Q x) : PY D H Y a Q :=
  CostP.congr hP e

variable (hA : Alph D Y)
include hA

theorem const (P : Prop) : PY D H Y 0 fun _ => P := by
  unfold PY
  rw [pow_zero]
  exact CostP.const hA.one_lt P

theorem rel {a : ℕ} {f g : Inp → ℕ} (r : ℕ → ℕ → Prop) (hf : CY D H Y a f) (hg : CY D H Y a g) :
    PY D H Y (a + 1) fun x => r (f x) (g x) :=
  CostP.mono (CostP.rel hA.one_lt r hf hg) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem rel1 {a : ℕ} {f : Inp → ℕ} (r : ℕ → Prop) (hf : CY D H Y a f) : PY D H Y (a + 1) fun x => r (f x) :=
  CostP.mono (CostP.rel1 hA.one_lt r hf) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem and {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (hQ : PY D H Y a Q) :
    PY D H Y (a + 1) fun x => P x ∧ Q x :=
  CostP.mono (CostP.and hA.one_lt hP hQ) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem or {a : ℕ} {P Q : Inp → Prop} (hP : PY D H Y a P) (hQ : PY D H Y a Q) :
    PY D H Y (a + 1) fun x => P x ∨ Q x :=
  CostP.mono (CostP.or hA.one_lt hP hQ) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem not {a : ℕ} {P : Inp → Prop} (hP : PY D H Y a P) : PY D H Y (a + 1) fun x => ¬ P x :=
  CostP.mono (CostP.not hA.one_lt hP) (by
    have := hA.step a
    have := hA.pow_pos a
    omega)

theorem exists_mem {κ : Type*} (s : Finset κ) {a : ℕ} {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∃ i ∈ s, P i x :=
  CostP.mono (CostP.exists_mem hA.one_lt s hP) (hA.sum_step hs)

theorem forall_mem {κ : Type*} (s : Finset κ) {a : ℕ} {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∀ i ∈ s, P i x :=
  CostP.mono (CostP.forall_mem hA.one_lt s hP) (hA.sum_step hs)

theorem forall_univ {κ : Type*} [Fintype κ] {a : ℕ} {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∀ i, P i x :=
  (forall_mem hA univ hs fun i _ => hP i).congr fun x => by simp

theorem exists_univ {κ : Type*} [Fintype κ] {a : ℕ} {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, PY D H Y a (P i)) : PY D H Y (a + 2) fun x => ∃ i, P i x :=
  (exists_mem hA univ hs fun i _ => hP i).congr fun x => by simp

omit hA in

theorem toCY {a : ℕ} {P : Inp → Prop} (hP : PY D H Y a P) : CY D H Y a (ind P) := hP

end PY

variable {inp : ι → Inp → Fin D}


def SY (inp : ι → Inp → Fin D) (Y p c : ℕ) (H : Set (Inp → ℕ)) : Prop := SlpN inp (p + c * Y ^ 12) H


theorem SY.add (hA : Alph D Y) {p c : ℕ} (h : SY inp Y p c H) {κ : Type*} [Fintype κ] (f : κ → Inp → ℕ) {a e : ℕ}
    (hκ : Fintype.card κ ≤ Y ^ e) (hf : ∀ i, CY D H Y a (f i)) (hae : a + e ≤ 12) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ ∀ i, f i ∈ H' := by
  refine ⟨H ∪ Set.range f, (SlpN.stage hA.zero_lt h f (Y ^ a) hf).le hA.zero_lt ?_, Set.subset_union_left,
    fun i => Or.inr ⟨i, rfl⟩⟩
  have h1 : Fintype.card κ * Y ^ a ≤ Y ^ 12 := by
    calc Fintype.card κ * Y ^ a ≤ Y ^ e * Y ^ a := Nat.mul_le_mul_right _ hκ
      _ = Y ^ (a + e) := by rw [← pow_add, add_comm]
      _ ≤ Y ^ 12 := Nat.pow_le_pow_right hA.pos hae
  have e2 : (c + 1) * Y ^ 12 = c * Y ^ 12 + Y ^ 12 := by ring
  rw [e2]
  omega

theorem SY.le (hA : Alph D Y) {p c c' : ℕ} (h : SY inp Y p c H) (hc : c ≤ c') : SY inp Y p c' H :=
  SlpN.le hA.zero_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _) h

end Nc.Tow
end
/- Source module Paper.Heavy. -/
section
set_option linter.unusedSectionVars false

namespace Paper

open Finset


structure Staged (P : ℕ) where
  
  par : Fin P → Fin P
  
  stage : Fin P → ℕ
  
  depth : ℕ
  
  root : Fin P
  stage_le : ∀ p, stage p ≤ depth
  stage_root : ∀ p, stage p = depth ↔ p = root
  stage_par : ∀ p, p ≠ root → stage (par p) = stage p + 1

namespace Staged

variable {P : ℕ} (T : Staged P)


def nxt (p : Fin P) : Fin P := if p = T.root then p else T.par p


def Below (q p : Fin P) : Prop := T.stage q ≤ T.stage p ∧ T.nxt^[T.stage p - T.stage q] q = p

open Classical in

noncomputable def below (f : Fin P → ℕ) (p : Fin P) : ℕ := ∑ q, if T.Below q p then f q else 0


def kids (f : Fin P → ℕ) (p : Fin P) : ℕ := ∑ q ∈ univ.filter (fun q => q ≠ T.root ∧ T.par q = p), f q

variable (giv u : Fin P → ℕ) (M Y k : ℕ)


def Heavy (p : Fin P) : Prop :=
  p = T.root ∨ 8 * M * Y < k * (T.below giv p * (2 * Y) + T.below u p * (4 * M))


def Head (p : Fin P) : Prop := p = T.root ∨ T.Heavy giv u M Y k (T.par p)

open Classical in

noncomputable def top : ℕ → Fin P → Fin P
  | 0, p => p
  | d + 1, p => if T.Head giv u M Y k p then p else top d (T.par p)


noncomputable def hd (p : Fin P) : Fin P := T.top giv u M Y k (T.depth - T.stage p) p

open Classical in

noncomputable def rank (p : Fin P) : ℕ := (univ.filter fun q => T.Head giv u M Y k q ∧ q < p).card


noncomputable def piece (p : Fin P) : ℕ := T.rank giv u M Y k (T.hd giv u M Y k p)

variable {T giv u M Y k}

theorem below_refl (p : Fin P) : T.Below p p := ⟨le_rfl, by rw [Nat.sub_self]; rfl⟩

theorem stage_lt {p : Fin P} (hp : p ≠ T.root) : T.stage p < T.depth :=
  lt_of_le_of_ne (T.stage_le p) fun e => hp ((T.stage_root p).1 e)

theorem below_up {q p : Fin P} (h : T.Below q p) (hp : p ≠ T.root) : T.Below q (T.par p) := by
  refine ⟨by rw [T.stage_par p hp]; exact Nat.le_succ_of_le h.1, ?_⟩
  rw [T.stage_par p hp, Nat.succ_sub h.1, Function.iterate_succ_apply', h.2, nxt, if_neg hp]

theorem below_down {q p : Fin P} (hq : q ≠ T.root) (h : T.Below (T.par q) p) : T.Below q p := by
  have h1 := h.1
  have h2 := h.2
  rw [T.stage_par q hq] at h1 h2
  refine ⟨by omega, ?_⟩
  have e : T.stage p - T.stage q = T.stage p - (T.stage q + 1) + 1 := by omega
  rw [e, Function.iterate_succ_apply]
  rwa [show T.nxt q = T.par q from if_neg hq]

open Classical in
theorem below_mono (f : Fin P → ℕ) {p : Fin P} (hp : p ≠ T.root) : T.below f p ≤ T.below f (T.par p) :=
  Finset.sum_le_sum fun q _ => by
    by_cases h : T.Below q p
    · rw [if_pos h, if_pos (below_up h hp)]
    · rw [if_neg h]
      exact Nat.zero_le _

open Classical in

theorem below_stage (f : Fin P → ℕ) (s : ℕ) :
    ∑ p ∈ univ.filter (fun p => T.stage p = s), T.below f p ≤ ∑ q, f q := by
  unfold below
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  refine le_trans (Nat.mul_le_mul_right _ (card_le_one.2 fun p hp p' hp' => ?_)) (le_of_eq (one_mul _))
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  obtain ⟨h1', h2'⟩ := mem_filter.1 hp'
  rw [← h2.2, ← h2'.2, (mem_filter.1 h1).2, (mem_filter.1 h1').2]

open Classical in
theorem below_kids (f : Fin P → ℕ) (p : Fin P) : T.below (T.kids f) p ≤ T.below f p := by
  have h1 : T.below (T.kids f) p = ∑ q ∈ univ.filter (fun q => q ≠ T.root), if T.Below (T.par q) p then f q else 0 := by
    have h2 : ∀ a, (if T.Below a p then T.kids f a else 0) =
        ∑ q ∈ univ.filter (fun q => q ≠ T.root), if T.par q = a then (if T.Below a p then f q else 0) else 0 := by
      intro a
      unfold kids
      rw [← Finset.sum_filter, Finset.filter_filter]
      split_ifs
      · rfl
      · simp
    unfold below
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq, if_pos (mem_univ _)]
  rw [h1]
  refine (Finset.sum_le_sum fun q hq => ?_).trans (Finset.sum_le_sum_of_subset (subset_univ _))
  by_cases h : T.Below (T.par q) p
  · rw [if_pos h, if_pos (below_down (mem_filter.1 hq).2 h)]
  · rw [if_neg h]
    exact Nat.zero_le _

open Classical in

theorem _root_.Paper.prop_pieces_heavy_few (hk : 0 < k) (hM : 0 < M) (hY : 0 < Y) (hg : ∑ q, giv q ≤ M) (hu : ∑ q, u q ≤ Y)
    {s : ℕ} (hs : s < T.depth) :
    (univ.filter fun p => T.stage p = s ∧ T.Heavy giv u M Y k p).card < k := by
  by_contra hcon
  push Not at hcon
  set S := univ.filter fun p => T.stage p = s ∧ T.Heavy giv u M Y k p
  have hw : ∀ p ∈ S, 8 * M * Y + 1 ≤ k * (T.below giv p * (2 * Y) + T.below u p * (4 * M)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
    rcases h2 with h2 | h2
    · rw [(T.stage_root p).2 h2] at h1
      omega
    · exact h2
  have h3 : ∑ p ∈ S, (T.below giv p * (2 * Y) + T.below u p * (4 * M)) ≤ M * (2 * Y) + Y * (4 * M) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have hsub : S ⊆ univ.filter fun p => T.stage p = s := fun p hp => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2.1⟩
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (((Finset.sum_le_sum_of_subset hsub).trans (below_stage _ s)).trans hg))
      (Nat.mul_le_mul_right _ (((Finset.sum_le_sum_of_subset hsub).trans (below_stage _ s)).trans hu))
  have h4 : k * (8 * M * Y + 1) ≤ k * (M * (2 * Y) + Y * (4 * M)) := by
    refine le_trans (Nat.mul_le_mul_right _ hcon) ?_
    calc S.card * (8 * M * Y + 1) = ∑ _p ∈ S, (8 * M * Y + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ S, k * (T.below giv p * (2 * Y) + T.below u p * (4 * M)) := Finset.sum_le_sum hw
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ h3
  have h5 := Nat.le_of_mul_le_mul_left h4 hk
  nlinarith


theorem _root_.Paper.prop_pieces_heavy_up {p : Fin P} (hp : p ≠ T.root) (h : T.Heavy giv u M Y k p) :
    T.Heavy giv u M Y k (T.par p) := by
  refine Or.inr (lt_of_lt_of_le (h.resolve_left hp) (Nat.mul_le_mul_left _ ?_))
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (below_mono _ hp)) (Nat.mul_le_mul_right _ (below_mono _ hp))

theorem head_of_heavy {p : Fin P} (h : T.Heavy giv u M Y k p) : T.Head giv u M Y k p := by
  by_cases hp : p = T.root
  · exact Or.inl hp
  · exact Or.inr (prop_pieces_heavy_up hp h)

theorem top_spec : ∀ d p, T.stage p + d = T.depth → T.Head giv u M Y k (T.top giv u M Y k d p) ∧
    T.Below p (T.top giv u M Y k d p) ∧
    (T.top giv u M Y k d p = p ∨ ¬ T.Heavy giv u M Y k (T.top giv u M Y k d p)) := by
  intro d
  induction d with
  | zero => exact fun p hp => ⟨Or.inl ((T.stage_root p).1 hp), below_refl p, Or.inl rfl⟩
  | succ d ih =>
    intro p hp
    rw [top]
    by_cases h : T.Head giv u M Y k p
    · rw [if_pos h]
      exact ⟨h, below_refl p, Or.inl rfl⟩
    · rw [if_neg h]
      have hr : p ≠ T.root := fun e => h (Or.inl e)
      obtain ⟨a1, a2, a3⟩ := ih (T.par p) (by rw [T.stage_par p hr]; omega)
      refine ⟨a1, below_down hr a2, Or.inr ?_⟩
      rcases a3 with a3 | a3
      · rw [a3]
        exact fun e => h (Or.inr e)
      · exact a3

theorem hd_spec (p : Fin P) : T.Head giv u M Y k (T.hd giv u M Y k p) ∧ T.Below p (T.hd giv u M Y k p) ∧
    (T.hd giv u M Y k p = p ∨ ¬ T.Heavy giv u M Y k (T.hd giv u M Y k p)) :=
  top_spec _ p (by have := T.stage_le p; omega)

theorem hd_head {p : Fin P} (h : T.Head giv u M Y k p) : T.hd giv u M Y k p = p := by
  unfold hd
  generalize T.depth - T.stage p = d
  cases d with
  | zero => rfl
  | succ d => rw [top, if_pos h]

theorem hd_par {p : Fin P} (h : ¬ T.Head giv u M Y k p) : T.hd giv u M Y k p = T.hd giv u M Y k (T.par p) := by
  have hr : p ≠ T.root := fun e => h (Or.inl e)
  unfold hd
  have hlt := stage_lt hr
  rw [T.stage_par p hr, show T.depth - T.stage p = T.depth - (T.stage p + 1) + 1 by omega, top, if_neg h]

theorem rank_inj {p q : Fin P} (hp : T.Head giv u M Y k p) (hq : T.Head giv u M Y k q)
    (e : T.rank giv u M Y k p = T.rank giv u M Y k q) : p = q := by
  classical
  have key : ∀ {x y : Fin P}, T.Head giv u M Y k x → x < y → T.rank giv u M Y k x < T.rank giv u M Y k y := by
    intro x y hx hxy
    refine card_lt_card ((ssubset_iff_of_subset ?_).2
      ⟨x, mem_filter.2 ⟨mem_univ _, hx, hxy⟩, fun hc => lt_irrefl _ (mem_filter.1 hc).2.2⟩)
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hz
    exact mem_filter.2 ⟨h1, h2, h3.trans hxy⟩
  rcases lt_trichotomy p q with h | h | h
  · have := key hp h
    omega
  · exact h
  · have := key hq h
    omega

theorem piece_hd {p q : Fin P} (e : T.piece giv u M Y k p = T.piece giv u M Y k q) :
    T.hd giv u M Y k p = T.hd giv u M Y k q := rank_inj (hd_spec p).1 (hd_spec q).1 e

theorem piece_head {p : Fin P} (h : T.Head giv u M Y k p) : T.piece giv u M Y k p = T.rank giv u M Y k p := by
  rw [piece, hd_head h]

theorem below_subtree {x : Fin P} (hx : ¬ T.Heavy giv u M Y k x) :
    ∀ d p, T.Below p x → T.stage x = T.stage p + d → T.hd giv u M Y k p = T.hd giv u M Y k x := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    obtain ⟨-, h2⟩ := hp
    rw [Nat.add_zero] at hd
    rw [hd, Nat.sub_self] at h2
    rw [show p = x from h2]
  | succ d ih =>
    intro p hp hd
    have hr : p ≠ T.root := fun e => by
      have h1 := (T.stage_root p).2 e
      have h2 := T.stage_le x
      omega
    have hpar : T.Below (T.par p) x := by
      obtain ⟨-, h2⟩ := hp
      refine ⟨by rw [T.stage_par p hr]; omega, ?_⟩
      rw [show T.stage x - T.stage p = d + 1 by omega, Function.iterate_succ_apply,
        show T.nxt p = T.par p from if_neg hr] at h2
      rw [T.stage_par p hr, show T.stage x - (T.stage p + 1) = d by omega]
      exact h2
    have hnh : ∀ e q, T.Below q x → T.stage x = T.stage q + e → ¬ T.Heavy giv u M Y k q := by
      intro e
      induction e with
      | zero =>
        intro q hq he
        obtain ⟨-, h2⟩ := hq
        rw [Nat.add_zero] at he
        rw [he, Nat.sub_self] at h2
        rwa [show q = x from h2]
      | succ e ih' =>
        intro q hq he hh
        have hq' : q ≠ T.root := fun e' => by
          have h1 := (T.stage_root q).2 e'
          have h2 := T.stage_le x
          omega
        refine ih' (T.par q) ?_ (by rw [T.stage_par q hq']; omega) (prop_pieces_heavy_up hq' hh)
        obtain ⟨-, h2⟩ := hq
        refine ⟨by rw [T.stage_par q hq']; omega, ?_⟩
        rw [show T.stage x - T.stage q = e + 1 by omega, Function.iterate_succ_apply,
          show T.nxt q = T.par q from if_neg hq'] at h2
        rw [T.stage_par q hq', show T.stage x - (T.stage q + 1) = e by omega]
        exact h2
    have hp' : ¬ T.Head giv u M Y k p := fun e =>
      hnh d (T.par p) hpar (by rw [T.stage_par p hr]; omega) (e.resolve_left hr)
    rw [hd_par hp']
    exact ih (T.par p) hpar (by rw [T.stage_par p hr]; omega)

open Classical in


theorem _root_.Paper.prop_pieces_shape (g : ℕ) (hne : ∃ p, T.piece giv u M Y k p = g) :
    ∃ x, (T.Heavy giv u M Y k x ∧ ∀ p, T.piece giv u M Y k p = g ↔ p = x) ∨
      (¬ T.Heavy giv u M Y k x ∧ T.Heavy giv u M Y k (T.par x) ∧ ∀ p, T.piece giv u M Y k p = g ↔ T.Below p x) := by
  obtain ⟨p0, hp0⟩ := hne
  have hs := hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p0
  have hx : T.piece giv u M Y k (T.hd giv u M Y k p0) = g := by rw [piece_head hs.1]; exact hp0
  refine ⟨T.hd giv u M Y k p0, ?_⟩
  have he : ∀ p, T.piece giv u M Y k p = g → T.hd giv u M Y k p = T.hd giv u M Y k p0 :=
    fun p hp => piece_hd (hp.trans hp0.symm)
  by_cases hh : T.Heavy giv u M Y k (T.hd giv u M Y k p0)
  · refine Or.inl ⟨hh, fun p => ⟨fun hp => ?_, fun e => e ▸ hx⟩⟩
    rcases (hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p).2.2 with h | h
    · exact h.symm.trans (he p hp)
    · exact absurd (he p hp ▸ hh) h
  · refine Or.inr ⟨hh, hs.1.resolve_left fun e => hh (Or.inl e), fun p => ⟨fun hp => he p hp ▸ (hd_spec p).2.1, fun hp => ?_⟩⟩
    rw [piece, below_subtree hh (T.stage (T.hd giv u M Y k p0) - T.stage p) p hp (by have := hp.1; omega)]
    exact hx

open Classical in

theorem piece_sum_le (f : Fin P → ℕ) (B : ℕ) (hB : ∀ p, f p ≤ B)
    (hl : ∀ x, ¬ T.Heavy giv u M Y k x → T.below f x ≤ B) (g : ℕ) :
    ∑ p ∈ univ.filter (fun p => T.piece giv u M Y k p = g), f p ≤ B := by
  by_cases hne : ∃ p, T.piece giv u M Y k p = g
  · obtain ⟨x, ⟨-, h⟩ | ⟨hx, -, h⟩⟩ := prop_pieces_shape g hne
    · refine (Finset.sum_le_sum_of_subset (t := {x}) fun p hp => mem_singleton.2 ((h p).1 (mem_filter.1 hp).2)).trans ?_
      rw [Finset.sum_singleton]
      exact hB x
    · refine le_trans ?_ (hl x hx)
      unfold below
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset fun p hp => mem_filter.2 ⟨mem_univ _, (h p).1 (mem_filter.1 hp).2⟩
  · rw [Finset.filter_false_of_mem fun p _ hp => hne ⟨p, hp⟩, Finset.sum_empty]
    exact Nat.zero_le _

theorem light_le {x : Fin P} (hM : 0 < M) (hY : 0 < Y) (hx : ¬ T.Heavy giv u M Y k x) :
    k * T.below giv x ≤ 4 * M ∧ k * T.below u x ≤ 2 * Y := by
  have h : k * (T.below giv x * (2 * Y) + T.below u x * (4 * M)) ≤ 8 * M * Y := not_lt.1 fun h => hx (Or.inr h)
  have h1 : k * T.below giv x * (2 * Y) ≤ 4 * M * (2 * Y) := by linarith [Nat.zero_le (k * (T.below u x * (4 * M))), mul_add k (T.below giv x * (2 * Y)) (T.below u x * (4 * M)), mul_assoc k (T.below giv x) (2 * Y)]
  have h2 : k * T.below u x * (4 * M) ≤ 2 * Y * (4 * M) := by linarith [Nat.zero_le (k * (T.below giv x * (2 * Y))), mul_add k (T.below giv x * (2 * Y)) (T.below u x * (4 * M)), mul_assoc k (T.below u x) (4 * M)]
  exact ⟨Nat.le_of_mul_le_mul_right h1 (by omega), Nat.le_of_mul_le_mul_right h2 (by omega)⟩


theorem piece_boundary (g : ℕ) : ∃ x, ∀ q, q ≠ T.root →
    ¬ (T.piece giv u M Y k q = g ↔ T.piece giv u M Y k (T.par q) = g) → q = x ∨ T.par q = x := by
  have hb : ∀ q, q ≠ T.root → ¬ (T.piece giv u M Y k q = g ↔ T.piece giv u M Y k (T.par q) = g) →
      ∃ y, T.Head giv u M Y k y ∧ T.rank giv u M Y k y = g ∧ (q = y ∨ T.par q = y) := by
    intro q hr hne
    have hh : T.Head giv u M Y k q := by
      by_contra h
      exact hne (by rw [piece, hd_par h]; rfl)
    have hp : T.Head giv u M Y k (T.par q) := head_of_heavy (hh.resolve_left hr)
    by_cases h1 : T.piece giv u M Y k q = g
    · exact ⟨q, hh, (piece_head hh).symm.trans h1, Or.inl rfl⟩
    · refine ⟨T.par q, hp, (piece_head hp).symm.trans ?_, Or.inr rfl⟩
      by_contra h2
      exact hne ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  by_cases hex : ∃ y, T.Head giv u M Y k y ∧ T.rank giv u M Y k y = g
  · obtain ⟨x, hx, hx2⟩ := hex
    refine ⟨x, fun q hr hne => ?_⟩
    obtain ⟨y, hy, hy2, hy3⟩ := hb q hr hne
    rwa [rank_inj hx hy (hx2.trans hy2.symm)]
  · refine ⟨T.root, fun q hr hne => ?_⟩
    obtain ⟨y, hy, hy2, -⟩ := hb q hr hne
    exact absurd ⟨y, hy, hy2⟩ hex

open Classical in

theorem _root_.Paper.prop_pieces_count {b C : ℕ} (hk : 0 < k) (hM : 0 < M) (hY : 0 < Y) (hg : ∑ q, giv q ≤ M)
    (hu : ∑ q, u q ≤ Y) (hb : ∀ p, p ≠ T.root → (univ.filter fun q => q ≠ T.root ∧ T.par q = p).card ≤ b)
    (hC : (univ.filter fun q => q ≠ T.root ∧ T.par q = T.root).card ≤ C) (p : Fin P) :
    T.piece giv u M Y k p < 1 + C + b * (T.depth * k) := by
  have hall : (univ.filter fun q => T.Head giv u M Y k q).card ≤ 1 + C + b * (T.depth * k) := by
    have hsub : (univ.filter fun q => T.Head giv u M Y k q) ⊆ ({T.root} ∪
        univ.filter fun q => q ≠ T.root ∧ T.par q = T.root) ∪
        ((range T.depth).biUnion fun s => univ.filter fun y => T.stage y = s ∧ T.Heavy giv u M Y k y).biUnion
          fun y => univ.filter fun q => q ≠ T.root ∧ T.par q = y := by
      intro q hq
      have hq := (mem_filter.1 hq).2
      by_cases h1 : q = T.root
      · exact mem_union_left _ (mem_union_left _ (mem_singleton.2 h1))
      by_cases h2 : T.par q = T.root
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨mem_univ _, h1, h2⟩))
      exact mem_union_right _ (mem_biUnion.2 ⟨T.par q, mem_biUnion.2 ⟨T.stage (T.par q),
        mem_range.2 (stage_lt h2), mem_filter.2 ⟨mem_univ _, rfl, hq.resolve_left h1⟩⟩,
        mem_filter.2 ⟨mem_univ _, h1, rfl⟩⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add
      ((card_union_le _ _).trans (Nat.add_le_add (by rw [card_singleton]) hC)) ?_))
    refine card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum (g := fun _ => b) fun y hy => hb y fun e => ?_).trans ?_
    · obtain ⟨s, hs, hy⟩ := mem_biUnion.1 hy
      have := mem_range.1 hs
      have := (mem_filter.1 hy).2.1
      rw [(T.stage_root y).2 e] at this
      omega
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    refine Nat.mul_le_mul_left _ (card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum (g := fun _ => k) fun s hs =>
      (prop_pieces_heavy_few hk hM hY hg hu (mem_range.1 hs)).le).trans (le_of_eq ?_)
    simp
  refine lt_of_lt_of_le ?_ hall
  unfold piece rank
  exact card_lt_card ((ssubset_iff_of_subset fun q hq => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hq).2.1⟩).2
    ⟨T.hd giv u M Y k p, mem_filter.2 ⟨mem_univ _, (hd_spec p).1⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩)

theorem piece_lt (p : Fin P) : T.piece giv u M Y k p < P := by
  classical
  have h := (hd_spec (T := T) (giv := giv) (u := u) (M := M) (Y := Y) (k := k) p).1
  unfold piece rank
  calc _ < (univ.filter fun q => T.Head giv u M Y k q).card :=
        card_lt_card ((ssubset_iff_of_subset fun q hq => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hq).2.1⟩).2
          ⟨_, mem_filter.2 ⟨mem_univ _, h⟩, fun h => lt_irrefl _ (mem_filter.1 h).2.2⟩)
    _ ≤ P := (card_le_univ _).trans (le_of_eq (Fintype.card_fin P))

end Staged

end Paper
end
/- Source module Paper.HeavyProg. -/
section
set_option linter.unusedSectionVars false

namespace Paper

open Finset Unc Nc.Tow Nc.Cut


theorem slp_cast {Inp ι : Type} {D D' p : ℕ} {inp : ι → Inp → Fin D} {inp' : ι → Inp → Fin D'} {H : Set (Inp → ℕ)}
    (hD : D ≤ D') (hinp : ∀ i x, (inp' i x : ℕ) = inp i x) (h : SlpN inp p H) : SlpN inp' p H := by
  obtain ⟨fn, h1, h2⟩ := h
  let cast : Fin D → Fin D' := fun a => ⟨a.1, lt_of_lt_of_le a.2 hD⟩
  refine ⟨fun k x => cast (fn k x), fun k hk => ?_, fun f hf => ?_⟩
  · rcases h1 k hk with ⟨i, e⟩ | ⟨c, e⟩ | ⟨i, hi, j, hj, φ, e⟩
    · exact Or.inl ⟨i, funext fun x => Fin.ext (by rw [hinp]; simp [cast, e])⟩
    · exact Or.inr (Or.inl ⟨cast c, funext fun x => by simp [e]⟩)
    · refine Or.inr (Or.inr ⟨i, hi, j, hj, fun a b => if ha : a.1 < D then
        (if hb : b.1 < D then cast (φ ⟨a, ha⟩ ⟨b, hb⟩) else a) else a, fun x => ?_⟩)
      simp only []
      rw [dif_pos (show (cast (fn i x)).1 < D from (fn i x).2), dif_pos (show (cast (fn j x)).1 < D from (fn j x).2)]
      exact congrArg cast (e x)
  · obtain ⟨k, hk, e⟩ := h2 f hf
    exact ⟨k, hk, e⟩

namespace Staged

variable {Inp ι : Type} {D Y : ℕ} {inp : ι → Inp → Fin D} {p c : ℕ} {H : Set (Inp → ℕ)} {P : ℕ}
  {T : Inp → Staged P} {st : Fin P → ℕ} {dp : ℕ} {rt : Fin P}
  (hst : ∀ x, (T x).stage = st) (hdp : ∀ x, (T x).depth = dp) (hrt : ∀ x, (T x).root = rt)
  (hA : Alph D Y) (hP : P ≤ Y)
include hst hdp hrt hA hP

omit hst hdp in

theorem anc_stage (hS : SY inp Y p c H) (hpar : ∀ q q', ind (fun x => (T x).par q = q') ∈ H) (t : ℕ) :
    ∃ H', SY inp Y p (c + t) H' ∧ H ⊆ H' ∧ ∀ j < t, ∀ q q', ind (fun x => (T x).nxt^[j] q = q') ∈ H' := by
  classical
  induction t with
  | zero => exact ⟨H, hS, subset_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    have hY := hA.pos
    have hκ : Fintype.card (Fin P × Fin P) ≤ Y ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fin, pow_two]
      exact Nat.mul_le_mul hP hP
    obtain ⟨H1, s1, u1, f1⟩ := s0.add hA (fun q : Fin P × Fin P => ind fun x => (T x).nxt^[t] q.1 = q.2) (a := 3) (e := 2)
      hκ (fun q => by
        cases t with
        | zero => exact (((PY.const hA (q.1 = q.2)).congr fun x => Iff.rfl).toCY).mono hY (Nat.zero_le 3)
        | succ t =>
          have h1 : PY D H0 Y 3 fun x => ∃ q', (T x).nxt^[t] q.1 = q' ∧ (T x).nxt q' = q.2 :=
            PY.exists_univ hA (by simpa using hP) fun q' => PY.and hA (PY.base (f0 t (Nat.lt_succ_self t) q.1 q') hY) (by
              by_cases h : q' = rt
              · refine (PY.const hA (q' = q.2)).congr fun x => ?_
                unfold nxt
                rw [if_pos (h.trans (hrt x).symm)]
              · refine (PY.base (u0 (hpar q' q.2)) hY).congr fun x => ?_
                unfold nxt
                rw [if_neg fun e => h (e.trans (hrt x))])
          refine (h1.congr fun x => ?_).toCY
          rw [Function.iterate_succ_apply']
          exact ⟨fun ⟨q', e, e'⟩ => e ▸ e', fun e => ⟨_, rfl, e⟩⟩) (by omega)
    refine ⟨H1, s1, u0.trans u1, fun j hj q q' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact u1 (f0 j hj q q')
    · exact f1 (q, q')

variable {giv : Fin P → ℕ} {u : Inp → Fin P → ℕ} {M Yh k : ℕ}

open Classical in

theorem piece_prog (hS : SY inp Y p c H) (hpar : ∀ q q', ind (fun x => (T x).par q = q') ∈ H)
    (hu : ∀ q, (fun x => u x q) ∈ H) (hgiv : ∀ q, giv q ≤ 1) (hub : ∀ x q, u x q ≤ Y) :
    ∃ H', SY inp Y p (c + 2 * dp + 9) H' ∧ H ⊆ H' ∧
      ∀ q, (fun x => (T x).piece giv (u x) M Yh k q) ∈ H' := by
  have hY := hA.pos
  have hPc : Fintype.card (Fin P) ≤ Y ^ 1 := by rwa [Fintype.card_fin, pow_one]
  have hPP : Fintype.card (Fin P × Fin P) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hP hP
  have hsum : ∀ (f : Fin P → ℕ), (∀ q, f q ≤ Y) → ∑ q, f q < D := fun f hf => by
    refine hA.lt_of_le3 ?_
    calc ∑ q, f q ≤ ∑ _q : Fin P, Y := Finset.sum_le_sum fun q _ => hf q
      _ = P * Y := by simp
      _ ≤ Y * Y := Nat.mul_le_mul_right _ hP
      _ ≤ 2 * Y ^ 3 := by
          have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
          rw [pow_two] at this
          omega
  obtain ⟨H1, s1, u1, f1⟩ := anc_stage hrt hA hP hS hpar (dp + 1)
  -- below
  have hB : ∀ q q', PY D H1 Y 0 fun x => (T x).Below q q' := fun q q' => by
    by_cases h : st q ≤ st q'
    · have h1 : st q' - st q < dp + 1 ∨ ∀ x : Inp, False := by
        by_cases hne : Nonempty Inp
        · obtain ⟨x⟩ := hne
          left
          have := (T x).stage_le q'
          rw [hst, hdp] at this
          omega
        · exact Or.inr fun x => hne ⟨x⟩
      rcases h1 with h1 | h1
      · refine (PY.base (f1 _ h1 q q') hY).congr fun x => ?_
        unfold Below
        rw [hst]
        exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
      · exact (PY.const hA True).congr fun x => (h1 x).elim
    · refine (PY.const hA False).congr fun x => ⟨False.elim, fun e => h ?_⟩
      rw [← hst x]
      exact e.1
  have hbel : ∀ f : Inp → Fin P → ℕ, (∀ q, CY D H1 Y 0 fun x => f x q) → (∀ x q, f x q ≤ Y) →
      ∀ q', CY D H1 Y 3 fun x => (T x).below (f x) q' := by
    intro f hf hf' q'
    have e : ∀ x, (T x).below (f x) q' = ∑ q ∈ univ, ind (fun x => (T x).Below q q') x * f x q := fun x => by
      unfold below
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : (T x).Below q q'
      · rw [if_pos h, ind_true (P := fun x => (T x).Below q q') h, one_mul]
      · rw [if_neg h, ind_false (P := fun x => (T x).Below q q') h, zero_mul]
    refine CY.congr ?_ fun x => (e x).symm
    have hle : ∀ x q, ind (fun x => (T x).Below q q') x * f x q ≤ Y := fun x q =>
      (Nat.mul_le_mul (ind_le _ _) (hf' x q)).trans (le_of_eq (one_mul _))
    exact CY.sum hA univ (by simpa using hP)
      (fun q _ => CY.op hA (fun a b => a * b) (hB q q').toCY (hf q) fun x => hA.lt_of_le (hle x q))
      fun x => hsum _ (hle x)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (fun q x => (T x).below giv q) (a := 3) (e := 1) hPc
    (hbel (fun _ => giv) (fun q => CY.const _ (hA.lt_of_le ((hgiv q).trans hY))) fun x q => (hgiv q).trans hY) (by omega)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (fun q x => (T x).below (u x) q) (a := 3) (e := 1) hPc
    (fun q => (hbel u (fun q => CY.base (u1 (hu q)) hY) hub q).weaken u2) (by omega)
  -- heavy and heads
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (fun q => ind fun x => (T x).Heavy giv (u x) M Yh k q) (a := 1) (e := 1) hPc
    (fun q => by
      by_cases h : q = rt
      · exact ((((PY.const hA True).congr fun x => ⟨fun _ => Or.inl (h.trans (hrt x).symm), fun _ => trivial⟩)).toCY).mono hY
          (Nat.zero_le 1)
      · refine ((PY.rel hA (fun a b => 8 * M * Yh < k * (a * (2 * Yh) + b * (4 * M))) (CY.base (u3 (f2 q)) hY)
          (CY.base (f3 q) hY)).congr fun x => ?_).toCY
        exact ⟨Or.inr, fun e => e.resolve_left fun e => h (e.trans (hrt x))⟩) (by omega)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (fun q => ind fun x => (T x).Head giv (u x) M Yh k q) (a := 3) (e := 1) hPc
    (fun q => by
      by_cases h : q = rt
      · exact ((((PY.const hA True).congr fun x => ⟨fun _ => Or.inl (h.trans (hrt x).symm), fun _ => trivial⟩)).toCY).mono hY
          (Nat.zero_le 3)
      · have h1 : PY D H4 Y 3 fun x => ∃ q', (T x).par q = q' ∧ (T x).Heavy giv (u x) M Yh k q' :=
          PY.exists_univ hA (by simpa using hP) fun q' =>
            PY.and hA (PY.base (u4 (u3 (u2 (u1 (hpar q q'))))) hY) (PY.base (f4 q') hY)
        refine (h1.congr fun x => ?_).toCY
        exact ⟨fun ⟨q', e, e'⟩ => Or.inr (e ▸ e'),
          fun e => ⟨_, rfl, e.resolve_left fun e => h (e.trans (hrt x))⟩⟩) (by omega)
  -- the head above
  have htop : ∀ t, ∃ H', SY inp Y p (c + (dp + 1) + 1 + 1 + 1 + 1 + t) H' ∧ H5 ⊆ H' ∧
      ∀ d < t, ∀ q q', ind (fun x => (T x).top giv (u x) M Yh k d q = q') ∈ H' := by
    intro t
    induction t with
    | zero => exact ⟨H5, s5, subset_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ t ih =>
      obtain ⟨H0, s0, u0, f0⟩ := ih
      obtain ⟨H', s', u', f'⟩ := s0.add hA
        (fun q : Fin P × Fin P => ind fun x => (T x).top giv (u x) M Yh k t q.1 = q.2) (a := 5) (e := 2) hPP (fun q => by
        cases t with
        | zero => exact (((PY.const hA (q.1 = q.2)).congr fun x => Iff.rfl).toCY).mono hY (Nat.zero_le 5)
        | succ t =>
          have hd : PY D H0 Y 0 fun x => (T x).Head giv (u x) M Yh k q.1 := PY.base (u0 (f5 q.1)) hY
          have h1 : PY D H0 Y 3 fun x => ∃ q', (T x).par q.1 = q' ∧ (T x).top giv (u x) M Yh k t q' = q.2 :=
            PY.exists_univ hA (by simpa using hP) fun q' =>
              PY.and hA (PY.base (u0 (u5 (u4 (u3 (u2 (u1 (hpar q.1 q'))))))) hY)
                (PY.base (f0 t (Nat.lt_succ_self t) q' q.2) hY)
          have h2 := PY.or hA
            ((PY.and hA hd (PY.const hA (q.1 = q.2))).mono hY (show 1 ≤ 4 by omega))
            (PY.and hA ((PY.not hA hd).mono hY (show 1 ≤ 3 by omega)) h1)
          refine (h2.congr fun x => ?_).toCY
          rw [top]
          by_cases h : (T x).Head giv (u x) M Yh k q.1
          · rw [if_pos h]
            exact ⟨fun e => e.elim (fun e => e.2) fun e => absurd h e.1, fun e => Or.inl ⟨h, e⟩⟩
          · rw [if_neg h]
            exact ⟨fun e => e.elim (fun e => absurd e.1 h) fun ⟨_, q', e, e'⟩ => e ▸ e',
              fun e => Or.inr ⟨h, _, rfl, e⟩⟩) (by omega)
      refine ⟨H', s', u0.trans u', fun d hd q q' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
      · exact u' (f0 d hd q q')
      · exact f' (q, q')
  obtain ⟨H6, s6, u6, f6⟩ := htop (dp + 1)
  obtain ⟨H7, s7, u7, f7⟩ := s6.add hA (fun q x => (T x).rank giv (u x) M Yh k q) (a := 2) (e := 1) hPc (fun q => by
    have e : ∀ x, (T x).rank giv (u x) M Yh k q = ∑ q' ∈ univ.filter (fun q' => q' < q),
        ind (fun x => (T x).Head giv (u x) M Yh k q') x := by
      intro x
      unfold rank
      rw [Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun q' _ => ?_
      by_cases h : (T x).Head giv (u x) M Yh k q'
      · by_cases h' : q' < q
        · rw [if_pos ⟨h, h'⟩, if_pos h', ind_true (P := fun x => (T x).Head giv (u x) M Yh k q') h]
        · rw [if_neg fun e => h' e.2, if_neg h']
      · rw [if_neg fun e => h e.1, ind_false (P := fun x => (T x).Head giv (u x) M Yh k q') h]
        split_ifs <;> rfl
    refine CY.congr ?_ fun x => (e x).symm
    refine CY.sum hA _ ((card_filter_le _ _).trans (by simpa using hP)) (fun q' _ => CY.base (u6 (f5 q')) hY) fun x => ?_
    refine hA.lt_of_le ((Finset.sum_le_sum fun q' _ => ind_le _ x).trans ?_)
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact (card_filter_le _ _).trans (by simpa using hP)) (by omega)
  obtain ⟨H8, s8, u8, f8⟩ := s7.add hA (fun q x => (T x).piece giv (u x) M Yh k q) (a := 3) (e := 1) hPc (fun q => by
    have e : ∀ x, (T x).piece giv (u x) M Yh k q =
        ∑ q' ∈ univ, ind (fun x => (T x).top giv (u x) M Yh k (dp - st q) q = q') x *
          (T x).rank giv (u x) M Yh k q' := by
      intro x
      have e0 : (T x).hd giv (u x) M Yh k q = (T x).top giv (u x) M Yh k (dp - st q) q := by
        unfold hd
        rw [hdp, hst]
      rw [piece, e0, Finset.sum_eq_single ((T x).top giv (u x) M Yh k (dp - st q) q)]
      · rw [ind_true (P := fun y => (T y).top giv (u y) M Yh k (dp - st q) q = (T x).top giv (u x) M Yh k (dp - st q) q) rfl,
          one_mul]
      · intro q' _ hne
        rw [ind_false (P := fun y => (T y).top giv (u y) M Yh k (dp - st q) q = q') hne.symm, zero_mul]
      · exact fun hn => absurd (mem_univ _) hn
    refine CY.congr ?_ fun x => (e x).symm
    have hle : ∀ x q', ind (fun x => (T x).top giv (u x) M Yh k (dp - st q) q = q') x *
        (T x).rank giv (u x) M Yh k q' ≤ Y := fun x q' => by
      refine (Nat.mul_le_mul_right _ (ind_le _ x)).trans ?_
      rw [one_mul]
      unfold rank
      exact (card_filter_le _ _).trans (by simpa using hP)
    exact CY.sum hA univ (by simpa using hP) (fun q' _ => CY.op hA (fun a b => a * b)
      (CY.base (u7 (f6 _ (by omega) q q')) hY) (CY.base (f7 q') hY) fun x => hA.lt_of_le (hle x q'))
      fun x => hsum _ (hle x)) (by omega)
  exact ⟨H8, s8.le hA (by omega),
    u1.trans (u2.trans (u3.trans (u4.trans (u5.trans (u6.trans (u7.trans u8)))))), f8⟩

end Staged

end Paper
end
/- Source module Paper.Pieces. -/
section
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1000

namespace Paper

open Finset Nc Nc.G Nc.Dl Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee)
open NS1 (lg)

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q]

section Identity

variable (mu : Nc.Letter S Unit Γ → Matrix Q Q A) {T c ub K N M b G₁ C : ℕ} (cb : Option Γ → Fin c → Bool)
  {laws : List (G.Law A)} {γ : ℝ}


def yOf {AA E U1 : ℕ} {sysN : Type} [Fintype sysN] [DecidableEq sysN] (n : Fin AA → Fin AA → Fin (N + 1)) (a : Fin AA)
    (w : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a} → Fin ub → Bool) :
    Uid AA N sysN U1 → UW ub
  | .init p q k => if h : k.1 < (n p q).1 ∧ (p = a ∨ q = a) then some (w ⟨⟨p, q, ⟨k.1, h.1⟩⟩, h.2⟩) else none
  | .new _ _ => none

variable (TT : ThinTrees A laws (K + K) N ub M b G₁ C γ) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K)) (n : Dl.NN K N)


noncomputable def runTab (a : Fin (K + K)) : NodeTable A (fun a c => (n a c).1) ub a := fun w =>
  G.tabInit mu T cb q x (fun s => ρ s a) (fun a b => (n a b).1) a
    (yOf (E := TT.E) (U1 := TT.U1) (sysN := TT.sys.N) n a w)

variable {mu cb TT q x ρ n}

theorem startTab_run (p : Fin (K + K + TT.A')) (y : Uid (K + K) N TT.sys.N TT.U1 → UW ub)
    (hy : ∀ a b (k : Fin N), ¬ (k.1 < (n a b).1 ∧ Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p (Uid.init a b k : Uid (K + K) N TT.sys.N TT.U1)) →
      y (Uid.init a b k) = none) :
    startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p y =
      initAll mu T cb TT.A' q x ρ n p y := by
  classical
  revert hy
  refine Fin.addCases (fun a => ?_) (fun e _ => ?_) p
  swap
  · simp only [startTab, initAll, Fin.addCases_right]
  intro hy
  simp only [startTab, initAll, Fin.addCases_left]
  split_ifs with hc
  · unfold runTab
    refine tabInit_congr fun p' q' k => ?_
    simp only [yOf]
    split_ifs with h
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hc ⟨⟨p', q', ⟨k.1, h.1⟩⟩, h.2⟩)
      have hk : Fin.castLE (Nat.le_of_lt_succ (n p' q').2) (⟨k.1, h.1⟩ : Fin (n p' q').1) = k := Fin.ext rfl
      simp only [hk] at hv ⊢
      rw [hv]
      rfl
    · refine (hy p' q' k fun h' => h ⟨h'.1, ?_⟩).symm
      rcases h'.2 with e | e
      · exact Or.inl (Fin.castAdd_injective _ _ e).symm
      · exact Or.inr (Fin.castAdd_injective _ _ e).symm
  · by_contra h0
    refine hc fun u => tabInit_ne_none (np := TT.sys.np) (Ne.symm h0) _ (init_mem_seen0.2 u.1.2.2.2) ?_
    rcases u.2 with e | e
    · exact Or.inl (congrArg (Fin.castAdd TT.A') e.symm)
    · exact Or.inr (congrArg (Fin.castAdd TT.A') e.symm)

open Classical in



theorem prop_pieces_identity (hn : ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ N) {num : ℕ}
    (grp : (TT.sys.N → Fin TT.U1) → Fin (K + K + TT.A') → Fin num) :
    posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
        (fun y => ∏ p : Fin (K + K), G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
          (y (Fin.castAdd TT.A' p))) =
      ∑ o : TT.sys.N → Fin TT.U1, if ∀ z, TT.plan.good n o z then
        ∑ b ∈ Common (none : UW ub) (cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) (grp o) (TT.plan.cur n o TT.E)),
          ∏ g, G.grpVal mu T cb TT.plan q x ρ n o (grp o) g b
      else 0 := by
  have e0 : posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
      (fun y => ∏ p : Fin (K + K), G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
        (y (Fin.castAdd TT.A' p))) =
      posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
        (fun y => ∏ p, startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p (y p)) := by
    unfold posVal
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Nc.mem_contents_iff] at hy
    have e1 : ∀ p, startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p (y p) =
        initAll mu T cb TT.A' q x ρ n p (y p) := fun p => startTab_run p (y p) fun a b k hk => hy p _ fun h => hk
      ⟨init_mem_seen0.1 h.1, h.2⟩
    simp only []
    rw [Finset.prod_congr rfl fun p _ => e1 p]
    conv_rhs => rw [Fin.prod_univ_add]
    simp [initAll]
  rw [e0, posVal_start, TT.value n hn]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hg : ∀ z, TT.plan.good n o z
  swap
  · rw [if_neg hg, if_neg hg]
  rw [if_pos hg, if_pos hg, ← posVal_groups, posVal_groups _ _ _ _ _ (grp o)]
  refine Finset.sum_congr rfl fun bb _ => Finset.prod_congr rfl fun g _ => ?_
  unfold G.grpVal groupVal
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Nc.mem_gcontents_iff] at hy
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [tabFinal_eq]
  simp only [partyTab]
  rw [startTab_run a (y a) fun p' q' k hk => hy a _ fun h => hk ⟨Plan.init_mem_seenAt.1 h.2.1, h.2.2⟩]

end Identity

section Build

variable {K N ℓ M b G₁ C : ℕ} {laws : List (G.Law A)} {γ : ℝ} (TT : ThinTrees A laws (K + K) N ℓ M b G₁ C γ)


def treeAt (x : Dl.NN K N × (TT.sys.N → Fin TT.U1)) : Staged (K + K + TT.A') where
  par := TT.par x.1 x.2
  stage := TT.stage
  depth := TT.depth
  root := TT.root
  stage_le := TT.stage_le
  stage_root := TT.stage_root
  stage_par := TT.stage_par x.1 x.2


def given (K A' : ℕ) (p : Fin (K + K + A')) : ℕ := if (p : ℕ) < K + K then 1 else 0


def yhat (N M C : ℕ) : ℕ := lg M ^ C * M * (N + M ^ 2)

variable (k : ℕ)


noncomputable def pieceAt (n : Dl.NN K N) (o : TT.sys.N → Fin TT.U1) (p : Fin (K + K + TT.A')) : ℕ :=
  (treeAt TT (n, o)).piece (given K TT.A') (TT.up n o) M (yhat N M C) k p


def pieceNum : ℕ := min (1 + C + b * (TT.depth * k)) (K + K + TT.A')

theorem pieceNum_pos : 0 < pieceNum TT k := lt_min (by omega) (Fin.pos TT.root)


noncomputable def pieceFin (n : Dl.NN K N) (o : TT.sys.N → Fin TT.U1) (p : Fin (K + K + TT.A')) : Fin (pieceNum TT k) :=
  if h : pieceAt TT k n o p < pieceNum TT k then ⟨_, h⟩ else ⟨0, pieceNum_pos TT k⟩

theorem sum_given (A' : ℕ) : ∑ p, given K A' p = K + K := by
  rw [Fin.sum_univ_add]
  simp [given]

theorem given_le (A' : ℕ) (p : Fin (K + K + A')) : given K A' p ≤ 1 := by
  unfold given
  split_ifs <;> omega

variable {TT k} {n : Dl.NN K N} {o : TT.sys.N → Fin TT.U1} (hn : ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N)
  (hg : ∀ z, TT.plan.good n o z) (hK : 0 < K) (hM : K + K ≤ M) (hk : 0 < k)
include hn hg hK hM hk

theorem yhat_pos : 0 < yhat N M C := by
  have hlg : 0 < lg M := Nat.succ_pos _
  have hM0 : 0 < M := by omega
  exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hlg) hM0) (Nat.add_pos_right _ (Nat.pow_pos hM0))

theorem pieceFin_val (p : Fin (K + K + TT.A')) : (pieceFin TT k n o p : ℕ) = pieceAt TT k n o p := by
  have h : pieceAt TT k n o p < pieceNum TT k := lt_min
    (prop_pieces_count hk (by omega) (yhat_pos hn hg hK hM hk) ((sum_given _).le.trans hM) (TT.up_total n hn o hg)
      (fun p hp => TT.children_le n o p hp) (TT.root_children_le n o) p)
    (Staged.piece_lt p)
  rw [pieceFin, dif_pos h]

theorem pieceFin_iff (p : Fin (K + K + TT.A')) (g : Fin (pieceNum TT k)) :
    pieceFin TT k n o p = g ↔ pieceAt TT k n o p = g.val := by rw [Fin.ext_iff, pieceFin_val hn hg hK hM hk]


theorem piece_given (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    k * ∑ p ∈ univ.filter (fun p => pieceFin TT k n o p = g), given K TT.A' p ≤ 4 * M := by
  classical
  rw [Finset.mul_sum, Finset.filter_congr fun p _ => pieceFin_iff hn hg hK hM hk p g]
  refine Staged.piece_sum_le _ _ (fun p => ?_) (fun x hx => ?_) _
  · exact (Nat.mul_le_mul_left _ (given_le _ p)).trans (by rwa [Nat.mul_one])
  · refine le_trans (le_of_eq ?_) (Staged.light_le (by omega) (yhat_pos hn hg hK hM hk) hx).1
    unfold Staged.below
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp

theorem piece_blocks (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    (univ.filter fun p : Fin (K + K) => pieceFin TT k n o (Fin.castAdd TT.A' p) = g).card * k ≤ 4 * M := by
  refine le_trans ?_ (piece_given hn hg hK hM hk hk' g)
  rw [Nat.mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  rw [Finset.sum_filter, Fin.sum_univ_add, card_filter]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (Nat.le_add_right _ _)
  simp [given]

variable {w : ℕ} (hkw : k ≤ w)
  (hnode : ∀ X : ℕ, (X : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) → X * w ≤ yhat N M C)
include hkw hnode

open Classical in

theorem piece_cut (g : Fin (pieceNum TT k)) :
    ((TT.plan.cur n o TT.E).filter (Nc.Plus.OneIn (hold0 TT.sys.np) (hold1 TT.sys.np) (pieceFin TT k n o) g)).card * w ≤
      yhat N M C + M ^ C * w := by
  obtain ⟨x, hx⟩ := Staged.piece_boundary (T := treeAt TT (n, o)) (giv := given K TT.A') (u := TT.up n o) (M := M)
    (Y := yhat N M C) (k := k) g.val
  refine le_trans (Nat.mul_le_mul_right w (card_le_card (t := (cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id
    (TT.plan.cur n o TT.E \ TT.dead o)).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) x) ∪ TT.dead o) ?_)) ?_
  · intro id hid
    obtain ⟨hcur, hone⟩ := mem_filter.1 hid
    by_cases hd : id ∈ TT.dead o
    · exact mem_union_right _ hd
    refine mem_union_left _ ?_
    have hl : hold0 TT.sys.np id ≠ hold1 TT.sys.np id := fun e => by
      unfold Nc.Plus.OneIn at hone
      rw [e] at hone
      tauto
    have hu : id ∈ cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) _root_.id (TT.plan.cur n o TT.E \ TT.dead o) :=
      mem_filter.2 ⟨mem_sdiff.2 ⟨hcur, hd⟩, hl⟩
    refine mem_filter.2 ⟨hu, ?_⟩
    obtain ⟨q, hq, he⟩ := TT.edge n hn o hg id hu
    have hne : ¬ (pieceAt TT k n o q = g.val ↔ pieceAt TT k n o (TT.par n o q) = g.val) := by
      rw [← pieceFin_iff hn hg hK hM hk, ← pieceFin_iff hn hg hK hM hk]
      unfold Nc.Plus.OneIn at hone
      rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at hone
        tauto
      · rw [e1, e2] at hone
        tauto
    have hxm : x ∈ s(hold0 TT.sys.np id, hold1 TT.sys.np id) := by
      rw [he, Sym2.mem_iff]
      exact (hx q hq hne).imp Eq.symm Eq.symm
    exact (Sym2.mem_iff.1 hxm)
  · refine (Nat.mul_le_mul_right _ (card_union_le _ _)).trans ?_
    rw [add_mul]
    exact Nat.add_le_add (hnode _ (TT.node_le n hn o hg x)) (Nat.mul_le_mul_right _ (TT.dead_le o))

open Classical in

theorem piece_all (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    (evG (fun n o => pieceFin TT k n o) n o g + pdG TT.plan (fun n o => pieceFin TT k n o) n o g) * k ≤
      C * (4 * yhat N M C) + 4 * M * (lg M ^ C * N) + 2 * C * M ^ C * k := by
  set S := univ.filter fun p => pieceFin TT k n o p = g with hS
  have h1 : evG (fun n o => pieceFin TT k n o) n o g + pdG TT.plan (fun n o => pieceFin TT k n o) n o g =
      ∑ p ∈ S, (((Plan.seenAt n o TT.E).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card +
        ∑ r ∈ univ.filter (fun r : TT.sys.R => TT.sys.rp r = p),
          (1 + Fintype.card ((TT.sys.kind r.1).SlAt r.2)) * TT.plan.num n o r.1) := by
    rw [Finset.sum_add_distrib]
    congr 1
    unfold pdG
    rw [← Finset.sum_fiberwise_of_maps_to (g := TT.sys.rp) (t := S)
      (fun r hr => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hr).2⟩)]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun r _ => ⟨fun e => e.2, fun e => ⟨?_, e⟩⟩
    rw [e]
    exact (mem_filter.1 hp).2
  rw [h1]
  refine (Nat.mul_le_mul_right _ (Finset.sum_le_sum fun p _ => TT.copies_le n hn o hg p)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_mul, add_mul]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · rw [← Finset.mul_sum, Nat.mul_assoc, Finset.sum_mul]
    refine Nat.mul_le_mul_left _ ?_
    rw [hS, Finset.filter_congr fun p _ => pieceFin_iff hn hg hK hM hk p g]
    refine Staged.piece_sum_le _ _ (fun p => ?_) (fun y hy => ?_) _
    · refine (Nat.mul_le_mul_left _ hkw).trans ((hnode _ ?_).trans (Nat.le_mul_of_pos_left _ (by norm_num)))
      exact TT.up_node n hn o hg p
    · have h2 := (Staged.light_le (by omega) (yhat_pos hn hg hK hM hk) hy).2
      have h3 := Staged.below_kids (T := treeAt TT (n, o)) (TT.up n o) y
      have e : (treeAt TT (n, o)).below (fun p => (TT.up n o p + (treeAt TT (n, o)).kids (TT.up n o) p) * k) y =
          ((treeAt TT (n, o)).below (TT.up n o) y + (treeAt TT (n, o)).below ((treeAt TT (n, o)).kids (TT.up n o)) y) * k := by
        unfold Staged.below
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
      refine le_of_eq_of_le e ?_
      calc _ ≤ ((treeAt TT (n, o)).below (TT.up n o) y + (treeAt TT (n, o)).below (TT.up n o) y) * k :=
            Nat.mul_le_mul_right _ (Nat.add_le_add_left h3 _)
        _ = 2 * (k * (treeAt TT (n, o)).below (TT.up n o) y) := by ring
        _ ≤ _ := by omega
  · calc (∑ p ∈ S, if (p : ℕ) < K + K then lg M ^ C * N else 0) * k =
        (k * ∑ p ∈ S, given K TT.A' p) * (lg M ^ C * N) := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          unfold given
          split_ifs <;> ring
      _ ≤ _ := Nat.mul_le_mul_right _ (piece_given hn hg hK hM hk hk' g)
  · refine Nat.mul_le_mul_right _ ?_
    calc ∑ p ∈ S, C * ((TT.dead o).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card ≤
        C * ∑ p, ((TT.dead o).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum_of_subset (subset_univ _)
      _ ≤ C * (2 * (TT.dead o).card) := by
          refine Nat.mul_le_mul_left _ ?_
          simp only [card_filter]
          rw [Finset.sum_comm, Nat.mul_comm 2, ← smul_eq_mul (a := (TT.dead o).card), ← Finset.sum_const]
          refine Finset.sum_le_sum fun u _ => ?_
          rw [← card_filter]
          refine (card_le_card (t := {hold0 TT.sys.np u, hold1 TT.sys.np u}) fun p hp => ?_).trans card_le_two
          rw [mem_insert, mem_singleton]
          exact (mem_filter.1 hp).2
      _ ≤ C * (2 * M ^ C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (TT.dead_le o))
      _ = _ := by ring

end Build

theorem ind_ite {X : Type} {P : X → Prop} {x : X} {i : Decidable (P x)} : ind P x = @ite ℕ (P x) i 1 0 := by
  by_cases hp : P x
  · rw [ind_true hp, if_pos hp]
  · rw [ind_false hp, if_neg hp]

theorem ind_eq_one {X : Type} {P : X → Prop} {x : X} : ind P x = 1 ↔ P x := by
  by_cases hp : P x
  · simp [ind_true hp, hp]
  · simp [ind_false hp, hp]

section Prog


theorem slp_inputs {Inp ι : Type} [Fintype ι] {D p : ℕ} {inp : ι → Inp → Fin D} {H : Set (Inp → ℕ)}
    (h : SlpN inp p H) : SlpN inp (p + Fintype.card ι) (H ∪ Set.range fun i x => (inp i x : ℕ)) := by
  classical
  have : ∀ s : Finset ι, SlpN inp (p + s.card) (H ∪ (fun i x => (inp i x : ℕ)) '' (s : Set ι)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi]
      refine (ih.snoc (inp i) (Or.inl ⟨i, rfl⟩)).mono ?_
      rintro f (hf | ⟨j, hj, rfl⟩)
      · exact Set.mem_insert_of_mem _ (Or.inl hf)
      · rcases mem_insert.mp (mem_coe.mp hj) with h | h
        · subst h; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Or.inr ⟨j, mem_coe.mpr h, rfl⟩)
  have h2 := this univ
  rw [coe_univ, Set.image_univ, card_univ] at h2
  exact h2

variable {K N ℓ M b G₁ C : ℕ} {laws : List (G.Law A)} {γ : ℝ} (TT : ThinTrees A laws (K + K) N ℓ M b G₁ C γ)

open Classical in


theorem prop_pieces_program (k : ℕ) {Y : ℕ} (hY : 16 ≤ Y) (hMY : (M * N) ^ C ≤ Y) (hKY : K + K ≤ Y) (hNY : N ≤ Y)
    (hdY : TT.depth ≤ Y) (hin : (K + K) * (K + K) + Fintype.card TT.sys.N ≤ Y) :
    N < Y ^ 4 ∧ TT.U1 ≤ Y ^ 4 ∧ pieceNum TT k ≤ Y ^ 4 ∧
    ∃ tab : SlpTab TT.plan (fun n o => pieceFin TT k n o) (Y ^ 4) (Y ^ 15),
      ∀ n, tab.valid n ↔ ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N := by
  obtain ⟨D₀, s₀, inp₀, H₀, d1, d2, d3, d4, d5, d6, i1, i2, hS, p1, p2, p3, p4, p5, p6⟩ := TT.computed
  have hA : Alph (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hY4 : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hDY : D₀ ≤ Y := d1.trans hMY
  have hP : K + K + TT.A' ≤ Y := d3.trans hMY
  have hnum : pieceNum TT k ≤ Y := (min_le_right _ _).trans hP
  refine ⟨by omega, by omega, by omega, ?_⟩
  let inp : (Fin (K + K) × Fin (K + K)) ⊕ TT.sys.N → Dl.NN K N × (TT.sys.N → Fin TT.U1) → Fin (Y ^ 4) := fun i x =>
    ⟨(inp₀ i x).1, by have := (inp₀ i x).2; omega⟩
  have s0 := slp_inputs (slp_cast (inp' := inp) (show D₀ ≤ Y ^ 4 by omega) (fun i x => rfl) hS)
  set H : Set (Dl.NN K N × (TT.sys.N → Fin TT.U1) → ℕ) := H₀ ∪ Set.range fun i x => (inp i x : ℕ) with hH
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ = s₀ + Fintype.card ((Fin (K + K) × Fin (K + K)) ⊕ TT.sys.N) := ⟨_, rfl⟩
  have hS0 : SY inp Y p₀ 0 H := by
    unfold SY
    rw [Nat.zero_mul, Nat.add_zero, hp₀]
    exact s0
  have hlt : ∀ f ∈ H₀, ∀ x, f x ≤ Y := fun f hf x => by
    obtain ⟨fn, -, h2⟩ := hS
    obtain ⟨i, -, e⟩ := h2 f hf
    rw [← e x]
    exact (fn i x).2.le.trans hDY
  obtain ⟨H1, s1, u1, f1⟩ := Staged.piece_prog (T := treeAt TT) (st := TT.stage) (dp := TT.depth) (rt := TT.root)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hA hP (giv := given K TT.A') (u := fun x => TT.up x.1 x.2) (M := M)
    (Yh := yhat N M C) (k := k) hS0 (fun q q' => Or.inl (p1 q q')) (fun q => Or.inl (p5 q)) (given_le _)
    (fun x q => hlt _ (p5 q) x)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (fun p x => (pieceFin TT k x.1 x.2 p : ℕ)) (a := 1) (e := 1)
    (by rw [Fintype.card_fin, pow_one]; exact hP) (fun p => by
      have e : ∀ x : Dl.NN K N × (TT.sys.N → Fin TT.U1), (pieceFin TT k x.1 x.2 p : ℕ) =
          (fun a => if a < pieceNum TT k then a else 0) (pieceAt TT k x.1 x.2 p) := fun x => by
        unfold pieceFin
        split_ifs with h <;> simp [h]
      refine CY.congr ?_ fun x => (e x).symm
      exact CY.op1 hA (fun a => if a < pieceNum TT k then a else 0) (CY.base (f1 p) hA.pos) fun x => by
        refine lt_of_eq_of_lt (e x).symm ?_
        exact hA.lt_of_le ((pieceFin TT k x.1 x.2 p).2.le.trans hnum)) (by omega)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (fun id => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      id ∈ TT.plan.cur x.1 x.2 TT.E ∧
        pieceFin TT k x.1 x.2 (hold0 TT.sys.np id) ≠ pieceFin TT k x.1 x.2 (hold1 TT.sys.np id)) (a := 2) (e := 1)
    (by rw [pow_one]; exact d6.trans hMY) (fun id => by
      refine (PY.congr (PY.and hA ((PY.base (u2 (u1 (Or.inl (p2 id)))) hA.pos).mono hA.pos (show 0 ≤ 1 by omega))
        (PY.rel hA (fun a c => a ≠ c) (CY.base (f2 (hold0 TT.sys.np id)) hA.pos)
          (CY.base (f2 (hold1 TT.sys.np id)) hA.pos))) fun x => ?_).toCY
      exact and_congr_right fun _ => not_congr Fin.val_inj) (by omega)
  have hin' : ∀ i, (fun x => (inp i x : ℕ)) ∈ H3 := fun i => u3 (u2 (u1 (Or.inr ⟨i, rfl⟩)))
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (fun p : Fin (K + K) => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N) (a := 4) (e := 1) (by rw [Fintype.card_fin, pow_one]; exact hKY)
    (fun p => by
      have hb : ∀ (x : Dl.NN K N × (TT.sys.N → Fin TT.U1)) c, (x.1 p c).val + (x.1 c p).val ≤ 2 * Y := fun x c => by
        have := (x.1 p c).2
        have := (x.1 c p).2
        omega
      have h1 : CY (Y ^ 4) H3 Y 3 fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
          ∑ c ∈ univ, ((x.1 p c).val + (x.1 c p).val) := by
        refine CY.sum hA univ (by simpa using hKY) (fun c _ => CY.op hA (fun a b => a + b)
          ((CY.base (hin' (.inl (p, c))) hA.pos).congr fun x => i1 p c x)
          ((CY.base (hin' (.inl (c, p))) hA.pos).congr fun x => i1 c p x)
          fun x => hA.lt_of_le3 ((hb x c).trans ?_)) fun x => hA.lt_of_le3 ?_
        · exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
        · calc ∑ c ∈ univ, ((x.1 p c).val + (x.1 c p).val) ≤ ∑ _c : Fin (K + K), 2 * Y :=
                Finset.sum_le_sum fun c _ => hb x c
            _ = (K + K) * (2 * Y) := by simp
            _ ≤ Y * (2 * Y) := Nat.mul_le_mul_right _ hKY
            _ = 2 * Y ^ 2 := by ring
            _ ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA.pos (by norm_num))
      exact (PY.rel1 hA (fun a => a ≤ N) h1).toCY) (by omega)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (fun _ : Unit => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      ∀ p, ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N) (a := 2) (e := 1) (by rw [Fintype.card_unit, pow_one]; omega)
    (fun _ => (PY.forall_univ hA (by simpa using hKY) fun p => PY.base (f4 p) hA.pos).toCY) (by omega)
  have hsteps : p₀ + (0 + 2 * TT.depth + 9 + 1 + 1 + 1 + 1) * Y ^ 12 ≤ Y ^ 15 := by
    have h1 : p₀ ≤ 2 * Y := by
      rw [hp₀, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      have := d2.trans hMY
      omega
    have h2 : 0 + 2 * TT.depth + 9 + 1 + 1 + 1 + 1 ≤ 3 * Y := by omega
    have h3 : 2 * Y ≤ 2 * Y * Y ^ 12 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hA.pos)
    calc _ ≤ 2 * Y * Y ^ 12 + 3 * Y * Y ^ 12 := Nat.add_le_add (h1.trans h3) (Nat.mul_le_mul_right _ h2)
      _ = 5 * Y ^ 13 := by ring
      _ ≤ Y * Y ^ 13 := Nat.mul_le_mul_right _ (by omega)
      _ = Y ^ 14 := by ring
      _ ≤ Y ^ 15 := Nat.pow_le_pow_right hA.pos (by norm_num)
  obtain ⟨fn, hst, hfn⟩ := SlpN.le hA.zero_lt hsteps s5
  have ex : ∀ f, f ∈ H5 → ∃ q : Fin (Y ^ 15), ∀ x, (fn q x : ℕ) = f x := by
    intro f hf
    obtain ⟨q, hq, hx⟩ := hfn f hf
    exact ⟨⟨q, hq⟩, hx⟩
  choose ix hix using ex
  have l0 : ∀ f, f ∈ H₀ → f ∈ H5 := fun f hf => u5 (u4 (u3 (u2 (u1 (Or.inl hf)))))
  refine ⟨{
    fn := fn
    inp := inp
    inpN := fun a c x => i1 a c x
    inpO := fun ν x => i2 ν x
    step := hst
    kcur := fun id => ix _ (l0 _ (p2 id))
    hcur := fun id x => by rw [hix]; exact ind_ite (P := fun x : Dl.NN K N × _ => id ∈ TT.plan.cur x.1 x.2 TT.E)
    kcut := fun id => ix _ (u5 (u4 (f3 id)))
    hcut := fun id x => (hix _ _ x).trans ind_ite
    kcons := fun z id => ix _ (l0 _ (p3 z id))
    hcons := fun z id x => by rw [hix]; exact ind_ite (P := fun x : Dl.NN K N × _ => id ∈ TT.plan.cons x.1 x.2 z)
    knum := fun y => ix _ (l0 _ (p4 y))
    hnum := fun y x => by rw [hix]
    kcond := fun y => match y with
      | none => ix _ (f5 ())
      | some y => ix _ (l0 _ (p6 y))
    valid := fun n => ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N
    hgood := fun y x => by
      rw [hix]
      exact ind_eq_one (P := fun x : Dl.NN K N × _ => TT.plan.good x.1 x.2 y)
    hvalid := fun x => by
      rw [hix]
      exact ind_eq_one (P := fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) => ∀ p, ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N)
    kgrp := fun p => ix _ (u5 (u4 (u3 (f2 p))))
    hgrp := fun p x => by rw [hix] }, fun n => Iff.rfl⟩

end Prog


theorem prop_pieces_dead {v e M C₀ a' T : ℕ} (hv : 1 ≤ v) (hM : M ≤ v ^ (e + 1)) (ha : (e + 1) * C₀ + 300 ≤ a') {ub : ℕ}
    (hub : ub = T / v ^ a') : M ^ C₀ * v ^ 300 * ub ≤ T := by
  refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM C₀))) ?_
  rw [← pow_mul, ← pow_add, Nat.mul_comm, hub]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv ha)).trans (Nat.div_mul_le_self _ _)



theorem pieces_numbers {c σ v e M C₀ a' T : ℕ} (hc : 1 ≤ c) (hσ : 1 ≤ σ) (hv : 8 * c + 2 * σ + 16 ≤ v) (hM1 : 1 ≤ M)
    (hM : M ≤ v ^ (e + 1)) (ha : (e + 2) * (C₀ + 2) + 300 ≤ a') (hT : v ^ (a' + e + 3) ≤ T) {ub load : ℕ}
    (hub : ub = T / v ^ a') (hload : load = 2 * ((T + M * σ) * c / ub + M)) :
    0 < ub ∧ ub ≤ T ∧ load * ub ≤ (4 * c + 4) * T ∧ M ^ 2 * ub ≤ T ∧ M ^ C₀ * v ^ 300 * ub ≤ T ∧
      load ≤ v ^ (a' + 1) ∧ (T + σ) * c / ub + 1 ≤ load := by
  have pw : ∀ x y, x ≤ y → v ^ x ≤ v ^ y := fun x y h => Nat.pow_le_pow_right (by omega) h
  have hp : 0 < v ^ a' := Nat.pow_pos (by omega)
  have hub0 : 0 < ub := hub ▸ Nat.div_pos ((pw a' _ (by omega)).trans hT) hp
  have hubT : ub * v ^ a' ≤ T := hub ▸ Nat.div_mul_le_self _ _
  have hTub : T < (ub + 1) * v ^ a' := by
    rw [hub, add_mul, one_mul]
    exact Nat.lt_div_mul_add hp
  have hMσ : M * σ ≤ T := by
    calc M * σ ≤ v ^ (e + 1) * v := Nat.mul_le_mul hM (by omega)
      _ ≤ T := by rw [← pow_succ]; exact (pw _ _ (by omega)).trans hT
  have hmul : ∀ d, d ≤ a' → v ^ d * ub ≤ T := fun d hd => by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ (pw d a' hd)).trans hubT
  have hM2 : M ^ 2 * ub ≤ T := by
    refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)) ?_
    rw [← pow_mul]
    exact hmul _ (by nlinarith)
  have hMub : M * ub ≤ T := (Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) M)).trans hM2
  have h2T : (T + M * σ) * c ≤ 2 * T * c := Nat.mul_le_mul_right _ (by omega)
  refine ⟨hub0, (Nat.le_mul_of_pos_right _ hp).trans hubT, ?_, hM2, ?_, ?_, ?_⟩
  · have h1 := Nat.div_mul_le_self ((T + M * σ) * c) ub
    have e1 : load * ub = 2 * ((T + M * σ) * c / ub * ub) + 2 * (M * ub) := by rw [hload]; ring
    have e2 : (4 * c + 4) * T = 2 * (2 * T * c) + 4 * T := by ring
    omega
  · exact prop_pieces_dead (by omega) hM (by nlinarith) hub
  · have h1 : (T + M * σ) * c / ub ≤ 4 * c * v ^ a' := by
      refine Nat.div_le_of_le_mul (h2T.trans ?_)
      calc 2 * T * c ≤ 2 * ((ub + ub) * v ^ a') * c := by
            refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hTub.le.trans ?_))
            gcongr
            omega
        _ = ub * (4 * c * v ^ a') := by ring
    have h2 : M ≤ v ^ a' := hM.trans (pw _ _ (by nlinarith))
    calc load ≤ 2 * (4 * c * v ^ a' + v ^ a') := by rw [hload]; gcongr
      _ = (8 * c + 2) * v ^ a' := by ring
      _ ≤ v * v ^ a' := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a' + 1) := (pow_succ' v a').symm
  · have h1 : (T + σ) * c / ub ≤ (T + M * σ) * c / ub :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hM1) _))
    omega


theorem pieces_gain {M q w Λ R X : ℕ} (hq : 0 < q) (hM : 0 < M) (hw : w ^ q ≤ M)
    (hX : (X : ℝ) ≤ (Λ : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * R) : X * w ≤ Λ * M * R := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (w : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ)) := by
    have h2 : (w : ℝ) ^ q ≤ (M : ℝ) := by exact_mod_cast hw
    have h3 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg w) hq.ne'] at h3
    rwa [one_div]
  have h4 : ((X * w : ℕ) : ℝ) ≤ ((Λ * M * R : ℕ) : ℝ) := by
    push_cast
    refine (mul_le_mul hX h1 (Nat.cast_nonneg _) (by positivity)).trans (le_of_eq ?_)
    calc (Λ : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * R * (M : ℝ) ^ (1 / (q : ℝ)) =
        Λ * ((M : ℝ) ^ (1 - 1 / (q : ℝ)) * (M : ℝ) ^ (1 / (q : ℝ))) * R := by ring
      _ = _ := by rw [← Real.rpow_add hM0, sub_add_cancel, Real.rpow_one]
  exact_mod_cast h4

set_option maxHeartbeats 1600000 in













theorem prop_pieces {h : ℕ} [NeZero h] (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a e : ℕ, 300 ≤ e ∧ ∀ (Γ S Q : Type) [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
      (mu : Nc.Letter S Unit Γ → Matrix Q Q A),
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧
        ∀ T k, v ^ a ≤ T → 2 ≤ k → k ≤ v ^ 64 →
          Nonempty (PieceCut (kindList A ((univ : Finset VL.Di).toList.map VL.L)) mu (2 ^ ee h)
            (goodBound VL.C₁ VL.a₁) v K T k C) := by
  classical
  obtain ⟨C₀, htree⟩ := ValiantBorder.lawThinTrees VL h3 hgain
  have hq : 0 < ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  obtain ⟨e, he⟩ : ∃ e, e = 300 * ee h + 64 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = (e + 2) * (C₀ + 2) + 300 := ⟨_, rfl⟩
  refine ⟨a' + e + 3, e, by omega, fun Γ S Q _ _ _ _ _ _ mu => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Fintype.card (Option Γ) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact Fintype.card_pos
  obtain ⟨cb, hcb⟩ : ∃ cb : Option Γ → Fin c → Bool, Function.Injective cb := by
    refine ⟨fun z j => decide (Fin.cast hc.symm (Fintype.equivFin _ z) = j), fun z z' h => ?_⟩
    have := congrFun h (Fin.cast hc.symm (Fintype.equivFin _ z'))
    simp only [decide_true, decide_eq_true_eq] at this
    exact (Fintype.equivFin _).injective (Fin.ext (by simpa using congrArg Fin.val this))
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = Fintype.card S + 1 := ⟨_, rfl⟩
  obtain ⟨bY, hbY⟩ : ∃ b, b = (e + a' + 2) * C₀ + 2 * e + a' + 8 := ⟨_, rfl⟩
  obtain ⟨Ee, hEe⟩ : ∃ x, x = (e + 2) ^ C₀ := ⟨_, rfl⟩
  have hEe1 : 1 ≤ Ee := hEe ▸ Nat.one_le_pow _ _ (by omega)
  obtain ⟨W, hW⟩ : ∃ W, W = 18 * (C₀ + 1) * (4 * c + 5) * Ee := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = W + C₀ + (1 + C₀ + 2 ^ ee h * Ee) + 16 * bY + c + 8 + (4 * c + 4) := ⟨_, rfl⟩
  refine ⟨C, 8 * c + 2 * σ + 16, fun v hv => ?_⟩
  have hv1 : 1 ≤ v := by omega
  refine ⟨v ^ e, le_rfl, Nat.le_mul_of_pos_left _ (by omega), fun T k hT hk hk' => ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, K = v ^ e := ⟨_, rfl⟩
  rw [← hK]
  have vp : ∀ {x y}, x ≤ y → v ^ x ≤ v ^ y := fun h => Nat.pow_le_pow_right hv1 h
  have hK0 : 0 < K := hK ▸ Nat.pow_pos hv1
  have hMv : K + K ≤ v ^ (e + 1) := by
    rw [pow_succ, ← hK]
    calc K + K = K * 2 := (Nat.mul_two K).symm
      _ ≤ K * v := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨ub, hub⟩ : ∃ ub, ub = T / v ^ a' := ⟨_, rfl⟩
  obtain ⟨load, hload⟩ : ∃ l, l = 2 * ((T + (K + K) * σ) * c / ub + (K + K)) := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := pieces_numbers (C₀ := C₀) (σ := σ) hc0 (by omega) hv (by omega) hMv ha'.ge hT
    hub hload
  have hload1 : 1 ≤ load := (Nat.le_add_left 1 _).trans b7
  obtain ⟨TT⟩ := htree A (K + K) (K + K) load ub (by omega) le_rfl hload1 b1
  have hk64 : k ≤ v ^ 300 := hk'.trans (vp (by norm_num))
  have hkM : k ≤ 4 * (K + K) := by
    have : v ^ 64 ≤ K := hK ▸ vp (by omega)
    omega
  have hγ : (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ)) = 1 / (ee h : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hnode : ∀ X : ℕ, (X : ℝ) ≤ (lg (K + K) ^ C₀ : ℕ) *
      ((K + K : ℕ) : ℝ) ^ (1 - 1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ)) * (load + ((K + K : ℕ) : ℝ) ^ 2) →
      X * v ^ 300 ≤ yhat load (K + K) C₀ := by
    intro X hX
    rw [hγ] at hX
    refine pieces_gain hq (by omega) ?_ (R := load + (K + K) ^ 2) (by push_cast at hX ⊢; exact hX)
    rw [← pow_mul]
    exact (vp (show 300 * ee h ≤ e by omega)).trans (by omega)
  -- bits
  obtain ⟨L, hL⟩ : ∃ L, L = lg v := ⟨_, rfl⟩
  have hL2 : 2 ≤ L := hL ▸ lg_two (by omega)
  have hPL : lg (K + K) ^ C₀ ≤ Ee * L ^ C₀ := by
    rw [hEe, ← mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    have h1 : K + K < 2 ^ ((e + 1) * L) := by
      calc K + K ≤ v ^ (e + 1) := hMv
        _ < (2 ^ L) ^ (e + 1) := Nat.pow_lt_pow_left (hL ▸ Nat.lt_pow_succ_log_self (by norm_num) v) (by omega)
        _ = 2 ^ ((e + 1) * L) := by rw [← pow_mul, Nat.mul_comm]
    have h2 : Nat.log 2 (K + K) < (e + 1) * L := Nat.log_lt_of_lt_pow (by omega) h1
    have e1 : (e + 2) * L = (e + 1) * L + L := by ring
    unfold lg
    omega
  have hWC : ∀ X, X ≤ W * L ^ C₀ * (K * T) → X ≤ K * T * lg v ^ C := fun X hX => by
    rw [← hL, Nat.mul_comm (K * T)]
    exact hX.trans (Nat.mul_le_mul_right _ (const_mul_pow_le hL2 (by omega)))
  have hYub : yhat load (K + K) C₀ * ub ≤ 2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T) := by
    calc yhat load (K + K) C₀ * ub = lg (K + K) ^ C₀ * (K + K) * (load * ub + (K + K) ^ 2 * ub) := by unfold yhat; ring
      _ ≤ Ee * L ^ C₀ * (K + K) * ((4 * c + 4) * T + T) := by gcongr
      _ = _ := by ring
  have hKT : T ≤ K * T := Nat.le_mul_of_pos_left _ hK0
  have hL1 : 1 ≤ L ^ C₀ := Nat.one_le_pow _ _ (by omega)
  -- the program
  have hNc : Fintype.card TT.sys.N ≤ ((K + K) * load) ^ C₀ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, d6, -⟩ := TT.computed
    exact (Fintype.card_le_of_injective (fun ν => (Uid.new ν ⟨0, TT.U1_pos⟩ : Uid (K + K) load TT.sys.N TT.U1))
      fun a b e => (Uid.new.inj e).1).trans d6
  have hMN : ((K + K) * load) ^ C₀ ≤ v ^ ((e + a' + 2) * C₀) := by
    rw [pow_mul]
    refine Nat.pow_le_pow_left ((Nat.mul_le_mul hMv b6).trans ?_) _
    rw [← pow_add]
    exact vp (by omega)
  have hdep : TT.depth ≤ Ee * L ^ C₀ := TT.depth_le.trans hPL
  have hdY : TT.depth ≤ v ^ bY := by
    refine TT.depth_le.trans (le_trans ?_ (hMN.trans (vp (by omega))))
    refine Nat.pow_le_pow_left ?_ _
    exact (Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))).trans (Nat.le_mul_of_pos_right _ hload1)
  have hin : (K + K) * (K + K) + Fintype.card TT.sys.N ≤ v ^ bY := by
    have h1 : (K + K) * (K + K) ≤ v ^ (bY - 1) := by
      refine (Nat.mul_le_mul hMv hMv).trans ?_
      rw [← pow_add]
      exact vp (by omega)
    have h2 : Fintype.card TT.sys.N ≤ v ^ (bY - 1) := hNc.trans (hMN.trans (vp (by omega)))
    calc _ ≤ v ^ (bY - 1) * 2 := by omega
      _ ≤ v ^ (bY - 1) * v := Nat.mul_le_mul_left _ (by omega)
      _ = v ^ bY := by rw [← pow_succ]; congr 1; omega
  obtain ⟨g1, g2, g3, tab, htab⟩ := prop_pieces_program TT k (Y := v ^ bY)
    (le_trans (by omega) (Nat.le_self_pow (show bY ≠ 0 by omega) v)) (hMN.trans (vp (by omega)))
    (hMv.trans (vp (by omega))) (b6.trans (vp (by omega))) hdY hin
  refine ⟨{
    c := c
    cb := cb
    cb_inj := hcb
    c_le := by omega
    ub := ub
    ub_pos := b1
    U0 := load
    load := load
    unit_le := ⟨b2, ?_⟩
    A' := TT.A'
    E := TT.E
    U1 := TT.U1
    U1_pos := TT.U1_pos
    num := pieceNum TT k
    D := (v ^ bY) ^ 4
    steps := (v ^ bY) ^ 15
    sys := TT.sys
    plan := TT.plan
    cap := TT.cap
    ok := TT.ok
    isLaw := TT.isLaw
    relay_kind := fun x hx => by simpa [hx] using TT.kinds x
    good_iff := TT.good_iff
    poss_good := TT.poss_good
    grp := fun n o => pieceFin TT k n o
    tab := tab
    tab_valid := htab
    digits := ⟨g1, g2, g3, ?_⟩
    kinds_mem := fun r => ?_
    outcomes_le := hNc.trans (hMN.trans (vp (by omega)))
    num_le := ?_
    blocks_le := fun n o hn hg g => ?_
    cut_le := fun n o hn hg g => ?_
    all_le := fun n o hn hg g => ?_
    steps_le := ?_
    value := fun i e' u ℓ' hℓ hu => ?_ }⟩
  · rw [← hL, Nat.mul_comm T]
    refine b3.trans (Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (const_mul_pow_le (e := 0) hL2 (show 4 * c + 4 + 0 ≤ C by omega))))
    simp
  · exact Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by omega))
  · have hk' : TT.sys.kind r.1 ∈ relay A :: (univ : Finset VL.Di).toList.map VL.L := by
      have h1 := TT.kinds r.1
      split_ifs at h1 with hl
      · obtain ⟨L', h2, h4⟩ := List.mem_map.1 h1
        rw [← h4]
        exact List.mem_cons_of_mem _ h2
      · rw [h1]
        exact List.mem_cons_self
    exact List.mem_flatMap.2 ⟨_, hk', List.mem_map.2 ⟨r.2, by simp, rfl⟩⟩
  · refine (min_le_left _ _).trans ?_
    rw [← hL]
    calc 1 + C₀ + 2 ^ ee h * (TT.depth * k) ≤ (1 + C₀) * (L ^ C₀ * k) + 2 ^ ee h * (Ee * L ^ C₀ * k) :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.mul_pos hL1 (by omega)))
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdep))
      _ = k * ((1 + C₀ + 2 ^ ee h * Ee) * L ^ C₀) := by ring
      _ ≤ k * L ^ C := Nat.mul_le_mul_left _ (const_mul_pow_le hL2 (by omega))
  · refine (piece_blocks hn hg hK0 le_rfl (by omega) hkM g).trans ?_
    calc 4 * (K + K) = 8 * K := by ring
      _ ≤ C * K := Nat.mul_le_mul_right _ (by omega)
  · refine hWC _ ?_
    have h1 := piece_cut hn hg hK0 le_rfl (by omega) hk64 hnode g
    calc _ = _ * v ^ 300 * ub := by ring
      _ ≤ (yhat load (K + K) C₀ + (K + K) ^ C₀ * v ^ 300) * ub := Nat.mul_le_mul_right _ h1
      _ = yhat load (K + K) C₀ * ub + (K + K) ^ C₀ * v ^ 300 * ub := by ring
      _ ≤ 2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T) + 1 * L ^ C₀ * (K * T) :=
          Nat.add_le_add hYub (b5.trans (hKT.trans (Nat.le_mul_of_pos_left _ (by omega))))
      _ = (2 * (4 * c + 5) * Ee + 1) * L ^ C₀ * (K * T) := by ring
      _ ≤ _ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          rw [hW]
          nlinarith
  · refine hWC _ ?_
    have h1 := piece_all hn hg hK0 le_rfl (by omega) hk64 hnode hkM g
    have h2 : (K + K) ^ C₀ * k * ub ≤ T := (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk64)).trans b5
    calc _ = _ * k * ub := by ring
      _ ≤ (C₀ * (4 * yhat load (K + K) C₀) + 4 * (K + K) * (lg (K + K) ^ C₀ * load) + 2 * C₀ * (K + K) ^ C₀ * k) * ub :=
          Nat.mul_le_mul_right _ h1
      _ = 4 * C₀ * (yhat load (K + K) C₀ * ub) + 8 * K * lg (K + K) ^ C₀ * (load * ub) +
          2 * C₀ * ((K + K) ^ C₀ * k * ub) := by ring
      _ ≤ 4 * C₀ * (2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T)) + 8 * K * (Ee * L ^ C₀) * ((4 * c + 4) * T) +
          2 * C₀ * (1 * L ^ C₀ * (K * T)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hYub) (Nat.mul_le_mul (Nat.mul_le_mul_left _ hPL) b3))
            (Nat.mul_le_mul_left _ (h2.trans (hKT.trans (Nat.le_mul_of_pos_left _ (by omega)))))
      _ = (8 * C₀ * (4 * c + 5) * Ee + 8 * (4 * c + 4) * Ee + 2 * C₀) * L ^ C₀ * (K * T) := by ring
      _ ≤ _ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          rw [hW]
          nlinarith [Nat.zero_le (C₀ * c * Ee)]
  · obtain ⟨-, -, -, -, -, -, d3, d4, d5, -⟩ := TT.computed
    have hMY := hMN.trans (vp (show (e + a' + 2) * C₀ ≤ C by omega))
    refine ⟨?_, ?_, d3.trans hMY, d4.trans hMY, b6.trans (vp (by omega)), d5.trans hMY⟩
    · rw [← pow_mul]
      exact vp (by omega)
    · rw [← pow_mul]
      exact vp (by omega)
  · have hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ load := by rwa [← hσ]
    obtain ⟨hr1, hr2⟩ := lem_runnet (U0 := load) (U1 := TT.U1) (A' := TT.A') mu cb hcb hc0 b1 hU TT.sys.np i e' u hℓ hu
    rw [hr1]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun ρ _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load
    · rw [if_pos hn]
      exact prop_pieces_identity hn fun o => pieceFin TT k n o
    · rw [if_neg hn]
      push Not at hn
      obtain ⟨p, hp⟩ := hn
      unfold posVal
      refine Finset.sum_eq_zero fun y _ => ?_
      split_ifs
      swap
      · rfl
      refine Finset.prod_eq_zero (mem_univ p) ?_
      by_contra h0
      have := hr2 q (fun s => ρ s p) n p _ h0
      rw [← hσ, ← hload] at this
      exact absurd this (not_le.2 hp)

end Paper
end

open Finset Nc Nc.Tow Nc.Vp Paper
open Nc.Tower (ee)
theorem solution {A : Type} [CommRing A] {h : ℕ} [NeZero h] (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a e : ℕ, 300 ≤ e ∧ ∀ (Γ S Q : Type) [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
      (mu : Nc.Letter S Unit Γ → Matrix Q Q A),
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧
        ∀ T k, v ^ a ≤ T → 2 ≤ k → k ≤ v ^ 64 →
          Nonempty (PieceCut (kindList A ((univ : Finset VL.Di).toList.map VL.L)) mu (2 ^ ee h)
            (goodBound VL.C₁ VL.a₁) v K T k C) := Paper.prop_pieces VL h3 hgain
