-- Prove2me | solution 1 for ValiantBorder.lawThinTrees
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:36:01.177418+00:00
-- url     : https://prove2.me/submissions/5c28c3a9-c078-46f5-9ee8-7c6817b7122d

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_thinTrees
import Theorems.Thm_ValiantBorder_lawTowers
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




noncomputable def hat (f : Series F (Z × Γ)) (v : Z → List Γ) : F := ∑ o ∈ fib v, f o


def anti (v : Z → List Γ) : Finset ((Z → List Γ) × (Z → List Γ)) :=
  (Fintype.piFinset fun z => range ((v z).length + 1)).image fun k =>
    (fun z => (v z).take (k z), fun z => (v z).drop (k z))














def Series.ne (f : Series F (Z × Γ)) : Series F (Z × Γ) := fun o => if o = [] then 0 else f o








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



section Loop

variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def Series.body (wd : κ → List (Z × Γ)) (c : κ → F) : Series F (Z × Γ) :=
  ∑ k, c k • Series.word (wd k)

theorem RatLe.body (wd : κ → List (Z × Γ)) (c : κ → F) :
    RatLe (∑ k, (2 * (wd k).length + 1)) (Series.body wd c) :=
  RatLe.sum _ _ _ fun k _ => (RatLe.word (wd k)).smul (c k)



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




noncomputable def val (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : F :=
  ∑ W ∈ contents S Γ t, hat P (tup W u)


def Bdd (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : Prop :=
  ∀ W, hat P (tup W u) ≠ 0 → ∑ s, (W s).length ≤ t



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







end Nc
end
/- Source module Nc.Cut.Blocks. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]
























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





theorem RowOk.flag {d : RowData A} {X : Fin A → List Γ} (h : RowOk d X) {b : Fin A} (hb : X b ≠ []) :
    d.1 = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [RowOk, if_pos hc] at h
  exact hb (h b)





noncomputable def hiBefore (X : Fin A → Fin A → List Γ) (q : ℕ) : ℕ :=
  open Classical in (univ.filter fun z : Fin A × Fin A => z.1.1 < q ∧ X z.1 z.2 ≠ []).sup fun z => z.2.1








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







variable {c : ℕ} {cb : Option Γ → Fin c → Bool}





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











end Cat

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ)




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




end Party


noncomputable def segW (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p)


noncomputable def segs (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T



variable {mu T}






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
/- Source module Nc.Tow.Load. -/
section
namespace Nc.Tow

open Finset

variable {h b D J r : ℕ} (T : Tower h b D J r)

namespace Tower


def be {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (c : T.X j) : ℕ :=
  ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e else 0


def nEnd {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : ℕ :=
  ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0


noncomputable def kap {j : ℕ} (n : T.Ed j → ℕ) : ℝ :=
  √((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e, (n e : ℝ) ^ 2)

variable {T}

theorem kap_nonneg {j : ℕ} (n : T.Ed j → ℕ) : 0 ≤ T.kap n := Real.sqrt_nonneg _

theorem kap_sq {j : ℕ} (n : T.Ed j → ℕ) :
    T.kap n ^ 2 = (r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e, (n e : ℝ) ^ 2 :=
  Real.sq_sqrt (mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => sq_nonneg _))

theorem card_V {j : ℕ} (hj : j ≤ J) (i : Fin h) : Fintype.card (T.V j i) * b = Fintype.card (T.X j) := by
  rw [Fintype.card_of_bijective (T.vx_co hj i), Fintype.card_prod, T.card_fl]


theorem sq_sum_le {κ : Type*} (s : Finset κ) (f : κ → ℝ) {k : ℕ} (hk : s.card ≤ k) :
    (∑ x ∈ s, f x) ^ 2 ≤ k * ∑ x ∈ s, f x ^ 2 := by
  refine (sq_sum_le_card_mul_sum_sq (s := s) (f := f)).trans ?_
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Finset.sum_nonneg fun x _ => sq_nonneg _)

section Stage

variable {j : ℕ} {i : Fin h} {n : T.Ed j → ℕ}


theorem mid_le (hj : j < J) {n' : T.Ed (j + 1) → ℕ}
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e) :
    ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      D * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := by
  have h1 : ∀ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      D * ∑ e ∈ univ.filter (fun e => T.πE e = e'), (n e : ℝ) ^ 2 := by
    intro e' he'
    have h2 := hmid e' (mem_filter.1 he').2
    have h3 : (n' e' : ℝ) ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), (n e : ℝ) := by exact_mod_cast h2
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2).trans ?_
    exact sq_sum_le _ _ (T.fibre hj e')
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun e : T.Ed j => T.ty e = i)
    (t := univ.filter fun e' : T.Ed (j + 1) => T.ty e' = i) (g := T.πE) (f := fun e => (n e : ℝ) ^ 2)]
  · refine Finset.sum_congr rfl fun e' he' => Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hh
      refine ⟨?_, hh⟩
      rw [← T.π_ty hj e, hh]
      exact (mem_filter.1 he').2
    · exact fun hh => hh.2
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [T.π_ty hj e, he]


theorem sum_be_sq (hj : j ≤ J) : ∑ c, (T.be i n c : ℝ) ^ 2 ≤
    2 * r * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := by
  have h1 : ∀ c, (T.be i n c : ℝ) ^ 2 ≤
      r * ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0 := by
    intro c
    have e1 : (T.be i n c : ℝ) = ∑ e ∈ univ.filter (fun e => T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c)), (n e : ℝ) := by
      unfold be
      rw [Finset.sum_filter]
      push_cast
      rfl
    rw [e1, ← Finset.sum_filter]
    exact sq_sum_le _ _ (T.deg j hj c i)
  refine (Finset.sum_le_sum fun c _ => h1 c).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ e : T.Ed j, (∑ c, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0) =
      if T.ty e = i then 2 * (n e : ℝ) ^ 2 else 0 := by
    intro e
    by_cases ht : T.ty e = i
    · rw [if_pos ht]
      have h3 : ∀ c, (if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then (n e : ℝ) ^ 2 else 0) =
          (if T.e0 e = c then (n e : ℝ) ^ 2 else 0) + if T.e1 e = c then (n e : ℝ) ^ 2 else 0 := by
        intro c
        have hne := T.e_ne e
        by_cases h0 : T.e0 e = c
        · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
          simp [ht, h0, h1]
        · by_cases h1 : T.e1 e = c <;> simp [ht, h0, h1]
      rw [Finset.sum_congr rfl fun c _ => h3 c, Finset.sum_add_distrib]
      simp
      ring
    · rw [if_neg ht]
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => ht hh.1
  rw [Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun e _ => ?_)
  split_ifs <;> ring


theorem card_two (hj : j < J) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q).card ≤ 2 := by
  induction q using Sym2.inductionOn with
  | _ f f' =>
    have h1 : (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
        s(T.co i (T.host i (T.vx i c)), T.co i c) = s(f, f')).card ≤ ({(f, f'), (f', f)} : Finset (T.Fl × T.Fl)).card := by
      refine card_le_card_of_injOn (fun c => (T.co i (T.host i (T.vx i c)), T.co i c)) ?_ ?_
      · intro c hc
        have := (mem_filter.1 (mem_coe.1 hc)).2.2
        rw [Sym2.eq_iff] at this
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        exact this
      · intro c hc c' hc' heq
        simp only [Prod.mk.injEq] at heq
        have hv := (mem_filter.1 (mem_coe.1 hc)).2.1
        have hv' := (mem_filter.1 (mem_coe.1 hc')).2.1
        have hh : T.host i (T.vx i c) = T.host i (T.vx i c') := by
          apply (T.vx_co (Nat.succ_le_of_lt hj) i).1
          simp only [Prod.mk.injEq]
          refine ⟨?_, heq.1⟩
          rw [T.host_vx hj, T.host_vx hj, hv, hv']
        have hvx := T.host_inj hj i hh
        apply (T.vx_co hj.le i).1
        simp only [Prod.mk.injEq]
        exact ⟨hvx, heq.2⟩
    exact h1.trans card_le_two


theorem sum_end_sq (hj : j < J) :
    ∑ ω, ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 ≤ 2 * ∑ c, (T.be i n c : ℝ) ^ 2 := by
  have h1 : ∀ ω q, (T.nEnd i n ω q : ℝ) ^ 2 ≤ 2 * ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then (T.be i n c : ℝ) ^ 2 else 0 := by
    intro ω q
    have e1 : (T.nEnd i n ω q : ℝ) = ∑ c ∈ univ.filter (fun c : T.X j => T.πV (T.vx i c) = ω ∧
        s(T.co i (T.host i (T.vx i c)), T.co i c) = q), (T.be i n c : ℝ) := by
      unfold nEnd
      rw [Finset.sum_filter]
      push_cast
      rfl
    rw [e1, ← Finset.sum_filter]
    have := sq_sum_le _ (fun c => (T.be i n c : ℝ)) (card_two (T := T) hj ω q)
    exact_mod_cast this
  refine (Finset.sum_le_sum fun ω _ => Finset.sum_le_sum fun q _ => h1 ω q).trans ?_
  simp only [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  have e2 : ∀ ω, (∑ q : Sym2 T.Fl, ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then (T.be i n c : ℝ) ^ 2 else 0) =
      ∑ c : T.X j, if T.πV (T.vx i c) = ω then (T.be i n c : ℝ) ^ 2 else 0 := by
    intro ω
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hω : T.πV (T.vx i c) = ω
    · simp [hω]
    · simp [hω]
  rw [Finset.sum_congr rfl fun ω _ => e2 ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

end Stage


theorem minkowski {κ : Type*} [Fintype κ] (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) :
    √(∑ x, (f x + a) ^ 2) ≤ √(∑ x, f x ^ 2) + √(Fintype.card κ) * a := by
  have h1 : 0 ≤ ∑ x, f x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have hcs : ∑ x, f x ≤ √(Fintype.card κ) * √(∑ x, f x ^ 2) := by
    rw [← Real.sqrt_mul hc]
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset κ)) (f := f)
    rwa [card_univ] at this
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have e1 : ∑ x, (f x + a) ^ 2 = ∑ x, f x ^ 2 + 2 * a * ∑ x, f x + Fintype.card κ * a ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : (√(∑ x, f x ^ 2) + √(Fintype.card κ) * a) ^ 2 =
      ∑ x, f x ^ 2 + 2 * a * (√(Fintype.card κ) * √(∑ x, f x ^ 2)) + Fintype.card κ * a ^ 2 := by
    rw [add_sq, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt hc]
    ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hcs (by linarith : 0 ≤ 2 * a)
  linarith

theorem alg {C N y k : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hy : 0 ≤ y) (hk : k ^ 2 ≤ N ^ 2 + C * (√8 * N + y) ^ 2) :
    k ≤ √(1 + 8 * C) * N + √C * y := by
  have hS0 : 0 ≤ √(1 + 8 * C) := Real.sqrt_nonneg _
  have hS2 : √(1 + 8 * C) ^ 2 = 1 + 8 * C := Real.sq_sqrt (by linarith)
  have hc0 : 0 ≤ √C := Real.sqrt_nonneg _
  have hc2 : √C ^ 2 = C := Real.sq_sqrt hC
  have h82 : (√8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hcross : √C * √8 ≤ √(1 + 8 * C) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hc2, h82]
    linarith
  generalize √(1 + 8 * C) = S at *
  generalize hs : √C = s at *
  generalize (√8 : ℝ) = e at *
  have h0 : 0 ≤ S * N + s * y := by positivity
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  refine hk.trans ?_
  have e1 : C * (e * N + y) ^ 2 = 8 * C * N ^ 2 + 2 * (s * (s * e) * (N * y)) + C * y ^ 2 := by
    have : C * (e * N + y) ^ 2 = e ^ 2 * C * N ^ 2 + 2 * (C * e * (N * y)) + C * y ^ 2 := by ring
    rw [this, h82, ← hc2]
    ring
  have e2 : (S * N + s * y) ^ 2 = (1 + 8 * C) * N ^ 2 + 2 * (s * S * (N * y)) + C * y ^ 2 := by
    have : (S * N + s * y) ^ 2 = S ^ 2 * N ^ 2 + 2 * (s * S * (N * y)) + s ^ 2 * y ^ 2 := by ring
    rw [this, hS2, hc2]
  have h1 : s * (s * e) ≤ s * S := mul_le_mul_of_nonneg_left hcross hc0
  have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hN hy)
  rw [e1, e2]
  linarith

theorem NN2_nonneg (hb : 0 < b) (m : Sym2 T.Fl → ℕ) : 0 ≤ T.NN2 m := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold NN2
  refine mul_nonneg ?_ (Finset.sum_nonneg fun q _ => ?_)
  · have : (0 : ℝ) ≤ b - 1 := by linarith
    positivity
  · split_ifs
    · exact le_rfl
    · exact sq_nonneg _


theorem end_norm {j : ℕ} (hj : j < J) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h} {n : T.Ed j → ℕ} :
    (Fintype.card (T.X (j + 1)) : ℝ) / b * ∑ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤
      8 * ((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hDb : (b : ℝ) ≤ 2 * D := by exact_mod_cast hbD
  have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hj
  rw [hcX]
  have h6 := sum_end_sq (T := T) (n := n) (i := i) hj
  have h7 := sum_be_sq (T := T) (n := n) (i := i) hj.le
  set Pn : ℝ := ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 with hP
  have hP0 : 0 ≤ Pn := Finset.sum_nonneg fun e _ => sq_nonneg _
  set x : ℝ := (Fintype.card (T.X (j + 1)) : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have h1 : ∀ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤ (b : ℝ) ^ 2 / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
    intro ω
    rw [Real.sq_sqrt (NN2_nonneg hb _)]
    unfold NN2
    have h2 : (∑ q : Sym2 T.Fl, if q.IsDiag then (0 : ℝ) else (T.nEnd i n ω q : ℝ) ^ 2) ≤
        ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun q _ => ?_
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    have h3 : (0 : ℝ) ≤ ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
    have h4 : (b : ℝ) * (b - 1) / 2 ≤ (b : ℝ) ^ 2 / 2 := by nlinarith
    have h5 : (0 : ℝ) ≤ (b : ℝ) * (b - 1) / 2 := by
      have : (0 : ℝ) ≤ b - 1 := by linarith
      positivity
    calc _ ≤ (b : ℝ) * (b - 1) / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h5
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 h3
  have hrP : (0 : ℝ) ≤ r * x * Pn := by positivity
  calc x / b * ∑ ω, √(T.NN2 (T.nEnd i n ω)) ^ 2 ≤
      x / b * ∑ ω, (b : ℝ) ^ 2 / 2 * ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => h1 ω) (by positivity)
    _ = x * b / 2 * ∑ ω, ∑ q : Sym2 T.Fl, (T.nEnd i n ω q : ℝ) ^ 2 := by
        rw [← Finset.mul_sum]
        field_simp
    _ ≤ x * b / 2 * (2 * (2 * r * Pn)) :=
        mul_le_mul_of_nonneg_left (h6.trans (by linarith)) (by positivity)
    _ = 2 * (r * x * Pn) * b := by ring
    _ ≤ 2 * (r * x * Pn) * (2 * D) := mul_le_mul_of_nonneg_left hDb (by positivity)
    _ = _ := by ring


theorem other_le {j : ℕ} (hj : j < J) (hr : 0 < r) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h}
    {n : T.Ed j → ℕ} {n' : T.Ed (j + 1) → ℕ} {C₁ a₁ N : ℝ} (hC : 0 ≤ C₁) (ha : 0 ≤ a₁) (hN0 : 0 ≤ N)
    (hN2 : N ^ 2 = (r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
    (t : T.V (j + 1) i → ℕ)
    (hal : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr (Nat.succ_le_of_lt hj) i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2)
    (ht : ∀ ω, a₁ * t ω ≤ √(T.NN2 (T.nEnd i n ω)) + a₁) :
    (r : ℝ) * Fintype.card (T.X (j + 1)) / 2 * ∑ e' ∈ univ.filter (fun e' => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 ≤
      C₁ * (√8 * N + a₁ * (Fintype.card (T.X (j + 1)) / b)) ^ 2 := by
  have hj' := Nat.succ_le_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hfsq := end_norm (T := T) (n := n) (i := i) hj hb hbD
  rw [← hN2] at hfsq
  set x : ℝ := (Fintype.card (T.X (j + 1)) : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hcV : (Fintype.card (T.V (j + 1) i) : ℝ) = x / b := by
    rw [hx, eq_div_iff hbR.ne']; exact_mod_cast card_V hj' i
  have hxb : 0 ≤ x / b := by positivity
  set f : T.V (j + 1) i → ℝ := fun ω => √(T.NN2 (T.nEnd i n ω)) with hf
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => Real.sqrt_nonneg _
  have e1 : ∑ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 =
      ∑ ω, ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 := by
    rw [← Fintype.sum_prod_type' (f := fun ω ν => (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2)]
    rw [← Equiv.sum_comp (T.nr hj' i) (fun p => (n' ((T.nr hj' i).symm p).1 : ℝ) ^ 2)]
    simp only [Equiv.symm_apply_apply]
    exact (Finset.sum_subtype (univ.filter fun e' : T.Ed (j + 1) => ¬ T.ty e' = i) (p := fun e' => T.ty e' ≠ i)
      (by simp) fun e' => (n' e' : ℝ) ^ 2)
  rw [e1]
  have h1 : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 ≤ C₁ * (f ω + a₁) ^ 2 := by
    intro ω
    refine (hal ω).trans ?_
    have h2 : (a₁ * (t ω : ℝ)) ^ 2 ≤ (f ω + a₁) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg ha (Nat.cast_nonneg _)) (ht ω) 2
    calc C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2 = C₁ * (a₁ * (t ω : ℝ)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC
  have h3 : (r : ℝ) * x / 2 * ∑ ω, ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 =
      x / b * ∑ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 := by
    rw [← Finset.mul_sum]
    field_simp
  rw [h3]
  have h4 : x / b * ∑ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr hj' i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * (x / b * ∑ ω, (f ω + a₁) ^ 2) := by
    calc _ ≤ x / b * ∑ ω, C₁ * (f ω + a₁) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => h1 ω) hxb
      _ = _ := by rw [← Finset.mul_sum]; ring
  refine h4.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hs0 : 0 ≤ ∑ ω, (f ω + a₁) ^ 2 := Finset.sum_nonneg fun ω _ => sq_nonneg _
  have h5 : √(x / b * ∑ ω, (f ω + a₁) ^ 2) ≤ √8 * N + a₁ * (x / b) := by
    rw [Real.sqrt_mul hxb]
    have h6 := minkowski f hf0 ha
    rw [hcV] at h6
    have h7 := mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg (x / b))
    refine h7.trans ?_
    rw [mul_add, ← Real.sqrt_mul hxb, ← mul_assoc, Real.mul_self_sqrt hxb]
    have h8 : √(x / b * ∑ ω, f ω ^ 2) ≤ √8 * N := by
      rw [← Real.sqrt_sq hN0, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hfsq
    linarith
  calc x / b * ∑ ω, (f ω + a₁) ^ 2 = √(x / b * ∑ ω, (f ω + a₁) ^ 2) ^ 2 :=
        (Real.sq_sqrt (mul_nonneg hxb hs0)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2


theorem load_step {j : ℕ} (hj : j < J) (hr : 0 < r) (hb : 0 < b) (hbD : b ≤ 2 * D) {i : Fin h}
    {n : T.Ed j → ℕ} {n' : T.Ed (j + 1) → ℕ} {C₁ a₁ ρ : ℝ} (hC : 0 ≤ C₁) (ha : 0 ≤ a₁) (hρ : 0 ≤ ρ)
    (hρ1 : 1 + 8 * C₁ ≤ ρ ^ 2 * h)
    (hi : (h : ℝ) * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 ≤ ∑ e, (n e : ℝ) ^ 2)
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e)
    (t : T.V (j + 1) i → ℕ)
    (hal : ∀ ω, (r : ℝ) * b / 2 * ∑ ν, (n' ((T.nr (Nat.succ_le_of_lt hj) i).symm (ω, ν)).1 : ℝ) ^ 2 ≤
      C₁ * a₁ ^ 2 * (t ω : ℝ) ^ 2)
    (ht : ∀ ω, a₁ * t ω ≤ √(T.NN2 (T.nEnd i n ω)) + a₁) :
    T.kap n' ≤ ρ * T.kap n + √C₁ * a₁ / b * Fintype.card (T.X (j + 1)) := by
  have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hj
  have hP0 : 0 ≤ ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hA : (0 : ℝ) ≤ (r : ℝ) * Fintype.card (T.X j) / 2 := by positivity
  have hN0 := Real.sqrt_nonneg ((r : ℝ) * Fintype.card (T.X j) / 2 *
    ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
  have hN2 := Real.sq_sqrt (mul_nonneg hA hP0)
  set N : ℝ := √((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) with hN
  have hother := other_le hj hr hb hbD hC ha hN0 hN2 t hal ht
  have hm' : (r : ℝ) * Fintype.card (T.X (j + 1)) / 2 *
      ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 ≤ N ^ 2 := by
    rw [hN2, hcX]
    have := mul_le_mul_of_nonneg_left (mid_le hj hmid)
      (by positivity : 0 ≤ (r : ℝ) * Fintype.card (T.X (j + 1)) / 2)
    refine this.trans (le_of_eq ?_)
    ring
  have hsum : ∑ e', (n' e' : ℝ) ^ 2 = ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), (n' e' : ℝ) ^ 2 +
      ∑ e' ∈ univ.filter (fun e' => ¬ T.ty e' = i), (n' e' : ℝ) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hk2 : T.kap n' ^ 2 ≤ N ^ 2 + C₁ * (√8 * N + a₁ * (Fintype.card (T.X (j + 1)) / b)) ^ 2 := by
    rw [kap_sq, hsum, mul_add]
    exact add_le_add hm' hother
  have hkap := alg hC hN0 (by positivity) hk2
  have hSN : √(1 + 8 * C₁) * N ≤ ρ * T.kap n := by
    have h0 : 0 ≤ ρ * T.kap n := mul_nonneg hρ (kap_nonneg n)
    refine (abs_le_of_sq_le_sq' ?_ h0).2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + 8 * C₁), hN2, kap_sq]
    calc (1 + 8 * C₁) * ((r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2)
        ≤ (ρ ^ 2 * h) * ((r : ℝ) * Fintype.card (T.X j) / 2 *
          ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hA hP0)
      _ = ρ ^ 2 * ((r : ℝ) * Fintype.card (T.X j) / 2) *
          (h * ∑ e ∈ univ.filter (fun e => T.ty e = i), (n e : ℝ) ^ 2) := by ring
      _ ≤ ρ ^ 2 * ((r : ℝ) * Fintype.card (T.X j) / 2) * ∑ e, (n e : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hi (mul_nonneg (sq_nonneg _) hA)
      _ = _ := by ring
  have e3 : √C₁ * (a₁ * (Fintype.card (T.X (j + 1)) / b)) = √C₁ * a₁ / b * Fintype.card (T.X (j + 1)) := by ring
  linarith

end Tower

end Nc.Tow
end
/- Source module Nc.Tow.Relay. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section Relay

variable (F : Type) [CommRing F]

end Relay


theorem exists_mono_equiv {κ : Type} [Fintype κ] (time : κ → ℕ) :
    ∃ e : Fin (Fintype.card κ) ≃ κ, ∀ x y, time x < time y → e.symm x < e.symm y := by
  classical
  let e0 := (Fintype.equivFin κ).symm
  let σ := Tuple.sort (time ∘ e0)
  refine ⟨σ.trans e0, fun x y hxy => ?_⟩
  have hm : Monotone ((time ∘ e0) ∘ σ) := Tuple.monotone_sort _
  by_contra hn
  have h1 := hm (not_lt.1 hn)
  simp only [Function.comp_apply] at h1
  have h2 : ∀ z, e0 (σ ((σ.trans e0).symm z)) = z := fun z => (σ.trans e0).apply_symm_apply z
  rw [h2, h2] at h1
  omega

end Nc.Tow
end
/- Source module Nc.Tow.Path. -/
section
namespace Nc.Tow

open Finset

namespace Tower

variable {h b D J r : ℕ} {T : Tower h b D J r} {j : ℕ}

theorem step_ends (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) :
    s(T.e0 e, T.e1 e) = s(c, T.step e c) := by
  unfold step
  by_cases h0 : T.e0 e = c
  · rw [if_pos h0, h0]
  · have h1 : T.e1 e = c := hc.resolve_left h0
    rw [if_neg h0, h1, Sym2.eq_swap]

theorem step_ne (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) : c ≠ T.step e c := by
  intro heq
  have h1 := step_ends e hc
  rw [← heq, Sym2.eq_iff] at h1
  have := T.e_ne e
  rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> exact this (h2.trans h3.symm)

theorem step_mem (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) :
    T.e0 e = T.step e c ∨ T.e1 e = T.step e c := by
  have h1 := step_ends e hc
  rw [Sym2.eq_iff] at h1
  rcases h1 with ⟨_, h3⟩ | ⟨h2, _⟩
  · exact Or.inr h3
  · exact Or.inl h2

theorem step_step (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) : T.step e (T.step e c) = c := by
  have h1 := step_ends e hc
  have h2 := step_ends e (step_mem e hc)
  rw [h1, Sym2.eq_iff] at h2
  rcases h2 with ⟨h3, h4⟩ | ⟨h3, _⟩
  · exact h4.symm.trans h3.symm
  · exact h3.symm


def nodeAt (c : T.X j) (l : List (T.Ed j)) (s : ℕ) : T.X j := (l.take s).foldl (fun c e => T.step e c) c

theorem nodeAt_cons (c : T.X j) (e : T.Ed j) (l : List (T.Ed j)) (s : ℕ) :
    nodeAt c (e :: l) (s + 1) = nodeAt (T.step e c) l s := rfl

theorem walk_end {c c' : T.X j} {l : List (T.Ed j)} (hw : T.Walk c l c') : nodeAt c l l.length = c' := by
  induction l generalizing c with
  | nil => exact hw
  | cons e l ih =>
    rw [List.length_cons, nodeAt_cons]
    exact ih hw.2

theorem walk_step {c c' : T.X j} {l : List (T.Ed j)} (hw : T.Walk c l c') {s : ℕ} {e : T.Ed j}
    (he : l[s]? = some e) : (T.e0 e = nodeAt c l s ∨ T.e1 e = nodeAt c l s) ∧
      nodeAt c l (s + 1) = T.step e (nodeAt c l s) := by
  induction l generalizing c s with
  | nil => simp at he
  | cons e' l ih =>
    cases s with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      exact ⟨hw.1, rfl⟩
    | succ s =>
      simp only [List.getElem?_cons_succ] at he
      rw [nodeAt_cons, nodeAt_cons]
      exact ih hw.2 he

theorem walk_append {c c' c'' : T.X j} {l l' : List (T.Ed j)} (h1 : T.Walk c l c') (h2 : T.Walk c' l' c'') :
    T.Walk c (l ++ l') c'' := by
  induction l generalizing c with
  | nil =>
    have : c = c' := h1
    subst this
    exact h2
  | cons e l ih => exact ⟨h1.1, ih h1.2⟩

theorem walk_reverse {c c' : T.X j} {l : List (T.Ed j)} (h1 : T.Walk c l c') : T.Walk c' l.reverse c := by
  induction l generalizing c with
  | nil => exact h1.symm
  | cons e l ih =>
    rw [List.reverse_cons]
    refine walk_append (ih h1.2) ⟨step_mem e h1.1, ?_⟩
    exact step_step e h1.1

end Tower

namespace Routes

variable {h b D J r : ℕ} {T : Tower h b D J r} {m Uu : ℕ} (R : Routes T m Uu)


def path (c c' γ : T.X 0) : List (T.Ed 0) := R.rt c γ ++ (R.rt c' γ).reverse

theorem path_walk (c c' γ : T.X 0) : T.Walk c (R.path c c' γ) c' :=
  Tower.walk_append (R.walk c γ) (Tower.walk_reverse (R.walk c' γ))

theorem length_path (c c' γ : T.X 0) : (R.path c c' γ).length ≤ 2 * m := by
  rw [path, List.length_append, List.length_reverse]
  have := R.len c γ
  have := R.len c' γ
  omega

theorem exists_end (c c' γ : T.X 0) : ∃ s, Tower.nodeAt c (R.path c c' γ) s = c' :=
  ⟨_, Tower.walk_end (R.path_walk c c' γ)⟩


def pl (c c' γ : T.X 0) : ℕ := Nat.find (R.exists_end c c' γ)


def pn (c c' γ : T.X 0) (s : ℕ) : T.X 0 := Tower.nodeAt c (R.path c c' γ) s

theorem pn_pl (c c' γ : T.X 0) : R.pn c c' γ (R.pl c c' γ) = c' := Nat.find_spec (R.exists_end c c' γ)

theorem pn_ne (c c' γ : T.X 0) {s : ℕ} (hs : s < R.pl c c' γ) : R.pn c c' γ s ≠ c' :=
  Nat.find_min (R.exists_end c c' γ) hs

theorem pl_le (c c' γ : T.X 0) : R.pl c c' γ ≤ (R.path c c' γ).length :=
  Nat.find_min' _ (Tower.walk_end (R.path_walk c c' γ))

theorem pl_pos {c c' : T.X 0} (hne : c ≠ c') (γ : T.X 0) : 0 < R.pl c c' γ := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have := R.pn_pl c c' γ
  rw [h0] at this
  exact hne this


theorem exists_edge (c c' γ : T.X 0) {s : ℕ} (hs : s < R.pl c c' γ) :
    ∃ e, (R.path c c' γ)[s]? = some e ∧ s(T.e0 e, T.e1 e) = s(R.pn c c' γ s, R.pn c c' γ (s + 1)) ∧
      R.pn c c' γ s ≠ R.pn c c' γ (s + 1) := by
  have hlt : s < (R.path c c' γ).length := lt_of_lt_of_le hs (R.pl_le c c' γ)
  refine ⟨(R.path c c' γ)[s], List.getElem?_eq_getElem hlt, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Tower.walk_step (R.path_walk c c' γ) (List.getElem?_eq_getElem hlt)
    unfold pn
    rw [h2]
    exact Tower.step_ends _ h1
  · obtain ⟨h1, h2⟩ := Tower.walk_step (R.path_walk c c' γ) (List.getElem?_eq_getElem hlt)
    unfold pn
    rw [h2]
    exact Tower.step_ne _ h1

end Routes

end Nc.Tow
end
/- Source module Nc.Tow.Net. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ}


abbrev Nd (T : Tower h b D J r) := Option (Σ j : Fin (J + 1), T.X j)


def nd (T : Tower h b D J r) (j : ℕ) (hj : j ≤ J) (c : T.X j) : Nd T := some ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩

theorem nd_inj {T : Tower h b D J r} {j : ℕ} {hj hj' : j ≤ J} {c c' : T.X j} :
    nd T j hj c = nd T j hj' c' ↔ c = c' := by
  unfold nd
  rw [Option.some_inj, Sigma.mk.injEq]
  simp

theorem nd_ne {T : Tower h b D J r} {j j' : ℕ} (hjj : j ≠ j') {hj : j ≤ J} {hj' : j' ≤ J} {c : T.X j} {c' : T.X j'} :
    nd T j hj c ≠ nd T j' hj' c' := by
  unfold nd
  rw [Ne, Option.some_inj, Sigma.mk.injEq]
  rintro ⟨h1, -⟩
  exact hjj (congrArg Fin.val h1)

theorem nd_ne_none {T : Tower h b D J r} {j : ℕ} {hj : j ≤ J} {c : T.X j} : nd T j hj c ≠ none := by
  unfold nd; exact Option.some_ne_none _


inductive RM (T : Tower h b D J r) (m AA : ℕ) where
  
  | start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m))
  
  | inn (j : Fin J) (i : Fin h) (e : T.Ed j)
  
  | mid (j : Fin J) (e : T.Ed j) (s : Fin 4)
  
  | fin (e : T.Ed J)


def rmEquiv (T : Tower h b D J r) (m AA : ℕ) : RM T m AA ≃ (Fin AA × Fin AA × T.X 0 × Fin (2 * m)) ⊕
    ((Σ j : Fin J, Fin h × T.Ed j) ⊕ ((Σ j : Fin J, T.Ed j × Fin 4) ⊕ T.Ed J)) where
  toFun
    | .start a c γ s => .inl (a, c, γ, s)
    | .inn j i e => .inr (.inl ⟨j, i, e⟩)
    | .mid j e s => .inr (.inr (.inl ⟨j, e, s⟩))
    | .fin e => .inr (.inr (.inr e))
  invFun
    | .inl x => .start x.1 x.2.1 x.2.2.1 x.2.2.2
    | .inr (.inl x) => .inn x.1 x.2.1 x.2.2
    | .inr (.inr (.inl x)) => .mid x.1 x.2.1 x.2.2
    | .inr (.inr (.inr e)) => .fin e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ <;> rfl

instance (T : Tower h b D J r) (m AA : ℕ) : Fintype (RM T m AA) := Fintype.ofEquiv _ (rmEquiv T m AA).symm


inductive Tg (T : Tower h b D J r) (m AA : ℕ) where
  
  | done
  
  | edge (j : Fin (J + 1)) (e : T.Ed j)
  
  | nxt (x : RM T m AA)
  
  | seg (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl)

noncomputable instance (T : Tower h b D J r) (m AA : ℕ) : DecidableEq (Tg T m AA) := Classical.decEq _

section

variable (T : Tower h b D J r) (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0)


abbrev hst {j : ℕ} (i : Fin h) (c : T.X j) : T.X (j + 1) := T.host i (T.vx i c)


def tri : RM T m AA → Fin 3 → Nd T
  | .start a c γ s => ![nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ s), nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ (s + 1)),
      nd T 0 (Nat.zero_le _) (ch c)]
  | .inn j i e => ![nd T j j.2.le (T.e0 e), nd T (j + 1) j.2 (hst T i (T.e0 e)), nd T j j.2.le (T.e1 e)]
  | .mid j e s =>
    let H := nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e))
    let H' := nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e))
    let p := nd T (j + 1) j.2 (T.π (T.e0 e))
    let p' := nd T (j + 1) j.2 (T.π (T.e1 e))
    ![![nd T j j.2.le (T.e0 e), H, p, p'] s, ![H, p, p', H'] s, nd T j j.2.le (T.e1 e)]
  | .fin e => ![nd T J le_rfl (T.e0 e), none, nd T J le_rfl (T.e1 e)]


def okR : RM T m AA → Prop
  | .start a c γ s => a ≠ c ∧ s.1 + 1 < R.pl (ch a) (ch c) γ
  | .inn _ i e => T.ty e ≠ i
  | .mid _ e s => (s = 1 → hst T (T.ty e) (T.e0 e) ≠ T.π (T.e0 e)) ∧ (s = 3 → T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e))
  | .fin _ => True

theorem inj3 {α : Type*} {x y z : α} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : Function.Injective ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

variable {T R ch}

theorem π_ne {j : ℕ} (hj : j < J) (e : T.Ed j) : T.π (T.e0 e) ≠ T.π (T.e1 e) := by
  intro heq
  have h1 := T.π_ends hj e
  rw [heq, Sym2.eq_iff] at h1
  have := T.e_ne (T.πE e)
  rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> exact this (h2.trans h3.symm)

theorem tri_inj {x : RM T m AA} (hx : okR T R ch x) : Function.Injective (tri T R ch x) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · obtain ⟨-, h2⟩ := hx
    refine inj3 ?_ ?_ ?_
    · rw [Ne, nd_inj]
      obtain ⟨e, -, -, h3⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by omega)
      exact h3
    · rw [Ne, nd_inj]
      exact R.pn_ne _ _ _ (by omega)
    · rw [Ne, nd_inj]
      exact R.pn_ne _ _ _ h2
  · exact inj3 (nd_ne (by omega)) (by rw [Ne, nd_inj]; exact T.e_ne e) (nd_ne (by omega))
  · refine inj3 ?_ ?_ ?_
    · fin_cases s
      · change nd T j j.2.le (T.e0 e) ≠ nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e))
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T (j + 1) j.2 (T.π (T.e0 e))
        rw [Ne, nd_inj]
        exact hx.1 rfl
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T (j + 1) j.2 (T.π (T.e1 e))
        rw [Ne, nd_inj]
        exact π_ne j.2 e
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e))
        rw [Ne, nd_inj]
        exact hx.2 rfl
    · fin_cases s
      · change nd T j j.2.le (T.e0 e) ≠ nd T j j.2.le (T.e1 e)
        rw [Ne, nd_inj]
        exact T.e_ne e
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
    · fin_cases s
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
  · exact inj3 nd_ne_none (by rw [Ne, nd_inj]; exact T.e_ne e) nd_ne_none.symm

variable (T R ch)


def edgeO : Option (T.Ed 0) → Tg T m AA
  | some e => .edge 0 e
  | none => .done

open Classical in

noncomputable def tgR : RM T m AA → Bool → Tg T m AA
  | .start a c γ s, false => edgeO T ((R.path (ch a) (ch c) γ)[s.1]?)
  | .start a c γ s, true =>
    if hs : s.1 + 1 < 2 * m ∧ s.1 + 2 < R.pl (ch a) (ch c) γ then .nxt (.start a c γ ⟨s.1 + 1, hs.1⟩)
    else edgeO T ((R.path (ch a) (ch c) γ)[s.1 + 1]?)
  | .inn _ _ _, _ => .done
  | .mid j e s, false =>
    ![.done, .seg j (T.ty e) (T.πV (T.vx (T.ty e) (T.e0 e))) s(T.co (T.ty e) (hst T (T.ty e) (T.e0 e)), T.co (T.ty e) (T.e0 e)),
      .edge j.succ (T.πE e),
      .seg j (T.ty e) (T.πV (T.vx (T.ty e) (T.e1 e))) s(T.co (T.ty e) (hst T (T.ty e) (T.e1 e)), T.co (T.ty e) (T.e1 e))] s
  | .mid j e s, true =>
    ![if hst T (T.ty e) (T.e0 e) ≠ T.π (T.e0 e) then .nxt (.mid j e 1) else .nxt (.mid j e 2),
      .nxt (.mid j e 2), if T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e) then .nxt (.mid j e 3) else .done, .done] s
  | .fin _, _ => .done


def inpR : RM T m AA → Tg T m AA
  | .inn j _ e => .edge j.castSucc e
  | .mid j e s => if s = 0 then .edge j.castSucc e else .nxt (.mid j e s)
  | .fin e => .edge (Fin.last J) e
  | x => .nxt x


def timeR : RM T m AA → ℕ
  | .start _ _ _ s => s
  | .inn j _ _ => 2 * m + 6 * j
  | .mid j _ s => 2 * m + 6 * j + s
  | .fin _ => 2 * m + 6 * J


noncomputable def gam (a : Fin AA) (k : ℕ) : T.X 0 :=
  (Fintype.equivFin (T.X 0)).symm ⟨k % Fintype.card (T.X 0), Nat.mod_lt _ (Fintype.card_pos_iff.2 ⟨ch a⟩)⟩

open Classical in

noncomputable def tgB (a c : Fin AA) (k : ℕ) : Tg T m AA :=
  if a = c then .done
  else if hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k) then .nxt (.start a c (gam T ch a k) ⟨0, hs.1⟩)
  else edgeO T ((R.path (ch a) (ch c) (gam T ch a k))[0]?)


abbrev LMv (FL : FlagLaws F T) := Σ j : Fin J, Σ i : Fin h, T.V (j + 1) i × FL.Di


abbrev Mv (FL : FlagLaws F T) := {x : RM T m AA // okR T R ch x} ⊕ LMv T FL

noncomputable instance (FL : FlagLaws F T) : Fintype (Mv T R ch FL) := by
  classical exact inferInstance

variable {T}


def kindM (FL : FlagLaws F T) : Mv T R ch FL → Law F
  | .inl _ => relay F
  | .inr l => FL.L l.2.2.2


noncomputable def atv {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.X j :=
  (Equiv.ofBijective _ (T.vx_co hj i)).symm (ω, f)

theorem atv_vx {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.vx i (atv hj i ω f) = ω := by
  have := (Equiv.ofBijective _ (T.vx_co hj i)).apply_symm_apply (ω, f)
  exact congrArg Prod.fst this

theorem atv_co {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.co i (atv hj i ω f) = f := by
  have := (Equiv.ofBijective _ (T.vx_co hj i)).apply_symm_apply (ω, f)
  exact congrArg Prod.snd this

theorem atv_eq {j : ℕ} (hj : j ≤ J) (i : Fin h) (c : T.X j) : atv hj i (T.vx i c) (T.co i c) = c :=
  (Equiv.ofBijective _ (T.vx_co hj i)).symm_apply_apply c


noncomputable def partM (FL : FlagLaws F T) : (mv : Mv T R ch FL) → (kindM R ch FL mv).Ro → Nd T
  | .inl x => fun p => tri T R ch x.1 p
  | .inr l => fun p => nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p))

theorem partM_inj (FL : FlagLaws F T) (mv : Mv T R ch FL) : Function.Injective (partM R ch FL mv) := by
  rcases mv with x | l
  · exact tri_inj x.2
  · intro p q hpq
    have h1 : atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p) = atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 q) :=
      (nd_inj (hj := l.1.2) (hj' := l.1.2)).1 hpq
    have h2 := congrArg (T.co l.2.1) h1
    rw [atv_co, atv_co] at h2
    exact (FL.ro l.2.2.2).injective h2


def timeM (FL : FlagLaws F T) : Mv T R ch FL → ℕ
  | .inl x => timeR T x.1
  | .inr l => 2 * m + 6 * l.1 + 4


noncomputable def tgM (FL : FlagLaws F T) : (mv : Mv T R ch FL) → (kindM R ch FL mv).Cn → Tg T m AA
  | .inl x => fun ν => tgR T R ch x.1 ν
  | .inr l => fun ν => .edge l.1.succ ((T.nr l.1.2 l.2.1).symm (l.2.2.1, FL.cn l.2.2.2 ν)).1

end


structure Place (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) (A' : ℕ) where
  
  pt : Nd T ≃ Fin (AA + A')
  pt_base : ∀ a, pt (nd T 0 (Nat.zero_le _) (ch a)) = Fin.castAdd A' a

section Sys

variable {T : Tower h b D J r} (R : Routes T m Uu) {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) {A' : ℕ}
  (Pl : Place T ch A')


noncomputable def eE : Fin (Fintype.card (Mv T R ch FL)) ≃ Mv T R ch FL :=
  (exists_mono_equiv (timeM R ch FL)).choose

theorem eE_lt {x y : Mv T R ch FL} (hxy : timeM R ch FL x < timeM R ch FL y) :
    (eE R FL).symm x < (eE R FL).symm y := (exists_mono_equiv (timeM R ch FL)).choose_spec x y hxy


noncomputable def sys : Sys F (AA + A') (Fintype.card (Mv T R ch FL)) where
  kind x := kindM R ch FL (eE R FL x)
  part x p := Pl.pt (partM R ch FL (eE R FL x) p)
  inj x := Pl.pt.injective.comp (partM_inj R ch FL _)


abbrev NM := Σ mv : Mv T R ch FL, (kindM R ch FL mv).Cn


abbrev ZM := Σ mv : Mv T R ch FL, (kindM R ch FL mv).Sl


noncomputable def eN : (sys R FL Pl).N ≃ NM R FL (ch := ch) :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Cn) (eE R FL)


noncomputable def eZ : (sys R FL Pl).Z ≃ ZM R FL (ch := ch) :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Sl) (eE R FL)

theorem eN_fst (ν : (sys R FL Pl).N) : (eN R FL Pl ν).1 = eE R FL ν.1 := rfl

theorem eZ_fst (z : (sys R FL Pl).Z) : (eZ R FL Pl z).1 = eE R FL z.1 := rfl

theorem np_eq (ν : (sys R FL Pl).N) (d : Bool) : (sys R FL Pl).np ν d =
    Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 d)) := rfl

theorem zp_eq (z : (sys R FL Pl).Z) (d : Bool) : (sys R FL Pl).zp z d =
    Pl.pt (partM R ch FL (eZ R FL Pl z).1 ((kindM R ch FL (eZ R FL Pl z).1).slEnd (eZ R FL Pl z).2 d)) := rfl

end Sys

end Nc.Tow
end
/- Source module Nc.Tow.Flow. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
  (o : NM R FL (ch := ch) → ℕ)

noncomputable instance : DecidableEq (NM R FL (ch := ch)) := Classical.decEq _

noncomputable instance : Fintype (NM R FL (ch := ch)) := inferInstanceAs (Fintype (Σ mv : Mv T R ch FL, (kindM R ch FL mv).Cn))


def Valid : Prop := ∀ a, ∑ c, (if c = a then 0 else n a c + n c a) ≤ lhat

instance : Decidable (Valid lhat n) := by unfold Valid; infer_instance


noncomputable def bt (τ : Tg T m AA) : ℕ :=
  if Valid lhat n then ∑ a, ∑ c, ((range (n a c)).filter fun k => tgB T R ch a c k = τ).card else 0


def GoodL (l : LMv T FL) (t : ℕ) : Prop :=
  r * b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 ≤ FL.G₁ * t ^ 2

instance (l : LMv T FL) (t : ℕ) : Decidable (GoodL R ch FL o l t) := by unfold GoodL; infer_instance


def alvN : NM R FL (ch := ch) → ℕ → ℕ
  | ⟨.inl x, ν⟩, t => if o ⟨.inl x, ν⟩ = t then t else 0
  | ⟨.inr l, ν⟩, t => if GoodL R ch FL o l t then o ⟨.inr l, ν⟩ else min (o ⟨.inr l, ν⟩) t


noncomputable def ld (N : Mv T R ch FL → ℕ) (τ : Tg T m AA) : ℕ :=
  bt R ch lhat n τ + ∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = τ then alvN R ch FL o ν (N ν.1) else 0


def sqs (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : ℕ :=
  ∑ e : T.Ed j, if T.ty e = i then L (.edge j e) ^ 2 else 0


def IsMin (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : Prop :=
  (∀ i', sqs L j i ≤ sqs L j i') ∧ ∀ i' < i, ¬ ∀ i'', sqs L j i' ≤ sqs L j i''


def ActR (L : Tg T m AA → ℕ) : RM T m AA → Prop
  | .inn j i _ => IsMin L j.castSucc i
  | .mid j e s => s = 0 → IsMin L j.castSucc (T.ty e)
  | _ => True


def pr (d : FL.Di) (e : (FL.L d).Sl) : Sym2 T.Fl := s(FL.ro d ((FL.L d).a e), FL.ro d ((FL.L d).b e))


def slo (d : FL.Di) (q : Sym2 T.Fl) : ℕ := (univ.filter fun e : (FL.L d).Sl => pr FL d e = q).card


def Fits (L : Tg T m AA → ℕ) (l : LMv T FL) (t : ℕ) : Prop :=
  ∀ q : Sym2 T.Fl, ¬ q.IsDiag → L (.seg l.1 l.2.1 l.2.2.1 q) ≤ slo FL l.2.2.2 q * t


def withD (l : LMv T FL) (d : FL.Di) : LMv T FL := ⟨l.1, l.2.1, l.2.2.1, d⟩


noncomputable def tmin (L : Tg T m AA → ℕ) (l : LMv T FL) : ℕ := sInf {t | ∃ d, Fits FL L (withD FL l d) t}


def Pick (L : Tg T m AA → ℕ) (l : LMv T FL) : Prop :=
  Fits FL L l (tmin FL L l) ∧ ∀ d, (Fintype.equivFin FL.Di d) < (Fintype.equivFin FL.Di l.2.2.2) →
    ¬ Fits FL L (withD FL l d) (tmin FL L l)

open Classical in

noncomputable def numF (L : Tg T m AA → ℕ) : Mv T R ch FL → ℕ
  | .inl x => if ActR L x.1 then L (inpR T x.1) else 0
  | .inr l => if Pick FL L l then tmin FL L l else 0


noncomputable def numS : ℕ → Mv T R ch FL → ℕ
  | 0, _ => 0
  | τ + 1, mv => if timeM R ch FL mv = τ then numF R ch FL (ld R ch FL lhat n o (numS τ)) mv else numS τ mv


def tend (J m : ℕ) : ℕ := 2 * m + 6 * J + 1


noncomputable def num (mv : Mv T R ch FL) : ℕ := numS R ch FL lhat n o (tend J m) mv


noncomputable def alv (ν : NM R FL (ch := ch)) : ℕ := alvN R ch FL o ν (num R ch FL lhat n o ν.1)


noncomputable def load (τ : Tg T m AA) : ℕ := ld R ch FL lhat n o (num R ch FL lhat n o) τ


def GoodMv : Mv T R ch FL → Prop
  | .inl x => ∀ ν : (kindM R ch FL (.inl x)).Cn, o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x)
  | .inr l => GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) ∧
      ∀ ν : (kindM R ch FL (.inr l)).Cn, num R ch FL lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩

variable {R ch FL lhat n o}

theorem alvN_inl (x : {x : RM T m AA // okR T R ch x}) (ν : (kindM R ch FL (.inl x)).Cn) (t : ℕ) :
    alvN R ch FL o ⟨.inl x, ν⟩ t = if o ⟨.inl x, ν⟩ = t then t else 0 := rfl

theorem alvN_inr (l : LMv T FL) (ν : (kindM R ch FL (.inr l)).Cn) (t : ℕ) :
    alvN R ch FL o ⟨.inr l, ν⟩ t = if GoodL R ch FL o l t then o ⟨.inr l, ν⟩ else min (o ⟨.inr l, ν⟩) t := rfl

theorem goodMv_inl (x : {x : RM T m AA // okR T R ch x}) : GoodMv R ch FL lhat n o (.inl x) ↔
    ∀ ν : (kindM R ch FL (.inl x)).Cn, o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x) := Iff.rfl

theorem goodMv_inr (l : LMv T FL) : GoodMv R ch FL lhat n o (.inr l) ↔
    GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) ∧
      ∀ ν : (kindM R ch FL (.inr l)).Cn, num R ch FL lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩ := Iff.rfl

theorem alv_inr (l : LMv T FL) (ν : (FL.L l.2.2.2).Cn) : alv R ch FL lhat n o ⟨.inr l, ν⟩ =
    if GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) then o ⟨.inr l, ν⟩
    else min (o ⟨.inr l, ν⟩) (num R ch FL lhat n o (.inr l)) := rfl

theorem inpR_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : inpR T (.mid j e s : RM T m AA) =
    if s = 0 then .edge j.castSucc e else .nxt (.mid j e s) := rfl

theorem alvN_le (ν : NM R FL (ch := ch)) (t : ℕ) : alvN R ch FL o ν t ≤ o ν := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl]
    split_ifs with h
    · exact h.ge
    · exact Nat.zero_le _
  · rw [alvN_inr]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _

theorem alvN_zero (hr : 0 < r) (hb : 0 < b) (ν : NM R FL (ch := ch)) : alvN R ch FL o ν 0 = 0 := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl]
    split_ifs <;> rfl
  · rw [alvN_inr]
    split_ifs with h
    · unfold GoodL at h
      have h1 : r * b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 = 0 := by simpa using h
      have h2 : ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 = 0 := by
        rcases Nat.mul_eq_zero.1 h1 with h3 | h3
        · have := Nat.mul_pos hr hb; omega
        · exact h3
      have h3 := (Finset.sum_eq_zero_iff.1 h2) ν (mem_univ _)
      exact pow_eq_zero_iff (by norm_num) |>.1 h3
    · exact Nat.min_zero _

theorem timeM_lt (mv : Mv T R ch FL) : timeM R ch FL mv < tend J m := by
  unfold tend
  rcases mv with ⟨x, hx⟩ | l
  · change timeR T x < _
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have := s.2; simp only [timeR]; omega
    · have := j.2; simp only [timeR]; omega
    · have := j.2; have := s.2; simp only [timeR]; omega
    · simp only [timeR]; omega
  · have := l.1.2
    simp only [timeM]; omega

theorem numS_zero_of_le {τ : ℕ} {mv : Mv T R ch FL} (h : τ ≤ timeM R ch FL mv) : numS R ch FL lhat n o τ mv = 0 := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [numS, if_neg (by omega)]
    exact ih (by omega)

theorem numS_stable {τ : ℕ} {mv : Mv T R ch FL} (h : timeM R ch FL mv < τ) :
    numS R ch FL lhat n o τ mv =
      numF R ch FL (ld R ch FL lhat n o (numS R ch FL lhat n o (timeM R ch FL mv))) mv := by
  induction τ with
  | zero => omega
  | succ τ ih =>
    rw [numS]
    by_cases h1 : timeM R ch FL mv = τ
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      exact ih (by omega)

theorem numS_eq (τ : ℕ) (mv : Mv T R ch FL) :
    numS R ch FL lhat n o τ mv = if timeM R ch FL mv < τ then num R ch FL lhat n o mv else 0 := by
  split_ifs with h
  · rw [numS_stable h, num, numS_stable (timeM_lt mv)]
  · exact numS_zero_of_le (not_lt.1 h)


def tgTime : Tg T m AA → ℕ
  | .done => tend J m
  | .edge j _ => 2 * m + 6 * j
  | .nxt x => timeR T x
  | .seg j _ _ _ => 2 * m + 6 * j + 4

theorem edgeO_time (e : Option (T.Ed 0)) : 2 * m ≤ tgTime (edgeO T e : Tg T m AA) := by
  cases e
  · simp only [edgeO, tgTime, tend]; omega
  · simp [edgeO, tgTime]

theorem tg_time (ν : NM R FL (ch := ch)) : timeM R ch FL ν.1 < tgTime (tgM R ch FL ν.1 ν.2) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · change timeR T x < tgTime (tgR T R ch x ν)
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have hs := s.2
      cases ν
      · refine lt_of_lt_of_le ?_ (edgeO_time _)
        exact hs
      · simp only [tgR]
        split_ifs
        · simp only [tgTime, timeR]; omega
        · refine lt_of_lt_of_le ?_ (edgeO_time _)
          exact hs
    · have := j.2
      simp only [tgR, tgTime, timeR, tend]; omega
    · have := j.2
      cases ν
      · fin_cases s
        · simp only [Fin.zero_eta, tgR, Matrix.cons_val_zero, tgTime, timeR, tend]
          change 2 * m + 6 * j.1 + 0 < _
          omega
        · simp [tgR, tgTime, timeR]
        · change 2 * m + 6 * j.1 + 2 < 2 * m + 6 * (j.1 + 1)
          omega
        · simp [tgR, tgTime, timeR]
      · fin_cases s
        · simp only [tgR, timeR, Fin.zero_eta, Matrix.cons_val_zero]
          split_ifs <;> simp [tgTime, timeR]
        · simp [tgR, tgTime, timeR]
        · simp only [tgR, timeR, Fin.reduceFinMk, Matrix.cons_val]
          split_ifs
          · simp [tgTime, timeR]
          · change 2 * m + 6 * j.1 + 2 < 2 * m + 6 * J + 1
            omega
        · change 2 * m + 6 * j.1 + 3 < 2 * m + 6 * J + 1
          omega
    · simp only [tgR, tgTime, timeR, tend]; omega
  · have := l.1.2
    simp only [tgM, tgTime, timeM, Fin.val_succ]
    omega

theorem ld_numS (hr : 0 < r) (hb : 0 < b) {τ : Tg T m AA} {t : ℕ} (h : tgTime τ ≤ t) :
    ld R ch FL lhat n o (numS R ch FL lhat n o t) τ = load R ch FL lhat n o τ := by
  unfold load ld
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · have := tg_time ν
    rw [hν] at this
    rw [numS_eq, if_pos (by omega)]
  · rfl

theorem inp_time (x : RM T m AA) : tgTime (inpR T x) ≤ timeR T x := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · simp [inpR, tgTime]
  · simp [inpR, tgTime, timeR]
  · rw [inpR_mid]
    split_ifs with hs
    · simp [tgTime, timeR]
    · simp [tgTime]
  · simp [inpR, tgTime, timeR]

theorem sqs_congr {L L' : Tg T m AA → ℕ} {j : Fin (J + 1)} (hL : ∀ e, L (.edge j e) = L' (.edge j e)) (i : Fin h) :
    sqs L j i = sqs L' j i := by
  unfold sqs
  simp only [hL]

theorem isMin_congr {L L' : Tg T m AA → ℕ} {j : Fin (J + 1)} (hL : ∀ e, L (.edge j e) = L' (.edge j e)) (i : Fin h) :
    IsMin L j i ↔ IsMin L' j i := by
  unfold IsMin
  simp only [sqs_congr hL]

theorem fits_congr {L L' : Tg T m AA → ℕ} {l : LMv T FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) (s : ℕ) :
    Fits FL L l s ↔ Fits FL L' l s := by
  unfold Fits
  simp only [hL]

theorem tmin_congr {L L' : Tg T m AA → ℕ} {l : LMv T FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) : tmin FL L l = tmin FL L' l := by
  unfold tmin
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  exact exists_congr fun d => fits_congr (l := withD FL l d) hL s

theorem pick_congr {L L' : Tg T m AA → ℕ} {l : LMv T FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) : Pick FL L l ↔ Pick FL L' l := by
  unfold Pick
  rw [tmin_congr hL, fits_congr hL]
  refine and_congr_right fun _ => forall_congr' fun d => imp_congr_right fun _ => not_congr ?_
  exact fits_congr (l := withD FL l d) hL _

theorem actR_congr {L L' : Tg T m AA → ℕ} {x : RM T m AA}
    (hL : ∀ τ, tgTime τ ≤ timeR T x → L τ = L' τ) : ActR L x ↔ ActR L' x := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact Iff.rfl
  · exact isMin_congr (fun e => hL _ (by simp [tgTime, timeR])) i
  · exact imp_congr_right fun _ => isMin_congr (fun e => hL _ (by simp [tgTime, timeR])) _
  · exact Iff.rfl

theorem numF_congr {L L' : Tg T m AA → ℕ} {mv : Mv T R ch FL}
    (hL : ∀ τ, tgTime τ ≤ timeM R ch FL mv → L τ = L' τ) : numF R ch FL L mv = numF R ch FL L' mv := by
  classical
  rcases mv with ⟨x, hx⟩ | l
  · unfold numF
    simp only [actR_congr (x := x) hL, hL _ (inp_time x)]
  · unfold numF
    have h1 : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q) := fun q => hL _ le_rfl
    simp only [pick_congr h1, tmin_congr h1]


theorem num_eq (hr : 0 < r) (hb : 0 < b) (mv : Mv T R ch FL) :
    num R ch FL lhat n o mv = numF R ch FL (load R ch FL lhat n o) mv := by
  rw [num, numS_stable (timeM_lt mv)]
  exact numF_congr fun τ hτ => ld_numS hr hb hτ

section Causal

variable {o' : NM R FL (ch := ch) → ℕ}

theorem alvN_congr {ν : NM R FL (ch := ch)} (hν : ∀ c, o ⟨ν.1, c⟩ = o' ⟨ν.1, c⟩) (t : ℕ) :
    alvN R ch FL o ν t = alvN R ch FL o' ν t := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl, alvN_inl, hν]
  · have hν' : ∀ c : (FL.L l.2.2.2).Cn, o ⟨.inr l, c⟩ = o' ⟨.inr l, c⟩ := hν
    have hg : GoodL R ch FL o l t ↔ GoodL R ch FL o' l t := by
      unfold GoodL
      rw [Finset.sum_congr rfl fun c _ => by rw [hν' c]]
    rw [alvN_inr, alvN_inr, hν]
    exact if_congr hg rfl rfl

theorem ld_congr (hr : 0 < r) (hb : 0 < b) {N : Mv T R ch FL → ℕ}
    (hN : ∀ mv, N mv ≠ 0 → ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) (τ : Tg T m AA) :
    ld R ch FL lhat n o N τ = ld R ch FL lhat n o' N τ := by
  unfold ld
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · by_cases h0 : N ν.1 = 0
    · rw [h0, alvN_zero hr hb, alvN_zero hr hb]
    · exact alvN_congr (hN ν.1 h0) _
  · rfl

theorem numS_congr (hr : 0 < r) (hb : 0 < b) {t : ℕ} (ho : ∀ mv : Mv T R ch FL, timeM R ch FL mv < t → ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) :
    numS R ch FL lhat n o t = numS R ch FL lhat n o' t := by
  induction t with
  | zero => funext mv; rfl
  | succ t ih =>
    have ih' := ih fun mv hmv => ho mv (by omega)
    funext mv
    rw [numS, numS, ← ih']
    split_ifs with h1
    · refine numF_congr fun τ _ => ld_congr hr hb ?_ τ
      intro mv' hmv'
      refine ho mv' ?_
      by_contra hcon
      exact hmv' (numS_zero_of_le (by omega))
    · rfl

theorem num_congr (hr : 0 < r) (hb : 0 < b) {mv : Mv T R ch FL}
    (ho : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL mv → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩) :
    num R ch FL lhat n o mv = num R ch FL lhat n o' mv := by
  rw [num, num, numS_stable (timeM_lt mv), numS_stable (timeM_lt mv), numS_congr hr hb ho]
  refine numF_congr fun τ _ => ld_congr hr hb ?_ τ
  intro mv' hmv'
  refine ho mv' ?_
  by_contra hcon
  exact hmv' (numS_zero_of_le (by omega))

theorem load_congr (hr : 0 < r) (hb : 0 < b) {τ : Tg T m AA} {t : ℕ} (hτ : tgTime τ ≤ t)
    (ho : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < t → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩) :
    load R ch FL lhat n o τ = load R ch FL lhat n o' τ := by
  rw [← ld_numS hr hb hτ, ← ld_numS hr hb hτ, numS_congr hr hb ho]
  refine ld_congr hr hb ?_ τ
  intro mv' hmv'
  refine ho mv' ?_
  by_contra hcon
  exact hmv' (numS_zero_of_le (by omega))

theorem good_congr (hr : 0 < r) (hb : 0 < b) {mv : Mv T R ch FL}
    (ho : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL mv → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩)
    (ho' : ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) : GoodMv R ch FL lhat n o mv ↔ GoodMv R ch FL lhat n o' mv := by
  have hnum := num_congr (lhat := lhat) (n := n) hr hb ho
  rcases mv with x | l
  · rw [goodMv_inl, goodMv_inl, hnum]
    exact forall_congr' fun ν => by rw [ho' ν]
  · rw [goodMv_inr, goodMv_inr, hnum]
    have hg : GoodL R ch FL o l (num R ch FL lhat n o' (.inr l)) ↔ GoodL R ch FL o' l (num R ch FL lhat n o' (.inr l)) := by
      unfold GoodL
      have : ∀ c : (FL.L l.2.2.2).Cn, o ⟨.inr l, c⟩ = o' ⟨.inr l, c⟩ := ho'
      rw [Finset.sum_congr rfl fun c _ => by rw [this c]]
    rw [hg]
    exact and_congr_right fun _ => forall_congr' fun ν => by rw [ho' ν]

end Causal

end Nc.Tow
end
/- Source module Nc.Tow.Ends. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}


noncomputable def hN (ν : NM R FL (ch := ch)) : Sym2 (Nd T) :=
  s(partM R ch FL ν.1 ((kindM R ch FL ν.1).c ν.2), partM R ch FL ν.1 ((kindM R ch FL ν.1).d ν.2))


def hB (ch : Fin AA ↪ T.X 0) (a c : Fin AA) : Sym2 (Nd T) := s(nd T 0 (Nat.zero_le _) (ch a), nd T 0 (Nat.zero_le _) (ch c))


noncomputable def hT (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) : Tg T m AA → Sym2 (Nd T)
  | .done => s(none, none)
  | .edge j e => s(nd T j (Nat.le_of_lt_succ j.2) (T.e0 e), nd T j (Nat.le_of_lt_succ j.2) (T.e1 e))
  | .nxt x => s(tri T R ch x 0, tri T R ch x 2)
  | .seg j i ω q => q.map fun f => nd T (j + 1) j.2 (atv j.2 i ω f)

theorem edgeO_hold {c c' γ : T.X 0} {s : ℕ} (hs : s < R.pl c c' γ) :
    (edgeO T ((R.path c c' γ)[s]?) : Tg T m AA) ≠ .done ∧
    hT R ch (edgeO T ((R.path c c' γ)[s]?) : Tg T m AA) =
      s(nd T 0 (Nat.zero_le _) (R.pn c c' γ s), nd T 0 (Nat.zero_le _) (R.pn c c' γ (s + 1))) := by
  obtain ⟨e, h1, h2, -⟩ := R.exists_edge c c' γ hs
  rw [h1]
  refine ⟨by simp [edgeO], ?_⟩
  have := congrArg (Sym2.map (nd T 0 (Nat.zero_le _))) h2
  simp only [Sym2.map_mk, Prod.map] at this
  exact this


theorem hB_eq {a c : Fin AA} {k : ℕ} (hd : tgB T R ch a c k ≠ .done) : hB ch a c = hT R ch (tgB T R ch a c k) := by
  unfold tgB at hd ⊢
  by_cases hac : a = c
  · rw [if_pos hac] at hd
    exact absurd rfl hd
  · rw [if_neg hac] at hd ⊢
    have hne : ch a ≠ ch c := fun hh => hac (ch.injective hh)
    have hpos := R.pl_pos hne (gam T ch a k)
    have hle := (R.pl_le (ch a) (ch c) (gam T ch a k)).trans (R.length_path _ _ _)
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dif_pos hs]
      rfl
    · rw [dif_neg hs]
      have h1 : R.pl (ch a) (ch c) (gam T ch a k) = 1 := by
        by_contra h1
        exact hs ⟨by omega, by omega⟩
      rw [(edgeO_hold (ch := ch) (AA := AA) (m := m) hpos).2]
      have h2 := R.pn_pl (ch a) (ch c) (gam T ch a k)
      rw [h1] at h2
      rw [h2]
      rfl

theorem seg_hold {j : ℕ} (hj : j < J) (i : Fin h) (c : T.X j) :
    (s(T.co i (hst T i c), T.co i c) : Sym2 T.Fl).map (fun f => nd T (j + 1) hj (atv hj i (T.πV (T.vx i c)) f)) =
      s(nd T (j + 1) hj (hst T i c), nd T (j + 1) hj (T.π c)) := by
  rw [Sym2.map_mk]
  have h1 : atv hj i (T.πV (T.vx i c)) (T.co i (hst T i c)) = hst T i c := by
    rw [← T.host_vx hj i (T.vx i c)]
    exact atv_eq hj i _
  have h2 : atv hj i (T.πV (T.vx i c)) (T.co i c) = T.π c := by
    rw [← T.π_vx hj i c, ← T.π_co hj i c]
    exact atv_eq hj i _
  simp only [Prod.map, h1, h2]


theorem hN_eq (ν : NM R FL (ch := ch)) (hd : tgM R ch FL ν.1 ν.2 ≠ .done) : hN ν = hT R ch (tgM R ch FL ν.1 ν.2) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · revert hd
    revert ν
    intro (ν : Bool) hd
    have e0 : hN (⟨.inl ⟨x, hx⟩, ν⟩ : NM R FL (ch := ch)) =
        if ν then s(tri T R ch x 1, tri T R ch x 2) else s(tri T R ch x 0, tri T R ch x 1) := by
      cases ν <;> rfl
    rw [e0]
    change tgR T R ch x ν ≠ .done at hd
    change _ = hT R ch (tgR T R ch x ν)
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · obtain ⟨hac, hs⟩ := hx
      have hle := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
      cases ν
      · simp only [tgR, Bool.false_eq_true, if_false]
        rw [(edgeO_hold (ch := ch) (AA := AA) (m := m) (by omega)).2]
        rfl
      · simp only [tgR, if_true]
        by_cases hs2 : s.1 + 1 < 2 * m ∧ s.1 + 2 < R.pl (ch a) (ch c) γ
        · rw [dif_pos hs2]
          rfl
        · rw [dif_neg hs2, (edgeO_hold (ch := ch) (AA := AA) (m := m) hs).2]
          have h1 : R.pl (ch a) (ch c) γ = s.1 + 1 + 1 := by
            by_contra h1
            exact hs2 ⟨by omega, by omega⟩
          have h2 := R.pn_pl (ch a) (ch c) γ
          rw [h1] at h2
          rw [h2]
          rfl
    · exact absurd rfl hd
    · cases ν
      · simp only [Bool.false_eq_true, if_false]
        fin_cases s
        · exact absurd rfl hd
        · exact (seg_hold j.2 (T.ty e) (T.e0 e)).symm
        · have h1 := T.π_ends j.2 e
          have h2 := congrArg (Sym2.map (nd T (j + 1) j.2)) h1
          simp only [Sym2.map_mk, Prod.map] at h2
          exact h2.symm
        · refine Eq.trans ?_ (seg_hold j.2 (T.ty e) (T.e1 e)).symm
          exact Sym2.eq_swap
      · simp only [if_true]
        fin_cases s
        · simp only [Fin.zero_eta, tgR, Matrix.cons_val_zero]
          by_cases hh : hst T (T.ty e) (T.e0 e) ≠ T.π (T.e0 e)
          · rw [if_pos hh]
            rfl
          · rw [if_neg hh]
            rw [not_not] at hh
            change s(nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)), nd T j j.2.le (T.e1 e)) =
              s(nd T (j + 1) j.2 (T.π (T.e0 e)), nd T j j.2.le (T.e1 e))
            rw [hh]
        · rfl
        · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hd ⊢
          by_cases hh : T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e)
          · rw [if_pos hh]
            rfl
          · rw [if_neg hh] at hd
            exact absurd rfl hd
        · exact absurd rfl hd
    · exact absurd rfl hd
  · change s(nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).c ν))),
      nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).d ν)))) = _
    set p := (T.nr l.1.2 l.2.1).symm (l.2.2.1, FL.cn l.2.2.2 ν) with hp
    have hp2 : T.nr l.1.2 l.2.1 p = (l.2.2.1, FL.cn l.2.2.2 ν) := by rw [hp, Equiv.apply_symm_apply]
    have h0 := T.nr_vx0 l.1.2 l.2.1 p
    have h1 := T.nr_vx1 l.1.2 l.2.1 p
    have h2 := T.nr_co l.1.2 l.2.1 p
    rw [hp2] at h0 h1 h2
    have h3 := (FL.ends l.2.2.2 ν).trans h2.symm
    have h4 := congrArg (Sym2.map fun f => nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f)) h3
    simp only [Sym2.map_mk, Prod.map] at h4
    rw [h4]
    have e1 : atv l.1.2 l.2.1 l.2.2.1 (T.co l.2.1 (T.e0 p.1)) = T.e0 p.1 := by
      have := atv_eq l.1.2 l.2.1 (T.e0 p.1)
      rwa [h0] at this
    have e2 : atv l.1.2 l.2.1 l.2.2.1 (T.co l.2.1 (T.e1 p.1)) = T.e1 p.1 := by
      have := atv_eq l.1.2 l.2.1 (T.e1 p.1)
      rwa [h1] at this
    rw [e1, e2]
    rfl

end Nc.Tow
end
/- Source module Nc.Tow.Rank. -/
section
namespace Nc.Tow

open Finset

variable {U κ : Type*} [DecidableEq κ] (idx : U → ℕ) (key : U → κ)


def rk (F : Finset U) (u : U) : ℕ := (F.filter fun v => key v = key u ∧ idx v < idx u).card

variable {idx key}

theorem rk_congr {F F' : Finset U} {u : U} (h : ∀ v, key v = key u → (v ∈ F ↔ v ∈ F')) :
    rk idx key F u = rk idx key F' u := by
  unfold rk
  congr 1
  ext v
  rw [mem_filter, mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h v h2).1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h v h2).2 h1, h2, h3⟩

theorem rk_lt {F : Finset U} {u : U} (hu : u ∈ F) : rk idx key F u < (F.filter fun v => key v = key u).card := by
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · exact ⟨u, mem_filter.mpr ⟨hu, rfl⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩
  · intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1⟩

theorem rk_lt_rk {F : Finset U} {u v : U} (hu : u ∈ F) (huv : key u = key v) (h : idx u < idx v) :
    rk idx key F u < rk idx key F v := by
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · exact ⟨u, mem_filter.mpr ⟨hu, huv, h⟩, fun h => lt_irrefl _ (mem_filter.mp h).2.2⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨h1, h2.trans huv, h3.trans h⟩

theorem rk_inj (hidx : Function.Injective idx) {F : Finset U} {u v : U} (hu : u ∈ F) (hv : v ∈ F)
    (huv : key u = key v) (h : rk idx key F u = rk idx key F v) : u = v := by
  rcases lt_trichotomy (idx u) (idx v) with h1 | h1 | h1
  · have := rk_lt_rk hu huv h1
    omega
  · exact hidx h1
  · have := rk_lt_rk hv huv.symm h1
    omega

theorem card_rk_le (hidx : Function.Injective idx) (F : Finset U) (k : κ) (a b : ℕ) :
    (F.filter fun u => key u = k ∧ a ≤ rk idx key F u ∧ rk idx key F u < b).card ≤ b - a := by
  rw [← Nat.card_Ico]
  refine card_le_card_of_injOn (rk idx key F) ?_ ?_
  · intro u hu
    have := (mem_filter.1 (mem_coe.1 hu)).2
    exact mem_coe.2 (mem_Ico.2 this.2)
  · intro u hu v hv h
    have hu' := mem_filter.1 (mem_coe.1 hu)
    have hv' := mem_filter.1 (mem_coe.1 hv)
    exact rk_inj hidx hu'.1 hv'.1 (hu'.2.1.trans hv'.2.1.symm) h


theorem exists_rk (hidx : Function.Injective idx) (F : Finset U) (k : κ) {w : ℕ}
    (hw : w < (F.filter fun u => key u = k).card) : ∃ u ∈ F, key u = k ∧ rk idx key F u = w := by
  have hinj : Set.InjOn (rk idx key F) (F.filter fun u => key u = k) := by
    intro u hu v hv h
    have hu' := mem_filter.1 (mem_coe.1 hu)
    have hv' := mem_filter.1 (mem_coe.1 hv)
    exact rk_inj hidx hu'.1 hv'.1 (hu'.2.trans hv'.2.symm) h
  have himg : (F.filter fun u => key u = k).image (rk idx key F) = range (F.filter fun u => key u = k).card := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro ρ hρ
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hρ
      obtain ⟨h1, h2⟩ := mem_filter.1 hu
      rw [mem_range, ← h2]
      exact rk_lt h1
    · rw [card_range, card_image_of_injOn hinj]
  have : w ∈ (F.filter fun u => key u = k).image (rk idx key F) := by
    rw [himg, mem_range]; exact hw
  obtain ⟨u, hu, rfl⟩ := mem_image.1 this
  obtain ⟨h1, h2⟩ := mem_filter.1 hu
  exact ⟨u, h1, h2, rfl⟩

end Nc.Tow
end
/- Source module Nc.Tow.Plan. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') (lhat : ℕ)


abbrev Un (U0 U1 : ℕ) := Uid AA U0 (sys R FL Pl).N U1


def nn (n : Fin AA → Fin AA → Fin (U0 + 1)) : Fin AA → Fin AA → ℕ := fun a c => (n a c).1


noncomputable def oo (o : (sys R FL Pl).N → Fin U1) : NM R FL (ch := ch) → ℕ := fun ν => (o ((eN R FL Pl).symm ν)).1


noncomputable def tgU : Un R FL Pl U0 U1 → Tg T m AA
  | .init a c k => tgB T R ch a c k
  | .new ν _ => tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2

variable (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1)


def AlU : Un R FL Pl U0 U1 → Prop
  | .init a c k => Valid lhat (nn n) ∧ k.1 < (n a c).1
  | .new ν k => k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν)

open Classical in

noncomputable def Al : Finset (Un R FL Pl U0 U1) := univ.filter (AlU R FL Pl lhat n o)


noncomputable def ix (u : Un R FL Pl U0 U1) : ℕ := (Fintype.equivFin (Un R FL Pl U0 U1) u).1


noncomputable def rkU (u : Un R FL Pl U0 U1) : ℕ := rk (ix R FL Pl) (tgU R FL Pl) (Al R FL Pl lhat n o) u


noncomputable def su (d : FL.Di) (e : (FL.L d).Sl) : ℕ :=
  rk (fun e => (Fintype.equivFin (FL.L d).Sl e).1) (pr FL d) univ e

open Classical in

noncomputable def consM : ZM R FL (ch := ch) → Finset (Un R FL Pl U0 U1)
  | ⟨.inl x, _⟩ => if ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) x.1 then
      (Al R FL Pl lhat n o).filter fun u => tgU R FL Pl u = inpR T x.1 else ∅
  | ⟨.inr l, e⟩ => if Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l then
      (Al R FL Pl lhat n o).filter fun u => tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) ∧
        su FL l.2.2.2 e * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ rkU R FL Pl lhat n o u ∧
        rkU R FL Pl lhat n o u < (su FL l.2.2.2 e + 1) * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) else ∅


noncomputable def plan (U0 U1 : ℕ) : Plan (sys R FL Pl) U0 U1 where
  cons n o z := consM R FL Pl lhat n o (eZ R FL Pl z)
  num n o x := num R ch FL lhat (nn n) (oo R FL Pl o) (eE R FL x)
  good n o x := GoodMv R ch FL lhat (nn n) (oo R FL Pl o) (eE R FL x)

variable {R FL Pl lhat n o}

theorem ix_inj : Function.Injective (ix R FL Pl : Un R FL Pl U0 U1 → ℕ) := fun u v huv =>
  (Fintype.equivFin (Un R FL Pl U0 U1)).injective (Fin.ext huv)

theorem mem_Al {u : Un R FL Pl U0 U1} : u ∈ Al R FL Pl lhat n o ↔ AlU R FL Pl lhat n o u := by
  classical
  unfold Al
  simp

theorem card_fin_lt' (N c : ℕ) (hc : c ≤ N) : ((univ : Finset (Fin N)).filter fun k => k.1 < c).card = c := by
  have h1 : ((univ : Finset (Fin N)).filter fun k => k.1 < c).card = (range c).card := by
    refine card_bij (fun k _ => k.1) ?_ ?_ ?_
    · intro k hk
      exact mem_range.2 (mem_filter.1 hk).2
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro k hk
      have hk' := mem_range.1 hk
      exact ⟨⟨k, by omega⟩, mem_filter.2 ⟨mem_univ _, hk'⟩, rfl⟩
  rw [h1, card_range]


theorem sum_units {M : Type*} [AddCommMonoid M] (f : Un R FL Pl U0 U1 → M) :
    ∑ u, f u = (∑ a, ∑ c, ∑ k, f (.init a c k)) + ∑ ν, ∑ k, f (.new ν k) := by
  let e : Un R FL Pl U0 U1 ≃ (Fin AA × Fin AA × Fin U0) ⊕ ((sys R FL Pl).N × Fin U1) :=
    { toFun := fun u => match u with
        | .init a c k => .inl (a, c, k)
        | .new ν k => .inr (ν, k)
      invFun := fun s => match s with
        | .inl p => .init p.1 p.2.1 p.2.2
        | .inr p => .new p.1 p.2
      left_inv := fun u => by cases u <;> rfl
      right_inv := fun s => by rcases s with ⟨a, c, k⟩ | ⟨ν, k⟩ <;> rfl }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl


theorem load_eq (τ : Tg T m AA) : load R ch FL lhat (nn n) (oo R FL Pl o) τ =
    ((Al R FL Pl lhat n o).filter fun u => tgU R FL Pl u = τ).card := by
  classical
  have e1 : ((Al R FL Pl lhat n o).filter fun u => tgU R FL Pl u = τ).card =
      ∑ u : Un R FL Pl U0 U1, if AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = τ then 1 else 0 := by
    rw [← card_filter]
    congr 1
    ext u
    simp only [mem_filter, mem_Al, mem_univ, true_and]
  rw [e1, sum_units, load, ld]
  congr 1
  · unfold bt
    by_cases hv : Valid lhat (nn n)
    · rw [if_pos hv]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [← card_filter]
      refine card_bij' (fun k hk => ⟨k, ?_⟩) (fun k _ => k.1) ?_ ?_ ?_ ?_
      · have h1 := mem_range.1 (mem_filter.1 hk).1
        have h2 := (n a c).2
        have h3 : nn n a c = (n a c).1 := rfl
        omega
      · intro k hk
        obtain ⟨h1, h2⟩ := mem_filter.1 hk
        exact mem_filter.2 ⟨mem_univ _, ⟨hv, mem_range.1 h1⟩, h2⟩
      · intro k hk
        obtain ⟨-, h1, h2⟩ := mem_filter.1 hk
        exact mem_filter.2 ⟨mem_range.2 h1.2, h2⟩
      · intro k _; rfl
      · intro k _; rfl
    · rw [if_neg hv]
      symm
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      rintro ⟨⟨h1, -⟩, -⟩
      exact hv h1
  · rw [← Equiv.sum_comp (eN R FL Pl) fun ν : NM R FL (ch := ch) => if tgM R ch FL ν.1 ν.2 = τ then
      alvN R ch FL (oo R FL Pl o) ν (num R ch FL lhat (nn n) (oo R FL Pl o) ν.1) else 0]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hle : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≤ U1 := by
      refine (alvN_le _ _).trans ?_
      exact (o _).2.le
    by_cases hν : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = τ
    · rw [if_pos hν]
      have e2 : (∑ k : Fin U1, if AlU R FL Pl lhat n o (.new ν k) ∧ tgU R FL Pl (.new ν k : Un R FL Pl U0 U1) = τ
          then 1 else 0) = ((univ : Finset (Fin U1)).filter fun k => k.1 <
            alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν)).card := by
        rw [card_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        refine if_congr ?_ rfl rfl
        exact ⟨fun hh => hh.1, fun hh => ⟨hh, hν⟩⟩
      rw [e2, card_fin_lt' _ _ hle]
      rfl
    · rw [if_neg hν]
      symm
      refine Finset.sum_eq_zero fun k _ => if_neg ?_
      rintro ⟨-, h2⟩
      exact hν h2

end Nc.Tow
end
/- Source module Nc.Tow.Load2. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

theorem alv_le_num (hr : 0 < r) (hb : 0 < b) (x : {x : RM T m AA // okR T R ch x}) (ν : (kindM R ch FL (.inl x)).Cn) :
    alv R ch FL lhat n o ⟨.inl x, ν⟩ ≤ num R ch FL lhat n o (.inl x) := by
  unfold alv
  rw [alvN_inl]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem load_def (τ : Tg T m AA) : load R ch FL lhat n o τ = bt R ch lhat n τ +
    ∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = τ then alv R ch FL lhat n o ν else 0 := rfl


theorem load_le_sum {τ : Tg T m AA} (s : Finset (NM R FL (ch := ch))) (hbt : bt R ch lhat n τ = 0)
    (hs : ∀ ν : NM R FL (ch := ch), tgM R ch FL ν.1 ν.2 = τ → alv R ch FL lhat n o ν ≠ 0 → ν ∈ s) :
    load R ch FL lhat n o τ ≤ ∑ ν ∈ s, alv R ch FL lhat n o ν := by
  rw [load_def, hbt, Nat.zero_add, ← Finset.sum_filter]
  rw [← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset ?_
  intro ν hν
  obtain ⟨h1, h2⟩ := mem_filter.1 hν
  exact hs ν (mem_filter.1 h1).2 h2

theorem edgeO_cases (e : Option (T.Ed 0)) : (edgeO T e : Tg T m AA) = .done ∨ ∃ e', e = some e' ∧
    (edgeO T e : Tg T m AA) = .edge 0 e' := by
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, rfl⟩


theorem tgB_cases (a c : Fin AA) (k : ℕ) : (tgB T R ch a c k = .done) ∨
    (∃ hm, tgB T R ch a c k = .nxt (.start a c (gam T ch a k) ⟨0, hm⟩)) ∨
    ∃ e, (R.path (ch a) (ch c) (gam T ch a k))[0]? = some e ∧ tgB T R ch a c k = .edge 0 e ∧ a ≠ c ∧
      ¬ 1 < R.pl (ch a) (ch c) (gam T ch a k) := by
  have hle := (R.pl_le (ch a) (ch c) (gam T ch a k)).trans (R.length_path (ch a) (ch c) (gam T ch a k))
  unfold tgB
  by_cases hac : a = c
  · rw [if_pos hac]; exact Or.inl rfl
  · rw [if_neg hac]
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dif_pos hs]; exact Or.inr (Or.inl ⟨hs.1, rfl⟩)
    · rw [dif_neg hs]
      rcases edgeO_cases (m := m) (AA := AA) ((R.path (ch a) (ch c) (gam T ch a k))[0]?) with h1 | ⟨e, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨e, h1, h2, hac, fun hh => hs ⟨by omega, hh⟩⟩)

theorem bt_zero {τ : Tg T m AA} (hτ : ∀ a c k, tgB T R ch a c k ≠ τ) : bt R ch lhat n τ = 0 := by
  unfold bt
  split_ifs
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    rw [card_eq_zero]
    exact filter_false_of_mem fun k _ => hτ a c k
  · rfl

theorem bt_edge_succ (j : Fin J) (e : T.Ed (j + 1)) : bt R ch lhat n (.edge j.succ e) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk
  · simp at hk
  · simp at hk
  · exact absurd (Tg.edge.inj hk).1.symm (Fin.succ_ne_zero j)

theorem bt_seg (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    bt R ch lhat n (.seg j i ω q : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

theorem bt_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : bt R ch lhat n (.nxt (.mid j e s) : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

section Targets


theorem tgR_edge_succ {x : RM T m AA} {ν : Bool} {j : Fin J} {e' : T.Ed (j + 1)}
    (hx : tgR T R ch x ν = .edge j.succ e') : ∃ e, x = .mid j e 2 ∧ ν = false ∧ T.πE e = e' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
  · exfalso
    have : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .edge j.succ e' := by
      intro e he
      cases e
      · simp [edgeO] at he
      · exact absurd (Tg.edge.inj he).1.symm (Fin.succ_ne_zero j)
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s
      · simp [tgR] at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val, Tg.edge.injEq] at hx
        obtain ⟨h1, h2⟩ := hx
        have hj : j' = j := Fin.succ_injective _ h1
        subst hj
        exact ⟨e, rfl, rfl, eq_of_heq h2⟩
      · simp [tgR] at hx
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

theorem tgR_seg {x : RM T m AA} {ν : Bool} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl}
    (hx : tgR T R ch x ν = .seg j i ω q) : ∃ e : T.Ed j, ν = false ∧ T.ty e = i ∧
      ((x = .mid j e 1 ∧ (T.πV (T.vx i (T.e0 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e0 e)), T.co i (T.e0 e)) = q) ∨
      (x = .mid j e 3 ∧ (T.πV (T.vx i (T.e1 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e1 e)), T.co i (T.e1 e)) = q)) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · exfalso
    have : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .seg j i ω q := by
      intro e he
      cases e <;> simp [edgeO] at he
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s
      · simp [tgR] at hx
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Tg.seg.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        subst h2
        exact ⟨e, rfl, rfl, Or.inl ⟨rfl, eq_of_heq h3, h4⟩⟩
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val, Tg.seg.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        subst h2
        exact ⟨e, rfl, rfl, Or.inr ⟨rfl, eq_of_heq h3, h4⟩⟩
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

theorem tgR_mid {x : RM T m AA} {ν : Bool} {j : Fin J} {e : T.Ed j} {s : Fin 4}
    (hx : tgR T R ch x ν = .nxt (.mid j e s)) : ν = true ∧
      ((s = 1 ∧ x = .mid j e 0) ∨
      (s = 2 ∧ ((x = .mid j e 0 ∧ hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)) ∨ x = .mid j e 1)) ∨
      (s = 3 ∧ x = .mid j e 2)) := by
  rcases x with ⟨a, c, γ, s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · exfalso
    have : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) ≠ .nxt (.mid j e s) := by
      intro e' he
      cases e' <;> simp [edgeO] at he
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · simp at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s' <;> simp [tgR] at hx
    · refine ⟨rfl, ?_⟩
      fin_cases s'
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx with hh
        · simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
          obtain ⟨h1, h2, h3⟩ := hx
          subst h1
          have := eq_of_heq h2
          subst this
          exact Or.inl ⟨h3.symm, rfl⟩
        · simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
          obtain ⟨h1, h2, h3⟩ := hx
          subst h1
          have := eq_of_heq h2
          subst this
          rw [not_not] at hh
          exact Or.inr (Or.inl ⟨h3.symm, Or.inl ⟨rfl, hh⟩⟩)
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Tg.nxt.injEq, RM.mid.injEq] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        subst h1
        have := eq_of_heq h2
        subst this
        exact Or.inr (Or.inl ⟨h3.symm, Or.inr rfl⟩)
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx with hh
        simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        subst h1
        have := eq_of_heq h2
        subst this
        exact Or.inr (Or.inr ⟨h3.symm, rfl⟩)
      · simp [tgR] at hx
  · simp [tgR] at hx

end Targets

theorem sum_union_le {κ : Type*} [DecidableEq κ] (s t : Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

theorem sum_biUnion_le' {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (t : ι → Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le _ _ _).trans (Nat.add_le_add_left ih _)


theorem nEnd_eq {j : ℕ} {i : Fin h} (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : T.nEnd i n ω q =
    (∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) +
    ∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0 := by
  unfold Tower.nEnd
  have e2 : ∀ c : T.X j, (if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0) =
      ∑ e : T.Ed j, ((if T.e0 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) else 0) +
        if T.e1 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0) else 0) := by
    intro c
    unfold Tower.be
    by_cases hc : T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q
    · rw [if_pos hc]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hne := T.e_ne e
      by_cases h0 : T.e0 e = c
      · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
        subst h0
        by_cases ht : T.ty e = i
        · rw [if_pos ⟨ht, Or.inl rfl⟩, if_pos rfl, if_pos ⟨ht, hc⟩, if_neg h1, Nat.add_zero]
        · rw [if_neg fun hh => ht hh.1, if_pos rfl, if_neg fun hh => ht hh.1, if_neg h1, Nat.add_zero]
      · rw [if_neg h0, Nat.zero_add]
        by_cases h1 : T.e1 e = c
        · subst h1
          by_cases ht : T.ty e = i
          · rw [if_pos ⟨ht, Or.inr rfl⟩, if_pos rfl, if_pos ⟨ht, hc⟩]
          · rw [if_neg fun hh => ht hh.1, if_pos rfl, if_neg fun hh => ht hh.1]
        · rw [if_neg h1, if_neg]
          rintro ⟨-, hh | hh⟩
          · exact h0 hh
          · exact h1 hh
    · rw [if_neg hc]
      symm
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Nat.add_eq_zero_iff]
      constructor
      · by_cases h0 : T.e0 e = c
        · subst h0
          rw [if_pos rfl, if_neg fun hh => hc hh.2]
        · rw [if_neg h0]
      · by_cases h0 : T.e1 e = c
        · subst h0
          rw [if_pos rfl, if_neg fun hh => hc hh.2]
        · rw [if_neg h0]
  rw [Finset.sum_congr rfl fun c _ => e2 c, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (mem_univ _), if_pos (mem_univ _)]

section Mid

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_inl (x : {x : RM T m AA // okR T R ch x}) : num R ch FL lhat n o (.inl x) ≤
    load R ch FL lhat n o (inpR T x.1) := by
  classical
  rw [num_eq hr hb, numF]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem num_mid0 (j : Fin J) (e : T.Ed j) (hx : okR T R ch (.mid j e 0)) :
    num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) → num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) = 0) := by
  classical
  refine ⟨num_inl hr hb _, fun hn => ?_⟩
  rw [num_eq hr hb, numF, if_neg]
  intro ha
  exact hn (ha rfl)


theorem num_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) :
    ∃ hx0 : okR T R ch (.mid j e 0), num R ch FL lhat n o (.inl ⟨.mid j e s, hx⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
  have hx0 : okR T R ch (.mid j e 0) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
  refine ⟨hx0, ?_⟩
  have one : ∀ hx1 : okR T R ch (.mid j e 1), num R ch FL lhat n o (.inl ⟨.mid j e 1, hx1⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx1
    refine (num_inl hr hb _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 0, hx0⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 1) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
        have h3 : x = .mid j e 0 := by
          rcases h2 with h2 | h2 | h2
          · exact h2.2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM, inpR_mid] at hν
    · rw [Finset.sum_singleton]
      exact alv_le_num hr hb _ _
  have two : ∀ hx2 : okR T R ch (.mid j e 2), num R ch FL lhat n o (.inl ⟨.mid j e 2, hx2⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx2
    refine (num_inl hr hb _).trans ?_
    by_cases hh : hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)
    · refine (load_le_sum {(⟨.inl ⟨.mid j e 0, hx0⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 2) ?_).trans ?_
      · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
        · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
          have h3 : x = .mid j e 0 := by
            rcases h2 with h2 | h2 | h2
            · exact h2.2
            · rcases h2.2 with h3 | h3
              · exact h3.1
              · subst h3
                exact absurd hh (hx'.1 rfl)
            · exact absurd h2.1 (by decide)
          subst h3
          have h1 : ν = true := h1
          subst h1
          exact mem_singleton_self _
        · simp [tgM, inpR_mid] at hν
      · rw [Finset.sum_singleton]
        exact alv_le_num hr hb _ _
    · have hx1 : okR T R ch (.mid j e 1) := ⟨fun _ => hh, fun h3 => absurd h3 (by decide)⟩
      refine (load_le_sum {(⟨.inl ⟨.mid j e 1, hx1⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 2) ?_).trans ?_
      · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
        · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
          have h3 : x = .mid j e 1 := by
            rcases h2 with h2 | h2 | h2
            · exact absurd h2.1 (by decide)
            · rcases h2.2 with h3 | h3
              · exact absurd h3.2 hh
              · exact h3
            · exact absurd h2.1 (by decide)
          subst h3
          have h1 : ν = true := h1
          subst h1
          exact mem_singleton_self _
        · simp [tgM, inpR_mid] at hν
      · rw [Finset.sum_singleton]
        exact (alv_le_num hr hb _ _).trans (one hx1)
  fin_cases s
  · exact le_rfl
  · exact one hx
  · exact two hx
  · have hx2 : okR T R ch (.mid j e 2) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    refine (num_inl hr hb _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 2, hx2⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 3) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
        have h3 : x = .mid j e 2 := by
          rcases h2 with h2 | h2 | h2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
          · exact h2.2
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM, inpR_mid] at hν
    · rw [Finset.sum_singleton]
      exact (alv_le_num hr hb _ _).trans (two hx2)

theorem alv_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) (ν : Bool) :
    alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) →
      alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) = 0) := by
  obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
  have h2 := num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e hx0
  have h3 := alv_le_num (lhat := lhat) (n := n) (o := o) hr hb (⟨.mid j e s, hx⟩ : {x : RM T m AA // okR T R ch x}) ν
  refine ⟨h3.trans (h1.trans h2.1), fun hn => ?_⟩
  have := h2.2 hn
  omega


theorem seg_chan {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl} {ν : NM R FL (ch := ch)}
    (hν : tgM R ch FL ν.1 ν.2 = .seg j i ω q) : ∃ (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)),
      T.ty e = i ∧ ν = ⟨.inl ⟨.mid j e s, hx⟩, false⟩ ∧
      ((s = 1 ∧ T.πV (T.vx i (T.e0 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q) ∨
      (s = 3 ∧ T.πV (T.vx i (T.e1 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q)) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · obtain ⟨e, h1, h2, h3⟩ := tgR_seg (x := x) (ν := ν) hν
    have h1 : ν = false := h1
    subst h1
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3
      exact ⟨e, 1, hx, h2, rfl, Or.inl ⟨rfl, h4⟩⟩
    · subst h3
      exact ⟨e, 3, hx, h2, rfl, Or.inr ⟨rfl, h4⟩⟩
  · simp [tgM] at hν


theorem seg_zero {j : Fin J} {i : Fin h} (hn : ¬ IsMin (load R ch FL lhat n o) j.castSucc i) (ω : T.V (j + 1) i)
    (q : Sym2 T.Fl) : load R ch FL lhat n o (.seg j i ω q) = 0 := by
  rw [load_def, bt_seg, Nat.zero_add]
  refine Finset.sum_eq_zero fun ν _ => ?_
  split_ifs with hν
  · obtain ⟨e, s, hx, h1, h2, -⟩ := seg_chan hr hb hν
    rw [h2]
    exact (alv_mid_le hr hb j e s hx false).2 (by rw [h1]; exact hn)
  · rfl

open Classical in

noncomputable def segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : Finset (NM R FL (ch := ch)) :=
  if hx : okR T R ch (.mid j e s) then {⟨.inl ⟨.mid j e s, hx⟩, false⟩} else ∅

theorem sum_segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : ∑ ν ∈ segS (R := R) (ch := ch) (FL := FL) j s e, alv R ch FL lhat n o ν ≤
    load R ch FL lhat n o (.edge j.castSucc e) := by
  unfold segS
  split_ifs with hx
  · rw [Finset.sum_singleton]
    exact (alv_mid_le hr hb j e s hx false).1
  · rw [Finset.sum_empty]
    exact Nat.zero_le _


theorem seg_le (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    load R ch FL lhat n o (.seg j i ω q) ≤ T.nEnd i (fun e => load R ch FL lhat n o (.edge j.castSucc e)) ω q := by
  classical
  rw [nEnd_eq]
  refine (load_le_sum
    (((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 1)) ∪
    ((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 3)))
    (bt_seg j i ω q) ?_).trans ?_
  · intro ν hν _
    obtain ⟨e, s, hx, h1, h2, h3⟩ := seg_chan hr hb hν
    rcases h3 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · subst h5
      refine mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dif_pos hx, h2]
      exact mem_singleton_self _
    · subst h5
      refine mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dif_pos hx, h2]
      exact mem_singleton_self _
  · refine (sum_union_le _ _ _).trans (add_le_add ?_ ?_)
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 1 e
      · exact le_rfl
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 3 e
      · exact le_rfl

end Mid

end Nc.Tow
end
/- Source module Nc.Tow.Load3. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}


theorem exists_isMin (hh : 0 < h) (L : Tg T m AA → ℕ) (j : Fin (J + 1)) : ∃ i, IsMin L j i := by
  classical
  obtain ⟨i0, -, hi0⟩ := exists_min_image (univ : Finset (Fin h)) (sqs L j) ⟨⟨0, hh⟩, mem_univ _⟩
  have hex : ∃ k : ℕ, ∃ hk : k < h, ∀ i', sqs L j ⟨k, hk⟩ ≤ sqs L j i' := ⟨i0, i0.2, fun i' => hi0 i' (mem_univ _)⟩
  obtain ⟨hk, h1⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hk⟩, h1, fun i' hi' hcon => ?_⟩
  exact Nat.find_min hex hi' ⟨i'.2, hcon⟩


theorem isMin_le {L : Tg T m AA → ℕ} {j : Fin (J + 1)} {i : Fin h} (hi : IsMin L j i) :
    (h : ℝ) * ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (L (.edge j e) : ℝ) ^ 2 ≤
      ∑ e : T.Ed j, (L (.edge j e) : ℝ) ^ 2 := by
  have h1 : h * sqs L j i ≤ ∑ i', sqs L j i' := by
    calc h * sqs L j i = ∑ _i' : Fin h, sqs L j i := by simp
      _ ≤ _ := Finset.sum_le_sum fun i' _ => hi.1 i'
  have h2 : ∑ i', sqs L j i' = ∑ e : T.Ed j, L (.edge j e) ^ 2 := by
    unfold sqs
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp
  have h3 : (sqs L j i : ℝ) = ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (L (.edge j e) : ℝ) ^ 2 := by
    unfold sqs
    rw [Finset.sum_filter]
    push_cast
    rfl
  rw [h2] at h1
  rw [← h3]
  exact_mod_cast h1

theorem NN2_mono {n n' : Sym2 T.Fl → ℕ} (hb : 0 < b) (hn : ∀ q, n q ≤ n' q) : T.NN2 n ≤ T.NN2 n' := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold Tower.NN2
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) ?_
  · split_ifs
    · exact le_rfl
    · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn q) 2
  · have : (0 : ℝ) ≤ b - 1 := by linarith
    positivity


theorem exists_fits (L : Tg T m AA → ℕ) (l : LMv T FL) : ∃ t d, Fits FL L (withD FL l d) t := by
  have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
  obtain ⟨t, ht⟩ := exists_nat_ge (√(T.NN2 fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) / FL.a₁)
  obtain ⟨d, hd⟩ := FL.L1 (fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) t (by
    rw [div_le_iff₀ ha] at ht
    linarith)
  exact ⟨t, d, hd⟩

theorem exists_fits_seg (L : Tg T m AA → ℕ) (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) :
    ∃ t d, Fits FL L (⟨j, i, ω, d⟩ : LMv T FL) t := by
  have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
  obtain ⟨t, ht⟩ := exists_nat_ge (√(T.NN2 fun q => L (.seg j i ω q)) / FL.a₁)
  obtain ⟨d, hd⟩ := FL.L1 (fun q => L (.seg j i ω q)) t (by
    rw [div_le_iff₀ ha] at ht
    linarith)
  exact ⟨t, d, hd⟩

theorem tmin_spec (L : Tg T m AA → ℕ) (l : LMv T FL) : ∃ d, Fits FL L (withD FL l d) (tmin FL L l) := by
  obtain ⟨t, ht⟩ := exists_fits L l
  exact Nat.sInf_mem (s := {t | ∃ d, Fits FL L (withD FL l d) t}) ⟨t, ht⟩


theorem exists_pick (L : Tg T m AA → ℕ) (l : LMv T FL) : ∃ d, Pick FL L (withD FL l d) := by
  classical
  obtain ⟨d0, hd0⟩ := tmin_spec L l
  obtain ⟨d, hd, hmin⟩ := exists_min_image (univ.filter fun d => Fits FL L (withD FL l d) (tmin FL L l))
    (fun d => Fintype.equivFin FL.Di d) ⟨d0, mem_filter.2 ⟨mem_univ _, hd0⟩⟩
  refine ⟨d, (mem_filter.1 hd).2, fun d' hd' hf => ?_⟩
  have := hmin d' (mem_filter.2 ⟨mem_univ _, hf⟩)
  exact absurd hd' (not_lt.2 this)


theorem tmin_le (hb : 0 < b) (L : Tg T m AA → ℕ) (l : LMv T FL) {n' : Sym2 T.Fl → ℕ}
    (hn' : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) ≤ n' q) :
    (FL.a₁ : ℝ) * tmin FL L l ≤ √(T.NN2 n') + FL.a₁ := by
  have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
  rcases Nat.eq_zero_or_pos (tmin FL L l) with h0 | h0
  · rw [h0]
    have := Real.sqrt_nonneg (T.NN2 n')
    simp only [Nat.cast_zero, mul_zero]
    linarith
  · have h1 : ¬ ∃ d, Fits FL L (withD FL l d) (tmin FL L l - 1) := by
      intro hcon
      have := Nat.sInf_le (s := {t | ∃ d, Fits FL L (withD FL l d) t}) hcon
      change tmin FL L l ≤ _ at this
      omega
    have h2 : ¬ √(T.NN2 fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) ≤ (FL.a₁ : ℝ) * (tmin FL L l - 1 : ℕ) := by
      intro hcon
      obtain ⟨d, hd⟩ := FL.L1 _ _ hcon
      exact h1 ⟨d, hd⟩
    have h3 : √(T.NN2 fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) ≤ √(T.NN2 n') :=
      Real.sqrt_le_sqrt (NN2_mono hb hn')
    rw [Nat.cast_sub h0] at h2
    push_cast at h2
    have : (FL.a₁ : ℝ) * tmin FL L l = FL.a₁ * ((tmin FL L l : ℝ) - 1) + FL.a₁ := by ring
    linarith [not_le.1 h2]

theorem tmin_zero {L : Tg T m AA → ℕ} {l : LMv T FL} (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = 0) : tmin FL L l = 0 := by
  have : (0 : ℕ) ∈ {t | ∃ d, Fits FL L (withD FL l d) t} := by
    refine ⟨l.2.2.2, fun q _ => ?_⟩
    change L (.seg l.1 l.2.1 l.2.2.1 q) ≤ _
    rw [hL]
    exact Nat.zero_le _
  exact Nat.le_zero.1 (Nat.sInf_le this)

section Stage

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_inr_le (l : LMv T FL) : num R ch FL lhat n o (.inr l) ≤ tmin FL (load R ch FL lhat n o) l := by
  classical
  rw [num_eq hr hb, numF]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem num_inr_zero {l : LMv T FL} (hl : ¬ IsMin (load R ch FL lhat n o) l.1.castSucc l.2.1 ∨
    ¬ Pick FL (load R ch FL lhat n o) l) : num R ch FL lhat n o (.inr l) = 0 := by
  classical
  rcases hl with hl | hl
  · have h1 : tmin FL (load R ch FL lhat n o) l = 0 := tmin_zero fun q => seg_zero hr hb hl _ q
    have := num_inr_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb l
    omega
  · rw [num_eq hr hb, numF, if_neg hl]

theorem alv_inr_zero {l : LMv T FL} (hl : ¬ IsMin (load R ch FL lhat n o) l.1.castSucc l.2.1 ∨
    ¬ Pick FL (load R ch FL lhat n o) l) (ν : (kindM R ch FL (.inr l)).Cn) :
    alv R ch FL lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) = 0 := by
  unfold alv
  rw [num_inr_zero hr hb hl]
  exact alvN_zero hr hb _


theorem mid_load_le (j : Fin J) {i : Fin h} (hi : IsMin (load R ch FL lhat n o) j.castSucc i) (e' : T.Ed (j + 1))
    (he' : T.ty e' = i) : load R ch FL lhat n o (.edge j.succ e') ≤
      ∑ e ∈ univ.filter (fun e : T.Ed j => T.πE e = e'), load R ch FL lhat n o (.edge j.castSucc e) := by
  classical
  have hx2 : ∀ e : T.Ed j, okR T R ch (.mid j e 2) :=
    fun e => ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
  refine (load_le_sum ((univ.filter fun e : T.Ed j => T.πE e = e').image
    fun e => (⟨.inl ⟨.mid j e 2, hx2 e⟩, false⟩ : NM R FL (ch := ch))) (bt_edge_succ j e') ?_).trans ?_
  · rintro ⟨⟨x, hx⟩ | l, ν⟩ hν hne
    · obtain ⟨e, h1, h2, h3⟩ := tgR_edge_succ (x := x) (ν := ν) hν
      subst h1
      have h2 : ν = false := h2
      subst h2
      exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, h3⟩, rfl⟩
    · exfalso
      obtain ⟨j', i', ω, d⟩ := l
      obtain ⟨h1, h2⟩ := Tg.edge.inj hν
      have hj : j' = j := Fin.succ_injective _ h1
      subst hj
      have h3 := eq_of_heq h2
      have h4 := ((T.nr j'.2 i').symm (ω, FL.cn d ν)).2
      rw [h3, he'] at h4
      refine hne (alv_inr_zero hr hb (Or.inl fun hcon => ?_) ν)
      have : IsMin (load R ch FL lhat n o) j'.castSucc i' := hcon
      have h5 : i = i' := by
        rcases lt_trichotomy i i' with hlt | heq | hlt
        · exact absurd hi.1 (this.2 i hlt)
        · exact heq
        · exact absurd this.1 (hi.2 i' hlt)
      exact h4 h5
  · refine Finset.sum_image_le_of_nonneg ?_ |>.trans ?_
    · intro _ _; exact Nat.zero_le _
    · exact Finset.sum_le_sum fun e _ => (alv_mid_le hr hb j e 2 (hx2 e) false).1


theorem alive_sq (l : LMv T FL) : r * b * ∑ ν : (FL.L l.2.2.2).Cn, (alv R ch FL lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch))) ^ 2 ≤
    FL.G₁ * (num R ch FL lhat n o (.inr l)) ^ 2 := by
  classical
  set t := num R ch FL lhat n o (.inr l) with ht
  by_cases hg : GoodL R ch FL o l t
  · have h1 : ∀ ν : (FL.L l.2.2.2).Cn, alv R ch FL lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) = o ⟨.inr l, ν⟩ := by
      intro ν
      rw [alv_inr, ← ht, if_pos hg]
    rw [Finset.sum_congr rfl fun ν _ => by rw [h1 ν]]
    exact hg
  · have h1 : ∀ ν : (FL.L l.2.2.2).Cn, alv R ch FL lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) ≤ t := by
      intro ν
      rw [alv_inr, ← ht, if_neg hg]
      exact min_le_right _ _
    obtain ⟨i0⟩ := FL.nonempty l.2.2.2
    have h2 := FL.L2 l.2.2.2 i0
    have h3 : ∑ ν : (FL.L l.2.2.2).Cn, (alv R ch FL lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch))) ^ 2 ≤
        (∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun ν _ => ?_
      have h4 := FL.lam_pos l.2.2.2
      have h5 : 1 ≤ ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ t ^ 2 := Nat.pow_le_pow_left (h1 ν) 2
        _ ≤ _ := Nat.le_mul_of_pos_left _ h5
    calc _ ≤ r * b * ((∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2) :=
          Nat.mul_le_mul_left _ h3
      _ = (r * b * ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2 := by ring
      _ ≤ FL.G₁ * t ^ 2 := Nat.mul_le_mul_right _ h2


theorem other_load_le (j : Fin J) {i : Fin h} (hi : IsMin (load R ch FL lhat n o) j.castSucc i) (ω : T.V (j + 1) i)
    (d : FL.Di) (hd : Pick FL (load R ch FL lhat n o) ⟨j, i, ω, d⟩) (ν : T.Nr) :
    load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) ≤
      alv R ch FL lhat n o (⟨.inr ⟨j, i, ω, d⟩, (FL.cn d).symm ν⟩ : NM R FL (ch := ch)) := by
  classical
  refine (load_le_sum {(⟨.inr ⟨j, i, ω, d⟩, (FL.cn d).symm ν⟩ : NM R FL (ch := ch))} (bt_edge_succ j _) ?_).trans ?_
  · rintro ⟨⟨x, hx⟩ | l, ν'⟩ hν hne
    · exfalso
      obtain ⟨e, h1, h2, h3⟩ := tgR_edge_succ (x := x) (ν := ν') hν
      subst h1
      refine hne ((alv_mid_le hr hb j e 2 hx ν').2 fun hcon => ?_)
      have h4 : T.ty e = i := by
        rcases lt_trichotomy i (T.ty e) with hlt | heq | hlt
        · exact absurd hi.1 (hcon.2 i hlt)
        · exact heq.symm
        · exact absurd hcon.1 (hi.2 _ hlt)
      have h5 := ((T.nr j.2 i).symm (ω, ν)).2
      rw [← h3, T.π_ty j.2, h4] at h5
      exact h5 rfl
    · obtain ⟨j', i', ω', d'⟩ := l
      obtain ⟨h1, h2⟩ := Tg.edge.inj hν
      have hj : j' = j := Fin.succ_injective _ h1
      subst hj
      have h3 := eq_of_heq h2
      have hmin : IsMin (load R ch FL lhat n o) j'.castSucc i' := by
        by_contra hcon
        exact hne (alv_inr_zero hr hb (Or.inl hcon) ν')
      have hii : i' = i := by
        rcases lt_trichotomy i i' with hlt | heq | hlt
        · exact absurd hi.1 (hmin.2 i hlt)
        · exact heq.symm
        · exact absurd hmin.1 (hi.2 _ hlt)
      subst hii
      have h4 : (T.nr j'.2 i').symm (ω', FL.cn d' ν') = (T.nr j'.2 i').symm (ω, ν) := Subtype.ext h3
      have h5 := (T.nr j'.2 i').symm.injective h4
      simp only [Prod.mk.injEq] at h5
      obtain ⟨h6, h7⟩ := h5
      subst h6
      have hpk : Pick FL (load R ch FL lhat n o) ⟨j', i', ω', d'⟩ := by
        by_contra hcon
        exact hne (alv_inr_zero hr hb (Or.inr hcon) ν')
      have hdd : d' = d := by
        have e : tmin FL (load R ch FL lhat n o) (⟨j', i', ω', d'⟩ : LMv T FL) =
          tmin FL (load R ch FL lhat n o) (⟨j', i', ω', d⟩ : LMv T FL) := rfl
        rcases lt_trichotomy (Fintype.equivFin FL.Di d) (Fintype.equivFin FL.Di d') with hlt | heq | hlt
        · exact absurd hd.1 (hpk.2 d hlt)
        · exact ((Fintype.equivFin FL.Di).injective heq).symm
        · exact absurd hpk.1 (hd.2 d' hlt)
      subst hdd
      have h8 : ν' = (FL.cn d').symm ν := by
        rw [← h7]
        exact ((FL.cn d').symm_apply_apply ν').symm
      subst h8
      exact mem_singleton_self _
  · rw [Finset.sum_singleton]


theorem _root_.Paper.thm_tree_kappa (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (j : Fin J) :
    T.kap (fun e : T.Ed (j + 1) => load R ch FL lhat n o (.edge j.succ e)) ≤
      ρ * T.kap (fun e : T.Ed j => load R ch FL lhat n o (.edge j.castSucc e)) +
        √FL.C₁ * FL.a₁ / b * Fintype.card (T.X (j + 1)) := by
  classical
  obtain ⟨i, hi⟩ := exists_isMin hh (load R ch FL lhat n o) j.castSucc
  have hd0 : ∃ d0 : FL.Di, True := by
    by_contra hcon
    push Not at hcon
    have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
    obtain ⟨t, ht⟩ := exists_nat_ge (√(T.NN2 fun _ => 0) / FL.a₁)
    obtain ⟨d, -⟩ := FL.L1 (fun _ => 0) t (by rw [div_le_iff₀ ha] at ht; linarith)
    exact hcon d
  obtain ⟨d0, -⟩ := hd0
  refine Tower.load_step j.2 hr hb hbD FL.C₁_nonneg (Nat.cast_nonneg _) hρ hρ1 (i := i) ?_ ?_
    (fun ω => tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d0⟩ : LMv T FL)) ?_ ?_
  · exact isMin_le hi
  · intro e' he'
    exact mid_load_le hr hb j hi e' he'
  · intro ω
    obtain ⟨d, hd⟩ := exists_pick (load R ch FL lhat n o) (⟨j, i, ω, d0⟩ : LMv T FL)
    have hd : Pick FL (load R ch FL lhat n o) (⟨j, i, ω, d⟩ : LMv T FL) := hd
    have h1 := alive_sq (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hr hb (⟨j, i, ω, d⟩ : LMv T FL)
    have h2 := num_inr_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hr hb (⟨j, i, ω, d⟩ : LMv T FL)
    have h3 : num R ch FL lhat n o (.inr (⟨j, i, ω, d⟩ : LMv T FL)) ≤ tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d0⟩ : LMv T FL) := h2
    set t := tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d0⟩ : LMv T FL) with ht
    have h4 : ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1)) ^ 2 ≤
        ∑ ν : (FL.L d).Cn, (alv R ch FL lhat n o (⟨.inr ⟨j, i, ω, d⟩, ν⟩ : NM R FL (ch := ch))) ^ 2 := by
      rw [← Equiv.sum_comp (FL.cn d)]
      refine Finset.sum_le_sum fun ν _ => Nat.pow_le_pow_left ?_ 2
      have := other_load_le hr hb j hi ω d hd (FL.cn d ν)
      rwa [Equiv.symm_apply_apply] at this
    have h5 : r * b * ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1)) ^ 2 ≤ FL.G₁ * t ^ 2 :=
      (Nat.mul_le_mul_left _ h4).trans (h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 2)))
    have h6 : (r : ℝ) * b * ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) : ℝ) ^ 2 ≤
        FL.G₁ * (t : ℝ) ^ 2 := by exact_mod_cast h5
    have h7 : (FL.G₁ : ℝ) * (t : ℝ) ^ 2 ≤ 2 * FL.C₁ * (FL.a₁ : ℝ) ^ 2 * (t : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right FL.G₁_le (sq_nonneg _)
    change (r : ℝ) * b / 2 * ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) : ℝ) ^ 2 ≤ _
    have h8 : (r : ℝ) * b / 2 * ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) : ℝ) ^ 2 =
        ((r : ℝ) * b * ∑ ν : T.Nr, (load R ch FL lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) : ℝ) ^ 2) / 2 := by ring
    rw [h8]
    linarith
  · intro ω
    exact tmin_le hb _ _ fun q => seg_le hr hb j i ω q

end Stage

end Nc.Tow
end
/- Source module Nc.Tow.Slp1. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}


def tgEquiv (T : Tower h b D J r) (m AA : ℕ) : Tg T m AA ≃ Unit ⊕ ((Σ j : Fin (J + 1), T.Ed j) ⊕
    (RM T m AA ⊕ (Σ j : Fin J, Σ i : Fin h, T.V (j + 1) i × Sym2 T.Fl))) where
  toFun
    | .done => .inl ()
    | .edge j e => .inr (.inl ⟨j, e⟩)
    | .nxt x => .inr (.inr (.inl x))
    | .seg j i ω q => .inr (.inr (.inr ⟨j, i, ω, q⟩))
  invFun
    | .inl _ => .done
    | .inr (.inl x) => .edge x.1 x.2
    | .inr (.inr (.inl x)) => .nxt x
    | .inr (.inr (.inr x)) => .seg x.1 x.2.1 x.2.2.1 x.2.2.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ <;> rfl

instance (T : Tower h b D J r) (m AA : ℕ) : Fintype (Tg T m AA) := Fintype.ofEquiv _ (tgEquiv T m AA).symm

variable (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T)


noncomputable def Wb (U0 U1 : ℕ) : ℕ := AA * AA * U0 + Fintype.card (NM R FL (ch := ch)) * U1


structure Bnd (U0 U1 Y : ℕ) : Prop where
  aa : AA * AA ≤ Y
  w : Wb R ch FL U0 U1 ≤ Y
  nm : Fintype.card (NM R FL (ch := ch)) ≤ Y
  mv : Fintype.card (Mv T R ch FL) ≤ Y
  tg : Fintype.card (Tg T m AA) ≤ Y
  nd : Fintype.card (Nd T) ≤ Y
  fl : Fintype.card (Sym2 T.Fl) ≤ Y
  di : Fintype.card FL.Di ≤ Y
  h : h ≤ Y
  j : J + 1 ≤ Y
  t : tend J m ≤ Y
  tt : b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 ≤ Y

variable {R ch FL}

namespace Bnd

variable {Y : ℕ} (hB : Bnd R ch FL U0 U1 Y)
include hB

theorem u0 (a : Fin AA) : U0 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < AA * AA := Nat.mul_pos (Fin.pos a) (Fin.pos a)
  have h3 : U0 ≤ AA * AA * U0 := Nat.le_mul_of_pos_left _ h2
  omega

theorem u1 (ν : NM R FL (ch := ch)) : U1 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < Fintype.card (NM R FL (ch := ch)) := Fintype.card_pos_iff.2 ⟨ν⟩
  have h3 : U1 ≤ Fintype.card (NM R FL (ch := ch)) * U1 := Nat.le_mul_of_pos_left _ h2
  omega

theorem aa1 : AA ≤ Y := by
  have h1 := hB.aa
  rcases Nat.eq_zero_or_pos AA with h0 | h0
  · omega
  · exact (Nat.le_mul_of_pos_left _ h0).trans h1

theorem ed (j : Fin (J + 1)) : Fintype.card (T.Ed j) ≤ Y := by
  refine (Fintype.card_le_of_injective (fun e : T.Ed j => (Tg.edge j e : Tg T m AA)) ?_).trans hB.tg
  intro e e' he
  injection he

end Bnd

section Bounds

variable {lhat : ℕ} {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ}

theorem bt_le (hn : ∀ a c, n a c ≤ U0) (τ : Tg T m AA) : bt R ch lhat n τ ≤ AA * AA * U0 := by
  unfold bt
  split_ifs
  · calc _ ≤ ∑ _a : Fin AA, ∑ _c : Fin AA, U0 := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
          refine (card_filter_le _ _).trans ?_
          rw [card_range]
          exact hn a c
      _ = AA * AA * U0 := by simp; ring
  · exact Nat.zero_le _

theorem ld_le (hn : ∀ a c, n a c ≤ U0) (ho : ∀ ν, o ν ≤ U1) (N : Mv T R ch FL → ℕ) (τ : Tg T m AA) :
    ld R ch FL lhat n o N τ ≤ Wb R ch FL U0 U1 := by
  unfold ld Wb
  refine add_le_add (bt_le hn τ) ?_
  refine (Finset.sum_le_card_nsmul _ _ U1 fun ν _ => ?_).trans (by simp)
  split_ifs
  · exact (alvN_le _ _).trans (ho ν)
  · exact Nat.zero_le _

theorem fits_mono {L : Tg T m AA → ℕ} {l : LMv T FL} {s t : ℕ} (hst : s ≤ t) (hs : Fits FL L l s) :
    Fits FL L l t := fun q hq => (hs q hq).trans (Nat.mul_le_mul_left _ hst)


theorem tmin_lt (hb : 0 < b) {L : Tg T m AA → ℕ} (hL : ∀ τ, L τ ≤ Wb R ch FL U0 U1) (l : LMv T FL) :
    tmin FL L l < b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 := by
  set w := Wb R ch FL U0 U1 with hw
  set s := Fintype.card (Sym2 T.Fl) with hs
  have h1 := tmin_le hb L l (n' := fun _ => w) fun q => hL _
  have hN : T.NN2 (fun _ => w) ≤ ((b * s * w : ℕ) : ℝ) ^ 2 := by
    unfold Tower.NN2
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have e1 : (∑ q : Sym2 T.Fl, if q.IsDiag then (0 : ℝ) else ((w : ℕ) : ℝ) ^ 2) ≤ s * (w : ℝ) ^ 2 := by
      refine (Finset.sum_le_card_nsmul _ _ ((w : ℝ) ^ 2) fun q _ => ?_).trans (by simp [hs])
      split_ifs
      · positivity
      · exact le_rfl
    have e2 : ((b : ℝ) * (b - 1) / 2) ≤ (b : ℝ) ^ 2 := by nlinarith
    have e3 : (0 : ℝ) ≤ (b : ℝ) * (b - 1) / 2 := by
      have : (0 : ℝ) ≤ b - 1 := by linarith
      positivity
    have e4 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ s := by exact_mod_cast h0
        nlinarith
    calc _ ≤ ((b : ℝ) * (b - 1) / 2) * (s * (w : ℝ) ^ 2) := mul_le_mul_of_nonneg_left e1 e3
      _ ≤ (b : ℝ) ^ 2 * ((s : ℝ) ^ 2 * (w : ℝ) ^ 2) := by
          refine mul_le_mul e2 (mul_le_mul_of_nonneg_right e4 (by positivity)) (by positivity) (by positivity)
      _ = _ := by push_cast; ring
  have h2 : √(T.NN2 fun _ => w) ≤ ((b * s * w : ℕ) : ℝ) := by
    rw [show ((b * s * w : ℕ) : ℝ) = √(((b * s * w : ℕ) : ℝ) ^ 2) from (Real.sqrt_sq (Nat.cast_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hN
  have ha : (1 : ℝ) ≤ FL.a₁ := by exact_mod_cast FL.a₁_pos
  have h3 : (tmin FL L l : ℝ) ≤ (b * s * w : ℕ) + 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : (FL.a₁ : ℝ) * ((b * s * w : ℕ) + 1) < FL.a₁ * tmin FL L l :=
      mul_lt_mul_of_pos_left hcon (by linarith)
    have h5 : ((b * s * w : ℕ) : ℝ) ≤ FL.a₁ * (b * s * w : ℕ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) ha
    nlinarith
  have h4 : tmin FL L l ≤ b * s * w + 1 := by exact_mod_cast h3
  omega


theorem tmin_sum {L : Tg T m AA → ℕ} {l : LMv T FL} {B : ℕ} (hlt : tmin FL L l < B) :
    tmin FL L l = ∑ s ∈ range B, ind (fun _ : Unit => ¬ ∃ d, Fits FL L (withD FL l d) s) () := by
  classical
  have h1 : ∀ s, (ind (fun _ : Unit => ¬ ∃ d, Fits FL L (withD FL l d) s) ()) = if s < tmin FL L l then 1 else 0 := by
    intro s
    by_cases hs : s < tmin FL L l
    · rw [if_pos hs, ind_true]
      intro hd
      have h3 : tmin FL L l ≤ s := Nat.sInf_le hd
      omega
    · rw [if_neg hs, ind_false]
      intro hn
      obtain ⟨d, hd⟩ := tmin_spec L l
      exact hn ⟨d, fits_mono (not_lt.1 hs) hd⟩
  rw [Finset.sum_congr rfl fun s _ => h1 s, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : (range B).filter (fun s => s < tmin FL L l) = range (tmin FL L l) := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [h2, card_range]

end Bounds

end Nc.Tow
end
/- Source module Nc.Tow.Slp2. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable (nx : Inp → Fin AA → Fin AA → ℕ) (ox : Inp → NM R FL (ch := ch) → ℕ) (lhat : ℕ)


structure Base (H : Set (Inp → ℕ)) : Prop where
  n : ∀ a c, (fun x => nx x a c) ∈ H
  o : ∀ ν, (fun x => ox x ν) ∈ H

theorem Base.weaken {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {H H' : Set (Inp → ℕ)}
    (hb : Base nx ox H) (hH : H ⊆ H') : Base nx ox H' :=
  ⟨fun a c => hH (hb.n a c), fun ν => hH (hb.o ν)⟩


structure Stat (H : Set (Inp → ℕ)) : Prop extends Base nx ox H where
  valid : ind (fun x => Valid lhat (nx x)) ∈ H
  bt : ∀ τ : Tg T m AA, (fun x => bt R ch lhat (nx x) τ) ∈ H
  q : ∀ l : LMv T FL, (fun x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2) ∈ H

theorem Stat.weaken {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {lhat : ℕ}
    {H H' : Set (Inp → ℕ)} (hb : Stat nx ox lhat H) (hH : H ⊆ H') : Stat nx ox lhat H' :=
  ⟨hb.toBase.weaken hH, hH hb.valid, fun τ => hH (hb.bt τ), fun l => hH (hb.q l)⟩


structure Rng (U0 U1 : ℕ) : Prop where
  n : ∀ x a c, nx x a c ≤ U0
  o : ∀ x ν, ox x ν ≤ U1

variable {nx ox lhat} (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hR : Rng nx ox U0 U1)
include hA hB hR

theorem card_cn (l : LMv T FL) : Fintype.card (FL.L l.2.2.2).Cn ≤ Y := by
  refine (Fintype.card_le_of_injective
    (fun ν : (FL.L l.2.2.2).Cn => (⟨Sum.inr l, ν⟩ : NM R FL (ch := ch))) ?_).trans hB.nm
  intro ν ν' he
  have := eq_of_heq (Sigma.mk.inj he).2
  exact this

theorem py_valid (hb : Base nx ox H) : PY Dd H Y 6 fun x => Valid lhat (nx x) := by
  have hY := hA.pos
  unfold Valid
  refine PY.forall_univ hA (by simpa using hB.aa1) fun a => PY.rel1 hA (fun s => s ≤ lhat) ?_
  refine CY.sum hA univ (by simpa using hB.aa1) (fun c _ => ?_) fun x => hA.lt_of_le3 ?_
  · by_cases hca : c = a
    · simp only [if_pos hca]
      exact (CY.const 0 hA.zero_lt).mono hY (Nat.zero_le 1)
    · simp only [if_neg hca]
      refine CY.op hA (fun s t => s + t) (CY.base (hb.n a c) hY) (CY.base (hb.n c a) hY) fun x => hA.lt_of_le3 ?_
      have h1 := hR.n x a c
      have h2 := hR.n x c a
      have h3 := hB.u0 a
      have h4 : Y ≤ Y ^ 3 := Nat.le_self_pow (by omega) Y
      change nx x a c + nx x c a ≤ _
      omega
  · have h3 := hB.u0 a
    calc _ ≤ ∑ _c : Fin AA, 2 * Y := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h1 := hR.n x a c
          have h2 := hR.n x c a
          split_ifs <;> omega
      _ = AA * (2 * Y) := by simp
      _ ≤ Y * (2 * Y) := Nat.mul_le_mul_right _ hB.aa1
      _ = 2 * Y ^ 2 := by ring
      _ ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))

theorem cy_bt (hb : Base nx ox H) (hv : ind (fun x => Valid lhat (nx x)) ∈ H) (τ : Tg T m AA) :
    CY Dd H Y 7 fun x => bt R ch lhat (nx x) τ := by
  classical
  have hY := hA.pos
  have hb0 : ∀ x, ∑ a, ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card ≤ Y := by
    intro x
    refine le_trans ?_ hB.w
    unfold Wb
    refine le_trans ?_ (Nat.le_add_right _ _)
    calc _ ≤ ∑ _a : Fin AA, ∑ _c : Fin AA, U0 := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
          refine (card_filter_le _ _).trans ?_
          rw [card_range]
          exact hR.n x a c
      _ = AA * AA * U0 := by simp; ring
  have h1 : CY Dd H Y 5 fun x => ∑ a, ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card := by
    refine CY.sum hA univ (by simpa using hB.aa1) (fun a _ => ?_) fun x => hA.lt_of_le (hb0 x)
    refine CY.sum hA univ (by simpa using hB.aa1) (fun c _ => ?_) fun x => hA.lt_of_le ?_
    · refine CY.op1 hA (fun s => ((range s).filter fun k => tgB T R ch a c k = τ).card)
        (CY.base (hb.n a c) hY) fun x => hA.lt_of_le ?_
      refine (card_filter_le _ _).trans ?_
      rw [card_range]
      exact (hR.n x a c).trans (hB.u0 a)
    · refine le_trans ?_ (hb0 x)
      exact Finset.single_le_sum (f := fun a => ∑ c, ((range (nx x a c)).filter fun k => tgB T R ch a c k = τ).card)
        (fun _ _ => Nat.zero_le _) (mem_univ a)
  refine (CY.ite hA ((PY.base hv hY).mono hY (Nat.zero_le 5)) h1
    ((CY.const 0 hA.zero_lt).mono hY (Nat.zero_le 5)) (fun x => hA.lt_of_le (hb0 x)) fun _ => hA.zero_lt).congr
    fun x => ?_
  rfl

theorem cy_q (hb : Base nx ox H) (l : LMv T FL) :
    CY Dd H Y 3 fun x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2 := by
  have hY := hA.pos
  have h1 : ∀ x (ν : (FL.L l.2.2.2).Cn), ox x ⟨Sum.inr l, ν⟩ ^ 2 ≤ Y ^ 2 := fun x ν =>
    Nat.pow_le_pow_left ((hR.o x _).trans (hB.u1 (⟨Sum.inr l, ν⟩ : NM R FL (ch := ch)))) 2
  refine CY.sum hA univ (card_cn hA hB hR l) (fun ν _ => ?_) fun x => hA.lt_of_le3 ?_
  · refine CY.op1 hA (fun s => s ^ 2) (CY.base (hb.o _) hY) fun x => hA.lt_of_le3 ((h1 x ν).trans ?_)
    have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
    omega
  · calc _ ≤ ∑ _ν : (FL.L l.2.2.2).Cn, Y ^ 2 := Finset.sum_le_sum fun ν _ => h1 x ν
      _ = Fintype.card (FL.L l.2.2.2).Cn * Y ^ 2 := by simp
      _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ (card_cn hA hB hR l)
      _ = Y ^ 3 := by ring
      _ ≤ 2 * Y ^ 3 := by omega


theorem stat_stage (hS : SY inp Y p c H) (hb : Base nx ox H) :
    ∃ H', SY inp Y p (c + 3) H' ∧ H ⊆ H' ∧ Stat nx ox lhat H' := by
  have hY := hA.pos
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Unit) (fun _ => ind fun x => Valid lhat (nx x)) (a := 6) (e := 0)
    (by simp) (fun _ => py_valid hA hB hR hb) (by omega)
  have hb1 := hb.weaken u1
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Tg T m AA) (fun τ x => bt R ch lhat (nx x) τ) (a := 7) (e := 1)
    (by simpa using hB.tg) (fun τ => cy_bt hA hB hR hb1 (f1 ()) τ) (by omega)
  have hl : Fintype.card (LMv T FL) ≤ Y := by
    refine (Fintype.card_le_of_injective (fun l : LMv T FL => (Sum.inr l : Mv T R ch FL)) Sum.inr_injective).trans hB.mv
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := LMv T FL)
    (fun l x => ∑ ν : (FL.L l.2.2.2).Cn, ox x ⟨Sum.inr l, ν⟩ ^ 2) (a := 3) (e := 1)
    (by simpa using hl) (fun l => cy_q hA hB hR (hb1.weaken u2) l) (by omega)
  exact ⟨H3, s3, u1.trans (u2.trans u3), (hb1.weaken u2).weaken u3, u3 (u2 (f1 ())), fun τ => u3 (f2 τ), f3⟩


theorem cy_alvN (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ} (hN : ∀ mv, (fun x => Nf x mv) ∈ H)
    (ν : NM R FL (ch := ch)) : CY Dd H Y 3 fun x => alvN R ch FL (ox x) ν (Nf x ν.1) := by
  have hY := hA.pos
  have hlt : ∀ x, alvN R ch FL (ox x) ν (Nf x ν.1) ≤ Y := fun x =>
    ((alvN_le _ _).trans (hR.o x ν)).trans (hB.u1 ν)
  rcases ν with ⟨y | l, ν⟩
  · refine CY.mono hY (a := 1) ((CY.op hA (fun s t => if s = t then t else 0) (CY.base (hs.o _) hY)
      (CY.base (hN (.inl y)) hY) fun x => hA.lt_of_le (hlt x)).congr fun x => ?_) (by omega)
    exact (alvN_inl y ν _).symm
  · have hg : PY Dd H Y 1 fun x => GoodL R ch FL (ox x) l (Nf x (.inr l)) :=
      PY.rel hA (fun q t => r * b * q ≤ FL.G₁ * t ^ 2) (CY.base (hs.q l) hY) (CY.base (hN (.inr l)) hY)
    have ho : ∀ x, ox x ⟨.inr l, ν⟩ ≤ Y := fun x => (hR.o x _).trans (hB.u1 ⟨.inr l, ν⟩)
    have hm : CY Dd H Y 1 fun x => min (ox x ⟨.inr l, ν⟩) (Nf x (.inr l)) :=
      CY.op hA (fun s t => min s t) (CY.base (hs.o _) hY) (CY.base (hN (.inr l)) hY)
        fun x => hA.lt_of_le ((min_le_left _ _).trans (ho x))
    refine (CY.ite hA hg ((CY.base (hs.o ⟨.inr l, ν⟩) hY).mono hY (Nat.zero_le 1)) hm
      (fun x => hA.lt_of_le (ho x)) fun x => hA.lt_of_le ((min_le_left _ _).trans (ho x))).congr fun x => ?_
    exact (alvN_inr l ν _).symm


theorem cy_ld (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ}
    (ha : ∀ ν : NM R FL (ch := ch), (fun x => alvN R ch FL (ox x) ν (Nf x ν.1)) ∈ H) (τ : Tg T m AA) :
    CY Dd H Y 3 fun x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ := by
  have hY := hA.pos
  have hle : ∀ x, ld R ch FL lhat (nx x) (ox x) (Nf x) τ ≤ Y := fun x =>
    (ld_le (hR.n x) (hR.o x) _ _).trans hB.w
  have e : ∀ x, ld R ch FL lhat (nx x) (ox x) (Nf x) τ = bt R ch lhat (nx x) τ +
      ∑ ν ∈ univ.filter (fun ν : NM R FL (ch := ch) => tgM R ch FL ν.1 ν.2 = τ),
        alvN R ch FL (ox x) ν (Nf x ν.1) := by
    intro x
    rw [Finset.sum_filter]
    rfl
  have h1 : CY Dd H Y 2 fun x => ∑ ν ∈ univ.filter (fun ν : NM R FL (ch := ch) => tgM R ch FL ν.1 ν.2 = τ),
        alvN R ch FL (ox x) ν (Nf x ν.1) := by
    refine CY.sum hA _ ((card_filter_le _ _).trans hB.nm) (fun ν _ => CY.base (ha ν) hY) fun x => hA.lt_of_le ?_
    have := hle x
    rw [e] at this
    omega
  refine (CY.op hA (fun s t => s + t) ((CY.base (hs.bt τ) hY).mono hY (Nat.zero_le 2)) h1 fun x => ?_).congr
    fun x => (e x).symm
  have := hle x
  rw [e] at this
  exact hA.lt_of_le this


theorem ld_stage (hS : SY inp Y p c H) (hs : Stat nx ox lhat H) {Nf : Inp → Mv T R ch FL → ℕ}
    (hN : ∀ mv, (fun x => Nf x mv) ∈ H) : ∃ H', SY inp Y p (c + 2) H' ∧ H ⊆ H' ∧
      (∀ ν : NM R FL (ch := ch), (fun x => alvN R ch FL (ox x) ν (Nf x ν.1)) ∈ H') ∧
      ∀ τ, (fun x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ) ∈ H' := by
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := NM R FL (ch := ch))
    (fun ν x => alvN R ch FL (ox x) ν (Nf x ν.1)) (a := 3) (e := 1) (by simpa using hB.nm)
    (fun ν => cy_alvN hA hB hR hs hN ν) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Tg T m AA)
    (fun τ x => ld R ch FL lhat (nx x) (ox x) (Nf x) τ) (a := 3) (e := 1) (by simpa using hB.tg)
    (fun τ => cy_ld hA hB hR (hs.weaken u1) f1 τ) (by omega)
  exact ⟨H2, s2, u1.trans u2, fun ν => u2 (f1 ν), f2⟩

end Nc.Tow
end
/- Source module Nc.Tow.Slp3. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}

theorem ind_eq {X X' : Type} {P : X → Prop} {Q : X' → Prop} {x : X} {y : X'} (hi : P x ↔ Q y) :
    ind P x = ind Q y := by
  by_cases hp : P x
  · rw [ind_true hp, ind_true (hi.1 hp)]
  · rw [ind_false hp, ind_false fun hq => hp (hi.2 hq)]

section Loads

variable {L : Inp → Tg T m AA → ℕ} (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hb : 0 < b)
  (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hb hL

theorem sqs_le (x : Inp) (j : Fin (J + 1)) (i : Fin h) : sqs (L x) j i ≤ 2 * Y ^ 3 := by
  unfold sqs
  calc _ ≤ ∑ _e : T.Ed j, Y ^ 2 := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs
        · exact Nat.pow_le_pow_left ((hL x _).trans hB.w) 2
        · exact Nat.zero_le _
    _ = Fintype.card (T.Ed j) * Y ^ 2 := by simp
    _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ (hB.ed j)
    _ = Y ^ 3 := by ring
    _ ≤ 2 * Y ^ 3 := by omega

theorem cy_sqs (hm : ∀ τ, (fun x => L x τ) ∈ H) (j : Fin (J + 1)) (i : Fin h) :
    CY Dd H Y 3 fun x => sqs (L x) j i := by
  have hY := hA.pos
  have e : ∀ x, sqs (L x) j i = ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), L x (.edge j e) ^ 2 := by
    intro x
    rw [Finset.sum_filter]
    rfl
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ ((card_filter_le _ _).trans (hB.ed j)) (fun e _ => ?_) fun x => ?_
  · refine CY.op1 hA (fun s => s ^ 2) (CY.base (hm _) hY) fun x => hA.lt_of_le3 ?_
    calc L x (.edge j e) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left ((hL x _).trans hB.w) 2
      _ ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
      _ ≤ 2 * Y ^ 3 := by omega
  · rw [← e x]
    exact hA.lt_of_le3 (sqs_le hA hB hb hL x j i)

omit hb hL in
theorem py_isMin (hq : ∀ j i, (fun x => sqs (L x) j i) ∈ H) (j : Fin (J + 1)) (i : Fin h) :
    PY Dd H Y 7 fun x => IsMin (L x) j i := by
  have hY := hA.pos
  have h1 : ∀ i, PY Dd H Y 3 fun x => ∀ i', sqs (L x) j i ≤ sqs (L x) j i' := fun i =>
    PY.forall_univ hA (by simpa using hB.h) fun i' =>
      PY.rel hA (fun s t => s ≤ t) (CY.base (hq j i) hY) (CY.base (hq j i') hY)
  have h2 : PY Dd H Y 6 fun x => ∀ i' ∈ univ.filter (fun i' => i' < i), ¬ ∀ i'', sqs (L x) j i' ≤ sqs (L x) j i'' :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans (by simpa using hB.h)) fun i' _ => PY.not hA (h1 i')
  refine (PY.and hA ((h1 i).mono hY (by omega)) h2).congr fun x => ?_
  unfold IsMin
  simp

omit hb hL in
theorem py_fits {s : Inp → ℕ} {a : ℕ} (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : LMv T FL) (hs : CY Dd H Y a s) :
    PY Dd H Y (a + 3) fun x => Fits FL (L x) l (s x) := by
  classical
  have hY := hA.pos
  have h1 : PY Dd H Y (a + 1 + 2) fun x => ∀ q ∈ univ.filter (fun q : Sym2 T.Fl => ¬ q.IsDiag),
      L x (.seg l.1 l.2.1 l.2.2.1 q) ≤ slo FL l.2.2.2 q * s x :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans hB.fl) fun q _ =>
      PY.rel hA (fun u t => u ≤ slo FL l.2.2.2 q * t) ((CY.base (hm _) hY).mono hY (Nat.zero_le a)) hs
  refine h1.congr fun x => ?_
  unfold Fits
  simp

theorem cy_tmin (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : LMv T FL) : CY Dd H Y 8 fun x => tmin FL (L x) l := by
  have hY := hA.pos
  have h1 : ∀ s ∈ range Y, PY Dd H Y 6 fun x => ¬ ∃ d, Fits FL (L x) (withD FL l d) s := by
    intro s hs
    refine PY.not hA (PY.exists_univ hA hB.di fun d => ?_)
    exact py_fits hA hB hm (withD FL l d) (CY.const s (hA.lt_of_le (mem_range.1 hs).le))
  have hlt : ∀ x, tmin FL (L x) l < Y := fun x =>
    lt_of_lt_of_le (tmin_lt hb (fun τ => hL x τ) l) hB.tt
  have e : ∀ x, tmin FL (L x) l = ∑ s ∈ range Y, ind (fun x => ¬ ∃ d, Fits FL (L x) (withD FL l d) s) x := by
    intro x
    rw [tmin_sum (hlt x)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact ind_eq Iff.rfl
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ (by simp) (fun s hs => (h1 s hs).toCY) fun x => ?_
  rw [← e x]
  exact hA.lt_of_le (hlt x).le

omit hb hL in
theorem py_pick (hm : ∀ τ, (fun x => L x τ) ∈ H) (ht : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H) (l : LMv T FL) :
    PY Dd H Y 7 fun x => Pick FL (L x) l := by
  have hY := hA.pos
  have h1 : ∀ d, PY Dd H Y 3 fun x => Fits FL (L x) (withD FL l d) (tmin FL (L x) l) := fun d =>
    py_fits hA hB hm (withD FL l d) (CY.base (ht l) hY)
  have h0 : PY Dd H Y 3 fun x => Fits FL (L x) l (tmin FL (L x) l) := py_fits hA hB hm l (CY.base (ht l) hY)
  have h2 : PY Dd H Y 6 fun x => ∀ d ∈ univ.filter
      (fun d => Fintype.equivFin FL.Di d < Fintype.equivFin FL.Di l.2.2.2),
      ¬ Fits FL (L x) (withD FL l d) (tmin FL (L x) l) :=
    PY.forall_mem hA _ ((card_filter_le _ _).trans hB.di) fun d _ => PY.not hA (h1 d)
  refine (PY.and hA (h0.mono hY (by omega)) h2).congr fun x => ?_
  unfold Pick
  simp

omit hb hL in
theorem py_actR (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H) (y : RM T m AA) :
    PY Dd H Y 0 fun x => ActR (L x) y := by
  have hY := hA.pos
  rcases y with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact PY.const hA True
  · exact PY.base (hi _ _) hY
  · by_cases hs : s = 0
    · refine (PY.base (hi j.castSucc (T.ty e)) hY).congr fun x => ?_
      exact ⟨fun h _ => h, fun h => h hs⟩
    · refine (PY.const hA True).congr fun x => ?_
      exact ⟨fun _ h => absurd h hs, fun _ => trivial⟩
  · exact PY.const hA True

theorem cy_numF (hm : ∀ τ, (fun x => L x τ) ∈ H) (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H)
    (ht : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H) (hp : ∀ l : LMv T FL, ind (fun x => Pick FL (L x) l) ∈ H)
    (mv : Mv T R ch FL) : CY Dd H Y 2 fun x => numF R ch FL (L x) mv := by
  classical
  have hY := hA.pos
  rcases mv with y | l
  · refine (CY.ite hA (py_actR hA hB hi y.1) (CY.base (hm (inpR T y.1)) hY) (CY.const 0 hA.zero_lt)
      (fun x => hA.lt_of_le ((hL x _).trans hB.w)) fun _ => hA.zero_lt).congr fun x => ?_
    unfold numF
    by_cases ha : ActR (L x) y.1
    · rw [if_pos ha]
      exact (if_pos ha).symm
    · rw [if_neg ha]
      exact (if_neg ha).symm
  · refine (CY.ite hA (PY.base (hp l) hY) (CY.base (ht l) hY) (CY.const 0 hA.zero_lt)
      (fun x => hA.lt_of_le (lt_of_lt_of_le (tmin_lt hb (fun τ => hL x τ) l) hB.tt).le) fun _ => hA.zero_lt).congr
      fun x => ?_
    unfold numF
    by_cases ha : Pick FL (L x) l
    · rw [if_pos ha]
      exact (if_pos ha).symm
    · rw [if_neg ha]
      exact (if_neg ha).symm


structure Chosen (L : Inp → Tg T m AA → ℕ) (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T)
    (H : Set (Inp → ℕ)) : Prop where
  isMin : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H
  tmin : ∀ l : LMv T FL, (fun x => tmin FL (L x) l) ∈ H
  pick : ∀ l : LMv T FL, ind (fun x => Pick FL (L x) l) ∈ H
  numF : ∀ mv : Mv T R ch FL, (fun x => numF R ch FL (L x) mv) ∈ H

omit hA hB hb hL in
theorem Chosen.weaken {L : Inp → Tg T m AA → ℕ} {H H' : Set (Inp → ℕ)} (hc : Chosen L R ch FL H) (hH : H ⊆ H') :
    Chosen L R ch FL H' :=
  ⟨fun j i => hH (hc.isMin j i), fun l => hH (hc.tmin l), fun l => hH (hc.pick l), fun mv => hH (hc.numF mv)⟩

theorem pick_stage (hS : SY inp Y p c H) (hm : ∀ τ, (fun x => L x τ) ∈ H) :
    ∃ H', SY inp Y p (c + 5) H' ∧ H ⊆ H' ∧ Chosen L R ch FL H' := by
  have hjh : Fintype.card (Fin (J + 1) × Fin h) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB.j hB.h
  have hl : Fintype.card (LMv T FL) ≤ Y ^ 1 := by
    rw [pow_one]
    exact (Fintype.card_le_of_injective (fun l : LMv T FL => (Sum.inr l : Mv T R ch FL)) Sum.inr_injective).trans hB.mv
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Fin (J + 1) × Fin h) (fun q x => sqs (L x) q.1 q.2) (a := 3) (e := 2)
    hjh (fun q => cy_sqs hA hB hb hL hm q.1 q.2) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Fin (J + 1) × Fin h) (fun q => ind fun x => IsMin (L x) q.1 q.2)
    (a := 7) (e := 2) hjh (fun q => py_isMin hA hB (fun j i => f1 (j, i)) q.1 q.2) (by omega)
  have m2 : ∀ τ, (fun x => L x τ) ∈ H2 := fun τ => u2 (u1 (hm τ))
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := LMv T FL) (fun l x => tmin FL (L x) l) (a := 8) (e := 1) hl
    (fun l => cy_tmin hA hB hb hL m2 l) (by omega)
  have m3 : ∀ τ, (fun x => L x τ) ∈ H3 := fun τ => u3 (m2 τ)
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (κ := LMv T FL) (fun l => ind fun x => Pick FL (L x) l) (a := 7) (e := 1) hl
    (fun l => py_pick hA hB m3 f3 l) (by omega)
  have m4 : ∀ τ, (fun x => L x τ) ∈ H4 := fun τ => u4 (m3 τ)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (κ := Mv T R ch FL) (fun mv x => numF R ch FL (L x) mv) (a := 2) (e := 1)
    (by simpa using hB.mv) (fun mv => cy_numF hA hB hb hL m4 (fun j i => u4 (u3 (f2 (j, i)))) (fun l => u4 (f3 l)) f4 mv)
    (by omega)
  exact ⟨H5, s5, u1.trans (u2.trans (u3.trans (u4.trans u5))), fun j i => u5 (u4 (u3 (f2 (j, i)))),
    fun l => u5 (u4 (f3 l)), fun l => u5 (f4 l), f5⟩

end Loads

variable {nx : Inp → Fin AA → Fin AA → ℕ} {ox : Inp → NM R FL (ch := ch) → ℕ} {lhat : ℕ}
variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hR : Rng nx ox U0 U1) (hb : 0 < b)
include hA hB hR hb


theorem num_stage (hS : SY inp Y p c H) (hs : Stat nx ox lhat H) (t : ℕ) :
    ∃ H', SY inp Y p (c + 1 + 8 * t) H' ∧ H ⊆ H' ∧
      ∀ mv : Mv T R ch FL, (fun x => numS R ch FL lhat (nx x) (ox x) t mv) ∈ H' := by
  have hY := hA.pos
  induction t with
  | zero =>
    obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Mv T R ch FL) (fun mv x => numS R ch FL lhat (nx x) (ox x) 0 mv)
      (a := 0) (e := 1) (by simpa using hB.mv) (fun mv => CY.const 0 hA.zero_lt) (by omega)
    exact ⟨H1, s1, u1, f1⟩
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    obtain ⟨H1, s1, u1, f1, g1⟩ := ld_stage hA hB hR s0 (hs.weaken u0) f0
    obtain ⟨H2, s2, u2, f2⟩ := pick_stage hA hB hb
      (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s1 g1
    obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := Mv T R ch FL)
      (fun mv x => numS R ch FL lhat (nx x) (ox x) (t + 1) mv) (a := 0) (e := 1) (by simpa using hB.mv)
      (fun mv => by
        by_cases ht : timeM R ch FL mv = t
        · refine (CY.base (f2.numF mv) hY).congr fun x => ?_
          rw [numS, if_pos ht]
        · refine (CY.base (u2 (u1 (f0 mv))) hY).congr fun x => ?_
          rw [numS, if_neg ht]) (by omega)
    exact ⟨H3, s3.le hA (by omega), u0.trans (u1.trans (u2.trans u3)), f3⟩


structure After (nx : Inp → Fin AA → Fin AA → ℕ) (ox : Inp → NM R FL (ch := ch) → ℕ) (lhat : ℕ)
    (H : Set (Inp → ℕ)) : Prop extends Stat nx ox lhat H,
    Chosen (fun x => load R ch FL lhat (nx x) (ox x)) R ch FL H where
  num : ∀ mv : Mv T R ch FL, (fun x => num R ch FL lhat (nx x) (ox x) mv) ∈ H
  alv : ∀ ν : NM R FL (ch := ch), (fun x => alv R ch FL lhat (nx x) (ox x) ν) ∈ H
  load : ∀ τ : Tg T m AA, (fun x => load R ch FL lhat (nx x) (ox x) τ) ∈ H

omit hA hB hR hb in
theorem After.weaken {H H' : Set (Inp → ℕ)} (ha : After nx ox lhat H) (hH : H ⊆ H') : After nx ox lhat H' where
  toStat := ha.toStat.weaken hH
  toChosen := ha.toChosen.weaken hH
  num mv := hH (ha.num mv)
  alv ν := hH (ha.alv ν)
  load τ := hH (ha.load τ)

theorem after_stage (hS : SY inp Y p c H) (hbs : Base nx ox H) :
    ∃ H', SY inp Y p (c + 11 + 8 * Y) H' ∧ H ⊆ H' ∧ After nx ox lhat H' := by
  obtain ⟨H1, s1, u1, f1⟩ := stat_stage hA hB hR hS hbs (lhat := lhat)
  obtain ⟨H2, s2, u2, f2⟩ := num_stage hA hB hR hb s1 f1 (tend J m)
  obtain ⟨H3, s3, u3, f3, g3⟩ := ld_stage hA hB hR s2 (f1.weaken u2)
    (Nf := fun x => num R ch FL lhat (nx x) (ox x)) f2
  obtain ⟨H4, s4, u4, f4⟩ := pick_stage (L := fun x => load R ch FL lhat (nx x) (ox x)) hA hB hb
    (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s3 g3
  refine ⟨H4, s4.le hA ?_, u1.trans (u2.trans (u3.trans u4)), (f1.weaken (u2.trans (u3.trans u4))), f4,
    fun mv => u4 (u3 (f2 mv)), fun ν => u4 (f3 ν), fun τ => u4 (g3 τ)⟩
  have := hB.t
  omega

end Nc.Tow
end
/- Source module Nc.Tow.Slp4. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

section Mem

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

theorem rkU_sum (u : Un R FL Pl U0 U1) : rkU R FL Pl lhat n o u =
    ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU R FL Pl v = tgU R FL Pl u ∧ ix R FL Pl v < ix R FL Pl u),
      ind (fun _ : Unit => AlU R FL Pl lhat n o v) () := by
  classical
  have h1 : ∀ v, ind (fun _ : Unit => AlU R FL Pl lhat n o v) () = if AlU R FL Pl lhat n o v then 1 else 0 := by
    intro v
    by_cases hv : AlU R FL Pl lhat n o v
    · rw [if_pos hv, ind_true (P := fun _ : Unit => AlU R FL Pl lhat n o v) hv]
    · rw [if_neg hv, ind_false (P := fun _ : Unit => AlU R FL Pl lhat n o v) hv]
  rw [Finset.sum_congr rfl fun v _ => h1 v, ← Finset.card_filter, Finset.filter_filter]
  unfold rkU rk
  congr 1
  ext v
  simp only [mem_filter, mem_Al, mem_univ, true_and]
  tauto

theorem mem_cons_inl (y : {x : RM T m AA // okR T R ch x}) (s : (kindM R ch FL (.inl y)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl y, s⟩ ↔
      ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) y.1 ∧ AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpR T y.1 := by
  classical
  simp only [consM]
  by_cases ha : ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) y.1
  · rw [if_pos ha, mem_filter, mem_Al]
    exact ⟨fun hu => ⟨ha, hu⟩, fun hu => hu.2⟩
  · rw [if_neg ha]
    exact ⟨fun hu => absurd hu (notMem_empty _), fun hu => absurd hu.1 ha⟩

theorem mem_cons_inr (l : LMv T FL) (e : (FL.L l.2.2.2).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔
      Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ∧ AlU R FL Pl lhat n o u ∧
        tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) ∧
        su FL l.2.2.2 e * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ rkU R FL Pl lhat n o u ∧
        rkU R FL Pl lhat n o u < (su FL l.2.2.2 e + 1) * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) := by
  classical
  simp only [consM]
  by_cases ha : Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l
  · rw [if_pos ha, mem_filter, mem_Al]
    exact ⟨fun hu => ⟨ha, hu⟩, fun hu => hu.2⟩
  · rw [if_neg ha]
    exact ⟨fun hu => absurd hu (notMem_empty _), fun hu => absurd hu.1 ha⟩


def SeenU (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) : Un R FL Pl U0 U1 → Prop
  | .init a c k => k.1 < (n a c).1
  | .new ν k => k.1 ≤ (o ν).1

theorem mem_cur (u : Un R FL Pl U0 U1) :
    u ∈ (plan R FL Pl lhat U0 U1).cur n o (Fintype.card (Mv T R ch FL)) ↔
      SeenU n o u ∧ ¬ ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
  classical
  unfold Plan.cur
  rw [mem_sdiff]
  refine and_congr ?_ (not_congr ?_)
  · unfold Plan.seenAt
    rw [mem_union, mem_biUnion]
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp [seen0, newUnits, SeenU]
    · constructor
      · rintro (h1 | ⟨x', -, h2⟩)
        · simp [seen0] at h1
        · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq] at h2
          exact h2.2
      · intro h1
        refine Or.inr ⟨ν.1, mem_filter.2 ⟨mem_univ _, ν.1.2⟩, ?_⟩
        simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        exact h1
  · unfold Plan.used
    rw [mem_biUnion]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨eZ R FL Pl z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨(eZ R FL Pl).symm z, mem_filter.2 ⟨mem_univ _, ((eZ R FL Pl).symm z).1.2⟩, ?_⟩
      change u ∈ consM R FL Pl lhat n o (eZ R FL Pl ((eZ R FL Pl).symm z))
      rw [Equiv.apply_symm_apply]
      exact hz

end Mem

variable {Inp ι : Type} {Dd Y p c TM : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}


structure Bnd2 (R : Routes T m Uu) (FL : FlagLaws F T) (Pl : Place T ch A') (U0 U1 Y TM : ℕ) : Prop where
  zm : Fintype.card (ZM R FL (ch := ch)) ≤ Y
  un : Fintype.card (Un R FL Pl U0 U1) ≤ Y
  tm : TM ≤ Y


def nX (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (x : Inp) : Fin AA → Fin AA → ℕ := nn (nI x)


noncomputable def oX (oI : Inp → (sys R FL Pl).N → Fin U1) (x : Inp) : NM R FL (ch := ch) → ℕ := oo R FL Pl (oI x)

theorem rng : Rng (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) U0 U1 where
  n x a c := Nat.le_of_lt_succ (nI x a c).2
  o x _ := (oI x _).2.le


structure Units (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (oI : Inp → (sys R FL Pl).N → Fin U1) (lhat TM : ℕ)
    (H : Set (Inp → ℕ)) : Prop where
  cons : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H
  num : ∀ mv : Mv T R ch FL, (fun x => num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  lt : ∀ (mv : Mv T R ch FL) (τ : Fin TM), ind (fun x => τ.1 < Tow.num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  pad : ∀ (z : ZM R FL (ch := ch)) (τ : Fin TM), ind (fun x => (consM R FL Pl lhat (nI x) (oI x) z).card ≤ τ.1 ∧
    τ.1 < Tow.num R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) z.1) ∈ H
  cur : ∀ u, ind (fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL))) ∈ H
  good : ∀ mv : Mv T R ch FL, ind (fun x => GoodMv R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  good' : ind (fun x => ∀ mv : Mv T R ch FL, GoodMv R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)) mv) ∈ H
  valid : ind (fun x => Valid lhat (nn (nI x))) ∈ H

theorem Units.weaken {H H' : Set (Inp → ℕ)} (hu : Units nI oI lhat TM H) (hH : H ⊆ H') : Units nI oI lhat TM H' :=
  ⟨fun z u => hH (hu.cons z u), fun mv => hH (hu.num mv), fun mv τ => hH (hu.lt mv τ), fun z τ => hH (hu.pad z τ),
    fun u => hH (hu.cur u), fun mv => hH (hu.good mv), hH hu.good', hH hu.valid⟩

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y TM)
include hA hB hB2

theorem py_al (ha : After (nX nI) (oX oI) lhat H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 2 fun x => AlU R FL Pl lhat (nI x) (oI x) u := by
  have hY := hA.pos
  rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
  · exact PY.and hA ((PY.base ha.valid hY).mono hY (Nat.zero_le 1))
      (PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c) hY))
  · exact (PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.alv (eN R FL Pl ν)) hY)).mono hY (by omega)

theorem cy_rk (hal : ∀ u, ind (fun x => AlU R FL Pl lhat (nI x) (oI x) u) ∈ H) (u : Un R FL Pl U0 U1) :
    CY Dd H Y 2 fun x => rkU R FL Pl lhat (nI x) (oI x) u := by
  have hY := hA.pos
  have e : ∀ x, rkU R FL Pl lhat (nI x) (oI x) u =
      ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU R FL Pl v = tgU R FL Pl u ∧ ix R FL Pl v < ix R FL Pl u),
        ind (fun x => AlU R FL Pl lhat (nI x) (oI x) v) x := by
    intro x
    rw [rkU_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : AlU R FL Pl lhat (nI x) (oI x) v
    · rw [ind_true (P := fun x => AlU R FL Pl lhat (nI x) (oI x) v) hv,
        ind_true (P := fun _ : Unit => AlU R FL Pl lhat (nI x) (oI x) v) hv]
    · rw [ind_false (P := fun x => AlU R FL Pl lhat (nI x) (oI x) v) hv,
        ind_false (P := fun _ : Unit => AlU R FL Pl lhat (nI x) (oI x) v) hv]
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ ((card_filter_le _ _).trans hB2.un) (fun v _ => CY.base (hal v) hY) fun x => hA.lt_of_le ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun v _ => ind_le _ _).trans ?_
  rw [smul_eq_mul, mul_one]
  exact (card_filter_le _ _).trans hB2.un

theorem py_cons (ha : After (nX nI) (oX oI) lhat H)
    (hal : ∀ u, ind (fun x => AlU R FL Pl lhat (nI x) (oI x) u) ∈ H)
    (hrk : ∀ u, (fun x => rkU R FL Pl lhat (nI x) (oI x) u) ∈ H) (z : ZM R FL (ch := ch)) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 5 fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z := by
  have hY := hA.pos
  rcases z with ⟨y | l, e⟩
  · have h1 : PY Dd H Y 0 fun x => ActR (load R ch FL lhat (nX nI x) (oX oI x)) y.1 := py_actR hA hB ha.isMin y.1
    have h2 := PY.and hA (h1.mono hY (Nat.zero_le 1)) (PY.and hA (PY.base (hal u) hY)
      (PY.const hA (tgU R FL Pl u = inpR T y.1)))
    exact (h2.congr fun x => (mem_cons_inl y e u).symm).mono hY (by omega)
  · have h1 : PY Dd H Y 0 fun x => Pick FL (load R ch FL lhat (nX nI x) (oX oI x)) l := PY.base (ha.pick l) hY
    have h3 : PY Dd H Y 1 fun x => su FL l.2.2.2 e * Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) ≤
        rkU R FL Pl lhat (nI x) (oI x) u :=
      PY.rel hA (fun s t => su FL l.2.2.2 e * s ≤ t) (CY.base (ha.num (.inr l)) hY) (CY.base (hrk u) hY)
    have h4 : PY Dd H Y 1 fun x => rkU R FL Pl lhat (nI x) (oI x) u <
        (su FL l.2.2.2 e + 1) * Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) :=
      PY.rel hA (fun s t => t < (su FL l.2.2.2 e + 1) * s) (CY.base (ha.num (.inr l)) hY) (CY.base (hrk u) hY)
    have h5 := PY.and hA (h1.mono hY (Nat.zero_le 4)) (PY.and hA ((PY.base (hal u) hY).mono hY (Nat.zero_le 3))
      (PY.and hA ((PY.const hA (tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e))).mono hY (Nat.zero_le 2))
        (PY.and hA h3 h4)))
    exact h5.congr fun x => (mem_cons_inr l e u).symm

theorem py_cur (ha : After (nX nI) (oX oI) lhat H)
    (hco : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 4 fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL)) := by
  have hY := hA.pos
  have h1 : PY Dd H Y 1 fun x => SeenU (nI x) (oI x) u := by
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · exact PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c) hY)
    · refine (PY.rel1 hA (fun s => k.1 ≤ s) (CY.base (ha.o (eN R FL Pl ν)) hY)).congr fun x => ?_
      have : oX oI x (eN R FL Pl ν) = (oI x ν).1 := by
        unfold oX oo
        rw [Equiv.symm_apply_apply]
      rw [this]
      exact Iff.rfl
  have h2 : PY Dd H Y 2 fun x => ∃ z, u ∈ consM R FL Pl lhat (nI x) (oI x) z :=
    PY.exists_univ hA hB2.zm fun z => PY.base (hco z u) hY
  exact (PY.and hA (h1.mono hY (by omega)) (PY.not hA h2)).congr fun x => (mem_cur u).symm

theorem py_good (ha : After (nX nI) (oX oI) lhat H) (mv : Mv T R ch FL) :
    PY Dd H Y 4 fun x => GoodMv R ch FL lhat (nX nI x) (oX oI x) mv := by
  have hY := hA.pos
  rcases mv with y | l
  · have hc : Fintype.card (kindM R ch FL (.inl y)).Cn ≤ Y := by
      refine (Fintype.card_le_of_injective
        (fun ν : (kindM R ch FL (.inl y)).Cn => (⟨Sum.inl y, ν⟩ : NM R FL (ch := ch))) ?_).trans hB.nm
      intro ν ν' he
      exact eq_of_heq (Sigma.mk.inj he).2
    have h1 : PY Dd H Y 3 fun x => ∀ ν : (kindM R ch FL (.inl y)).Cn, oX oI x ⟨.inl y, ν⟩ =
        Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inl y) :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s = t) (CY.base (ha.o _) hY) (CY.base (ha.num _) hY)
    exact h1.mono hY (by omega)
  · have hc : Fintype.card (kindM R ch FL (.inr l)).Cn ≤ Y := card_cn hA hB (rng (nI := nI) (oI := oI)) l
    have h1 : PY Dd H Y 1 fun x => GoodL R ch FL (oX oI x) l (Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l)) :=
      PY.rel hA (fun q t => r * b * q ≤ FL.G₁ * t ^ 2) (CY.base (ha.q l) hY) (CY.base (ha.num (.inr l)) hY)
    have h2 : PY Dd H Y 3 fun x => ∀ ν : (kindM R ch FL (.inr l)).Cn,
        Tow.num R ch FL lhat (nX nI x) (oX oI x) (.inr l) ≤ oX oI x ⟨.inr l, ν⟩ :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s ≤ t) (CY.base (ha.num _) hY) (CY.base (ha.o _) hY)
    exact PY.and hA (h1.mono hY (by omega)) h2

theorem units_stage (hS : SY inp Y p c H) (ha : After (nX nI) (oX oI) lhat H) :
    ∃ H', SY inp Y p (c + 9) H' ∧ H ⊆ H' ∧ Units nI oI lhat TM H' := by
  have hY := hA.pos
  have hun : Fintype.card (Un R FL Pl U0 U1) ≤ Y ^ 1 := by simpa using hB2.un
  have hzt : Fintype.card (ZM R FL (ch := ch) × Fin TM) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB2.zm hB2.tm
  have hmt : Fintype.card (Mv T R ch FL × Fin TM) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hB.mv hB2.tm
  have hzu : Fintype.card (ZM R FL (ch := ch) × Un R FL Pl U0 U1) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, pow_two]
    exact Nat.mul_le_mul hB2.zm hB2.un
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => AlU R FL Pl lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => py_al hA hB hB2 ha u) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Un R FL Pl U0 U1)
    (fun u x => rkU R FL Pl lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => cy_rk hA hB hB2 f1 u) (by omega)
  have a2 := ha.weaken (u1.trans u2)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := ZM R FL (ch := ch) × Un R FL Pl U0 U1)
    (fun q => ind fun x => q.2 ∈ consM R FL Pl lhat (nI x) (oI x) q.1) (a := 5) (e := 2) hzu
    (fun q => py_cons hA hB hB2 a2 (fun u => u2 (f1 u)) f2 q.1 q.2) (by omega)
  have a3 := a2.weaken u3
  have c3 : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H3 := fun z u => f3 (z, u)
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (κ := ZM R FL (ch := ch))
    (fun z x => (consM R FL Pl lhat (nI x) (oI x) z).card) (a := 2) (e := 1) (by simpa using hB2.zm)
    (fun z => by
      classical
      have e : ∀ x, (consM R FL Pl lhat (nI x) (oI x) z).card =
          ∑ u ∈ univ, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) x := by
        intro x
        have h1 : ∀ u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) x =
            if u ∈ consM R FL Pl lhat (nI x) (oI x) z then 1 else 0 := by
          intro u
          by_cases hu : u ∈ consM R FL Pl lhat (nI x) (oI x) z
          · rw [if_pos hu, ind_true (P := fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) hu]
          · rw [if_neg hu, ind_false (P := fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) hu]
        rw [Finset.sum_congr rfl fun u _ => h1 u, ← Finset.card_filter]
        congr 1
        ext u
        simp
      refine CY.congr ?_ fun x => (e x).symm
      refine CY.sum hA univ hB2.un (fun u _ => CY.base (c3 z u) hY) fun x => hA.lt_of_le ?_
      refine (Finset.sum_le_card_nsmul _ _ 1 fun v _ => ind_le _ _).trans ?_
      rw [smul_eq_mul, mul_one]
      exact hB2.un) (by omega)
  have a4 := a3.weaken u4
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (κ := Mv T R ch FL × Fin TM)
    (fun q => ind fun x => q.2.1 < Tow.num R ch FL lhat (nX nI x) (oX oI x) q.1) (a := 1) (e := 2) hmt
    (fun q => PY.rel1 hA (fun s => q.2.1 < s) (CY.base (a4.num q.1) hY)) (by omega)
  obtain ⟨H6, s6, u6, f6⟩ := s5.add hA (κ := ZM R FL (ch := ch) × Fin TM)
    (fun q => ind fun x => (consM R FL Pl lhat (nI x) (oI x) q.1).card ≤ q.2.1 ∧
      q.2.1 < Tow.num R ch FL lhat (nX nI x) (oX oI x) q.1.1) (a := 2) (e := 2) hzt
    (fun q => PY.and hA (PY.rel1 hA (fun s => s ≤ q.2.1) (CY.base (u5 (f4 q.1)) hY))
      (PY.rel1 hA (fun s => q.2.1 < s) (CY.base (u5 (a4.num q.1.1)) hY))) (by omega)
  have c6 : ∀ z u, ind (fun x => u ∈ consM R FL Pl lhat (nI x) (oI x) z) ∈ H6 := fun z u => u6 (u5 (u4 (c3 z u)))
  have a6 := a4.weaken (u5.trans u6)
  obtain ⟨H7, s7, u7, f7⟩ := s6.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv T R ch FL)))
    (a := 4) (e := 1) hun (fun u => py_cur hA hB hB2 a6 c6 u) (by omega)
  have a7 := a6.weaken u7
  obtain ⟨H8, s8, u8, f8⟩ := s7.add hA (κ := Mv T R ch FL)
    (fun mv => ind fun x => GoodMv R ch FL lhat (nX nI x) (oX oI x) mv) (a := 4) (e := 1) (by simpa using hB.mv)
    (fun mv => py_good hA hB hB2 a7 mv) (by omega)
  obtain ⟨H9, s9, u9, f9⟩ := s8.add hA (κ := Unit)
    (fun _ => ind fun x => ∀ mv, GoodMv R ch FL lhat (nX nI x) (oX oI x) mv) (a := 2) (e := 0) (by simp)
    (fun _ => PY.forall_univ hA hB.mv fun mv => PY.base (f8 mv) hY) (by omega)
  have v79 := u8.trans u9
  refine ⟨H9, s9, ?_, ⟨fun z u => v79 (u7 (c6 z u)), fun mv => v79 (a7.num mv), fun mv τ => v79 (u7 (u6 (f5 (mv, τ)))),
    fun z τ => v79 (u7 (f6 (z, τ))), fun u => v79 (f7 u), fun mv => u9 (f8 mv), f9 (), v79 a7.valid⟩⟩
  exact u1.trans (u2.trans (u3.trans (u4.trans (u5.trans (u6.trans (u7.trans v79))))))

end Nc.Tow
end
/- Source module Nc.Tow.Load0. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}


noncomputable def Bt (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ) (a c : Fin AA)
    (γ : T.X 0) : ℕ :=
  if Valid lhat n then ((range (n a c)).filter fun k => gam T ch a k = γ).card else 0

theorem Bt_le (a c : Fin AA) (γ : T.X 0) : Bt T ch lhat n a c γ ≤ n a c / Fintype.card (T.X 0) + 1 := by
  unfold Bt
  split_ifs
  · have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨ch a⟩
    rw [← card_range (n a c / Fintype.card (T.X 0) + 1)]
    refine card_le_card_of_injOn (fun k => k / Fintype.card (T.X 0)) ?_ ?_
    · intro k hk
      have h1 := mem_range.1 (mem_filter.1 (mem_coe.1 hk)).1
      exact mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right h1.le)))
    · intro k hk k' hk' heq
      have h1 := (mem_filter.1 (mem_coe.1 hk)).2
      have h2 := (mem_filter.1 (mem_coe.1 hk')).2
      have h3 : gam T ch a k = gam T ch a k' := h1.trans h2.symm
      unfold gam at h3
      have h4 := (Fintype.equivFin (T.X 0)).symm.injective h3
      have h5 : k % Fintype.card (T.X 0) = k' % Fintype.card (T.X 0) := congrArg Fin.val h4
      simp only at heq
      rw [← Nat.div_add_mod k (Fintype.card (T.X 0)), ← Nat.div_add_mod k' (Fintype.card (T.X 0)), heq, h5]
  · exact Nat.zero_le _

theorem bt_start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) :
    bt R ch lhat n (.nxt (.start a c γ s) : Tg T m AA) ≤ if s.1 = 0 then Bt T ch lhat n a c γ else 0 := by
  classical
  unfold bt Bt
  by_cases hv : Valid lhat n
  · rw [if_pos hv]
    have h1 : ∀ a' c', ((range (n a' c')).filter fun k => tgB T R ch a' c' k = .nxt (.start a c γ s)).card ≤
        if a' = a ∧ c' = c then (if s.1 = 0 then ((range (n a c)).filter fun k => gam T ch a k = γ).card else 0) else 0 := by
      intro a' c'
      by_cases hac : a' = a ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := hac
        rw [if_pos ⟨rfl, rfl⟩]
        by_cases hs : s.1 = 0
        · rw [if_pos hs]
          refine card_le_card fun k hk => ?_
          obtain ⟨h2, h3⟩ := mem_filter.1 hk
          refine mem_filter.2 ⟨h2, ?_⟩
          rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
          · simp at h3
          · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
            exact h3.2.2.1
          · simp at h3
        · rw [if_neg hs, Nat.le_zero, card_eq_zero]
          refine filter_false_of_mem fun k _ h3 => ?_
          rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
          · simp at h3
          · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
            exact hs (congrArg Fin.val h3.2.2.2).symm
          · simp at h3
      · rw [if_neg hac, Nat.le_zero, card_eq_zero]
        refine filter_false_of_mem fun k _ h3 => ?_
        rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
        · simp at h3
        · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
          exact hac ⟨h3.1, h3.2.1⟩
        · simp at h3
    refine (Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun c' _ => h1 a' c').trans ?_
    rw [Finset.sum_eq_single a, Finset.sum_eq_single c]
    · rw [if_pos ⟨rfl, rfl⟩, if_pos hv]
    · intro c' _ hc'
      rw [if_neg fun hh => hc' hh.2]
    · intro hn; exact absurd (mem_univ _) hn
    · intro a' _ ha'
      exact Finset.sum_eq_zero fun c' _ => if_neg fun hh => ha' hh.1
    · intro hn; exact absurd (mem_univ _) hn
  · rw [if_neg hv]
    exact Nat.zero_le _

theorem tgR_start {x : RM T m AA} {ν : Bool} {a c : Fin AA} {γ : T.X 0} {s : Fin (2 * m)}
    (hx : tgR T R ch x ν = .nxt (.start a c γ s)) : ν = true ∧ ∃ s' : Fin (2 * m), x = .start a c γ s' ∧ s.1 = s'.1 + 1 := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · have this : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) ≠ .nxt (.start a c γ s) := by
      intro e' he
      cases e' <;> simp [edgeO] at he
    cases ν
    · exact absurd hx (this _)
    · simp only [tgR] at hx
      split_ifs at hx with hs
      · simp only [Tg.nxt.injEq, RM.start.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1 h2 h3
        exact ⟨rfl, s', rfl, (congrArg Fin.val h4).symm⟩
      · exact absurd hx (this _)
  · simp [tgR] at hx
  · cases ν
    · fin_cases s' <;> simp [tgR] at hx
    · fin_cases s'
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx <;> simp at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
        simp at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

section

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_start_le (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) (hx : okR T R ch (.start a c γ s)) :
    num R ch FL lhat n o (.inl ⟨.start a c γ s, hx⟩) ≤ Bt T ch lhat n a c γ := by
  classical
  obtain ⟨s, hs⟩ := s
  induction s with
  | zero =>
    have h1 : num R ch FL lhat n o (.inl ⟨.start a c γ ⟨0, hs⟩, hx⟩) ≤
        load R ch FL lhat n o (.nxt (.start a c γ ⟨0, hs⟩)) := by
      rw [num_eq hr hb, numF]
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    refine h1.trans ?_
    rw [load_def, Finset.sum_eq_zero]
    · exact (bt_start a c γ ⟨0, hs⟩).trans (by simp)
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ _
      · rw [if_neg]
        intro hν
        obtain ⟨-, s', -, h3⟩ := tgR_start (x := x) (ν := ν) hν
        simp at h3
      · rw [if_neg]
        intro hν
        simp [tgM] at hν
  | succ s ih =>
    have hs0 : s < 2 * m := by omega
    have hx0 : okR T R ch (.start a c γ ⟨s, hs0⟩) := by
      obtain ⟨h1, h2⟩ := hx
      exact ⟨h1, by simp only at h2 ⊢; omega⟩
    have h1 : num R ch FL lhat n o (.inl ⟨.start a c γ ⟨s + 1, hs⟩, hx⟩) ≤
        load R ch FL lhat n o (.nxt (.start a c γ ⟨s + 1, hs⟩)) := by
      rw [num_eq hr hb, numF]
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    refine h1.trans ?_
    have hbt : bt R ch lhat n (.nxt (.start a c γ ⟨s + 1, hs⟩) : Tg T m AA) = 0 := by
      have := bt_start (R := R) (ch := ch) (lhat := lhat) (n := n) a c γ ⟨s + 1, hs⟩
      rw [if_neg (by simp)] at this
      omega
    refine (load_le_sum {(⟨.inl ⟨.start a c γ ⟨s, hs0⟩, hx0⟩, true⟩ : NM R FL (ch := ch))} hbt ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h2, s', h3, h4⟩ := tgR_start (x := x) (ν := ν) hν
        have h2 : ν = true := h2
        subst h2
        have h4 : s + 1 = s'.1 + 1 := h4
        have h5 : s' = ⟨s, hs0⟩ := Fin.ext (by change s'.1 = s; omega)
        subst h5
        subst h3
        exact mem_singleton_self _
      · simp [tgM] at hν
    · rw [Finset.sum_singleton]
      exact (alv_le_num hr hb _ _).trans (ih hs0 hx0)

end

theorem card_filter_getElem {α : Type*} [DecidableEq α] (l : List α) (e : α) :
    ((range l.length).filter fun p => l[p]? = some e).card = l.count e := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.count_cons, ← ih, card_filter, card_filter, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    congr 1
    by_cases h1 : a = e <;> simp [h1]


theorem steps_le {α : Type*} [DecidableEq α] (l : List α) (e : α) (L M : ℕ) (hL : 0 < L) (hLl : L ≤ l.length) :
    (∑ s ∈ range M, ((if s + 1 < L ∧ l[s]? = some e then 1 else 0) +
      if s + 2 = L ∧ l[s + 1]? = some e then 1 else 0)) + (if L ≤ 1 ∧ l[0]? = some e then 1 else 0) ≤ l.count e := by
  rw [← card_filter_getElem]
  have h1 : ((range L).filter fun p => l[p]? = some e).card ≤ ((range l.length).filter fun p => l[p]? = some e).card :=
    card_le_card (filter_subset_filter _ (range_subset_range.2 hLl))
  refine le_trans ?_ h1
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [card_filter, Finset.sum_range_succ, Finset.sum_add_distrib, add_assoc]
  refine add_le_add ?_ ?_
  · have h2 : ∀ s ∈ range M, (if s + 1 < L' + 1 ∧ l[s]? = some e then 1 else 0) =
        if s ∈ range L' then (if l[s]? = some e then 1 else 0) else 0 := by
      intro s _
      by_cases hs : s < L'
      · simp [hs]
      · simp [hs]
    rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun s hs => (mem_filter.1 hs).2
  · by_cases hc : l[L']? = some e
    · rw [if_pos hc]
      by_cases h0 : L' = 0
      · subst h0
        rw [Finset.sum_eq_zero]
        · simp [hc]
        · intro s _
          rw [if_neg]
          omega
      · rw [if_neg (by omega : ¬ (L' + 1 ≤ 1 ∧ l[0]? = some e)), add_zero]
        have h3 : ∀ s ∈ range M, (if s + 2 = L' + 1 ∧ l[s + 1]? = some e then 1 else 0) ≤ if s = L' - 1 then 1 else 0 := by
          intro s _
          split_ifs with h4 h5 h5
          · exact le_rfl
          · omega
          · exact Nat.zero_le _
          · exact le_rfl
        refine (Finset.sum_le_sum h3).trans ?_
        rw [Finset.sum_ite_eq']
        split_ifs <;> omega
    · rw [if_neg hc, Nat.le_zero, Nat.add_eq_zero_iff]
      constructor
      · refine Finset.sum_eq_zero fun s _ => if_neg ?_
        rintro ⟨h4, h5⟩
        have : s + 1 = L' := by omega
        rw [this] at h5
        exact hc h5
      · rw [if_neg]
        rintro ⟨h4, h5⟩
        have : L' = 0 := by omega
        rw [this] at hc
        exact hc h5

section

variable (hr : 0 < r) (hb : 0 < b)
include hr hb


theorem load_start_le (e : T.Ed 0) : load R ch FL lhat n o (.edge 0 e) ≤
    ∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e := by
  classical
  -- initial units
  have h1 : bt R ch lhat n (.edge 0 e : Tg T m AA) ≤ ∑ a, ∑ c, ∑ γ, if a = c then 0 else
      Bt T ch lhat n a c γ * if R.pl (ch a) (ch c) γ ≤ 1 ∧ (R.path (ch a) (ch c) γ)[0]? = some e then 1 else 0 := by
    unfold bt
    by_cases hv : Valid lhat n
    · rw [if_pos hv]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
      by_cases hac : a = c
      · rw [card_eq_zero.2]
        · exact Nat.zero_le _
        · refine filter_false_of_mem fun k _ h3 => ?_
          rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, h2, -⟩
          · rw [h1] at h3; simp at h3
          · rw [h1] at h3; simp at h3
          · exact h2 hac
      · simp only [if_neg hac]
        rw [card_eq_sum_card_fiberwise (f := fun k => gam T ch a k) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
        refine Finset.sum_le_sum fun γ _ => ?_
        by_cases hc : R.pl (ch a) (ch c) γ ≤ 1 ∧ (R.path (ch a) (ch c) γ)[0]? = some e
        · rw [if_pos hc, Nat.mul_one]
          unfold Bt
          rw [if_pos hv]
          refine card_le_card fun k hk => ?_
          obtain ⟨h2, h3⟩ := mem_filter.1 hk
          exact mem_filter.2 ⟨(mem_filter.1 h2).1, h3⟩
        · rw [if_neg hc, Nat.mul_zero, Nat.le_zero, card_eq_zero]
          refine filter_false_of_mem fun k hk h3 => hc ?_
          have h4 := (mem_filter.1 hk).2
          rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', h0, h1, h2, h5⟩ <;> rw [h1] at h4
          · simp at h4
          · simp at h4
          · have h6 : e' = e := eq_of_heq (Tg.edge.inj h4).2
            subst h6
            rw [h3] at h0 h5
            exact ⟨by omega, h0⟩
    · rw [if_neg hv]
      exact Nat.zero_le _
  -- relays
  have h2 : (∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = .edge 0 e then alv R ch FL lhat n o ν else 0) ≤
      ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if a = c then 0 else Bt T ch lhat n a c γ *
        ((if s.1 + 1 < R.pl (ch a) (ch c) γ ∧ (R.path (ch a) (ch c) γ)[s.1]? = some e then 1 else 0) +
        if s.1 + 2 = R.pl (ch a) (ch c) γ ∧ (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e then 1 else 0) := by
    -- only the relays of the start
    have h3 : ∀ ν : NM R FL (ch := ch), (if tgM R ch FL ν.1 ν.2 = .edge 0 e then alv R ch FL lhat n o ν else 0) ≤
        ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), ((if ∃ hx : okR T R ch (.start a c γ s), ν = ⟨.inl ⟨.start a c γ s, hx⟩, false⟩ ∧
            (R.path (ch a) (ch c) γ)[s.1]? = some e then Bt T ch lhat n a c γ else 0) +
          if ∃ hx : okR T R ch (.start a c γ s), ν = ⟨.inl ⟨.start a c γ s, hx⟩, true⟩ ∧ s.1 + 2 = R.pl (ch a) (ch c) γ ∧
            (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e then Bt T ch lhat n a c γ else 0) := by
      intro ν
      split_ifs with hν
      · rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
        · change tgR T R ch x ν = .edge 0 e at hν
          have hnum := alv_le_num (lhat := lhat) (n := n) (o := o) (FL := FL) hr hb ⟨x, hx⟩ ν
          rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
          · have hB := hnum.trans (num_start_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb a c γ s hx)
            refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ c, ∑ γ, ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ a))
            refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ γ, ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ c))
            refine le_trans ?_ (Finset.single_le_sum (f := fun γ => ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ γ))
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ s))
            have hedge : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) = .edge 0 e → e' = some e := by
              intro e' he
              cases e' with
              | none => simp [edgeO] at he
              | some e'' =>
                have h6 : e'' = e := eq_of_heq (Tg.edge.inj he).2
                rw [h6]
            cases ν
            · rw [if_pos ⟨hx, rfl, hedge _ hν⟩]
              exact hB.trans (Nat.le_add_right _ _)
            · simp only [tgR] at hν
              split_ifs at hν with hs
              have h4 : s.1 + 2 = R.pl (ch a) (ch c) γ := by
                obtain ⟨-, h5⟩ := hx
                have h6 := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
                by_contra h7
                exact hs ⟨by omega, by omega⟩
              rw [if_pos (⟨hx, rfl, h4, hedge _ hν⟩ : ∃ hx : okR T R ch (.start a c γ s),
                (⟨.inl ⟨.start a c γ s, _⟩, true⟩ : NM R FL (ch := ch)) = ⟨.inl ⟨.start a c γ s, hx⟩, true⟩ ∧ s.1 + 2 = R.pl (ch a) (ch c) γ ∧
                (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e)]
              exact hB.trans (Nat.le_add_left _ _)
          · simp [tgR] at hν
          · exfalso
            cases ν
            · fin_cases s'
              · simp [tgR] at hν
              · simp [tgR] at hν
              · exact absurd (Tg.edge.inj hν).1 (Fin.succ_ne_zero _)
              · simp [tgR] at hν
            · fin_cases s'
              · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hν
                split_ifs at hν
              · simp [tgR] at hν
              · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hν
                split_ifs at hν
              · simp [tgR] at hν
          · simp [tgR] at hν
        · exfalso
          exact absurd (Tg.edge.inj hν).1 (Fin.succ_ne_zero _)
      · exact Nat.zero_le _
    refine (Finset.sum_le_sum fun ν _ => h3 ν).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun γ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_add_distrib]
    have sgl : ∀ (d : Bool) (P : Prop) [Decidable P] (v : ℕ), (∑ ν : NM R FL (ch := ch), if ∃ hx : okR T R ch (.start a c γ s),
        ν = ⟨.inl ⟨.start a c γ s, hx⟩, d⟩ ∧ P then v else 0) ≤
          if okR T R ch (.start a c γ s) ∧ P then v else 0 := by
      intro d P _ v
      by_cases hc : okR T R ch (.start a c γ s) ∧ P
      · rw [if_pos hc, Finset.sum_eq_single (⟨.inl ⟨.start a c γ s, hc.1⟩, d⟩ : NM R FL (ch := ch))]
        · rw [if_pos ⟨hc.1, rfl, hc.2⟩]
        · intro ν _ hν
          rw [if_neg]
          rintro ⟨hx', h3, -⟩
          exact hν h3
        · intro hn; exact absurd (mem_univ _) hn
      · rw [Finset.sum_eq_zero]
        · exact Nat.zero_le _
        · intro ν _
          rw [if_neg]
          rintro ⟨hx, -, h1⟩
          exact hc ⟨hx, h1⟩
    refine (add_le_add (sgl false _ _) (sgl true _ _)).trans ?_
    by_cases hac : a = c
    · rw [if_pos hac, if_neg (fun hh => hh.1.1 hac), if_neg (fun hh => hh.1.1 hac)]
    · rw [if_neg hac, Nat.mul_add]
      refine add_le_add ?_ ?_
      · split_ifs with h4 h5 h5
        · rw [Nat.mul_one]
        · exact absurd ⟨h4.1.2, h4.2⟩ h5
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      · split_ifs with h4 h5 h5
        · rw [Nat.mul_one]
        · exact absurd h4.2 h5
        · exact Nat.zero_le _
        · exact Nat.zero_le _
  rw [load_def]
  refine (add_le_add h1 h2).trans ?_
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun γ _ => ?_
  by_cases hac : a = c
  · simp [hac]
  · simp only [if_neg hac]
    rw [← Finset.mul_sum, ← Nat.mul_add]
    refine Nat.mul_le_mul_left _ ?_
    have hne : ch a ≠ ch c := fun hh => hac (ch.injective hh)
    have := steps_le (R.path (ch a) (ch c) γ) e (R.pl (ch a) (ch c) γ) (2 * m) (R.pl_pos hne γ) (R.pl_le _ _ _)
    rw [Finset.sum_range] at this
    rw [Nat.add_comm]
    exact this

omit hr hb in

theorem batch_le (e : T.Ed 0) : (∑ a, ∑ c, ∑ γ, if a = c then 0 else
    Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) ≤ Uu * (lhat / Fintype.card (T.X 0) + 2 * AA) := by
  classical
  by_cases hv : Valid lhat n
  swap
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ => ?_
    unfold Bt
    rw [if_neg hv]
    simp
  -- split the paths
  set cn : Fin AA → T.X 0 → ℕ := fun a γ => (R.rt (ch a) γ).count e with hcn
  have e1 : ∀ a c γ, (if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) =
      (if a = c then 0 else Bt T ch lhat n a c γ * cn a γ) + if a = c then 0 else Bt T ch lhat n a c γ * cn c γ := by
    intro a c γ
    split_ifs
    · rfl
    · rw [Routes.path, List.count_append, List.count_reverse, Nat.mul_add]
  have e2 : (∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * cn c γ) =
      ∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n c a γ * cn a γ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun γ _ => ?_
    exact if_congr eq_comm rfl rfl
  have e3 : (∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) =
      ∑ a, ∑ γ, cn a γ * ∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ := by
    simp only [e1, Finset.sum_add_distrib]
    rw [e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    have : ∀ c, (∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * cn a γ) + (∑ γ, if a = c then 0 else Bt T ch lhat n c a γ * cn a γ) =
        ∑ γ, if a = c then 0 else cn a γ * (Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) := by
      intro c
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs
      · rfl
      · ring
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hac : a = c
    · simp [hac]
    · rw [if_neg hac, if_neg (Ne.symm hac)]
  rw [e3]
  have hB : ∀ a γ, (∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) ≤
      lhat / Fintype.card (T.X 0) + 2 * AA := by
    intro a γ
    have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨ch a⟩
    have h1 : (∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) ≤
        ∑ c, ((if c = a then 0 else n a c / Fintype.card (T.X 0) + n c a / Fintype.card (T.X 0)) + 2) := by
      refine Finset.sum_le_sum fun c _ => ?_
      split_ifs
      · exact Nat.zero_le _
      · have := Bt_le (ch := ch) (lhat := lhat) (n := n) a c γ
        have := Bt_le (ch := ch) (lhat := lhat) (n := n) c a γ
        omega
    refine h1.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm AA 2]
    refine Nat.add_le_add_right ?_ _
    rw [Nat.le_div_iff_mul_le hX, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hv a)
    split_ifs
    · simp
    · rw [Nat.add_mul]
      exact add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)
  calc ∑ a, ∑ γ, cn a γ * _ ≤ ∑ a, ∑ γ, cn a γ * (lhat / Fintype.card (T.X 0) + 2 * AA) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun γ _ => Nat.mul_le_mul_left _ (hB a γ)
    _ = (∑ a, ∑ γ, cn a γ) * (lhat / Fintype.card (T.X 0) + 2 * AA) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
    _ ≤ _ := by
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans ?_ (R.use e)
        calc ∑ a, ∑ γ, cn a γ = ∑ c ∈ univ.map ch, ∑ γ, (R.rt c γ).count e := by rw [Finset.sum_map]
          _ ≤ _ := Finset.sum_le_sum_of_subset (subset_univ _)



theorem _root_.Paper.thm_tree_start (e : T.Ed 0) : load R ch FL lhat n o (.edge 0 e) ≤
    Uu * (lhat / Fintype.card (T.X 0) + 2 * AA) := (load_start_le hr hb e).trans (batch_le e)

end

end Nc.Tow
end
/- Source module Nc.Tow.Load4. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

namespace Tower

variable {j : ℕ}

theorem card_ed_real (hj : j ≤ J) : (Fintype.card (T.Ed j) : ℝ) = h * (r * Fintype.card (T.X j) / 2) := by
  have h1 : Fintype.card (T.Ed j) = ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i).card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))
  have h2 : 2 * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by
    rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => T.card_ed j hj i]
    simp
  have h3 : (2 : ℝ) * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by exact_mod_cast h2
  linarith


def bet (n : T.Ed j → ℕ) (c : T.X j) : ℕ := ∑ e, if T.e0 e = c ∨ T.e1 e = c then n e else 0

theorem card_at (hj : j ≤ J) (c : T.X j) : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card ≤ h * r := by
  have h1 : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card =
      ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c)).card := by
    rw [card_eq_sum_card_fiberwise (f := fun e : T.Ed j => T.ty e) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [filter_filter]
    congr 1
    ext e
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  rw [h1]
  calc _ ≤ ∑ _i : Fin h, r := Finset.sum_le_sum fun i _ => T.deg j hj c i
    _ = h * r := by simp

theorem sum_sq_eq (hr : 0 < r) (hX : 0 < Fintype.card (T.X j)) (n : T.Ed j → ℕ) :
    ∑ e, (n e : ℝ) ^ 2 = 2 / (r * Fintype.card (T.X j)) * T.kap n ^ 2 := by
  rw [kap_sq]
  have h1 : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  field_simp


theorem bet_le (hj : j ≤ J) (hr : 0 < r) (n : T.Ed j → ℕ) (c : T.X j) :
    (T.bet n c : ℝ) ≤ √(2 * h / Fintype.card (T.X j)) * T.kap n := by
  have hX : 0 < Fintype.card (T.X j) := Fintype.card_pos_iff.2 ⟨c⟩
  have hXR : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have e1 : (T.bet n c : ℝ) = ∑ e ∈ univ.filter (fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c), (n e : ℝ) := by
    unfold bet
    rw [Finset.sum_filter]
    push_cast
    rfl
  have h1 : (T.bet n c : ℝ) ^ 2 ≤ 2 * h / Fintype.card (T.X j) * T.kap n ^ 2 := by
    rw [e1]
    refine (sq_sum_le _ _ (T.card_at hj c)).trans ?_
    have h2 : ∑ e ∈ univ.filter (fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c), (n e : ℝ) ^ 2 ≤ ∑ e, (n e : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    rw [sum_sq_eq hr hX] at h2
    push_cast
    calc (h : ℝ) * r * _ ≤ h * r * (2 / (r * Fintype.card (T.X j)) * T.kap n ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  have h0 : 0 ≤ √(2 * h / Fintype.card (T.X j)) * T.kap n := mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact h1

theorem sum_bet (n : T.Ed j → ℕ) : ∑ c, T.bet n c = 2 * ∑ e, n e := by
  unfold bet
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : ∀ c, (if T.e0 e = c ∨ T.e1 e = c then n e else 0) =
      (if T.e0 e = c then n e else 0) + if T.e1 e = c then n e else 0 := by
    intro c
    have hne := T.e_ne e
    by_cases h0 : T.e0 e = c
    · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
      simp [h0, h1]
    · by_cases h1 : T.e1 e = c <;> simp [h0, h1]
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_add_distrib]
  simp
  ring


theorem sum_bet_le (hj : j ≤ J) (hr : 0 < r) (n : T.Ed j → ℕ) :
    ((∑ c, T.bet n c : ℕ) : ℝ) ≤ 2 * (√h * T.kap n) := by
  rw [sum_bet]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rcases Nat.eq_zero_or_pos (Fintype.card (T.X j)) with hX | hX
  · have h1 := card_ed_real (T := T) hj
    rw [hX] at h1
    have h2 : Fintype.card (T.Ed j) = 0 := by
      have : (Fintype.card (T.Ed j) : ℝ) = 0 := by rw [h1]; simp
      exact_mod_cast this
    have : IsEmpty (T.Ed j) := Fintype.card_eq_zero_iff.1 h2
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  have hXR : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h0 : 0 ≤ √h * T.kap n := mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have h1 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (T.Ed j))) (f := fun e => (n e : ℝ))
  rw [card_univ, sum_sq_eq hr hX, card_ed_real hj] at h1
  refine h1.trans (le_of_eq ?_)
  field_simp

end Tower


noncomputable def lds (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
    (o : NM R FL (ch := ch) → ℕ) (j : Fin (J + 1)) : T.Ed j → ℕ := fun e => load R ch FL lhat n o (.edge j e)


def nhat (T : Tower h b D J r) (Uu AA lhat : ℕ) : ℕ := Uu * (lhat / Fintype.card (T.X 0) + 2 * AA)


noncomputable def kbar (FL : FlagLaws F T) (Uu AA lhat : ℕ) : ℝ :=
  √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat + √FL.C₁ * FL.a₁ / b * Fintype.card (T.X 0)

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

theorem kbar_nonneg : 0 ≤ kbar FL Uu AA lhat := by
  unfold kbar
  have := Real.sqrt_nonneg FL.C₁
  positivity

include hr hb in
theorem kap_zero_le : T.kap (lds R ch FL lhat n o 0) ≤ √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat := by
  have h1 : ∀ e : T.Ed 0, (lds R ch FL lhat n o 0 e : ℝ) ^ 2 ≤ (nhat T Uu AA lhat : ℝ) ^ 2 := by
    intro e
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2
    exact_mod_cast Paper.thm_tree_start (R := R) (ch := ch) (FL := FL) (n := n) (o := o) hr hb e
  have h0 : 0 ≤ √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat := by positivity
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [Tower.kap_sq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have h2 : ∑ e : T.Ed 0, (lds R ch FL lhat n o 0 e : ℝ) ^ 2 ≤ Fintype.card (T.Ed 0) * (nhat T Uu AA lhat : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum fun e _ => h1 e).trans (le_of_eq ?_)
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
  rw [Tower.card_ed_real (T := T) (Nat.zero_le _)] at h2
  have hA : (0 : ℝ) ≤ r * Fintype.card (T.X 0) / 2 := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hA).trans (le_of_eq ?_)
  ring

include hr hb hh hbD hρ hρ1 hρD in

theorem kap_le : ∀ j : ℕ, ∀ hj : j < J + 1, T.kap (lds R ch FL lhat n o ⟨j, hj⟩) +
    √FL.C₁ * FL.a₁ / b * Fintype.card (T.X j) ≤ ρ ^ j * kbar FL Uu AA lhat := by
  intro j
  induction j with
  | zero =>
    intro hj
    have h1 := kap_zero_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb
    rw [pow_zero, one_mul]
    unfold kbar
    exact add_le_add h1 le_rfl
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hjJ : j < J := by omega
    have h2 := Paper.thm_tree_kappa (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ.le hρ1 ⟨j, hjJ⟩
    have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hjJ
    set c : ℝ := √FL.C₁ * FL.a₁ / b with hc
    have hc0 : 0 ≤ c := by
      have := Real.sqrt_nonneg FL.C₁
      positivity
    have hX0 : (0 : ℝ) ≤ Fintype.card (T.X (j + 1)) := Nat.cast_nonneg _
    have h3 : T.kap (lds R ch FL lhat n o ⟨j + 1, hj⟩) ≤ ρ * T.kap (lds R ch FL lhat n o ⟨j, by omega⟩) +
        c * Fintype.card (T.X (j + 1)) := h2
    have h4 := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [hcX] at h4
    have h5 : 2 * (c * Fintype.card (T.X (j + 1))) ≤ ρ * D * (c * Fintype.card (T.X (j + 1))) :=
      mul_le_mul_of_nonneg_right hρD (mul_nonneg hc0 hX0)
    rw [pow_succ]
    linarith

include hr hb hh hbD hρ hρ1 hρD in
theorem kap_le' (j : Fin (J + 1)) : T.kap (lds R ch FL lhat n o j) ≤ ρ ^ j.1 * kbar FL Uu AA lhat := by
  have h1 := kap_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j.1 j.2
  have : 0 ≤ √FL.C₁ * FL.a₁ / b * Fintype.card (T.X j.1) := by
    have := Real.sqrt_nonneg FL.C₁
    positivity
  linarith

theorem card_X_pow : ∀ j ≤ J, (Fintype.card (T.X 0) : ℝ) = (D : ℝ) ^ j * Fintype.card (T.X j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ih (by omega)]
    have : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j (by omega)
    rw [this, pow_succ]
    ring

theorem sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : √(x ^ j) = √x ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx j), ih]


noncomputable def bhat (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℝ :=
  √(2 * h / Fintype.card (T.X 0)) * (max 1 (√D * ρ)) ^ J * kbar FL Uu AA lhat

include hr hb hh hbD hρ hρ1 hρD in

theorem bet_le_bhat (j : Fin (J + 1)) (c : T.X j) :
    (T.bet (lds R ch FL lhat n o j) c : ℝ) ≤ bhat FL Uu AA lhat ρ := by
  have hX : 0 < Fintype.card (T.X j.1) := Fintype.card_pos_iff.2 ⟨c⟩
  have hXR : (0 : ℝ) < Fintype.card (T.X j.1) := by exact_mod_cast hX
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hjJ : j.1 ≤ J := Nat.le_of_lt_succ j.2
  have h1 := T.bet_le hjJ hr (lds R ch FL lhat n o j) c
  have h2 := kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j
  have h0 := card_X_pow (T := T) j.1 hjJ
  have hk := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have e1 : √(2 * h / Fintype.card (T.X j.1)) = √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 := by
    rw [h0, ← sqrt_pow' (by positivity : (0 : ℝ) ≤ D), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  refine h1.trans ?_
  rw [e1]
  calc √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 * T.kap (lds R ch FL lhat n o j) ≤
      √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 * (ρ ^ j.1 * kbar FL Uu AA lhat) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = √(2 * h / Fintype.card (T.X 0)) * (√D * ρ) ^ j.1 * kbar FL Uu AA lhat := by rw [mul_pow]; ring
    _ ≤ √(2 * h / Fintype.card (T.X 0)) * (max 1 (√D * ρ)) ^ J * kbar FL Uu AA lhat := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)) hk
        calc (√D * ρ) ^ j.1 ≤ (max 1 (√D * ρ)) ^ j.1 := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
          _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hjJ

include hr hb hh hbD hρ hρ1 hρD in

theorem sum_bet_le_kbar (j : Fin (J + 1)) :
    ((∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤ 2 * √h * ρ ^ j.1 * kbar FL Uu AA lhat := by
  have h1 := T.sum_bet_le (Nat.le_of_lt_succ j.2) hr (lds R ch FL lhat n o j)
  have h2 := kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j
  refine h1.trans ?_
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * √h)
  linarith

end

end Nc.Tow
end
/- Source module Nc.Tow.Tree. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset


theorem exists_im {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) : ∃ i, (∀ i', f i ≤ f i') ∧ ∀ i' < i, ¬ ∀ i'', f i' ≤ f i'' := by
  classical
  obtain ⟨i0, -, hi0⟩ := exists_min_image (univ : Finset (Fin h)) f ⟨⟨0, hh⟩, mem_univ _⟩
  have hex : ∃ k : ℕ, ∃ hk : k < h, ∀ i', f ⟨k, hk⟩ ≤ f i' := ⟨i0, i0.2, fun i' => hi0 i' (mem_univ _)⟩
  obtain ⟨hk, h1⟩ := Nat.find_spec hex
  exact ⟨⟨Nat.find hex, hk⟩, h1, fun i' hi' hcon => Nat.find_min hex hi' ⟨i'.2, hcon⟩⟩


noncomputable def im {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) : Fin h := (exists_im hh f).choose

theorem im_unique {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) {i : Fin h} (h1 : ∀ i', f i ≤ f i')
    (h2 : ∀ i' < i, ¬ ∀ i'', f i' ≤ f i'') : i = im hh f := by
  obtain ⟨h3, h4⟩ := (exists_im hh f).choose_spec
  rcases lt_trichotomy i (im hh f) with hlt | heq | hlt
  · exact absurd h1 (h4 i hlt)
  · exact heq
  · exact absurd h3 (h2 _ hlt)

variable {h b D J r m AA : ℕ} {T : Tower h b D J r} (hh : 0 < h) (ch : Fin AA ↪ T.X 0)


def lev (L : Tg T m AA → ℕ) (j : ℕ) : T.Ed j → ℕ := fun e => if hj : j < J + 1 then L (.edge ⟨j, hj⟩ e) else 0

variable (Lf : ∀ j, T.Ed j → ℕ)


noncomputable def imin (j : ℕ) : Fin h := im hh fun i => ∑ e : T.Ed j, if T.ty e = i then Lf j e ^ 2 else 0

theorem isMin_iff (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : IsMin L j i ↔ i = imin hh (lev L) j.1 := by
  have e1 : (fun i => ∑ e : T.Ed j.1, if T.ty e = i then lev L j.1 e ^ 2 else 0) = sqs L j := by
    funext i
    unfold sqs lev
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [dif_pos j.2]
  unfold imin
  rw [e1]
  constructor
  · rintro ⟨h1, h2⟩
    exact im_unique hh _ h1 h2
  · rintro rfl
    exact (exists_im hh (sqs L j)).choose_spec


noncomputable def hostj {j : ℕ} (c : T.X j) : T.X (j + 1) := T.host (imin hh Lf j) (T.vx (imin hh Lf j) c)


def fb (j : ℕ) (c : T.X j) : ℕ := T.bet (Lf j) c

variable {hh Lf}


theorem card_children {j : ℕ} (hj : j < J) (c' : T.X (j + 1)) :
    (univ.filter fun c : T.X j => hostj hh Lf c = c').card ≤ b := by
  refine le_trans ?_ T.card_fl.le
  rw [← card_univ (α := T.Fl)]
  refine card_le_card_of_injOn (fun c => T.co (imin hh Lf j) c) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  intro c hc c'' hc'' heq
  have h1 := (mem_filter.1 (mem_coe.1 hc)).2
  have h2 := (mem_filter.1 (mem_coe.1 hc'')).2
  have h3 := T.host_inj hj _ (h1.trans h2.symm)
  exact (T.vx_co hj.le (imin hh Lf j)).1 (Prod.ext h3 heq)

theorem nd_cases (ν : Nd T) : ν = none ∨ ∃ (j : ℕ) (hj : j ≤ J) (c : T.X j), ν = nd T j hj c := by
  rcases ν with _ | ⟨j, c⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j.1, Nat.le_of_lt_succ j.2, c, rfl⟩


def onN (f : ∀ j, T.X j → ℕ) (f0 : ℕ) : Nd T → ℕ
  | none => f0
  | some ⟨j, c⟩ => f j.1 c

theorem onN_nd (f : ∀ j, T.X j → ℕ) (f0 : ℕ) {j : ℕ} (hj : j ≤ J) (c : T.X j) : onN f f0 (nd T j hj c) = f j c := rfl

end Nc.Tow
end
/- Source module Nc.Tow.Slp5. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b D J r m Uu AA U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}
variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable (hh : 0 < h) {L : Inp → Tg T m AA → ℕ}

section Bounds

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hL

theorem lev_le (x : Inp) (j : ℕ) (e : T.Ed j) : lev (L x) j e ≤ Y := by
  unfold lev
  split_ifs
  · exact (hL x _).trans hB.w
  · exact Nat.zero_le _

theorem fb_leS (x : Inp) {j : ℕ} (hj : j ≤ J) (c : T.X j) : fb (lev (L x)) j c ≤ Y ^ 2 := by
  unfold fb Tower.bet
  calc _ ≤ ∑ _e : T.Ed j, Y := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs
        · exact lev_le hA hB hL x j e
        · exact Nat.zero_le _
    _ = Fintype.card (T.Ed j) * Y := by simp
    _ ≤ Y * Y := Nat.mul_le_mul_right _ (hB.ed ⟨j, Nat.lt_succ_of_le hj⟩)
    _ = Y ^ 2 := by ring

end Bounds


def HostOk (hh : 0 < h) (L : Inp → Tg T m AA → ℕ) (H : Set (Inp → ℕ)) : Prop :=
  ∀ (j : ℕ) (_ : j < J) (c : T.X j) (c' : T.X (j + 1)), ind (fun x => hostj hh (lev (L x)) c = c') ∈ H

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hL : ∀ x τ, L x τ ≤ Wb R ch FL U0 U1)
include hA hB hL

omit hL in
theorem host_stage (hS : SY inp Y p c H) (hi : ∀ j i, ind (fun x => IsMin (L x) j i) ∈ H) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ HostOk hh L H' := by
  classical
  have hY := hA.pos
  have hc : Fintype.card (Σ j : Fin J, T.X j × T.X (j + 1)) ≤ Y ^ 2 := by
    rw [pow_two]
    refine le_trans (Fintype.card_le_of_injective (β := Nd T × Nd T)
      (fun q => (nd T q.1 q.1.2.le q.2.1, nd T (q.1 + 1) q.1.2 q.2.2)) ?_) (by
      rw [Fintype.card_prod]; exact Nat.mul_le_mul hB.nd hB.nd)
    rintro ⟨j, x, y⟩ ⟨j', x', y'⟩ he
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    have hj : j = j' := by
      by_contra hne
      exact nd_ne (fun hv => hne (Fin.ext hv)) h1
    subst hj
    have e1 := nd_inj.1 h1
    have e2 := nd_inj.1 h2
    simp only at e1 e2
    rw [e1, e2]
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Σ j : Fin J, T.X j × T.X (j + 1))
    (fun q => ind fun x => hostj hh (lev (L x)) q.2.1 = q.2.2) (a := 2) (e := 2) hc (fun q => by
      have h1 : PY Dd H Y 2 fun x => ∃ i ∈ univ.filter
          (fun i => T.host i (T.vx i q.2.1) = q.2.2), IsMin (L x) q.1.castSucc i :=
        PY.exists_mem hA _ ((card_filter_le _ _).trans (by simpa using hB.h)) fun i _ => PY.base (hi _ _) hY
      refine h1.congr fun x => ?_
      unfold hostj
      constructor
      · rintro ⟨i, hi, hm⟩
        rw [isMin_iff hh] at hm
        subst hm
        exact (mem_filter.1 hi).2
      · intro he
        exact ⟨imin hh (lev (L x)) q.1, mem_filter.2 ⟨mem_univ _, he⟩, (isMin_iff hh (L x) q.1.castSucc _).2 rfl⟩)
    (by omega)
  exact ⟨H1, s1, u1, fun j hj c c' => f1 ⟨⟨j, hj⟩, c, c'⟩⟩

omit hh in

theorem fb_stage (hS : SY inp Y p c H) (hm : ∀ τ, (fun x => L x τ) ∈ H) :
    ∃ H', SY inp Y p (c + 1) H' ∧ H ⊆ H' ∧ ∀ (j : ℕ) (_ : j ≤ J) (x' : T.X j),
      (fun x => fb (lev (L x)) j x') ∈ H' := by
  classical
  have hY := hA.pos
  have hX : Fintype.card (Σ j : Fin (J + 1), T.X j) ≤ Y ^ 1 := by
    rw [pow_one]
    refine le_trans (Fintype.card_le_of_injective (β := Nd T) some (Option.some_injective _)) hB.nd
  obtain ⟨H2, s2, u2, f2⟩ := hS.add hA (κ := Σ j : Fin (J + 1), T.X j) (fun q x => fb (lev (L x)) q.1 q.2)
    (a := 2) (e := 1) hX (fun q => by
      have e : ∀ x, fb (lev (L x)) q.1 q.2 =
          ∑ e ∈ univ.filter (fun e : T.Ed q.1 => T.e0 e = q.2 ∨ T.e1 e = q.2), L x (.edge q.1 e) := by
        intro x
        unfold fb Tower.bet lev
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [dif_pos q.1.2]
      refine CY.congr ?_ fun x => (e x).symm
      refine CY.sum hA _ ((card_filter_le _ _).trans (hB.ed q.1)) (fun e _ => CY.base (hm _) hY) fun x => ?_
      rw [← e]
      refine hA.lt_of_le3 ((fb_leS hA hB hL x (Nat.le_of_lt_succ q.1.2) q.2).trans ?_)
      have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
      omega) (by omega)
  exact ⟨H2, s2, u2, fun j hj x' => f2 ⟨⟨j, Nat.lt_succ_of_le hj⟩, x'⟩⟩

end Nc.Tow
end
/- Source module Nc.Tow.Ok. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

theorem isMin_unique {L : Tg T m AA → ℕ} {j : Fin (J + 1)} {i i' : Fin h} (h1 : IsMin L j i) (h2 : IsMin L j i') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hlt
  · exact absurd h1.1 (h2.2 i hlt)
  · exact heq
  · exact absurd h2.1 (h1.2 i' hlt)

theorem pick_unique {L : Tg T m AA → ℕ} {l : LMv T FL} {d : FL.Di} (h1 : Pick FL L l) (h2 : Pick FL L (withD FL l d)) :
    l.2.2.2 = d := by
  have e : tmin FL L (withD FL l d) = tmin FL L l := rfl
  rcases lt_trichotomy (Fintype.equivFin FL.Di d) (Fintype.equivFin FL.Di l.2.2.2) with hlt | heq | hlt
  · exact absurd h2.1 (h1.2 d hlt)
  · exact ((Fintype.equivFin FL.Di).injective heq).symm
  · exact absurd h1.1 (h2.2 l.2.2.2 hlt)


theorem inpR_unique {L : Tg T m AA → ℕ} {x x' : RM T m AA} (hx : okR T R ch x) (hx' : okR T R ch x')
    (ha : ActR L x) (ha' : ActR L x') (he : inpR T x = inpR T x') : x = x' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;>
    rcases x' with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · simpa [inpR] using he
  · simp [inpR] at he
  · rw [inpR_mid] at he
    split_ifs at he <;> simp [inpR] at he
  · simp [inpR] at he
  · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hj : j = j' := Fin.castSucc_injective _ h1
    subst hj
    have := eq_of_heq h2
    subst this
    rw [isMin_unique ha ha']
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      exact absurd (isMin_unique (ha' hs) ha) hx
    · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    exact absurd he.1 (Fin.castSucc_lt_last j).ne
  · rw [inpR_mid] at he
    split_ifs at he <;> simp [inpR] at he
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      exact absurd (isMin_unique (ha hs) ha') hx'
    · simp [inpR] at he
  · rw [inpR_mid, inpR_mid] at he
    split_ifs at he with hs hs' hs'
    · simp only [Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      rw [hs, hs']
    · simpa using he
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      exact absurd he.1 (Fin.castSucc_lt_last j).ne
    · simp [inpR] at he
  · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    exact absurd he.1.symm (Fin.castSucc_lt_last j').ne
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      exact absurd he.1.symm (Fin.castSucc_lt_last j').ne
    · simp [inpR] at he
  · simpa [inpR] using he

theorem inpR_ne_seg {x : RM T m AA} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl} :
    inpR T x ≠ .seg j i ω q := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · simp [inpR]
  · simp [inpR]
  · rw [inpR_mid]
    split_ifs <;> simp
  · simp [inpR]

theorem inpR_ne_done {x : RM T m AA} : inpR T x ≠ .done := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · simp [inpR]
  · simp [inpR]
  · rw [inpR_mid]
    split_ifs <;> simp
  · simp [inpR]

theorem su_inj {d : FL.Di} {e e' : (FL.L d).Sl} (hp : pr FL d e = pr FL d e') (hs : su FL d e = su FL d e') : e = e' :=
  rk_inj (fun a b hab => (Fintype.equivFin (FL.L d).Sl).injective (Fin.ext hab)) (mem_univ _) (mem_univ _) hp hs

section Plan

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}


def inpZ : ZM R FL (ch := ch) → Tg T m AA
  | ⟨.inl x, _⟩ => inpR T x.1
  | ⟨.inr l, e⟩ => .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e)

theorem consM_inl (x : {x : RM T m AA // okR T R ch x}) (e : (kindM R ch FL (.inl x)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl x, e⟩ ↔ ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) x.1 ∧
      AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpR T x.1 := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

theorem consM_inr (l : LMv T FL) (e : (kindM R ch FL (.inr l)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔ Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ∧
      AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) ∧
        su FL l.2.2.2 e * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ rkU R FL Pl lhat n o u ∧
        rkU R FL Pl lhat n o u < (su FL l.2.2.2 e + 1) * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

theorem consM_al {z : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z) :
    AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpZ z := by
  rcases z with ⟨x | l, e⟩
  · exact ((consM_inl x e u).1 hu).2
  · have := ((consM_inr l e u).1 hu).2
    exact ⟨this.1, this.2.1⟩

theorem inpZ_ne_done (z : ZM R FL (ch := ch)) : inpZ z ≠ .done := by
  rcases z with ⟨x | l, e⟩
  · exact inpR_ne_done
  · simp [inpZ]

theorem inpZ_time (z : ZM R FL (ch := ch)) : tgTime (inpZ z) ≤ timeM R ch FL z.1 := by
  rcases z with ⟨x | l, e⟩
  · exact inp_time x.1
  · exact le_rfl


theorem consM_unique {z z' : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z)
    (hu' : u ∈ consM R FL Pl lhat n o z') : z = z' := by
  rcases z with ⟨x | l, e⟩ <;> rcases z' with ⟨x' | l', e'⟩
  · obtain ⟨h1, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨h1', -, h2'⟩ := (consM_inl x' e' u).1 hu'
    have hx : x = x' := Subtype.ext (inpR_unique x.2 x'.2 h1 h1' (h2.symm.trans h2'))
    subst hx
    rfl
  · obtain ⟨-, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨-, -, h2', -⟩ := (consM_inr l' e' u).1 hu'
    exact absurd (h2.symm.trans h2') inpR_ne_seg
  · obtain ⟨-, -, h2, -⟩ := (consM_inr l e u).1 hu
    obtain ⟨-, -, h2'⟩ := (consM_inl x' e' u).1 hu'
    exact absurd (h2'.symm.trans h2) inpR_ne_seg
  · obtain ⟨h1, -, h2, h3, h4⟩ := (consM_inr l e u).1 hu
    obtain ⟨h1', -, h2', h3', h4'⟩ := (consM_inr l' e' u).1 hu'
    obtain ⟨j, i, ω, d⟩ := l
    obtain ⟨j', i', ω', d'⟩ := l'
    have he := h2.symm.trans h2'
    simp only [Tg.seg.injEq] at he
    obtain ⟨hj, hi, hω, hq⟩ := he
    subst hj
    subst hi
    have := eq_of_heq hω
    subst this
    have hd : d = d' := pick_unique (l := ⟨j, i, ω, d⟩) h1 h1'
    subst hd
    simp only at h3 h4 h3' h4' hq
    have hs : su FL d e = su FL d e' := by
      set t := num R ch FL lhat (nn n) (oo R FL Pl o) (.inr ⟨j, i, ω, d⟩)
      rcases lt_trichotomy (su FL d e) (su FL d e') with hlt | heq | hlt
      · have : (su FL d e + 1) * t ≤ su FL d e' * t := Nat.mul_le_mul_right t hlt
        omega
      · exact heq
      · have : (su FL d e' + 1) * t ≤ su FL d e * t := Nat.mul_le_mul_right t hlt
        omega
    have hee : e = e' := su_inj hq hs
    subst hee
    rfl


theorem card_consM (hr : 0 < r) (hb : 0 < b) (z : ZM R FL (ch := ch)) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)).card ≤ num R ch FL lhat (nn n) (oo R FL Pl o) z.1 := by
  classical
  rcases z with ⟨x | l, e⟩
  · rw [num_eq hr hb, consM, numF]
    split_ifs with ha
    · rw [load_eq]
    · simp
  · rw [consM]
    split_ifs with ha
    · refine (card_rk_le (ix_inj (R := R) (FL := FL) (Pl := Pl)) (Al R FL Pl lhat n o)
        (Tg.seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) : Tg T m AA) _ _).trans ?_
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    · simp

theorem time_lt_of_tg {ν : NM R FL (ch := ch)} {z : ZM R FL (ch := ch)} (hν : tgM R ch FL ν.1 ν.2 = inpZ z) :
    timeM R ch FL ν.1 < timeM R ch FL z.1 := by
  have h1 := tg_time ν
  rw [hν] at h1
  exact lt_of_lt_of_le h1 (inpZ_time z)

theorem lt_of_time {x y : Fin (Fintype.card (Mv T R ch FL))}
    (hxy : timeM R ch FL (eE R FL x) < timeM R ch FL (eE R FL y)) : x < y := by
  have := eE_lt R FL hxy
  rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this


theorem holds_eq {u : Un R FL Pl U0 U1} (hd : tgU R FL Pl u ≠ .done) :
    s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) = (hT R ch (tgU R FL Pl u)).map Pl.pt := by
  cases u with
  | init a c k =>
    have h1 := hB_eq (ch := ch) (R := R) hd
    change _ = (hT R ch (tgB T R ch a c k)).map Pl.pt
    rw [← h1, hB, Sym2.map_mk]
    simp only [Prod.map, Pl.pt_base]
    rfl
  | new ν k =>
    have h1 := hN_eq (eN R FL Pl ν) hd
    change _ = (hT R ch (tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2)).map Pl.pt
    rw [← h1, hN, Sym2.map_mk]
    rfl


theorem zp_hold (z : (sys R FL Pl).Z) :
    s((sys R FL Pl).zp z false, (sys R FL Pl).zp z true) = (hT R ch (inpZ (eZ R FL Pl z))).map Pl.pt := by
  rw [zp_eq, zp_eq]
  generalize eZ R FL Pl z = w
  rcases w with ⟨⟨x, hx⟩ | l, e⟩
  · change s(Pl.pt (tri T R ch x 0), Pl.pt (tri T R ch x 2)) = (hT R ch (inpR T x)).map Pl.pt
    have h1 : hT R ch (inpR T x) = s(tri T R ch x 0, tri T R ch x 2) := by
      rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
      · rfl
      · rfl
      · rw [inpR_mid]
        split_ifs with hs
        · subst hs; rfl
        · rfl
      · rfl
    rw [h1, Sym2.map_mk]
  · change s(Pl.pt (nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).a e)))),
      Pl.pt (nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).b e))))) = _
    simp only [inpZ, hT, pr, Sym2.map_mk, Prod.map]

section Causal

variable {o' : (sys R FL Pl).N → Fin U1} {t : ℕ}

theorem alU_congr (hr : 0 < r) (hb : 0 < b) (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < t →
    ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) {u : Un R FL Pl U0 U1} (hu : tgTime (tgU R FL Pl u) ≤ t) :
    AlU R FL Pl lhat n o u ↔ AlU R FL Pl lhat n o' u := by
  cases u with
  | init a c k => exact Iff.rfl
  | new ν k =>
    have h1 : timeM R ch FL (eN R FL Pl ν).1 < t := lt_of_lt_of_le (tg_time (eN R FL Pl ν)) hu
    have h2 : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) =
        alv R ch FL lhat (nn n) (oo R FL Pl o') (eN R FL Pl ν) := by
      unfold alv
      rw [num_congr hr hb fun mv' hmv' c => hag mv' (hmv'.trans h1) c]
      exact alvN_congr (fun c => hag _ h1 c) _
    change k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ↔
      k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o') (eN R FL Pl ν)
    rw [h2]

theorem consM_congr_inl (hr : 0 < r) (hb : 0 < b) (x : {x : RM T m AA // okR T R ch x}) (e : (kindM R ch FL (.inl x)).Sl)
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL (.inl x) →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl x, e⟩ ↔ u ∈ consM R FL Pl lhat n o' ⟨.inl x, e⟩ := by
  rw [consM_inl, consM_inl]
  have h1 : ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) x.1 ↔ ActR (load R ch FL lhat (nn n) (oo R FL Pl o')) x.1 :=
    actR_congr fun τ hτ => load_congr hr hb hτ hag
  rw [h1]
  refine and_congr_right fun _ => ?_
  have h2 : tgU R FL Pl u = inpR T x.1 → (AlU R FL Pl lhat n o u ↔ AlU R FL Pl lhat n o' u) := by
    intro hu
    refine alU_congr hr hb hag ?_
    rw [hu]
    exact inp_time x.1
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨(h2 h4).1 h3, h4⟩
  · rintro ⟨h3, h4⟩
    exact ⟨(h2 h4).2 h3, h4⟩

theorem consM_congr_inr (hr : 0 < r) (hb : 0 < b) (l : LMv T FL) (e : (kindM R ch FL (.inr l)).Sl)
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL (.inr l) →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔ u ∈ consM R FL Pl lhat n o' ⟨.inr l, e⟩ := by
  have hpk : Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ↔ Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o')) l :=
    pick_congr fun q => load_congr hr hb (le_refl _) hag
  have hnum : num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) = num R ch FL lhat (nn n) (oo R FL Pl o') (.inr l) :=
    num_congr hr hb hag
  have hal : ∀ v : Un R FL Pl U0 U1, tgU R FL Pl v = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) →
      (AlU R FL Pl lhat n o v ↔ AlU R FL Pl lhat n o' v) := by
    intro v hv
    refine alU_congr hr hb hag ?_
    rw [hv]
    exact le_refl _
  have hrk : tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) →
      rkU R FL Pl lhat n o u = rkU R FL Pl lhat n o' u := by
    intro hu
    unfold rkU
    exact rk_congr fun v hv => mem_Al.trans ((hal v (hv.trans hu)).trans mem_Al.symm)
  rw [consM_inr, consM_inr, hpk, hnum]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hrk h2] at h3
    exact ⟨(hal u h2).1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [← hrk h2] at h3
    exact ⟨(hal u h2).2 h1, h2, h3⟩

theorem consM_congr (hr : 0 < r) (hb : 0 < b) (z : ZM R FL (ch := ch))
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL z.1 →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)) = consM R FL Pl lhat n o' z := by
  ext u
  rcases z with ⟨x | l, e⟩
  · exact consM_congr_inl hr hb x e hag u
  · exact consM_congr_inr hr hb l e hag u

theorem agree_of (ho : ∀ ν : (sys R FL Pl).N, timeM R ch FL (eE R FL ν.1) < t → o ν = o' ν) :
    ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < t → ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩ := by
  intro mv' hmv' c
  unfold oo
  rw [ho]
  have h1 : (eN R FL Pl ((eN R FL Pl).symm ⟨mv', c⟩)).1 = mv' := by rw [Equiv.apply_symm_apply]
  rw [eN_fst] at h1
  rw [h1]
  exact hmv'

end Causal


theorem consM_cur {z : (sys R FL Pl).Z} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z)) :
    u ∈ (plan R FL Pl lhat U0 U1).cur n o z.1 := by
  obtain ⟨h1, h2⟩ := consM_al hu
  rw [Plan.cur, mem_sdiff]
  constructor
  · unfold Plan.seenAt
    rw [mem_union, mem_biUnion]
    cases u with
    | init a c k =>
      left
      simp only [seen0, mem_filter, mem_univ, true_and, decide_eq_true_eq]
      exact h1.2
    | new ν k =>
      right
      refine ⟨ν.1, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
      · have h3 := time_lt_of_tg (ν := eN R FL Pl ν) (z := eZ R FL Pl z) h2
        rw [eN_fst, eZ_fst] at h3
        exact lt_of_time h3
      · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        have h3 : k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) := h1
        have h4 : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≤ (o ν).1 := by
          refine (alvN_le _ _).trans ?_
          unfold oo
          rw [Equiv.symm_apply_apply]
        rw [Fin.le_def]
        omega
  · intro hmem
    unfold Plan.used at hmem
    rw [mem_biUnion] at hmem
    obtain ⟨z', hz', hu'⟩ := hmem
    have hlt := (mem_filter.1 hz').2
    have hu' : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z') := hu'
    have hzz := (eZ R FL Pl).injective (consM_unique hu hu')
    rw [hzz] at hlt
    exact lt_irrefl _ hlt


theorem plan_ok (hr : 0 < r) (hb : 0 < b) {cap : ℕ}
    (hcap : ∀ (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) mv,
      num R ch FL lhat (nn n) (oo R FL Pl o) mv ≤ cap) : (plan R FL Pl lhat U0 U1).Ok cap where
  causal n o o' z ho := by
    refine consM_congr hr hb (eZ R FL Pl z) (agree_of fun ν hν => ho ν ?_)
    rw [eZ_fst] at hν
    exact lt_of_time hν
  causal' n o o' x ho := by
    refine num_congr hr hb (agree_of fun ν hν => ho ν ?_)
    exact lt_of_time hν
  causal'' n o o' x ho := by
    refine good_congr hr hb (agree_of fun ν hν => ho ν (lt_of_time hν).le) fun c => ?_
    unfold oo
    rw [ho]
    have h1 : (eN R FL Pl ((eN R FL Pl).symm ⟨eE R FL x, c⟩)).1 = eE R FL x := by rw [Equiv.apply_symm_apply]
    rw [eN_fst] at h1
    exact ((eE R FL).injective h1).le
  sub n o z u hu := consM_cur hu
  hold n o z u hu := by
    have hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z) := hu
    obtain ⟨-, h2⟩ := consM_al hu
    have h3 := holds_eq (u := u) (by rw [h2]; exact inpZ_ne_done _)
    rw [h2, ← zp_hold, Sym2.eq_iff] at h3
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h3.2, h3.1⟩
  disj n o x e e' hee := by
    rw [disjoint_left]
    intro u hu hu'
    have hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl ⟨x, e⟩) := hu
    have hu' : u ∈ consM R FL Pl lhat n o (eZ R FL Pl ⟨x, e'⟩) := hu'
    have h1 := (eZ R FL Pl).injective (consM_unique hu hu')
    rw [Sigma.mk.injEq] at h1
    exact hee (eq_of_heq h1.2)
  card n o z := card_consM hr hb (eZ R FL Pl z)
  cap n o x := hcap n o _

end Plan

end Nc.Tow
end
/- Source module Nc.Tow.EndA. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}


theorem nxt_ok_R {x y : RM T m AA} (hx : okR T R ch x) {ν : Bool} (he : tgR T R ch x ν = .nxt y) :
    okR T R ch y ∧ inpR T y = .nxt y ∧ ∀ L : Tg T m AA → ℕ, ActR L y := by
  have hE : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .nxt y := by
    intro e he
    cases e <;> simp [edgeO] at he
  have mid : ∀ (j : Fin J) (e : T.Ed j) (s : Fin 4), s ≠ 0 → okR T R ch (.mid j e s) →
      okR T R ch (.mid j e s) ∧ inpR T (.mid j e s : RM T m AA) = .nxt (.mid j e s) ∧
        ∀ L : Tg T m AA → ℕ, ActR L (.mid j e s) := by
    intro j e s hs hok
    refine ⟨hok, ?_, fun L h0 => absurd h0 hs⟩
    rw [inpR_mid, if_neg hs]
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · cases ν
    · exact absurd he (hE _)
    · simp only [tgR] at he
      split_ifs at he with hs
      · have he := Tg.nxt.inj he
        subst he
        exact ⟨⟨hx.1, hs.2⟩, rfl, fun _ => trivial⟩
      · exact absurd he (hE _)
  · simp [tgR] at he
  · cases ν
    · fin_cases s <;> simp [tgR] at he
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at he
        split_ifs at he with hq
        · have he := Tg.nxt.inj he
          subst he
          exact mid j e 1 (by decide) ⟨fun _ => hq, fun h3 => absurd h3 (by decide)⟩
        · have he := Tg.nxt.inj he
          subst he
          exact mid j e 2 (by decide) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at he
        have he := Tg.nxt.inj he
        subst he
        exact mid j e 2 (by decide) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at he
        split_ifs at he with hq
        have he := Tg.nxt.inj he
        subst he
        exact mid j e 3 (by decide) ⟨fun h3 => absurd h3 (by decide), fun _ => hq⟩
      · simp [tgR] at he
  · simp [tgR] at he

theorem nxt_ok_B {a c : Fin AA} {k : ℕ} {y : RM T m AA} (he : tgB T R ch a c k = .nxt y) :
    okR T R ch y ∧ inpR T y = .nxt y ∧ ∀ L : Tg T m AA → ℕ, ActR L y := by
  have hE : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .nxt y := by
    intro e he
    cases e <;> simp [edgeO] at he
  unfold tgB at he
  by_cases hac : a = c
  · rw [if_pos hac] at he
    cases he
  · rw [if_neg hac] at he
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dif_pos hs] at he
      have he := Tg.nxt.inj he
      subst he
      exact ⟨⟨hac, hs.2⟩, rfl, fun _ => trivial⟩
    · rw [dif_neg hs] at he
      exact absurd he (hE _)


theorem seg_nondiag (hr : 0 < r) (hb : 0 < b) {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl}
    {ν : NM R FL (ch := ch)} (hν : tgM R ch FL ν.1 ν.2 = .seg j i ω q) : ¬ q.IsDiag := by
  have key : ∀ c : T.X j, T.host i (T.vx i c) ≠ T.π c → ¬ (s(T.co i (T.host i (T.vx i c)), T.co i c) : Sym2 T.Fl).IsDiag := by
    intro c hne hd
    rw [Sym2.mk_isDiag_iff] at hd
    apply hne
    apply (T.vx_co (Nat.succ_le_of_lt j.2) i).1
    refine Prod.ext ?_ ?_
    · simp only
      rw [T.host_vx j.2, T.π_vx j.2]
    · simp only
      rw [hd, T.π_co j.2]
  obtain ⟨e, s, hx, h1, -, h3⟩ := seg_chan hr hb hν
  subst h1
  rcases h3 with ⟨h5, -, h7⟩ | ⟨h5, -, h7⟩
  · subst h5
    rw [← h7]
    exact key _ (hx.1 rfl)
  · subst h5
    rw [← h7]
    exact key _ (hx.2 rfl).symm

section Plan

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}


theorem exists_cons (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) {u : Un R FL Pl U0 U1} (hu : AlU R FL Pl lhat n o u)
    (hd : tgU R FL Pl u ≠ .done) : ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
  classical
  set L := load R ch FL lhat (nn n) (oo R FL Pl o) with hL
  have one : ∀ x : RM T m AA, okR T R ch x → ActR L x → tgU R FL Pl u = inpR T x →
      ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
    intro x hx ha ht
    exact ⟨⟨.inl ⟨x, hx⟩, ()⟩, (consM_inl _ _ u).2 ⟨ha, hu, ht⟩⟩
  rcases hτ : tgU R FL Pl u with _ | ⟨j, e⟩ | x | ⟨j, i, ω, q⟩
  · exact absurd hτ hd
  · revert e
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro e hτ
      exact one (.fin e) trivial trivial hτ
    · intro e hτ
      obtain ⟨i, hi⟩ := exists_isMin hh L j.castSucc
      by_cases ht : T.ty e = i
      · refine one (.mid j e 0) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩ (fun _ => ?_) ?_
        · rw [ht]; exact hi
        · rw [hτ, inpR_mid, if_pos rfl]
      · exact one (.inn j i e) ht hi hτ
  · have h1 : okR T R ch x ∧ inpR T x = .nxt x ∧ ∀ L : Tg T m AA → ℕ, ActR L x := by
      cases u with
      | init a c k => exact nxt_ok_B hτ
      | new ν k =>
        have hτ : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = .nxt x := hτ
        revert hτ
        generalize eN R FL Pl ν = w
        intro hτ
        rcases w with ⟨⟨y, hy⟩ | l, w⟩
        · exact nxt_ok_R hy hτ
        · simp [tgM] at hτ
    exact one x h1.1 (h1.2.2 L) (hτ.trans h1.2.1.symm)
  · -- an end segment
    have hq : ¬ q.IsDiag := by
      cases u with
      | init a c k =>
        exfalso
        have hτ : tgB T R ch a c k = .seg j i ω q := hτ
        rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hτ <;> cases hτ
      | new ν k => exact seg_nondiag hr hb (ν := eN R FL Pl ν) hτ
    obtain ⟨t0, d0, -⟩ := exists_fits_seg (FL := FL) L j i ω
    obtain ⟨d, hd⟩ := exists_pick L (⟨j, i, ω, d0⟩ : LMv T FL)
    have hd : Pick FL L (⟨j, i, ω, d⟩ : LMv T FL) := hd
    have hnum : num R ch FL lhat (nn n) (oo R FL Pl o) (.inr (⟨j, i, ω, d⟩ : LMv T FL)) = tmin FL L (⟨j, i, ω, d⟩ : LMv T FL) := by
      rw [num_eq hr hb, numF, if_pos hd]
    set t := tmin FL L (⟨j, i, ω, d⟩ : LMv T FL) with ht
    have hfit := hd.1 q hq
    have hrk : rkU R FL Pl lhat n o u < L (.seg j i ω q) := by
      rw [hL, load_eq]
      have := rk_lt (idx := ix R FL Pl) (key := tgU R FL Pl) (mem_Al.2 hu)
      rw [hτ] at this
      exact this
    have hlt : rkU R FL Pl lhat n o u < slo FL d q * t := lt_of_lt_of_le hrk hfit
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at hlt
        exact absurd hlt (Nat.not_lt_zero _)
      · exact h0
    have hw : rkU R FL Pl lhat n o u / t < slo FL d q := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlt)
    obtain ⟨e, -, he1, he2⟩ := exists_rk (idx := fun e => (Fintype.equivFin (FL.L d).Sl e).1) (key := pr FL d)
      (fun a b hab => (Fintype.equivFin (FL.L d).Sl).injective (Fin.ext hab)) univ q hw
    have he2 : su FL d e = rkU R FL Pl lhat n o u / t := he2
    refine ⟨⟨.inr ⟨j, i, ω, d⟩, e⟩, (consM_inr (⟨j, i, ω, d⟩ : LMv T FL) e u).2 ⟨hd, hu, ?_, ?_, ?_⟩⟩
    · rw [hτ, he1]
    · rw [hnum, he2]
      exact Nat.div_mul_le_self _ _
    · rw [hnum, he2, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      exact Nat.lt_mul_div_succ _ htpos |>.trans_eq (by ring)


theorem mem_seen_new {ν : (sys R FL Pl).N} {k : Fin U1} :
    (Uid.new ν k : Un R FL Pl U0 U1) ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ↔ k ≤ o ν := by
  unfold Plan.seenAt
  rw [mem_union, mem_biUnion]
  constructor
  · rintro (h1 | ⟨x, -, h2⟩)
    · simp [seen0] at h1
    · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq] at h2
      exact h2.2
  · intro h1
    right
    refine ⟨ν.1, mem_filter.2 ⟨mem_univ _, ν.1.2⟩, ?_⟩
    simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
    exact h1

theorem mem_seen_init {a c : Fin AA} {k : Fin U0} :
    (Uid.init a c k : Un R FL Pl U0 U1) ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ↔ k.1 < (n a c).1 := by
  unfold Plan.seenAt
  rw [mem_union, mem_biUnion]
  constructor
  · rintro (h1 | ⟨x, -, h2⟩)
    · simpa [seen0] using h1
    · simp [newUnits] at h2
  · intro h1
    left
    simpa [seen0] using h1


theorem cur_end (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) {u : Un R FL Pl U0 U1}
    (hu : u ∈ (plan R FL Pl lhat U0 U1).cur n o (Fintype.card (Mv T R ch FL))) :
    u ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ∧
      (AlU R FL Pl lhat n o u → tgU R FL Pl u = .done) := by
  rw [Plan.cur, mem_sdiff] at hu
  refine ⟨hu.1, fun ha => ?_⟩
  by_contra hd
  obtain ⟨z, hz⟩ := exists_cons hr hb hh ha hd
  apply hu.2
  unfold Plan.used
  rw [mem_biUnion]
  refine ⟨(eZ R FL Pl).symm z, mem_filter.2 ⟨mem_univ _, ((eZ R FL Pl).symm z).1.2⟩, ?_⟩
  change u ∈ consM R FL Pl lhat n o (eZ R FL Pl ((eZ R FL Pl).symm z))
  rw [Equiv.apply_symm_apply]
  exact hz

end Plan

end Nc.Tow
end
/- Source module Nc.Tow.EndB. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ}


noncomputable def parN (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) (c : T.X j) : Nd T :=
  if hj : j + 1 ≤ J then nd T (j + 1) hj (hostj hh Lf c) else none


def chd : RM T m AA → Bool → Option (Σ j : Fin (J + 1), T.X j)
  | .inn j _ e, β => some ⟨j.castSucc, if β then T.e1 e else T.e0 e⟩
  | .mid j e _, β => some ⟨j.castSucc, if β then T.e1 e else T.e0 e⟩
  | .fin e, β => some ⟨Fin.last J, if β then T.e1 e else T.e0 e⟩
  | _, _ => none

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h)
include hr hb hh

theorem num_inn (j : Fin J) (i : Fin h) (e : T.Ed j) (hx : okR T R ch (.inn j i e)) (hne : num R ch FL lhat n o (.inl ⟨.inn j i e, hx⟩) ≠ 0) :
    i = imin hh (lev (load R ch FL lhat n o)) j.1 := by
  classical
  rw [num_eq hr hb, numF] at hne
  split_ifs at hne with ha
  · exact (isMin_iff hh _ j.castSucc i).1 ha
  · exact absurd rfl hne

theorem num_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s))
    (hne : num R ch FL lhat n o (.inl ⟨.mid j e s, hx⟩) ≠ 0) :
    T.ty e = imin hh (lev (load R ch FL lhat n o)) j.1 := by
  obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
  have h2 := (num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e hx0).2
  by_contra hcon
  have h3 : ¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) := fun hm => hcon ((isMin_iff hh _ j.castSucc _).1 hm)
  have := h2 h3
  omega


theorem done_hold {x : RM T m AA} (hx : okR T R ch x) {β : Bool} (hd : tgR T R ch x β = .done)
    (hne : num R ch FL lhat n o (.inl ⟨x, hx⟩) ≠ 0) :
    ∃ (j : ℕ) (hj : j ≤ J) (c : T.X j), chd x β = some ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩ ∧
      hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R FL (ch := ch)) =
        s(nd T j hj c, parN hh (lev (load R ch FL lhat n o)) j c) := by
  have e0 : ∀ β : Bool, hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R FL (ch := ch)) =
      if β then s(tri T R ch x 1, tri T R ch x 2) else s(tri T R ch x 0, tri T R ch x 1) := by
    intro β
    cases β <;> rfl
  rw [e0]
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exfalso
    obtain ⟨hac, hs⟩ := hx
    cases β
    · simp only [tgR] at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1) (by omega)).1 hd
    · simp only [tgR] at hd
      split_ifs at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1 + 1) hs).1 hd
  · have hi := num_inn hr hb hh j i e hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN hh (lev (load R ch FL lhat n o)) j.1 c = nd T (j + 1) j.2 (hst T i c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, rfl, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨j.1, j.2.le, T.e1 e, rfl, ?_⟩
      rw [hpar]
      have h1 : T.vx i (T.e0 e) = T.vx i (T.e1 e) := by
        rw [T.nr_vx0 j.2.le i ⟨e, hx⟩, T.nr_vx1 j.2.le i ⟨e, hx⟩]
      have h2 : hst T i (T.e0 e) = hst T i (T.e1 e) := by
        unfold hst
        rw [h1]
      change s(nd T (j + 1) j.2 (hst T i (T.e0 e)), nd T j j.2.le (T.e1 e)) = _
      rw [h2, Sym2.eq_swap]
  · have hi := num_mid hr hb hh j e s hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN hh (lev (load R ch FL lhat n o)) j.1 c = nd T (j + 1) j.2 (hst T (T.ty e) c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, rfl, ?_⟩
      rw [hpar]
      fin_cases s
      · rfl
      · simp [tgR] at hd
      · simp [tgR] at hd
      · simp [tgR] at hd
    · refine ⟨j.1, j.2.le, T.e1 e, rfl, ?_⟩
      rw [hpar]
      fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hd
        split_ifs at hd
      · simp [tgR] at hd
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hd
        split_ifs at hd with hq
        rw [not_not] at hq
        change s(nd T (j + 1) j.2 (T.π (T.e1 e)), nd T j j.2.le (T.e1 e)) = _
        rw [hq, Sym2.eq_swap]
      · change s(nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e)), nd T j j.2.le (T.e1 e)) = _
        rw [Sym2.eq_swap]
  · have hpar : ∀ c : T.X J, parN hh (lev (load R ch FL lhat n o)) J c = none := by
      intro c
      unfold parN
      rw [dif_neg (by omega)]
    cases β
    · refine ⟨J, le_rfl, T.e0 e, rfl, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨J, le_rfl, T.e1 e, rfl, ?_⟩
      rw [hpar]
      change s(none, nd T J le_rfl (T.e1 e)) = _
      rw [Sym2.eq_swap]

omit hr hb hh in

theorem sum_le_one {κ : Type*} (s : Finset κ) (f : κ → ℕ) (B : ℕ) (h1 : ∀ x ∈ s, ∀ y ∈ s, x = y) (h2 : ∀ x ∈ s, f x ≤ B) :
    ∑ x ∈ s, f x ≤ B := by
  rcases s.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · rw [h0, Finset.sum_empty]; exact Nat.zero_le _
  · have : s = {x} := by
      ext y
      rw [mem_singleton]
      exact ⟨fun hy => h1 y hy x hx, fun hy => hy ▸ hx⟩
    rw [this, Finset.sum_singleton]
    exact h2 x hx


def IsCh (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (ν : NM R FL (ch := ch)) (s : Σ j : Fin (J + 1), T.X j) : Prop :=
  ∃ (x : {x : RM T m AA // okR T R ch x}) (β : Bool), ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ chd x.1 β = some s


def OfEd (j : Fin J) (e : T.Ed j) (x : RM T m AA) : Prop := (∃ i, x = .inn j i e) ∨ ∃ s, x = .mid j e s


theorem ofEd_unique {j : Fin J} {e : T.Ed j} {β : Bool} {x x' : RM T m AA} (hx : okR T R ch x) (hx' : okR T R ch x')
    (h1 : OfEd j e x) (h1' : OfEd j e x') (hd : tgR T R ch x β = .done) (hd' : tgR T R ch x' β = .done)
    (hn : num R ch FL lhat n o (.inl ⟨x, hx⟩) ≠ 0) (hn' : num R ch FL lhat n o (.inl ⟨x', hx'⟩) ≠ 0) : x = x' := by
  have mm : ∀ s s' : Fin 4, okR T R ch (.mid j e s) → okR T R ch (.mid j e s') → tgR T R ch (.mid j e s : RM T m AA) β = .done →
      tgR T R ch (.mid j e s' : RM T m AA) β = .done → s = s' := by
    intro s s' hs hs' h2 h2'
    cases β
    · have h0 : ∀ s : Fin 4, tgR T R ch (.mid j e s : RM T m AA) false = .done → s = 0 := by
        intro s hs
        fin_cases s
        · rfl
        · simp [tgR] at hs
        · simp [tgR] at hs
        · simp [tgR] at hs
      rw [h0 s h2, h0 s' h2']
    · have h0 : ∀ s : Fin 4, tgR T R ch (.mid j e s : RM T m AA) true = .done → okR T R ch (.mid j e s) →
          (s = 2 ∧ T.π (T.e1 e) = hst T (T.ty e) (T.e1 e)) ∨ (s = 3 ∧ T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e)) := by
        intro s hs hok
        fin_cases s
        · exfalso
          simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hs
          split_ifs at hs
        · simp [tgR] at hs
        · left
          simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hs
          split_ifs at hs with hq
          exact ⟨rfl, not_not.1 hq⟩
        · exact Or.inr ⟨rfl, hok.2 rfl⟩
      rcases h0 s h2 hs with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h0 s' h2' hs' with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · rw [a1, b1]
      · exact absurd a2 b2
      · exact absurd b2 a2
      · rw [a1, b1]
  rcases h1 with ⟨i, rfl⟩ | ⟨s, rfl⟩ <;> rcases h1' with ⟨i', rfl⟩ | ⟨s', rfl⟩
  · rw [num_inn hr hb hh j i e hx hn, num_inn hr hb hh j i' e hx' hn']
  · exfalso
    have a1 := num_inn hr hb hh j i e hx hn
    have a2 := num_mid hr hb hh j e s' hx' hn'
    exact hx (a2.trans a1.symm)
  · exfalso
    have a1 := num_inn hr hb hh j i' e hx' hn'
    have a2 := num_mid hr hb hh j e s hx hn
    exact hx' (a2.trans a1.symm)
  · rw [mm s s' hx hx' hd hd']

open Classical in

theorem sum_edge_end (j : Fin J) (e : T.Ed j) (β : Bool) : ∑ ν ∈ (univ : Finset (NM R FL (ch := ch))).filter (fun ν =>
      alv R ch FL lhat n o ν ≠ 0 ∧ ∃ x : {x : RM T m AA // okR T R ch x}, ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ OfEd j e x.1),
      alv R ch FL lhat n o ν ≤ load R ch FL lhat n o (.edge j.castSucc e) := by
  have hnz : ∀ (x : {x : RM T m AA // okR T R ch x}), alv R ch FL lhat n o (⟨.inl x, β⟩ : NM R FL (ch := ch)) ≠ 0 →
      num R ch FL lhat n o (.inl x) ≠ 0 := by
    intro x hx
    have := alv_le_num (lhat := lhat) (n := n) (o := o) (FL := FL) hr hb x β
    omega
  refine sum_le_one _ _ _ ?_ ?_
  · intro ν hν ν' hν'
    obtain ⟨-, h0, ⟨x, hx⟩, rfl, h2, h3⟩ := mem_filter.1 hν
    obtain ⟨-, h0', ⟨x', hx'⟩, rfl, h2', h3'⟩ := mem_filter.1 hν'
    have : x = x' := ofEd_unique hr hb hh hx hx' h3 h3' h2 h2' (hnz _ h0) (hnz _ h0')
    subst this
    rfl
  · intro ν hν
    obtain ⟨-, h0, ⟨x, hx⟩, rfl, h2, h3⟩ := mem_filter.1 hν
    rcases h3 with ⟨i, h3⟩ | ⟨s, h3⟩
    · simp only at h3
      subst h3
      exact (alv_le_num hr hb _ _).trans (num_inl hr hb _)
    · simp only at h3
      subst h3
      exact (alv_mid_le hr hb j e s hx β).1

open Classical in

theorem sum_child_lt (j : Fin J) (c : T.X j) : (∑ ν : NM R FL (ch := ch), if IsCh R ch FL ν ⟨j.castSucc, c⟩ then
      alv R ch FL lhat n o ν else 0) ≤
    ∑ e : T.Ed j, if T.e0 e = c ∨ T.e1 e = c then load R ch FL lhat n o (.edge j.castSucc e) else 0 := by
  let C : T.Ed j → Bool → Finset (NM R FL (ch := ch)) := fun e β => (univ : Finset (NM R FL (ch := ch))).filter (fun ν =>
      alv R ch FL lhat n o ν ≠ 0 ∧ ∃ x : {x : RM T m AA // okR T R ch x}, ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ OfEd j e x.1)
  have hall : ∀ ν : NM R FL (ch := ch), (if IsCh R ch FL ν ⟨j.castSucc, c⟩ then alv R ch FL lhat n o ν else 0) ≤
      if ν ∈ ((univ.filter fun e : T.Ed j => T.e0 e = c).biUnion fun e => C e false) ∪
        ((univ.filter fun e : T.Ed j => T.e1 e = c).biUnion fun e => C e true) then alv R ch FL lhat n o ν else 0 := by
    intro ν
    by_cases h1 : IsCh R ch FL ν ⟨j.castSucc, c⟩
    swap
    · rw [if_neg h1]; exact Nat.zero_le _
    rw [if_pos h1]
    by_cases h0 : alv R ch FL lhat n o ν = 0
    · rw [h0]; exact Nat.zero_le _
    rw [if_pos]
    obtain ⟨x, β, hν, hd, hc⟩ := h1
    have hmem : ∀ e, OfEd j e x.1 → ν ∈ C e β := fun e he => mem_filter.2 ⟨mem_univ _, h0, x, hν, hd, he⟩
    have hex : ∃ e : T.Ed j, OfEd j e x.1 ∧ (if β then T.e1 e else T.e0 e) = c := by
      obtain ⟨x, hx⟩ := x
      simp only at hc ⊢
      rcases x with ⟨a, c', γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
      · simp [chd] at hc
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        obtain ⟨hj, hc⟩ := hc
        have hj : j' = j := Fin.castSucc_injective _ hj
        subst hj
        exact ⟨e, Or.inl ⟨i, rfl⟩, eq_of_heq hc⟩
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        obtain ⟨hj, hc⟩ := hc
        have hj : j' = j := Fin.castSucc_injective _ hj
        subst hj
        exact ⟨e, Or.inr ⟨s, rfl⟩, eq_of_heq hc⟩
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        exact absurd hc.1.symm (Fin.castSucc_lt_last j).ne
    obtain ⟨e, he, hce⟩ := hex
    cases β
    · exact mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem e he⟩)
    · exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem e he⟩)
  refine (Finset.sum_le_sum fun ν _ => hall ν).trans ?_
  rw [← Finset.sum_filter, filter_mem_eq_inter, univ_inter]
  refine (sum_union_le _ _ _).trans ?_
  refine (add_le_add (sum_biUnion_le' _ _ _) (sum_biUnion_le' _ _ _)).trans ?_
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hcon => hne (h0.trans hcon.symm)
    rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]
    exact sum_edge_end hr hb hh j e false
  · by_cases h1 : T.e1 e = c
    · rw [if_neg h0, if_pos h1, if_pos (Or.inr h1), Nat.zero_add]
      exact sum_edge_end hr hb hh j e true
    · rw [if_neg h0, if_neg h1]
      exact Nat.zero_le _

open Classical in

theorem sum_child_last (c : T.X J) : (∑ ν : NM R FL (ch := ch), if IsCh R ch FL ν ⟨Fin.last J, c⟩ then
      alv R ch FL lhat n o ν else 0) ≤
    ∑ e : T.Ed J, if T.e0 e = c ∨ T.e1 e = c then load R ch FL lhat n o (.edge (Fin.last J) e) else 0 := by
  let C : T.Ed J → Bool → Finset (NM R FL (ch := ch)) := fun e β => {⟨.inl ⟨.fin e, trivial⟩, β⟩}
  have hC : ∀ e β, ∑ ν ∈ C e β, alv R ch FL lhat n o ν ≤ load R ch FL lhat n o (.edge (Fin.last J) e) := by
    intro e β
    simp only [C]
    rw [Finset.sum_singleton]
    exact (alv_le_num hr hb _ _).trans (num_inl hr hb _)
  have hall : ∀ ν : NM R FL (ch := ch), (if IsCh R ch FL ν ⟨Fin.last J, c⟩ then alv R ch FL lhat n o ν else 0) ≤
      if ν ∈ ((univ.filter fun e : T.Ed J => T.e0 e = c).biUnion fun e => C e false) ∪
        ((univ.filter fun e : T.Ed J => T.e1 e = c).biUnion fun e => C e true) then alv R ch FL lhat n o ν else 0 := by
    intro ν
    by_cases h1 : IsCh R ch FL ν ⟨Fin.last J, c⟩
    swap
    · rw [if_neg h1]; exact Nat.zero_le _
    rw [if_pos h1, if_pos]
    obtain ⟨⟨x, hx⟩, β, hν, hd, hc⟩ := h1
    rcases x with ⟨a, c', γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
    · simp [chd] at hc
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      exact absurd hc.1 (Fin.castSucc_lt_last j').ne
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      exact absurd hc.1 (Fin.castSucc_lt_last j').ne
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      have hce : (if β then T.e1 e else T.e0 e) = c := eq_of_heq hc.2
      have hmem : ν ∈ C e β := by
        rw [hν]
        exact mem_singleton_self _
      cases β
      · exact mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem⟩)
      · exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem⟩)
  refine (Finset.sum_le_sum fun ν _ => hall ν).trans ?_
  rw [← Finset.sum_filter, filter_mem_eq_inter, univ_inter]
  refine (sum_union_le _ _ _).trans ?_
  refine (add_le_add (sum_biUnion_le' _ _ _) (sum_biUnion_le' _ _ _)).trans ?_
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hcon => hne (h0.trans hcon.symm)
    rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]
    exact hC e false
  · by_cases h1 : T.e1 e = c
    · rw [if_neg h0, if_pos h1, if_pos (Or.inr h1), Nat.zero_add]
      exact hC e true
    · rw [if_neg h0, if_neg h1]
      exact Nat.zero_le _

open Classical in

theorem sum_child (j : ℕ) (hj : j ≤ J) (c : T.X j) : (∑ ν : NM R FL (ch := ch),
      if IsCh R ch FL ν ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩ then alv R ch FL lhat n o ν else 0) ≤
    fb (lev (load R ch FL lhat n o)) j c := by
  have e1 : fb (lev (load R ch FL lhat n o)) j c = ∑ e : T.Ed j, if T.e0 e = c ∨ T.e1 e = c then
      load R ch FL lhat n o (.edge ⟨j, Nat.lt_succ_of_le hj⟩ e) else 0 := by
    unfold fb Tower.bet lev
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [dif_pos (Nat.lt_succ_of_le hj)]
  rw [e1]
  rcases hj.lt_or_eq with h1 | h1
  · exact sum_child_lt hr hb hh ⟨j, h1⟩ c
  · subst h1
    exact sum_child_last hr hb hh c

end Nc.Tow
end
/- Source module Nc.Tow.EndC. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section Ends

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}


def PossM (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
    (o : NM R FL (ch := ch) → ℕ) (ub : ℕ) (mv : Mv T R ch FL) : Prop :=
  ∃ i : Fin (num R ch FL lhat n o mv * ub) → (kindM R ch FL mv).I, ∀ ν,
    o ⟨mv, ν⟩ = (∑ k, ((kindM R ch FL mv).lam + (kindM R ch FL mv).len (i k) ν)) / ub

section

variable {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} {ub : ℕ}

theorem poss_inl (hub : 0 < ub) {x : {x : RM T m AA // okR T R ch x}} (hp : PossM R ch FL lhat n o ub (.inl x))
    (ν : (kindM R ch FL (.inl x)).Cn) : o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x) := by
  obtain ⟨i, hi⟩ := hp
  rw [hi ν]
  have h1 : ∀ k, ((kindM R ch FL (.inl x)).lam + (kindM R ch FL (.inl x)).len (i k) ν) = 1 := fun _ => rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  exact Nat.mul_div_cancel _ hub

theorem poss_inr (hub : 0 < ub) {l : LMv T FL} (hp : PossM R ch FL lhat n o ub (.inr l)) :
    GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (num R ch FL lhat n o (.inr l) * ub) → (FL.L l.2.2.2).I, ∀ ν : (FL.L l.2.2.2).Cn,
    o ⟨.inr l, ν⟩ = (∑ k, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν)) / ub := hp
  unfold GoodL
  revert i
  generalize num R ch FL lhat n o (.inr l) = t
  intro i hi
  have hi' : ∀ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ * ub ≤ ∑ k, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) := by
    intro ν
    rw [hi ν]
    exact Nat.div_mul_le_self _ _
  have h1 : ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨.inr l, ν⟩ * ub) ^ 2 ≤
      (t * ub) * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 := by
    calc _ ≤ ∑ ν : (FL.L l.2.2.2).Cn, (∑ k : Fin (t * ub), ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν)) ^ 2 :=
          Finset.sum_le_sum fun ν _ => Nat.pow_le_pow_left (hi' ν) 2
      _ ≤ ∑ ν : (FL.L l.2.2.2).Cn, (t * ub) * ∑ k : Fin (t * ub), ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 := by
          refine Finset.sum_le_sum fun ν _ => ?_
          have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (t * ub))))
            (f := fun k => ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν))
          rwa [card_univ, Fintype.card_fin] at this
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : r * b * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 ≤
      (t * ub) * FL.G₁ := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _k : Fin (t * ub), FL.G₁ := Finset.sum_le_sum fun k _ => FL.L2 l.2.2.2 (i k)
      _ = _ := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have h3 : (r * b * ∑ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ ^ 2) * ub ^ 2 ≤ (FL.G₁ * t ^ 2) * ub ^ 2 := by
    have e1 : (r * b * ∑ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ ^ 2) * ub ^ 2 =
        r * b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨.inr l, ν⟩ * ub) ^ 2 := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun ν _ => by rw [mul_pow]
    rw [e1]
    calc _ ≤ r * b * ((t * ub) * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2) :=
          Nat.mul_le_mul_left _ h1
      _ = (t * ub) * (r * b * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2) := by ring
      _ ≤ (t * ub) * ((t * ub) * FL.G₁) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)


theorem poss_good (hub : 0 < ub) {mv : Mv T R ch FL} (hp : PossM R ch FL lhat n o ub mv) : GoodMv R ch FL lhat n o mv := by
  rcases mv with x | l
  · exact fun ν => poss_inl hub hp ν
  · refine ⟨poss_inr hub hp, fun ν => ?_⟩
    obtain ⟨i, hi⟩ := hp
    rw [hi ν, Nat.le_div_iff_mul_le hub]
    calc num R ch FL lhat n o (.inr l) * ub = ∑ _k : Fin (num R ch FL lhat n o (.inr l) * ub), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k _ => (FL.lam_pos l.2.2.2).trans (Nat.le_add_right _ _)


theorem alv_good (ν : NM R FL (ch := ch)) (hp : GoodMv R ch FL lhat n o ν.1) : alv R ch FL lhat n o ν = o ν := by
  rcases ν with ⟨x | l, ν⟩
  · have h1 : o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x) := hp ν
    unfold alv
    rw [alvN_inl, if_pos h1, h1]
  · have h1 : GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) := hp.1
    unfold alv
    rw [alvN_inr, if_pos h1]

end

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

open Classical in

noncomputable def AsU (R : Routes T m Uu) (FL : FlagLaws F T) (Pl : Place T ch A') (lhat : ℕ)
    (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) (s : Σ j : Fin (J + 1), T.X j) : Finset (Un R FL Pl U0 U1) :=
  univ.filter fun u => ∃ (ν : (sys R FL Pl).N) (kk : Fin U1), u = Uid.new ν kk ∧
    kk.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ∧ IsCh R ch FL (eN R FL Pl ν) s

theorem mem_AsU_new {ν : (sys R FL Pl).N} {kk : Fin U1} {s : Σ j : Fin (J + 1), T.X j} :
    (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU R FL Pl lhat n o s ↔
      kk.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ∧ IsCh R ch FL (eN R FL Pl ν) s := by
  classical
  unfold AsU
  rw [mem_filter]
  constructor
  · rintro ⟨-, ν', k', he, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := Uid.new.inj he
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_univ _, ν, kk, rfl, h1, h2⟩

theorem mem_AsU_init {a c : Fin AA} {kk : Fin U0} {s : Σ j : Fin (J + 1), T.X j} :
    (Uid.init a c kk : Un R FL Pl U0 U1) ∉ AsU R FL Pl lhat n o s := by
  classical
  unfold AsU
  rw [mem_filter]
  rintro ⟨-, ν', k', he, -⟩
  cases he

theorem card_AsU (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (s : Σ j : Fin (J + 1), T.X j) :
    (AsU R FL Pl lhat n o s : Finset (Un R FL Pl U0 U1)).card ≤ fb (lev (load R ch FL lhat (nn n) (oo R FL Pl o))) s.1.1 s.2 := by
  classical
  obtain ⟨j, c⟩ := s
  have h1 : (AsU R FL Pl lhat n o ⟨j, c⟩ : Finset (Un R FL Pl U0 U1)).card =
      ∑ u : Un R FL Pl U0 U1, if u ∈ AsU R FL Pl lhat n o ⟨j, c⟩ then 1 else 0 := by
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  rw [h1, sum_units]
  have h2 : (∑ a, ∑ c', ∑ kk, if (Uid.init a c' kk : Un R FL Pl U0 U1) ∈ AsU R FL Pl lhat n o ⟨j, c⟩ then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c' _ => Finset.sum_eq_zero fun kk _ => if_neg mem_AsU_init
  rw [h2, Nat.zero_add]
  refine le_trans ?_ (sum_child (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := nn n) (o := oo R FL Pl o) hr hb hh j.1
    (Nat.le_of_lt_succ j.2) c)
  rw [← Equiv.sum_comp (eN R FL Pl)]
  refine Finset.sum_le_sum fun ν _ => ?_
  have hle : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≤ U1 := (alvN_le _ _).trans (o _).2.le
  by_cases hc : IsCh R ch FL (eN R FL Pl ν) ⟨j, c⟩
  · refine le_trans ?_ (le_of_eq (if_pos hc).symm)
    calc (∑ kk : Fin U1, if (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU R FL Pl lhat n o ⟨j, c⟩ then 1 else 0) ≤
        ∑ kk : Fin U1, if kk.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) then 1 else 0 := by
          refine Finset.sum_le_sum fun kk _ => ?_
          by_cases h3 : (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU R FL Pl lhat n o ⟨j, c⟩
          · rw [if_pos h3, if_pos (mem_AsU_new.1 h3).1]
          · rw [if_neg h3]; exact Nat.zero_le _
      _ = ((univ : Finset (Fin U1)).filter fun kk => kk.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν)).card := by
          rw [card_filter]
      _ ≤ _ := (card_fin_lt' _ _ hle).le
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    exact Finset.sum_eq_zero fun kk _ => if_neg fun hm => hc (mem_AsU_new.1 hm).2

open Classical in

noncomputable def deadU (R : Routes T m Uu) (FL : FlagLaws F T) (Pl : Place T ch A') (U0 : ℕ) (o : (sys R FL Pl).N → Fin U1) :
    Finset (Un R FL Pl U0 U1) := univ.image fun ν => Uid.new ν (o ν)

end Ends

end Nc.Tow
end
/- Source module Nc.Tow.Cap. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}


noncomputable def capN (FL : FlagLaws F T) (U0 Uu AA lhat : ℕ) : ℕ := U0 + 2 + ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD

theorem kap_le_kbar (j : Fin (J + 1)) : T.kap (lds R ch FL lhat n o j) ≤ kbar FL Uu AA lhat := by
  refine (kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j).trans ?_
  exact mul_le_of_le_one_left kbar_nonneg (pow_le_one₀ hρ.le hρ')


theorem load_edge_le (j : Fin (J + 1)) (e : T.Ed j) :
    (load R ch FL lhat n o (.edge j e) : ℝ) ≤ 2 * kbar FL Uu AA lhat := by
  have hX : 0 < Fintype.card (T.X j.1) := Fintype.card_pos_iff.2 ⟨T.e0 e⟩
  have hk := kap_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1 hρD j
  have hk0 : 0 ≤ T.kap (lds R ch FL lhat n o j) := Tower.kap_nonneg _
  have h1 := Tower.sum_sq_eq (T := T) hr hX (lds R ch FL lhat n o j)
  have h2 : (load R ch FL lhat n o (.edge j e) : ℝ) ^ 2 ≤ ∑ e, (lds R ch FL lhat n o j e : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun e => (lds R ch FL lhat n o j e : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ e)
  have h3 : (1 : ℝ) ≤ r * Fintype.card (T.X j.1) := by exact_mod_cast Nat.mul_pos hr hX
  have h4 : (2 : ℝ) / (r * Fintype.card (T.X j.1)) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h5 : (load R ch FL lhat n o (.edge j e) : ℝ) ^ 2 ≤ (2 * T.kap (lds R ch FL lhat n o j)) ^ 2 := by
    rw [h1] at h2
    have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (T.kap (lds R ch FL lhat n o j)))
    nlinarith [sq_nonneg (T.kap (lds R ch FL lhat n o j))]
  have h6 := (abs_le_of_sq_le_sq' h5 (by linarith)).2
  linarith


theorem tmin_real_le (l : LMv T FL) : (tmin FL (load R ch FL lhat n o) l : ℝ) ≤ 3 * b * kbar FL Uu AA lhat + 1 := by
  obtain ⟨j, i, ω, d⟩ := l
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have ha1 : (1 : ℝ) ≤ FL.a₁ := by exact_mod_cast FL.a₁_pos
  set nf : T.Ed j → ℕ := lds R ch FL lhat n o j.castSucc with hnf
  have h1 : (FL.a₁ : ℝ) * tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d⟩ : LMv T FL) ≤
      √(T.NN2 (T.nEnd i nf ω)) + FL.a₁ := tmin_le hb _ _ fun q => seg_le hr hb j i ω q
  have hX : 0 < Fintype.card (T.X (j.1 + 1)) := by
    rw [← Tower.card_V (T := T) (Nat.succ_le_of_lt j.2) i]
    exact Nat.mul_pos (Fintype.card_pos_iff.2 ⟨ω⟩) hb
  have hXR : (1 : ℝ) ≤ Fintype.card (T.X (j.1 + 1)) := by exact_mod_cast hX
  have h2 := Tower.end_norm (T := T) j.2 hb hbD (i := i) (n := nf)
  have h3 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ ∑ ω, √(T.NN2 (T.nEnd i nf ω)) ^ 2 :=
    Finset.single_le_sum (f := fun ω => √(T.NN2 (T.nEnd i nf ω)) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ ω)
  have hk0 : 0 ≤ T.kap nf := Tower.kap_nonneg _
  have h4 : (r : ℝ) * Fintype.card (T.X j.1) / 2 * ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (nf e : ℝ) ^ 2 ≤
      T.kap nf ^ 2 := by
    rw [Tower.kap_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  have h5 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ (3 * b * T.kap nf) ^ 2 := by
    have h6 : (Fintype.card (T.X (j.1 + 1)) : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ 8 * T.kap nf ^ 2 := by
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans (h2.trans ?_)
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    have h7 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ 8 * b * T.kap nf ^ 2 := by
      have h8 : (1 : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤
          (Fintype.card (T.X (j.1 + 1)) : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hXR hbR.le) (sq_nonneg _)
      have h9 := h8.trans h6
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hbR] at h9
      linarith
    have h10 : 8 * (b : ℝ) * T.kap nf ^ 2 ≤ (3 * b * T.kap nf) ^ 2 := by
      have : (3 * b * T.kap nf) ^ 2 = 9 * (b : ℝ) ^ 2 * T.kap nf ^ 2 := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith
    exact h7.trans h10
  have h6 : √(T.NN2 (T.nEnd i nf ω)) ≤ 3 * b * T.kap nf :=
    (abs_le_of_sq_le_sq' h5 (by positivity)).2
  have hk := kap_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1 hρD
    j.castSucc
  have h7 : 3 * b * T.kap nf ≤ 3 * b * kbar FL Uu AA lhat := mul_le_mul_of_nonneg_left hk (by positivity)
  set t : ℝ := (tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d⟩ : LMv T FL) : ℝ) with ht
  set Q : ℝ := 3 * b * kbar FL Uu AA lhat with hQ
  have hQ0 : 0 ≤ Q := by
    have := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
    positivity
  have h8 : (FL.a₁ : ℝ) * t ≤ FL.a₁ * (Q + 1) := by
    have h9 : Q ≤ FL.a₁ * Q := le_mul_of_one_le_left hQ0 ha1
    nlinarith
  exact le_of_mul_le_mul_left h8 (by linarith)


theorem num_le_cap {U0 : ℕ} (hn : ∀ a c, n a c ≤ U0) (mv : Mv T R ch FL) :
    num R ch FL lhat n o mv ≤ capN FL U0 Uu AA lhat := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have hceil : (3 * (b : ℝ) * kbar FL Uu AA lhat) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := Nat.le_ceil _
  have hedge : ∀ (j : Fin (J + 1)) (e : T.Ed j), load R ch FL lhat n o (.edge j e) ≤ capN FL U0 Uu AA lhat := by
    intro j e
    have h1 := load_edge_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1
      hρD j e
    have h2 : (load R ch FL lhat n o (.edge j e) : ℝ) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := by
      refine h1.trans (le_trans ?_ hceil)
      nlinarith
    have h3 : load R ch FL lhat n o (.edge j e) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := by exact_mod_cast h2
    unfold capN
    omega
  rcases mv with ⟨x, hx⟩ | l
  · rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have h1 := num_start_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb a c γ s hx
      have h2 := Bt_le (ch := ch) (lhat := lhat) (n := n) a c γ
      have h3 : n a c / Fintype.card (T.X 0) ≤ U0 := (Nat.div_le_self _ _).trans (hn a c)
      unfold capN
      omega
    · exact (num_inl hr hb _).trans (hedge j.castSucc e)
    · obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
      exact h1.trans ((num_mid0 hr hb j e hx0).1.trans (hedge j.castSucc e))
    · exact (num_inl hr hb _).trans (hedge (Fin.last J) e)
  · have h1 := num_inr_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb l
    have h2 := tmin_real_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1
      hρD l
    have h3 : (tmin FL (load R ch FL lhat n o) l : ℝ) ≤ ((⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : tmin FL (load R ch FL lhat n o) l ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ + 1 := by exact_mod_cast h3
    unfold capN
    omega

end




noncomputable def YhN (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℕ := ⌈2 * √h * kbar FL Uu AA lhat / (1 - ρ)⌉₊

theorem le_YhN (ρ : ℝ) : 2 * √h * kbar FL Uu AA lhat / (1 - ρ) ≤ YhN FL Uu AA lhat ρ := Nat.le_ceil _

theorem geom_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) : ∑ j ∈ range k, ρ ^ j ≤ 1 / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  rw [le_div_iff₀ h1]
  have h2 := geom_sum_mul ρ k
  have h3 : (∑ j ∈ range k, ρ ^ j) * (1 - ρ) = 1 - ρ ^ k := by linarith
  rw [h3]
  have := pow_nonneg hρ k
  linarith

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD in

theorem sum_bet_le_YhN : ∑ j : Fin (J + 1), ∑ c, T.bet (lds R ch FL lhat n o j) c ≤ YhN FL Uu AA lhat ρ := by
  have h1 : ((∑ j : Fin (J + 1), ∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤
      2 * √h * kbar FL Uu AA lhat / (1 - ρ) := by
    rw [Nat.cast_sum]
    have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
    calc ∑ j : Fin (J + 1), ((∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤
        ∑ j : Fin (J + 1), 2 * √h * kbar FL Uu AA lhat * ρ ^ j.1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := sum_bet_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1
            hρD j
          linarith
      _ = 2 * √h * kbar FL Uu AA lhat * ∑ j ∈ range (J + 1), ρ ^ j := by
          rw [← Finset.mul_sum, Finset.sum_range]
      _ ≤ 2 * √h * kbar FL Uu AA lhat * (1 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (geom_le hρ.le hρ' _) (by positivity)
      _ = _ := by ring
  exact_mod_cast h1.trans (le_YhN ρ)

omit hρ' in
include hb hρ hbD in

theorem bhat_pow_le (hh : 0 < h) (hX : 0 < Fintype.card (T.X J)) {p q : ℕ} (hpq : 2 * p ≤ q)
    (hgain : ρ ^ q * (D : ℝ) ^ p ≤ 1) :
    bhat FL Uu AA lhat ρ ^ q * (Fintype.card (T.X 0) : ℝ) ^ p ≤ (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by
  have hD : 0 < D := by omega
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hh1 : (1 : ℝ) ≤ 2 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have hXJ : (1 : ℝ) ≤ Fintype.card (T.X J) := by exact_mod_cast hX
  have hX0 : (Fintype.card (T.X 0) : ℝ) = (D : ℝ) ^ J * Fintype.card (T.X J) := card_X_pow J le_rfl
  set x : ℝ := (Fintype.card (T.X 0) : ℝ) with hx
  have hDJ : (D : ℝ) ^ J ≤ x := by
    rw [hX0]
    exact le_mul_of_one_le_right (by positivity) hXJ
  have hDJ1 : (1 : ℝ) ≤ (D : ℝ) ^ J := one_le_pow₀ hDR
  have hx1 : 1 ≤ x := hDJ1.trans hDJ
  have hx0 : 0 < x := by linarith
  set M : ℝ := max 1 (√D * ρ) with hM
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  -- the square of the base
  have hMq : (M ^ 2) ^ q ≤ (D : ℝ) ^ (q - 2 * p) := by
    have e1 : 1 ≤ (D : ℝ) ^ (q - 2 * p) := one_le_pow₀ hDR
    rcases le_total (√D * ρ) 1 with hle | hle
    · rw [hM, max_eq_left hle]
      simpa using e1
    · rw [hM, max_eq_right hle, mul_pow, Real.sq_sqrt (by linarith), mul_pow]
      have e2 : (ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2 ≤ 1 := by
        have : (ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2 = (ρ ^ q * (D : ℝ) ^ p) ^ 2 := by ring
        rw [this]
        exact pow_le_one₀ (by positivity) hgain
      have e3 : (D : ℝ) ^ q = (D : ℝ) ^ (q - 2 * p) * ((D : ℝ) ^ p) ^ 2 := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [e3]
      calc (D : ℝ) ^ (q - 2 * p) * ((D : ℝ) ^ p) ^ 2 * (ρ ^ 2) ^ q =
          (D : ℝ) ^ (q - 2 * p) * ((ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2) := by ring
        _ ≤ (D : ℝ) ^ (q - 2 * p) * 1 := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = _ := mul_one _
  have hsq : (bhat FL Uu AA lhat ρ ^ q * x ^ p) ^ 2 ≤ ((2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q) ^ 2 := by
    have e1 : (bhat FL Uu AA lhat ρ ^ q * x ^ p) ^ 2 =
        (2 * h / x) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
      have e0 : bhat FL Uu AA lhat ρ = √(2 * h / x) * M ^ J * kbar FL Uu AA lhat := rfl
      rw [e0]
      have e2 : √(2 * h / x) ^ 2 = 2 * h / x := Real.sq_sqrt (by positivity)
      have e3 : ∀ s : ℝ, ((s * M ^ J * kbar FL Uu AA lhat) ^ q * x ^ p) ^ 2 =
          (s ^ 2) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := fun s => by ring
      rw [e3, e2]
    rw [e1]
    have e3 : ((M ^ 2) ^ q) ^ J ≤ x ^ (q - 2 * p) := by
      calc ((M ^ 2) ^ q) ^ J ≤ ((D : ℝ) ^ (q - 2 * p)) ^ J := pow_le_pow_left₀ (by positivity) hMq J
        _ = ((D : ℝ) ^ J) ^ (q - 2 * p) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hDJ _
    have e4 : (2 * h / x) ^ q * x ^ (q - 2 * p) * (x ^ p) ^ 2 = (2 * (h : ℝ)) ^ q := by
      have : x ^ (q - 2 * p) * (x ^ p) ^ 2 = x ^ q := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [mul_assoc, this, ← mul_pow, div_mul_cancel₀ _ hx0.ne']
    calc (2 * h / x) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 ≤
        (2 * h / x) ^ q * x ^ (q - 2 * p) * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left e3 (by positivity)) (by positivity)) (by positivity)
      _ = (2 * h / x) ^ q * x ^ (q - 2 * p) * (x ^ p) ^ 2 * (kbar FL Uu AA lhat ^ q) ^ 2 := by ring
      _ = (2 * (h : ℝ)) ^ q * (kbar FL Uu AA lhat ^ q) ^ 2 := by rw [e4]
      _ ≤ ((2 * (h : ℝ)) ^ q) ^ 2 * (kbar FL Uu AA lhat ^ q) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : (1 : ℝ) ≤ (2 * (h : ℝ)) ^ q := one_le_pow₀ hh1
          exact le_self_pow₀ h1 (by norm_num)
      _ = _ := by ring
  have h0 : 0 ≤ (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by positivity
  exact (abs_le_of_sq_le_sq' hsq h0).2


theorem kbar_le (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0))
    (hX : 0 < Fintype.card (T.X 0)) (hb : 0 < b) :
    kbar FL Uu AA lhat ≤ (√h * r + √FL.C₁ * FL.a₁) *
      (m * Fintype.card (T.X 0) * (lhat + 2 * (Fintype.card (T.X 0) : ℝ) ^ 2)) := by
  set X := Fintype.card (T.X 0) with hXd
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : nhat T Uu AA lhat ≤ 2 * m * (lhat + 2 * X ^ 2) := by
    unfold nhat
    rw [← hXd]
    have h1 : X * (lhat / X) ≤ lhat := Nat.mul_div_le lhat X
    calc Uu * (lhat / X + 2 * AA) ≤ 2 * X * m * (lhat / X + 2 * X) := by gcongr
      _ = 2 * m * (X * (lhat / X) + 2 * X ^ 2) := by ring
      _ ≤ 2 * m * (lhat + 2 * X ^ 2) := by gcongr
  have hnR : (nhat T Uu AA lhat : ℝ) ≤ 2 * m * (lhat + 2 * (X : ℝ) ^ 2) := by exact_mod_cast hn
  have hC := Real.sqrt_nonneg FL.C₁
  have hsh := Real.sqrt_nonneg (h : ℝ)
  have hl0 : (0 : ℝ) ≤ lhat := Nat.cast_nonneg _
  have h2 : (1 : ℝ) ≤ m * (lhat + 2 * (X : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ lhat + 2 * (X : ℝ) ^ 2 := by nlinarith
    nlinarith
  unfold kbar
  rw [← hXd]
  have p1 : √h * (r * X / 2) * nhat T Uu AA lhat ≤ √h * r * (m * X * (lhat + 2 * (X : ℝ) ^ 2)) := by
    calc √h * (r * X / 2) * nhat T Uu AA lhat ≤ √h * (r * X / 2) * (2 * m * (lhat + 2 * (X : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hnR (by positivity)
      _ = _ := by ring
  have p2 : √FL.C₁ * FL.a₁ / b * X ≤ √FL.C₁ * FL.a₁ * (m * X * (lhat + 2 * (X : ℝ) ^ 2)) := by
    have h3 : √FL.C₁ * FL.a₁ / b ≤ √FL.C₁ * FL.a₁ := div_le_self (by positivity) hb1
    calc √FL.C₁ * FL.a₁ / b * X ≤ √FL.C₁ * FL.a₁ * X := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = √FL.C₁ * FL.a₁ * X * 1 := (mul_one _).symm
      _ ≤ √FL.C₁ * FL.a₁ * X * (m * (lhat + 2 * (X : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  linarith

end

end Nc.Tow
end
/- Source module Nc.Tow.CapOk. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}


noncomputable def BhN (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℕ := ⌊bhat FL Uu AA lhat ρ⌋₊

theorem bhat_nonneg (ρ : ℝ) : 0 ≤ bhat FL Uu AA lhat ρ := by
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have h1 : (0 : ℝ) ≤ max 1 (√D * ρ) := le_trans zero_le_one (le_max_left _ _)
  unfold bhat
  positivity

theorem lev_eq (L : Tg T m AA → ℕ) (j : Fin (J + 1)) : lev L j.1 = fun e => L (.edge j e) := by
  funext e
  unfold lev
  rw [dif_pos j.2]

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD


theorem plan_ok_cap : (plan R FL Pl lhat U0 U1).Ok (capN FL U0 Uu AA lhat) :=
  plan_ok hr hb fun n _ mv => num_le_cap hr hb hh hbD hρ hρ'.le hρ1 hρD
    (fun a c => Nat.le_of_lt_succ (n a c).2) mv


theorem sum_fb_le {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} :
    ∑ i ∈ range (J + 1), ∑ c, fb (lev (load R ch FL lhat n o)) i c ≤ YhN FL Uu AA lhat ρ := by
  rw [Finset.sum_range]
  refine le_trans (le_of_eq ?_) (sum_bet_le_YhN (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o)
    hr hb hh hbD hρ hρ' hρ1 hρD)
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  unfold fb
  rw [lev_eq]
  rfl

omit hρ' in

theorem fb_le {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} (j : ℕ) (hj : j ≤ J) (c : T.X j) :
    fb (lev (load R ch FL lhat n o)) j c ≤ BhN FL Uu AA lhat ρ := by
  refine Nat.le_floor ?_
  have h1 := bet_le_bhat (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD
    ⟨j, Nat.lt_succ_of_le hj⟩ c
  refine le_trans (le_of_eq ?_) h1
  unfold fb
  have := lev_eq (load R ch FL lhat n o) ⟨j, Nat.lt_succ_of_le hj⟩
  rw [this]
  rfl

omit hr hρ' hρ1 hρD in

theorem BhN_pow_le (hX : 0 < Fintype.card (T.X J)) {p q : ℕ} (hpq : 2 * p ≤ q) (hgain : ρ ^ q * (D : ℝ) ^ p ≤ 1) :
    (BhN FL Uu AA lhat ρ : ℝ) ^ q * (Fintype.card (T.X 0) : ℝ) ^ p ≤
      (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by
  refine le_trans ?_ (bhat_pow_le (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat) hb hbD hρ hh hX hpq hgain)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (bhat_nonneg ρ)) q

end

end Nc.Tow
end
/- Source module Nc.Tow.Cards. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section General

theorem sum_inj_le {α β : Type*} [Fintype α] [Fintype β] {g : α → β} (hg : Function.Injective g) (f : β → ℕ) :
    ∑ a, f (g a) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_image (f := f) (g := g) (s := univ) fun x _ y _ h => hg h]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

end General

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}

namespace Tower


theorem card_X_le (hD : 0 < D) : ∀ j ≤ J, Fintype.card (T.X j) ≤ Fintype.card (T.X 0) := by
  intro j
  induction j with
  | zero => exact fun _ => le_rfl
  | succ j ih =>
    intro hj
    refine le_trans ?_ (ih (by omega))
    rw [T.card_X j (by omega)]
    exact Nat.le_mul_of_pos_left _ hD

theorem two_card_ed {j : ℕ} (hj : j ≤ J) : 2 * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by
  have h1 : Fintype.card (T.Ed j) = ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i).card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => T.card_ed j hj i]
  simp

theorem card_ed_le (hD : 0 < D) {j : ℕ} (hj : j ≤ J) : Fintype.card (T.Ed j) ≤ h * r * Fintype.card (T.X 0) := by
  have h1 := two_card_ed (T := T) hj
  have h2 : h * (r * Fintype.card (T.X j)) ≤ h * r * Fintype.card (T.X 0) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (card_X_le hD j hj)
  omega

theorem card_V_le (hD : 0 < D) (hb : 0 < b) {j : ℕ} (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) ≤ Fintype.card (T.X 0) := by
  have h1 : Fintype.card (T.V j i) * b = Fintype.card (T.X j) := by
    rw [Fintype.card_of_bijective (T.vx_co hj i), Fintype.card_prod, T.card_fl]
  refine le_trans ?_ (card_X_le hD j hj)
  rw [← h1]
  exact Nat.le_mul_of_pos_right _ hb

theorem card_V_Nr {j : ℕ} (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) * Fintype.card T.Nr ≤ Fintype.card (T.Ed j) := by
  rw [← Fintype.card_prod, ← Fintype.card_congr (T.nr hj i)]
  exact Fintype.card_subtype_le _

end Tower


def rmN (h r m J AA X0 : ℕ) : ℕ := AA * (AA * (X0 * (2 * m))) + (J * (h + 4) + 1) * (h * r * X0)


def lmN (h J X0 dd : ℕ) : ℕ := J * (h * (X0 * dd))

theorem card_RM_le (hD : 0 < D) : Fintype.card (RM T m AA) ≤ rmN h r m J AA (Fintype.card (T.X 0)) := by
  rw [Fintype.card_congr (rmEquiv T m AA)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  have h1 : ∀ j : Fin J, Fintype.card (T.Ed j) ≤ h * r * Fintype.card (T.X 0) := fun j => Tower.card_ed_le hD j.2.le
  have h2 := Tower.card_ed_le (T := T) hD (le_refl J)
  have h3 : ∑ j : Fin J, h * Fintype.card (T.Ed j) ≤ J * (h * (h * r * Fintype.card (T.X 0))) := by
    calc ∑ j : Fin J, h * Fintype.card (T.Ed j) ≤ ∑ _j : Fin J, h * (h * r * Fintype.card (T.X 0)) :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (h1 j)
      _ = _ := by simp
  have h4 : ∑ j : Fin J, Fintype.card (T.Ed j) * 4 ≤ J * (h * r * Fintype.card (T.X 0) * 4) := by
    calc ∑ j : Fin J, Fintype.card (T.Ed j) * 4 ≤ ∑ _j : Fin J, h * r * Fintype.card (T.X 0) * 4 :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h1 j)
      _ = _ := by simp
  unfold rmN
  refine Nat.add_le_add_left ?_ _
  calc _ ≤ J * (h * (h * r * Fintype.card (T.X 0))) + (J * (h * r * Fintype.card (T.X 0) * 4) +
        h * r * Fintype.card (T.X 0)) := Nat.add_le_add h3 (Nat.add_le_add h4 h2)
    _ = _ := by ring

section Moves

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}

theorem card_LMv_le (hD : 0 < D) (hb : 0 < b) :
    Fintype.card (LMv T FL) ≤ lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) := by
  simp only [Fintype.card_sigma, Fintype.card_prod]
  unfold lmN
  calc ∑ j : Fin J, ∑ i : Fin h, Fintype.card (T.V (j + 1) i) * Fintype.card FL.Di ≤
      ∑ _j : Fin J, ∑ _i : Fin h, Fintype.card (T.X 0) * Fintype.card FL.Di :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
          Nat.mul_le_mul_right _ (Tower.card_V_le hD hb j.2 i)
    _ = _ := by simp


theorem sum_mv_le (f : Mv T R ch FL → ℕ) {a : ℕ} {g : LMv T FL → ℕ} (h1 : ∀ x, f (.inl x) ≤ a)
    (h2 : ∀ l, f (.inr l) ≤ g l) : ∑ mv, f mv ≤ Fintype.card (RM T m AA) * a + ∑ l, g l := by
  have hinj : Function.Injective (Sum.map Subtype.val id : Mv T R ch FL → RM T m AA ⊕ LMv T FL) :=
    Function.Injective.sumMap Subtype.val_injective Function.injective_id
  have h3 : ∀ mv : Mv T R ch FL, f mv ≤ Sum.elim (fun _ => a) g (Sum.map Subtype.val id mv) := by
    rintro (x | l)
    · exact h1 x
    · exact h2 l
  refine (Finset.sum_le_sum fun mv _ => h3 mv).trans ((sum_inj_le hinj (Sum.elim (fun _ => a) g)).trans ?_)
  rw [Fintype.sum_sum_type]
  simp

theorem sum_moves (f : Mv T R ch FL → ℕ) : ∑ x, f (eE R FL x) = ∑ mv, f mv := Equiv.sum_comp (eE R FL) f

theorem card_Mv_le (hD : 0 < D) (hb : 0 < b) : Fintype.card (Mv T R ch FL) ≤
    rmN h r m J AA (Fintype.card (T.X 0)) + lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) := by
  have h1 := sum_mv_le (R := R) (ch := ch) (FL := FL) (fun _ => 1) (a := 1) (g := fun _ => 1) (fun _ => le_rfl)
    fun _ => le_rfl
  simp only [Finset.sum_const, card_univ, smul_eq_mul, Nat.mul_one] at h1
  exact h1.trans (Nat.add_le_add (card_RM_le hD) (card_LMv_le hD hb))


theorem card_N_le (hD : 0 < D) : Fintype.card (sys R FL Pl).N ≤ rmN h r m J AA (Fintype.card (T.X 0)) * 2 +
    J * (h * (h * r * Fintype.card (T.X 0) * Fintype.card FL.Di)) := by
  have e : Fintype.card (sys R FL Pl).N = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Cn := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Cn
  rw [e]
  refine (sum_mv_le (a := 2) (g := fun _ => Fintype.card T.Nr) _ (fun x => ?_) fun l => ?_).trans ?_
  · exact le_of_eq (Fintype.card_congr (Equiv.refl Bool))
  · exact le_of_eq (Fintype.card_congr (FL.cn l.2.2.2))
  · refine Nat.add_le_add (Nat.mul_le_mul_right _ (card_RM_le hD)) ?_
    have h1 : ∑ _l : LMv T FL, Fintype.card T.Nr =
        ∑ j : Fin J, ∑ i : Fin h, Fintype.card (T.V (j + 1) i) * Fintype.card T.Nr * Fintype.card FL.Di := by
      rw [Finset.sum_const, card_univ, smul_eq_mul, Fintype.card_sigma, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.card_sigma, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.card_prod]
      ring
    rw [h1]
    calc _ ≤ ∑ _j : Fin J, ∑ _i : Fin h, h * r * Fintype.card (T.X 0) * Fintype.card FL.Di :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _
            ((Tower.card_V_Nr j.2 i).trans (Tower.card_ed_le hD j.2))
      _ = _ := by simp


theorem card_Z_le (hD : 0 < D) (hb : 0 < b) {S : ℕ} (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ S) :
    Fintype.card (sys R FL Pl).Z ≤ rmN h r m J AA (Fintype.card (T.X 0)) +
      lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * S := by
  have e : Fintype.card (sys R FL Pl).Z = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Sl := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Sl
  rw [e]
  refine (sum_mv_le (a := 1) (g := fun _ => S) _ (fun x => ?_) fun l => hS l.2.2.2).trans ?_
  · exact le_of_eq (Fintype.card_congr (Equiv.refl Unit))
  · rw [Nat.mul_one, Finset.sum_const, card_univ, smul_eq_mul]
    exact Nat.add_le_add (card_RM_le hD) (Nat.mul_le_mul_right _ (card_LMv_le hD hb))


theorem card_R_le (hD : 0 < D) (hb : 0 < b) : Fintype.card (sys R FL Pl).R ≤
    rmN h r m J AA (Fintype.card (T.X 0)) * 3 + lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * b := by
  have e : Fintype.card (sys R FL Pl).R = ∑ mv : Mv T R ch FL, Fintype.card (kindM R ch FL mv).Ro := by
    rw [Fintype.card_sigma]
    exact sum_moves fun mv => Fintype.card (kindM R ch FL mv).Ro
  rw [e]
  refine (sum_mv_le (a := 3) (g := fun _ => b) _ (fun x => ?_) fun l => ?_).trans ?_
  · exact le_of_eq ((Fintype.card_congr (Equiv.refl (Fin 3))).trans (Fintype.card_fin 3))
  · exact le_of_eq ((Fintype.card_congr (FL.ro l.2.2.2)).trans T.card_fl)
  · rw [Finset.sum_const, card_univ, smul_eq_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (card_RM_le hD)) (Nat.mul_le_mul_right _ (card_LMv_le hD hb))


theorem card_Un : Fintype.card (Un R FL Pl U0 U1) = AA * AA * U0 + Fintype.card (sys R FL Pl).N * U1 := by
  let e : Un R FL Pl U0 U1 ≃ (Fin AA × Fin AA × Fin U0) ⊕ ((sys R FL Pl).N × Fin U1) :=
    { toFun := fun u => match u with
        | .init a c k => .inl (a, c, k)
        | .new ν k => .inr (ν, k)
      invFun := fun s => match s with
        | .inl q => .init q.1 q.2.1 q.2.2
        | .inr q => .new q.1 q.2
      left_inv := fun u => by cases u <;> rfl
      right_inv := fun s => by rcases s with ⟨a, c, k⟩ | ⟨ν, k⟩ <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin]
  ring

end Moves


theorem card_Nd_le (hD : 0 < D) : Fintype.card (Nd T) ≤ (J + 1) * Fintype.card (T.X 0) + 1 := by
  rw [Fintype.card_option, Fintype.card_sigma]
  refine Nat.add_le_add_right ?_ _
  calc ∑ j : Fin (J + 1), Fintype.card (T.X j) ≤ ∑ _j : Fin (J + 1), Fintype.card (T.X 0) :=
        Finset.sum_le_sum fun j _ => Tower.card_X_le hD j.1 (Nat.le_of_lt_succ j.2)
    _ = _ := by simp


theorem card_party {ch : Fin AA ↪ T.X 0} (Pl : Place T ch A') : AA + A' = Fintype.card (Nd T) := by
  rw [Fintype.card_congr Pl.pt, Fintype.card_fin]



section Powers

variable {V : ℕ}

theorem rmN_le {X0 : ℕ} (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V) (hAA : AA ≤ V) (hX : X0 ≤ V) :
    rmN h r m J AA X0 ≤ 8 * V ^ 5 := by
  have h1 : rmN h r m J AA X0 ≤ V * (V * (V * (2 * V))) + (V * (V + 4) + 1) * (V * V * V) := by
    unfold rmN
    gcongr
  refine h1.trans ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hV
  ring_nf
  omega

theorem lmN_le {X0 dd : ℕ} (hh : h ≤ V) (hJ : J ≤ V) (hX : X0 ≤ V) (hdd : dd ≤ V) : lmN h J X0 dd ≤ V ^ 4 := by
  have h1 : lmN h J X0 dd ≤ V * (V * (V * V)) := by
    unfold lmN
    gcongr
  exact h1.trans (le_of_eq (by ring))

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}


theorem cards_le (hD : 0 < D) (hb : 0 < b) (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V)
    (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hdd : Fintype.card FL.Di ≤ V) (hbV : b ≤ V)
    (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ V) (hU0 : U0 ≤ V) (hU1 : U1 ≤ V) :
    Fintype.card (sys R FL Pl).N ≤ 17 * V ^ 6 ∧ Fintype.card (sys R FL Pl).Z ≤ 9 * V ^ 5 ∧
      Fintype.card (sys R FL Pl).R ≤ 25 * V ^ 5 ∧ Fintype.card (Un R FL Pl U0 U1) ≤ 18 * V ^ 7 ∧
      Fintype.card (Mv T R ch FL) ≤ 9 * V ^ 5 ∧ Fintype.card (Nd T) ≤ 3 * V ^ 2 := by
  have h1 := rmN_le (X0 := Fintype.card (T.X 0)) hV hh hr hm hJ hAA hX
  have h2 := lmN_le (X0 := Fintype.card (T.X 0)) hh hJ hX hdd
  have p45 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have p56 : V ^ 5 ≤ V ^ 6 := Nat.pow_le_pow_right hV (by norm_num)
  have p37 : V ^ 3 ≤ V ^ 7 := Nat.pow_le_pow_right hV (by norm_num)
  have p12 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) V
  have p02 : 1 ≤ V ^ 2 := Nat.one_le_pow _ _ hV
  have hN : Fintype.card (sys R FL Pl).N ≤ 17 * V ^ 6 := by
    have h3 := card_N_le (R := R) (FL := FL) (Pl := Pl) hD
    have h4 : J * (h * (h * r * Fintype.card (T.X 0) * Fintype.card FL.Di)) ≤ V * (V * (V * V * V * V)) := by gcongr
    have h5 : V * (V * (V * V * V * V)) = V ^ 6 := by ring
    omega
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 := card_Z_le (R := R) (FL := FL) (Pl := Pl) hD hb hS
    have h4 := Nat.mul_le_mul_right V h2
    have h5 : V ^ 4 * V = V ^ 5 := by ring
    omega
  · have h3 := card_R_le (R := R) (FL := FL) (Pl := Pl) hD hb
    have h4 : lmN h J (Fintype.card (T.X 0)) (Fintype.card FL.Di) * b ≤ V ^ 4 * V := Nat.mul_le_mul h2 hbV
    have h5 : V ^ 4 * V = V ^ 5 := by ring
    omega
  · rw [card_Un]
    have h4 : AA * AA * U0 ≤ V * V * V := by gcongr
    have h5 : Fintype.card (sys R FL Pl).N * U1 ≤ 17 * V ^ 6 * V := Nat.mul_le_mul hN hU1
    have h6 : V * V * V = V ^ 3 := by ring
    have h7 : 17 * V ^ 6 * V = 17 * V ^ 7 := by ring
    omega
  · have h3 := card_Mv_le (R := R) (ch := ch) (FL := FL) hD hb
    omega
  · have h3 := card_Nd_le (T := T) hD
    have h4 : (J + 1) * Fintype.card (T.X 0) ≤ (V + 1) * V := by gcongr
    have h5 : (V + 1) * V = V ^ 2 + V := by ring
    omega

end Powers

end Nc.Tow
end
/- Source module Nc.Tow.Ever1. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r}


theorem sum_RM {M : Type*} [AddCommMonoid M] (g : RM T m AA → M) : ∑ x, g x =
    (∑ a, ∑ c, ∑ γ, ∑ s, g (.start a c γ s)) + ((∑ j, ∑ i, ∑ e, g (.inn j i e)) +
      ((∑ j, ∑ e, ∑ s, g (.mid j e s)) + ∑ e, g (.fin e))) := by
  rw [← (rmEquiv T m AA).symm.sum_comp g]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma]
  rfl

section Levels

open Classical in

theorem sum_level (g : ∀ j : Fin J, T.X j → ℕ) (j0 : ℕ) (hj0 : j0 ≤ J) (c : T.X j0) :
    (∑ j : Fin J, ∑ x, if nd T j j.2.le x = nd T j0 hj0 c then g j x else 0) =
      if hlt : j0 < J then g ⟨j0, hlt⟩ c else 0 := by
  by_cases hlt : j0 < J
  · rw [dif_pos hlt, Finset.sum_eq_single ⟨j0, hlt⟩, Finset.sum_eq_single c]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg fun he => hx (nd_inj.1 he)]
    · intro hn; exact absurd (mem_univ _) hn
    · intro j _ hj
      refine Finset.sum_eq_zero fun x _ => if_neg ?_
      exact nd_ne fun he => hj (Fin.ext he)
    · intro hn; exact absurd (mem_univ _) hn
  · rw [dif_neg hlt]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => if_neg ?_
    exact nd_ne fun he : j.1 = j0 => hlt (he ▸ j.2)

open Classical in

theorem sum_level_zero (g : ∀ j : Fin J, T.X (j + 1) → ℕ) (c : T.X 0) :
    (∑ j : Fin J, ∑ x, if nd T (j + 1) j.2 x = nd T 0 (Nat.zero_le _) c then g j x else 0) = 0 := by
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => if_neg ?_
  exact nd_ne (Nat.succ_ne_zero _)

open Classical in

theorem sum_level_succ (g : ∀ j : Fin J, T.X (j + 1) → ℕ) (k : ℕ) (hk : k + 1 ≤ J) (c : T.X (k + 1)) :
    (∑ j : Fin J, ∑ x, if nd T (j + 1) j.2 x = nd T (k + 1) hk c then g j x else 0) = g ⟨k, hk⟩ c := by
  rw [Finset.sum_eq_single ⟨k, hk⟩, Finset.sum_eq_single c]
  · rw [if_pos rfl]
  · intro x _ hx
    rw [if_neg fun he => hx (nd_inj.1 he)]
  · intro hn; exact absurd (mem_univ _) hn
  · intro j _ hj
    refine Finset.sum_eq_zero fun x _ => if_neg ?_
    exact nd_ne fun he => hj (Fin.ext (Nat.succ_injective he))
  · intro hn; exact absurd (mem_univ _) hn


theorem sum_end {κ X : Type*} [Fintype κ] [Fintype X] [DecidableEq X] (w : κ → X) (p : X → Prop) [DecidablePred p]
    (f : κ → ℕ) :
    (∑ e, if p (w e) then f e else 0) = ∑ x, if p x then ∑ e, (if w e = x then f e else 0) else 0 := by
  have h1 : ∀ e, (if p (w e) then f e else 0) = ∑ x, if p x then (if w e = x then f e else 0) else 0 := by
    intro e
    rw [Finset.sum_eq_single (w e)]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg (Ne.symm hx)]
      split_ifs <;> rfl
    · intro hn; exact absurd (mem_univ _) hn
  rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rfl
  · simp

end Levels

variable (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ)

open Classical in

noncomputable def chs (j : ℕ) (x : T.X (j + 1)) : ℕ := ∑ c : T.X j, if hostj hh Lf c = x then fb Lf j c else 0

open Classical in
theorem fb_eq (j : ℕ) (c : T.X j) : fb Lf j c = (∑ e, if T.e0 e = c then Lf j e else 0) +
    ∑ e, if T.e1 e = c then Lf j e else 0 := by
  unfold fb Tower.bet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hc => hne (h0.trans hc.symm)
    simp [h0, h1]
  · by_cases h1 : T.e1 e = c <;> simp [h0, h1]

open Classical in
theorem chs_eq (j : ℕ) (x : T.X (j + 1)) : chs hh Lf j x =
    (∑ e, if hostj hh Lf (T.e0 e) = x then Lf j e else 0) + ∑ e, if hostj hh Lf (T.e1 e) = x then Lf j e else 0 := by
  unfold chs
  rw [sum_end (fun e => T.e0 e) (fun c => hostj hh Lf c = x), sum_end (fun e => T.e1 e) (fun c => hostj hh Lf c = x),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · exact fb_eq Lf j c
  · rfl

section Num

variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

variable (R ch FL lhat n o) in
open Classical in

noncomputable def nR (x : RM T m AA) : ℕ := if hx : okR T R ch x then num R ch FL lhat n o (.inl ⟨x, hx⟩) else 0

variable (R ch FL lhat n o) in

noncomputable abbrev ldL : ∀ j, T.Ed j → ℕ := lev (load R ch FL lhat n o)

theorem lev_castSucc (j : Fin J) (e : T.Ed j) : load R ch FL lhat n o (.edge j.castSucc e) =
    ldL R ch FL lhat n o j e := by
  unfold ldL lev
  rw [dif_pos (Nat.lt_succ_of_lt j.2)]
  rfl

theorem lev_succ (j : Fin J) (e : T.Ed (j + 1)) : load R ch FL lhat n o (.edge j.succ e) =
    ldL R ch FL lhat n o (j + 1) e := by
  unfold ldL lev
  rw [dif_pos (Nat.succ_lt_succ j.2)]
  rfl

theorem lev_last (e : T.Ed J) : load R ch FL lhat n o (.edge (Fin.last J) e) = ldL R ch FL lhat n o J e := by
  unfold ldL lev
  rw [dif_pos (Nat.lt_succ_self J)]
  rfl

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem nR_inn (j : Fin J) (i : Fin h) (e : T.Ed j) : nR R ch FL lhat n o (.inn j i e) ≤
    if i = imin hh (ldL R ch FL lhat n o) j then ldL R ch FL lhat n o j e else 0 := by
  classical
  unfold nR
  split_ifs with hx h1 h1
  · refine (num_inl hr hb _).trans (le_of_eq ?_)
    exact lev_castSucc j e
  · rw [num_eq hr hb, numF, if_neg]
    intro ha
    exact h1 ((isMin_iff hh _ j.castSucc i).1 ha)
  · exact Nat.zero_le _
  · exact le_rfl

theorem nR_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : nR R ch FL lhat n o (.mid j e s) ≤
    if T.ty e = imin hh (ldL R ch FL lhat n o) j then ldL R ch FL lhat n o j e else 0 := by
  classical
  unfold nR
  split_ifs with hx h1 h1
  · obtain ⟨hx0, h2⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
    refine h2.trans ((num_mid0 hr hb j e hx0).1.trans (le_of_eq ?_))
    exact lev_castSucc j e
  · obtain ⟨hx0, h2⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
    refine h2.trans (le_of_eq ?_)
    refine (num_mid0 hr hb j e hx0).2 fun hm => h1 ?_
    exact (isMin_iff hh _ j.castSucc _).1 hm
  · exact Nat.zero_le _
  · exact le_rfl

theorem nR_fin (e : T.Ed J) : nR R ch FL lhat n o (.fin e) ≤ ldL R ch FL lhat n o J e := by
  classical
  unfold nR
  split_ifs with hx
  · refine (num_inl hr hb _).trans (le_of_eq ?_)
    exact lev_last e
  · exact Nat.zero_le _

end Num

end Nc.Tow
end
/- Source module Nc.Tow.Ever2. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}


theorem sum_alv_le {κ : Type*} [DecidableEq κ] (τ : Tg T m AA) (s : Finset κ) (f : κ → NM R FL (ch := ch))
    (hf : Set.InjOn f s) (hτ : ∀ x ∈ s, tgM R ch FL (f x).1 (f x).2 = τ) :
    ∑ x ∈ s, alv R ch FL lhat n o (f x) ≤ load R ch FL lhat n o τ := by
  classical
  rw [load_def]
  refine le_trans ?_ (Nat.le_add_left _ _)
  have h1 : ∑ x ∈ s, alv R ch FL lhat n o (f x) = ∑ ν ∈ s.image f, alv R ch FL lhat n o ν :=
    (Finset.sum_image hf).symm
  rw [h1]
  calc ∑ ν ∈ s.image f, alv R ch FL lhat n o ν =
      ∑ ν ∈ s.image f, if tgM R ch FL ν.1 ν.2 = τ then alv R ch FL lhat n o ν else 0 := by
        refine Finset.sum_congr rfl fun ν hν => ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hν
        rw [if_pos (hτ x hx)]
    _ ≤ _ := Finset.sum_le_sum_of_subset (subset_univ _)

section

variable (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))

include hgR in
theorem alv_relay (x : {x : RM T m AA // okR T R ch x}) (ν : Bool) :
    alv R ch FL lhat n o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x) := by
  unfold alv
  have h1 : alvN R ch FL o ⟨.inl x, ν⟩ (num R ch FL lhat n o (.inl x)) =
      if o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x) then num R ch FL lhat n o (.inl x) else 0 := rfl
  rw [h1, if_pos (hgR x ν)]

theorem ok_mid2 (j : Fin J) (e : T.Ed j) : okR T R ch (.mid j e 2) :=
  ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩

include hr hb

theorem nR_mid3 (j : Fin J) (e : T.Ed j) : nR R ch FL lhat n o (.mid j e 3) ≤ nR R ch FL lhat n o (.mid j e 2) := by
  classical
  unfold nR
  rw [dif_pos (ok_mid2 j e)]
  split_ifs with hx
  · refine (num_inl hr hb _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 3) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
        have h3 : x = .mid j e 2 := by
          rcases h2 with h2 | h2 | h2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
          · exact h2.2
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM, inpR_mid] at hν
    · rw [Finset.sum_singleton]
      exact alv_le_num hr hb _ _
  · exact Nat.zero_le _

include hgR

theorem nR_mid1 (j : Fin J) (e : T.Ed j) : nR R ch FL lhat n o (.mid j e 1) ≤ nR R ch FL lhat n o (.mid j e 2) := by
  classical
  unfold nR
  rw [dif_pos (ok_mid2 j e)]
  split_ifs with hx
  · have h1 : num R ch FL lhat n o (.inl ⟨.mid j e 2, ok_mid2 j e⟩) = load R ch FL lhat n o (.nxt (.mid j e 2)) := by
      rw [num_eq hr hb, numF, if_pos]
      · rfl
      · intro hh
        exact absurd hh (by decide)
    rw [h1, ← alv_relay hgR ⟨.mid j e 1, hx⟩ true]
    have h2 := sum_alv_le (lhat := lhat) (n := n) (o := o) (.nxt (.mid j e 2)) ({()} : Finset Unit)
      (fun _ => (⟨.inl ⟨.mid j e 1, hx⟩, true⟩ : NM R FL (ch := ch))) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    rw [Finset.sum_singleton] at h2
    exact h2
  · exact Nat.zero_le _

open Classical in

theorem sum_mid2 (j : Fin J) (c : T.X (j + 1)) :
    ((∑ e : T.Ed j, if T.π (T.e0 e) = c then nR R ch FL lhat n o (.mid j e 2) else 0) +
      ∑ e : T.Ed j, if T.π (T.e1 e) = c then nR R ch FL lhat n o (.mid j e 2) else 0) ≤
      fb (ldL R ch FL lhat n o) (j + 1) c := by
  have h1 : ∀ e : T.Ed j, (if T.π (T.e0 e) = c then nR R ch FL lhat n o (.mid j e 2) else 0) +
      (if T.π (T.e1 e) = c then nR R ch FL lhat n o (.mid j e 2) else 0) =
      if T.e0 (T.πE e) = c ∨ T.e1 (T.πE e) = c then alv R ch FL lhat n o
        (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL (ch := ch)) else 0 := by
    intro e
    have h2 : nR R ch FL lhat n o (.mid j e 2) = alv R ch FL lhat n o
        (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL (ch := ch)) := by
      unfold nR
      rw [dif_pos (ok_mid2 j e)]
      exact (alv_relay hgR ⟨.mid j e 2, ok_mid2 j e⟩ false).symm
    rw [h2]
    have hne := π_ne j.2 e
    have h3 := T.π_ends j.2 e
    have h4 : (T.e0 (T.πE e) = c ∨ T.e1 (T.πE e) = c) ↔ (T.π (T.e0 e) = c ∨ T.π (T.e1 e) = c) := by
      have h5 : ∀ x y : T.X (j + 1), (x = c ∨ y = c) ↔ c ∈ s(x, y) := fun x y => by
        rw [Sym2.mem_iff]
        exact or_congr eq_comm eq_comm
      rw [h5, h5, h3]
    by_cases h0 : T.π (T.e0 e) = c
    · have h5 : ¬ T.π (T.e1 e) = c := fun hc => hne (h0.trans hc.symm)
      rw [if_pos h0, if_neg h5, if_pos (h4.2 (Or.inl h0)), Nat.add_zero]
    · rw [if_neg h0, Nat.zero_add]
      by_cases h5 : T.π (T.e1 e) = c
      · rw [if_pos h5, if_pos (h4.2 (Or.inr h5))]
      · rw [if_neg h5, if_neg]
        rw [h4]
        rintro (hc | hc)
        · exact h0 hc
        · exact h5 hc
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun e _ => h1 e,
    sum_end (fun e => T.πE e) (fun ē => T.e0 ē = c ∨ T.e1 ē = c)]
  unfold fb Tower.bet
  refine Finset.sum_le_sum fun ē _ => ?_
  split_ifs with hc
  · rw [← lev_succ, ← Finset.sum_filter]
    refine sum_alv_le (.edge j.succ ē) (univ.filter fun e : T.Ed j => T.πE e = ē)
      (fun e => (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL (ch := ch))) ?_ ?_
    · intro e _ e' _ hee
      have h2 : (Sum.inl ⟨.mid j e 2, ok_mid2 j e⟩ : Mv T R ch FL) = .inl ⟨.mid j e' 2, ok_mid2 j e'⟩ :=
        congrArg Sigma.fst hee
      have h3 := congrArg Subtype.val (Sum.inl_injective h2)
      simp only [RM.mid.injEq, heq_eq_eq, true_and, and_true] at h3
      exact h3
    · intro e he
      have h2 := (mem_filter.1 he).2
      subst h2
      rfl
  · exact le_rfl

end

section Node

variable (R ch FL lhat n o) in
open Classical in

noncomputable def NR (P : Nd T) : ℕ := ∑ x : RM T m AA, ∑ q : Fin 3, if tri T R ch x q = P then nR R ch FL lhat n o x else 0

variable (R ch FL lhat n o) in
open Classical in

noncomputable def NR0 (P : Nd T) : ℕ := ∑ a, ∑ c, ∑ γ, ∑ s, ∑ q : Fin 3,
  if tri T R ch (.start a c γ s) q = P then nR R ch FL lhat n o (.start a c γ s) else 0

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))
include hh hr hb hgR

open Classical in

theorem NR_le (P : Nd T) : NR R ch FL lhat n o P ≤ NR0 R ch FL lhat n o P +
    (∑ j : Fin J, ∑ x : T.X j, if nd T j j.2.le x = P then 5 * fb (ldL R ch FL lhat n o) j x else 0) +
    (∑ j : Fin J, ∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then
      3 * chs hh (ldL R ch FL lhat n o) j x + 2 * fb (ldL R ch FL lhat n o) (j + 1) x else 0) +
    (∑ x : T.X J, if nd T J le_rfl x = P then fb (ldL R ch FL lhat n o) J x else 0) +
    (if none = P then ∑ e : T.Ed J, ldL R ch FL lhat n o J e else 0) := by
  set Lf := ldL R ch FL lhat n o with hLf
  unfold NR NR0
  rw [sum_RM]
  have hinn : ∀ j : Fin J, (∑ i, ∑ e : T.Ed j, ∑ q : Fin 3, if tri T R ch (.inn j i e) q = P then
      nR R ch FL lhat n o (.inn j i e) else 0) ≤
      (∑ x : T.X j, if nd T j j.2.le x = P then fb Lf j x else 0) +
      ∑ e : T.Ed j, if nd T (j + 1) j.2 (hostj hh Lf (T.e0 e)) = P then Lf j e else 0 := by
    intro j
    have h1 : ∀ i, (∑ e : T.Ed j, ∑ q : Fin 3, if tri T R ch (.inn j i e) q = P then
        nR R ch FL lhat n o (.inn j i e) else 0) ≤ if i = imin hh Lf j then
        ∑ e : T.Ed j, ((if nd T j j.2.le (T.e0 e) = P then Lf j e else 0) +
          (if nd T (j + 1) j.2 (hostj hh Lf (T.e0 e)) = P then Lf j e else 0) +
          if nd T j j.2.le (T.e1 e) = P then Lf j e else 0) else 0 := by
      intro i
      split_ifs with hi
      · subst hi
        refine Finset.sum_le_sum fun e _ => ?_
        rw [Fin.sum_univ_three]
        have h2 := nR_inn (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) hh hr hb j (imin hh Lf j) e
        rw [if_pos rfl] at h2
        refine add_le_add (add_le_add ?_ ?_) ?_
        · change (if nd T j j.2.le (T.e0 e) = P then _ else 0) ≤ _
          split_ifs
          · exact h2
          · exact le_rfl
        · change (if nd T (j + 1) j.2 (hst T (imin hh Lf j) (T.e0 e)) = P then _ else 0) ≤
            if nd T (j + 1) j.2 (hst T (imin hh Lf j) (T.e0 e)) = P then _ else 0
          split_ifs
          · exact h2
          · exact le_rfl
        · change (if nd T j j.2.le (T.e1 e) = P then _ else 0) ≤ _
          split_ifs
          · exact h2
          · exact le_rfl
      · refine le_of_eq (Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun q _ => ?_)
        have h2 := nR_inn (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) hh hr hb j i e
        rw [if_neg hi] at h2
        split_ifs
        · omega
        · rfl
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [Finset.sum_ite_eq', if_pos (mem_univ _), Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_end (fun e => T.e0 e) (fun x => nd T j j.2.le x = P), sum_end (fun e => T.e1 e) (fun x => nd T j j.2.le x = P)]
    have h3 : (∑ x : T.X j, if nd T j j.2.le x = P then fb Lf j x else 0) =
        (∑ x : T.X j, if nd T j j.2.le x = P then (∑ e, if T.e0 e = x then Lf j e else 0) else 0) +
        ∑ x : T.X j, if nd T j j.2.le x = P then (∑ e, if T.e1 e = x then Lf j e else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · exact fb_eq Lf j x
      · rfl
    rw [h3]
    omega
  have hmid : ∀ j : Fin J, (∑ e : T.Ed j, ∑ s : Fin 4, ∑ q : Fin 3, if tri T R ch (.mid j e s) q = P then
      nR R ch FL lhat n o (.mid j e s) else 0) ≤
      4 * (∑ x : T.X j, if nd T j j.2.le x = P then fb Lf j x else 0) +
      (2 * (∑ e : T.Ed j, if nd T (j + 1) j.2 (hostj hh Lf (T.e0 e)) = P then Lf j e else 0) +
        ∑ e : T.Ed j, if nd T (j + 1) j.2 (hostj hh Lf (T.e1 e)) = P then Lf j e else 0) +
      2 * ∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then fb Lf (j + 1) x else 0 := by
    intro j
    have h1 : ∀ e : T.Ed j, (∑ s : Fin 4, ∑ q : Fin 3, if tri T R ch (.mid j e s) q = P then
        nR R ch FL lhat n o (.mid j e s) else 0) ≤
        ((if nd T j j.2.le (T.e0 e) = P then Lf j e else 0) + 4 * if nd T j j.2.le (T.e1 e) = P then Lf j e else 0) +
        (2 * (if nd T (j + 1) j.2 (hostj hh Lf (T.e0 e)) = P then Lf j e else 0) +
          if nd T (j + 1) j.2 (hostj hh Lf (T.e1 e)) = P then Lf j e else 0) +
        (2 * (if nd T (j + 1) j.2 (T.π (T.e0 e)) = P then nR R ch FL lhat n o (.mid j e 2) else 0) +
          2 * if nd T (j + 1) j.2 (T.π (T.e1 e)) = P then nR R ch FL lhat n o (.mid j e 2) else 0) := by
      intro e
      have hs : ∀ s, nR R ch FL lhat n o (.mid j e s) ≤ Lf j e ∧ (T.ty e ≠ imin hh Lf j →
          nR R ch FL lhat n o (.mid j e s) = 0) := by
        intro s
        have h2 := nR_mid (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) hh hr hb j e s
        constructor
        · refine h2.trans ?_
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
        · intro hne
          rw [if_neg hne] at h2
          omega
      have h3 := nR_mid3 (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) hr hb j e
      have h4 := nR_mid1 hr hb hgR j e
      -- the chambers on the next level
      have hH : ∀ s (c : T.X j), (if nd T (j + 1) j.2 (hst T (T.ty e) c) = P then nR R ch FL lhat n o (.mid j e s) else 0) ≤
          if nd T (j + 1) j.2 (hostj hh Lf c) = P then Lf j e else 0 := by
        intro s c
        by_cases ht : T.ty e = imin hh Lf j
        · have : hst T (T.ty e) c = hostj hh Lf c := by rw [ht]; rfl
          rw [this]
          split_ifs
          · exact (hs s).1
          · exact le_rfl
        · rw [(hs s).2 ht]
          split_ifs <;> exact Nat.zero_le _
      have hle : ∀ s (p : Prop) [Decidable p], (if p then nR R ch FL lhat n o (.mid j e s) else 0) ≤
          if p then Lf j e else 0 := by
        intro s p _
        split_ifs
        · exact (hs s).1
        · exact le_rfl
      have hp : ∀ s (p : Prop) [Decidable p], s = 1 ∨ s = 2 ∨ s = 3 → (if p then nR R ch FL lhat n o (.mid j e s) else 0) ≤
          if p then nR R ch FL lhat n o (.mid j e 2) else 0 := by
        intro s p _ hs'
        split_ifs
        · rcases hs' with rfl | rfl | rfl
          · exact h4
          · exact le_rfl
          · exact h3
        · exact le_rfl
      rw [Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
      have a0 := hle 0 (nd T j j.2.le (T.e0 e) = P)
      have b0 := hle 0 (nd T j j.2.le (T.e1 e) = P)
      have b1 := hle 1 (nd T j j.2.le (T.e1 e) = P)
      have b2 := hle 2 (nd T j j.2.le (T.e1 e) = P)
      have b3 := hle 3 (nd T j j.2.le (T.e1 e) = P)
      have c0 := hH 0 (T.e0 e)
      have c1 := hH 1 (T.e0 e)
      have c3 := hH 3 (T.e1 e)
      have d1 := hp 1 (nd T (j + 1) j.2 (T.π (T.e0 e)) = P) (Or.inl rfl)
      have d2 := hp 2 (nd T (j + 1) j.2 (T.π (T.e0 e)) = P) (Or.inr (Or.inl rfl))
      have d3 := hp 2 (nd T (j + 1) j.2 (T.π (T.e1 e)) = P) (Or.inr (Or.inl rfl))
      have d4 := hp 3 (nd T (j + 1) j.2 (T.π (T.e1 e)) = P) (Or.inr (Or.inr rfl))
      change ((if nd T j j.2.le (T.e0 e) = P then _ else 0) + (if nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) = P then _ else 0) +
          if nd T j j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) = P then _ else 0) +
          (if nd T (j + 1) j.2 (T.π (T.e0 e)) = P then _ else 0) + if nd T j j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd T (j + 1) j.2 (T.π (T.e0 e)) = P then _ else 0) +
          (if nd T (j + 1) j.2 (T.π (T.e1 e)) = P then _ else 0) + if nd T j j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd T (j + 1) j.2 (T.π (T.e1 e)) = P then _ else 0) +
          (if nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e)) = P then _ else 0) +
            if nd T j j.2.le (T.e1 e) = P then _ else 0) ≤ _
      omega
    refine (Finset.sum_le_sum fun e _ => h1 e).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e0 := sum_end (fun e : T.Ed j => T.e0 e) (fun x => nd T j j.2.le x = P) (fun e => Lf j e)
    have e1 := sum_end (fun e : T.Ed j => T.e1 e) (fun x => nd T j j.2.le x = P) (fun e => Lf j e)
    have e2 := sum_end (fun e : T.Ed j => T.π (T.e0 e)) (fun x => nd T (j + 1) j.2 x = P)
      (fun e => nR R ch FL lhat n o (.mid j e 2))
    have e3 := sum_end (fun e : T.Ed j => T.π (T.e1 e)) (fun x => nd T (j + 1) j.2 x = P)
      (fun e => nR R ch FL lhat n o (.mid j e 2))
    have h3 : (∑ x : T.X j, if nd T j j.2.le x = P then fb Lf j x else 0) =
        (∑ x : T.X j, if nd T j j.2.le x = P then (∑ e, if T.e0 e = x then Lf j e else 0) else 0) +
        ∑ x : T.X j, if nd T j j.2.le x = P then (∑ e, if T.e1 e = x then Lf j e else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · exact fb_eq Lf j x
      · rfl
    have h4 : (∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then
          (∑ e, if T.π (T.e0 e) = x then nR R ch FL lhat n o (.mid j e 2) else 0) else 0) +
        (∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then
          (∑ e, if T.π (T.e1 e) = x then nR R ch FL lhat n o (.mid j e 2) else 0) else 0) ≤
        ∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then fb Lf (j + 1) x else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · exact sum_mid2 hr hb hgR j x
      · exact le_rfl
    rw [e0, e1, e2, e3, h3]
    omega
  have hfin : (∑ e : T.Ed J, ∑ q : Fin 3, if tri T R ch (.fin e) q = P then nR R ch FL lhat n o (.fin e) else 0) ≤
      (∑ x : T.X J, if nd T J le_rfl x = P then fb Lf J x else 0) +
      if none = P then ∑ e : T.Ed J, Lf J e else 0 := by
    have h1 : ∀ e : T.Ed J, (∑ q : Fin 3, if tri T R ch (.fin e) q = P then nR R ch FL lhat n o (.fin e) else 0) ≤
        (if nd T J le_rfl (T.e0 e) = P then Lf J e else 0) + (if none = P then Lf J e else 0) +
          if nd T J le_rfl (T.e1 e) = P then Lf J e else 0 := by
      intro e
      have h2 := nR_fin (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) hr hb e
      rw [Fin.sum_univ_three]
      refine add_le_add (add_le_add ?_ ?_) ?_
      · change (if nd T J le_rfl (T.e0 e) = P then _ else 0) ≤ _
        split_ifs
        · exact h2
        · exact le_rfl
      · change (if none = P then _ else 0) ≤ _
        split_ifs
        · exact h2
        · exact le_rfl
      · change (if nd T J le_rfl (T.e1 e) = P then _ else 0) ≤ _
        split_ifs
        · exact h2
        · exact le_rfl
    refine (Finset.sum_le_sum fun e _ => h1 e).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_end (fun e => T.e0 e) (fun x => nd T J le_rfl x = P),
      sum_end (fun e => T.e1 e) (fun x => nd T J le_rfl x = P)]
    have h3 : (∑ x : T.X J, if nd T J le_rfl x = P then fb Lf J x else 0) =
        (∑ x : T.X J, if nd T J le_rfl x = P then (∑ e, if T.e0 e = x then Lf J e else 0) else 0) +
        ∑ x : T.X J, if nd T J le_rfl x = P then (∑ e, if T.e1 e = x then Lf J e else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · exact fb_eq Lf J x
      · rfl
    have h4 : (∑ _e : T.Ed J, if none = P then Lf J _e else 0) = if none = P then ∑ e : T.Ed J, Lf J e else 0 := by
      split_ifs
      · rfl
      · simp
    rw [h3, h4]
    omega
  have hchs : ∀ j : Fin J, (∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then chs hh Lf j x else 0) =
      (∑ e : T.Ed j, if nd T (j + 1) j.2 (hostj hh Lf (T.e0 e)) = P then Lf j e else 0) +
      ∑ e : T.Ed j, if nd T (j + 1) j.2 (hostj hh Lf (T.e1 e)) = P then Lf j e else 0 := by
    intro j
    rw [sum_end (fun e : T.Ed j => hostj hh Lf (T.e0 e)) (fun x => nd T (j + 1) j.2 x = P),
      sum_end (fun e : T.Ed j => hostj hh Lf (T.e1 e)) (fun x => nd T (j + 1) j.2 x = P), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · exact chs_eq hh Lf j x
    · rfl
  have hall : (∑ j, ∑ i, ∑ e, ∑ q : Fin 3, if tri T R ch (.inn j i e) q = P then nR R ch FL lhat n o (.inn j i e) else 0) +
      (∑ j, ∑ e, ∑ s, ∑ q : Fin 3, if tri T R ch (.mid j e s) q = P then nR R ch FL lhat n o (.mid j e s) else 0) ≤
      (∑ j : Fin J, ∑ x : T.X j, if nd T j j.2.le x = P then 5 * fb Lf j x else 0) +
      ∑ j : Fin J, ∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then 3 * chs hh Lf j x + 2 * fb Lf (j + 1) x else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hinn j
    have h2 := hmid j
    have h3 := hchs j
    have h4 : (∑ x : T.X j, if nd T j j.2.le x = P then 5 * fb Lf j x else 0) =
        5 * ∑ x : T.X j, if nd T j j.2.le x = P then fb Lf j x else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> rfl
    have h5 : (∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then 3 * chs hh Lf j x + 2 * fb Lf (j + 1) x else 0) =
        3 * (∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then chs hh Lf j x else 0) +
        2 * ∑ x : T.X (j + 1), if nd T (j + 1) j.2 x = P then fb Lf (j + 1) x else 0 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> rfl
    rw [h4, h5, h3]
    omega
  omega

end Node

end Nc.Tow
end
/- Source module Nc.Tow.Ever3. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

section Start


theorem sum_Bt (a c : Fin AA) : ∑ γ, Bt T ch lhat n a c γ = if Valid lhat n then n a c else 0 := by
  classical
  unfold Bt
  split_ifs
  · rw [← card_eq_sum_card_fiberwise (f := fun k => gam T ch a k) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)),
      card_range]
  · simp

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem nR_start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) : nR R ch FL lhat n o (.start a c γ s) ≤
    if a = c then 0 else Bt T ch lhat n a c γ := by
  unfold nR
  split_ifs with hx hac hac
  · exact absurd hac hx.1
  · exact num_start_le hr hb a c γ s hx
  · exact le_rfl
  · exact Nat.zero_le _

open Classical in

abbrev Q4 (T : Tower h b D J r) (m AA : ℕ) := Fin AA × Fin AA × T.X 0 × Fin (2 * m)


def stR (q : Q4 T m AA) : RM T m AA := .start q.1 q.2.1 q.2.2.1 q.2.2.2

variable (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))
include hgR

open Classical in

theorem paths_at (x : T.X 0) :
    (∑ q : Q4 T m AA, ((if R.pn (ch q.1) (ch q.2.1) q.2.2.1 q.2.2.2 = x then nR R ch FL lhat n o (stR q) else 0) +
      if R.pn (ch q.1) (ch q.2.1) q.2.2.1 (q.2.2.2 + 1) = x then nR R ch FL lhat n o (stR q) else 0)) ≤
      fb (ldL R ch FL lhat n o) 0 x := by
  -- one step
  have h1 : ∀ q : Q4 T m AA, ((if R.pn (ch q.1) (ch q.2.1) q.2.2.1 q.2.2.2 = x then nR R ch FL lhat n o (stR q) else 0) +
      if R.pn (ch q.1) (ch q.2.1) q.2.2.1 (q.2.2.2 + 1) = x then nR R ch FL lhat n o (stR q) else 0) ≤
      ∑ e : T.Ed 0, if T.e0 e = x ∨ T.e1 e = x then
        (if okR T R ch (stR q) ∧ (R.path (ch q.1) (ch q.2.1) q.2.2.1)[q.2.2.2.1]? = some e then
          nR R ch FL lhat n o (stR q) else 0) else 0 := by
    rintro ⟨a, c, γ, s⟩
    by_cases hx : okR T R ch (stR (a, c, γ, s))
    · obtain ⟨e, h2, h3, h4⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by have := hx.2; simp only at this; omega)
      have h6 : (T.e0 e = x ∨ T.e1 e = x) ↔ (R.pn (ch a) (ch c) γ s = x ∨ R.pn (ch a) (ch c) γ (s + 1) = x) := by
        have h7 : ∀ y z : T.X 0, (y = x ∨ z = x) ↔ x ∈ s(y, z) := fun y z => by
          rw [Sym2.mem_iff]
          exact or_congr eq_comm eq_comm
        rw [h7, h7, h3]
      by_cases h0 : R.pn (ch a) (ch c) γ s = x
      · have h8 : ¬ R.pn (ch a) (ch c) γ (s + 1) = x := fun hc => h4 (h0.trans hc.symm)
        simp only [if_pos h0, if_neg h8, Nat.add_zero]
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ e))
        rw [if_pos (h6.2 (Or.inl h0)), if_pos ⟨hx, h2⟩]
      · simp only [if_neg h0, Nat.zero_add]
        split_ifs with h8
        · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ e))
          rw [if_pos (h6.2 (Or.inr h8)), if_pos ⟨hx, h2⟩]
        · exact Nat.zero_le _
    · have h5 : nR R ch FL lhat n o (stR (a, c, γ, s)) = 0 := by
        unfold nR
        rw [dif_neg hx]
      rw [h5]
      simp
  refine (Finset.sum_le_sum fun q _ => h1 q).trans ?_
  rw [Finset.sum_comm]
  unfold fb Tower.bet
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs with he
  · rw [← Finset.sum_filter]
    have h2 : ldL R ch FL lhat n o 0 e = load R ch FL lhat n o (.edge 0 e) := by
      unfold ldL lev
      rw [dif_pos (Nat.succ_pos J)]
      rfl
    rw [h2, ← Finset.sum_attach]
    set S := univ.filter fun q : Q4 T m AA => okR T R ch (stR q) ∧
      (R.path (ch q.1) (ch q.2.1) q.2.2.1)[q.2.2.2.1]? = some e with hS
    have h3 : ∀ q : {q // q ∈ S}, nR R ch FL lhat n o (stR q.1) = alv R ch FL lhat n o
        (⟨.inl ⟨stR q.1, (mem_filter.1 q.2).2.1⟩, false⟩ : NM R FL (ch := ch)) := by
      intro q
      unfold nR
      rw [dif_pos (mem_filter.1 q.2).2.1]
      exact (alv_relay hgR ⟨stR q.1, (mem_filter.1 q.2).2.1⟩ false).symm
    rw [Finset.sum_congr rfl fun q _ => h3 q]
    refine sum_alv_le (.edge 0 e) S.attach
      (fun q => (⟨.inl ⟨stR q.1, (mem_filter.1 q.2).2.1⟩, false⟩ : NM R FL (ch := ch))) ?_ ?_
    · rintro ⟨⟨a, c, γ, s⟩, hq⟩ _ ⟨⟨a', c', γ', s'⟩, hq'⟩ _ hee
      have h4 : (Sum.inl ⟨stR (a, c, γ, s), (mem_filter.1 hq).2.1⟩ : Mv T R ch FL) =
          .inl ⟨stR (a', c', γ', s'), (mem_filter.1 hq').2.1⟩ := congrArg Sigma.fst hee
      have h5 := congrArg Subtype.val (Sum.inl_injective h4)
      simp only [stR, RM.start.injEq] at h5
      obtain ⟨e1, e2, e3, e4⟩ := h5
      subst e1 e2 e3 e4
      rfl
    · rintro ⟨⟨a, c, γ, s⟩, hq⟩ _
      have h4 := (mem_filter.1 hq).2.2
      change edgeO T ((R.path (ch a) (ch c) γ)[s.1]?) = _
      simp only at h4
      rw [h4]
      rfl
  · simp

open Classical in

theorem NR0_le (x : T.X 0) : NR0 R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) ≤
    (if ∃ c, ch c = x then 2 * m * lhat else 0) + fb (ldL R ch FL lhat n o) 0 x := by
  have h0 : ∀ a c γ (s : Fin (2 * m)), (∑ q : Fin 3, if tri T R ch (.start a c γ s) q = nd T 0 (Nat.zero_le _) x then
      nR R ch FL lhat n o (.start a c γ s) else 0) =
      ((if R.pn (ch a) (ch c) γ s = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
      if R.pn (ch a) (ch c) γ (s + 1) = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
      if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 := by
    intro a c γ s
    rw [Fin.sum_univ_three]
    change ((if nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ s) = nd T 0 (Nat.zero_le _) x then _ else 0) +
      (if nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ (s + 1)) = nd T 0 (Nat.zero_le _) x then _ else 0)) +
      (if nd T 0 (Nat.zero_le _) (ch c) = nd T 0 (Nat.zero_le _) x then _ else 0) = _
    simp only [nd_inj]
  have h1 : NR0 R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) =
      (∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m),
        ((if R.pn (ch a) (ch c) γ s = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
        if R.pn (ch a) (ch c) γ (s + 1) = x then nR R ch FL lhat n o (.start a c γ s) else 0)) +
      ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 := by
    unfold NR0
    simp only [h0, Finset.sum_add_distrib]
  rw [h1, Nat.add_comm]
  refine add_le_add ?_ ?_
  · -- as the end of paths
    have h2 : ∀ c, (∑ a, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0) ≤
        if ch c = x then 2 * m * lhat else 0 := by
      intro c
      split_ifs with hc
      · have h3 : ∀ a, (∑ γ, ∑ s : Fin (2 * m), nR R ch FL lhat n o (.start a c γ s)) ≤
            2 * m * if a = c then 0 else (if Valid lhat n then n a c else 0) := by
          intro a
          calc (∑ γ, ∑ s : Fin (2 * m), nR R ch FL lhat n o (.start a c γ s)) ≤
              ∑ γ, ∑ _s : Fin (2 * m), (if a = c then 0 else Bt T ch lhat n a c γ) :=
                Finset.sum_le_sum fun γ _ => Finset.sum_le_sum fun s _ => nR_start hr hb a c γ s
            _ = 2 * m * ∑ γ, (if a = c then 0 else Bt T ch lhat n a c γ) := by
                simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
                rw [Finset.mul_sum]
            _ = _ := by
                congr 1
                by_cases hac : a = c
                · simp [hac]
                · simp only [if_neg hac]
                  exact sum_Bt a c
        refine (Finset.sum_le_sum fun a _ => h3 a).trans ?_
        rw [← Finset.mul_sum]
        refine Nat.mul_le_mul_left _ ?_
        by_cases hv : Valid lhat n
        · refine le_trans (Finset.sum_le_sum fun a _ => ?_) (hv c)
          by_cases hac : a = c
          · simp [hac]
          · rw [if_neg hac, if_pos hv, if_neg hac]
            omega
        · simp [hv]
      · simp
    have h3 : (∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0) =
        ∑ c, ∑ a, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 :=
      Finset.sum_comm
    rw [h3]
    refine (Finset.sum_le_sum fun c _ => h2 c).trans ?_
    split_ifs with hx
    · obtain ⟨c0, rfl⟩ := hx
      rw [Finset.sum_eq_single c0]
      · rw [if_pos rfl]
      · intro c _ hc
        rw [if_neg fun he => hc (ch.injective he)]
      · intro hn; exact absurd (mem_univ _) hn
    · refine le_of_eq (Finset.sum_eq_zero fun c _ => if_neg fun he => hx ⟨c, he⟩)
  · -- on the paths
    refine le_trans (le_of_eq ?_) (paths_at hr hb hgR x)
    simp only [Fintype.sum_prod_type]
    rfl

omit hr hb hgR in
open Classical in
theorem NR0_succ {j : ℕ} (hj : j + 1 ≤ J) (x : T.X (j + 1)) : NR0 R ch FL lhat n o (nd T (j + 1) hj x) = 0 := by
  unfold NR0
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ =>
    Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun q _ => if_neg ?_
  fin_cases q <;> exact nd_ne (hj := Nat.zero_le J) (Nat.succ_ne_zero j).symm

omit hr hb hgR in
open Classical in
theorem NR0_none : NR0 R ch FL lhat n o none = 0 := by
  unfold NR0
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ =>
    Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun q _ => if_neg ?_
  fin_cases q <;> exact nd_ne_none (hj := Nat.zero_le J)

end Start

section Laws

variable (R ch FL lhat n o) in
open Classical in

noncomputable def NL (P : Nd T) : ℕ := ∑ l : LMv T FL, ∑ f : T.Fl,
  if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f) = P then num R ch FL lhat n o (.inr l) else 0

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgL : ∀ l : LMv T FL, GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) ∧
    ∀ ν, num R ch FL lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩)
  (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f)
include hr hb hgL hnr


theorem num_law_le (j : Fin J) (i : Fin h) (x : T.X (j + 1)) (d : FL.Di) :
    num R ch FL lhat n o (.inr ⟨j, i, T.vx i x, d⟩) ≤ fb (ldL R ch FL lhat n o) (j + 1) x := by
  classical
  set l : LMv T FL := ⟨j, i, T.vx i x, d⟩ with hl
  obtain ⟨ν, hν⟩ := hnr (T.co i x)
  set ν' : (FL.L d).Cn := (FL.cn d).symm ν with hν'
  have h1 : alv R ch FL lhat n o ⟨.inr l, ν'⟩ = o ⟨.inr l, ν'⟩ := by
    unfold alv
    have h2 : alvN R ch FL o ⟨.inr l, ν'⟩ (num R ch FL lhat n o (.inr l)) =
        if GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) then o ⟨.inr l, ν'⟩ else
          min (o ⟨.inr l, ν'⟩) (num R ch FL lhat n o (.inr l)) := rfl
    rw [h2, if_pos (hgL l).1]
  set p := (T.nr j.2 i).symm (T.vx i x, ν) with hp
  have hp2 : T.nr j.2 i p = (T.vx i x, ν) := by rw [hp, Equiv.apply_symm_apply]
  have v0 := T.nr_vx0 j.2 i p
  have v1 := T.nr_vx1 j.2 i p
  have v2 := T.nr_co j.2 i p
  rw [hp2] at v0 v1 v2
  have hend : T.e0 p.1 = x ∨ T.e1 p.1 = x := by
    have h3 : T.co i x ∈ s(T.co i (T.e0 p.1), T.co i (T.e1 p.1)) := by
      rw [v2, Sym2.mem_iff]
      rcases hν with hν | hν
      · exact Or.inl hν.symm
      · exact Or.inr hν.symm
    rw [Sym2.mem_iff] at h3
    rcases h3 with h3 | h3
    · exact Or.inl ((T.vx_co j.2 i).1 (Prod.ext v0 h3.symm))
    · exact Or.inr ((T.vx_co j.2 i).1 (Prod.ext v1 h3.symm))
  have htg : tgM R ch FL (⟨.inr l, ν'⟩ : NM R FL (ch := ch)).1 ν' = .edge j.succ p.1 := by
    change Tg.edge j.succ ((T.nr j.2 i).symm (T.vx i x, FL.cn d ν')).1 = _
    rw [hν', Equiv.apply_symm_apply]
  have h4 := sum_alv_le (lhat := lhat) (n := n) (o := o) (.edge j.succ p.1) ({()} : Finset Unit)
    (fun _ => (⟨.inr l, ν'⟩ : NM R FL (ch := ch))) (fun _ _ _ _ _ => rfl) (fun _ _ => htg)
  rw [Finset.sum_singleton, h1] at h4
  refine ((hgL l).2 ν').trans (h4.trans ?_)
  rw [lev_succ]
  unfold fb Tower.bet
  refine le_trans ?_ (Finset.single_le_sum (f := fun e : T.Ed (j + 1) => if T.e0 e = x ∨ T.e1 e = x then
    ldL R ch FL lhat n o (j + 1) e else 0) (fun _ _ => Nat.zero_le _) (mem_univ p.1))
  rw [if_pos hend]

include hh

open Classical in

theorem NL_succ {k : ℕ} (hk : k + 1 ≤ J) (x : T.X (k + 1)) : NL R ch FL lhat n o (nd T (k + 1) hk x) ≤
    Fintype.card FL.Di * fb (ldL R ch FL lhat n o) (k + 1) x := by
  have h1 : NL R ch FL lhat n o (nd T (k + 1) hk x) = ∑ j : Fin J, ∑ y : T.X (j + 1),
      if nd T (j + 1) j.2 y = nd T (k + 1) hk x then
        ∑ i, ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩) else 0 := by
    unfold NL
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_sigma]
    have h2 : ∀ i, (∑ p : T.V (j + 1) i × FL.Di, ∑ f : T.Fl,
        if nd T (j + 1) j.2 (atv j.2 i p.1 f) = nd T (k + 1) hk x then
          num R ch FL lhat n o (.inr ⟨j, i, p.1, p.2⟩) else 0) =
        ∑ y : T.X (j + 1), if nd T (j + 1) j.2 y = nd T (k + 1) hk x then
          ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩) else 0 := by
      intro i
      rw [← Equiv.sum_comp (Equiv.ofBijective _ (T.vx_co j.2 i)).symm, Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      have h3 : (Equiv.ofBijective _ (T.vx_co j.2 i)).symm (ω, f) = atv j.2 i ω f := rfl
      rw [h3, atv_vx]
      split_ifs
      · rfl
      · simp
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rfl
    · simp
  rw [h1, sum_level_succ (fun j y => ∑ i, ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩)) k hk x]
  set j : Fin J := ⟨k, hk⟩ with hj
  rw [Finset.sum_eq_single (imin hh (ldL R ch FL lhat n o) k)]
  · calc _ ≤ ∑ _d : FL.Di, fb (ldL R ch FL lhat n o) (k + 1) x :=
          Finset.sum_le_sum fun d _ => num_law_le hr hb hgL hnr j _ x d
      _ = _ := by rw [Finset.sum_const, card_univ, smul_eq_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun d _ => ?_
    refine num_inr_zero hr hb (Or.inl fun hm => hi ?_)
    exact (isMin_iff hh _ j.castSucc i).1 hm
  · intro hn; exact absurd (mem_univ _) hn

omit hr hb hgL hnr hh in
open Classical in
theorem NL_zero (x : T.X 0) : NL R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) = 0 := by
  unfold NL
  exact Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun f _ => if_neg (nd_ne (Nat.succ_ne_zero _))

omit hr hb hgL hnr hh in
open Classical in
theorem NL_none : NL R ch FL lhat n o none = 0 := by
  unfold NL
  exact Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun f _ => if_neg nd_ne_none

end Laws

section Final

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))
include hh hr hb hgR

open Classical in
theorem NR_zero (x : T.X 0) : NR R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) ≤
    (if ∃ c, ch c = x then 2 * m * lhat else 0) + 7 * fb (ldL R ch FL lhat n o) 0 x := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 := NR0_le hr hb hgR x
  have h2 := sum_level (fun j y => 5 * fb (ldL R ch FL lhat n o) j y) 0 (Nat.zero_le J) x
  have h3 := sum_level_zero (fun j y => 3 * chs hh (ldL R ch FL lhat n o) j y +
    2 * fb (ldL R ch FL lhat n o) (j + 1) y) x
  rw [h2, h3, if_neg nd_ne_none.symm]
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = nd T 0 (Nat.zero_le _) x then fb (ldL R ch FL lhat n o) J y else 0) ≤
      fb (ldL R ch FL lhat n o) 0 x := by
    by_cases hJ : J = 0
    · subst hJ
      simp only [nd_inj]
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro y _
        rw [if_neg (nd_ne hJ)]
  have h5 : (if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) 0 x else 0) ≤ 5 * fb (ldL R ch FL lhat n o) 0 x := by
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have h6 : (if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) (⟨0, hlt⟩ : Fin J) x else 0) =
      if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) 0 x else 0 := rfl
  omega

open Classical in
theorem NR_succ {k : ℕ} (hk : k + 1 ≤ J) (x : T.X (k + 1)) : NR R ch FL lhat n o (nd T (k + 1) hk x) ≤
    8 * fb (ldL R ch FL lhat n o) (k + 1) x + 3 * chs hh (ldL R ch FL lhat n o) k x := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 : NR0 R ch FL lhat n o (nd T (k + 1) hk x) = 0 := NR0_succ hk x
  have h2 := sum_level (fun j y => 5 * fb (ldL R ch FL lhat n o) j y) (k + 1) hk x
  have h3 := sum_level_succ (fun j y => 3 * chs hh (ldL R ch FL lhat n o) j y +
    2 * fb (ldL R ch FL lhat n o) (j + 1) y) k hk x
  rw [h1, h2, h3, if_neg nd_ne_none.symm]
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = nd T (k + 1) hk x then fb (ldL R ch FL lhat n o) J y else 0) ≤
      fb (ldL R ch FL lhat n o) (k + 1) x := by
    by_cases hJ : J = k + 1
    · subst hJ
      simp only [nd_inj]
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro y _
        rw [if_neg (nd_ne hJ)]
  have h5 : (if hlt : k + 1 < J then 5 * fb (ldL R ch FL lhat n o) (⟨k + 1, hlt⟩ : Fin J) x else 0) ≤
      5 * fb (ldL R ch FL lhat n o) (k + 1) x := by
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have h6 : 3 * chs hh (ldL R ch FL lhat n o) (⟨k, hk⟩ : Fin J) x + 2 * fb (ldL R ch FL lhat n o) ((⟨k, hk⟩ : Fin J) + 1) x =
      3 * chs hh (ldL R ch FL lhat n o) k x + 2 * fb (ldL R ch FL lhat n o) (k + 1) x := rfl
  omega

open Classical in
theorem NR_none : NR R ch FL lhat n o none ≤ ∑ e : T.Ed J, ldL R ch FL lhat n o J e := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 : NR0 R ch FL lhat n o none = 0 := NR0_none
  have h2 : (∑ j : Fin J, ∑ y : T.X j, if nd T j j.2.le y = none then 5 * fb (ldL R ch FL lhat n o) j y else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  have h3 : (∑ j : Fin J, ∑ y : T.X (j + 1), if nd T (j + 1) j.2 y = none then
      3 * chs hh (ldL R ch FL lhat n o) j y + 2 * fb (ldL R ch FL lhat n o) (j + 1) y else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = none then fb (ldL R ch FL lhat n o) J y else 0) = 0 :=
    Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  rw [h1, h2, h3, h4, if_pos rfl]
  omega

end Final

end Nc.Tow
end
/- Source module Nc.G.RouteFacts. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ}

section Plan

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}

theorem mem_newUnits_new {x : Fin E} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

theorem init_not_mem_newUnitsR {x : Fin E} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∉ newUnits M x o := by
  simp [newUnits]

theorem init_mem_seen0R {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ seen0 n ↔ k.1 < (n a b).1 := by
  simp [seen0]

theorem new_not_mem_seen0R {ν : M.N} {k : Fin U1} : (Uid.new ν k : Uid A U0 M.N U1) ∉ seen0 n := by
  simp [seen0]

theorem mem_seenAt_init {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ Plan.seenAt n o x ↔ k.1 < (n a b).1 := by
  unfold Plan.seenAt
  rw [Finset.mem_union, init_mem_seen0R]
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨x', -, h⟩ := Finset.mem_biUnion.1 h
      exact absurd h init_not_mem_newUnitsR
  · exact Or.inl

theorem mem_seenAt_new {x : ℕ} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ Plan.seenAt n o x ↔ ν.1.1 < x ∧ k ≤ o ν := by
  unfold Plan.seenAt
  rw [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact absurd h new_not_mem_seen0R
    · obtain ⟨x', hx', h⟩ := Finset.mem_biUnion.1 h
      obtain ⟨rfl, h2⟩ := mem_newUnits_new.1 h
      exact ⟨(Finset.mem_filter.1 hx').2, h2⟩
  · rintro ⟨h1, h2⟩
    refine Or.inr (Finset.mem_biUnion.2 ⟨ν.1, ?_, mem_newUnits_new.2 ⟨rfl, h2⟩⟩)
    simpa using h1


theorem mem_seen_iff {id : Uid A U0 M.N U1} : id ∈ Plan.seenAt n o E ↔ unum id < ucnt n o id := by
  cases id with
  | init a b k => rw [mem_seenAt_init]; rfl
  | new ν k =>
    rw [mem_seenAt_new]
    constructor
    · rintro ⟨-, h⟩
      exact Nat.lt_succ_of_le h
    · intro h
      exact ⟨ν.1.2, Nat.le_of_lt_succ h⟩

end Plan

end Nc.G
end
/- Source module Nc.Tow.Ever4. -/
section
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.G

open Finset

section Held

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ}


theorem sum_uid {N : Type} [Fintype N] [DecidableEq N] (f : Uid A U0 N U1 → ℕ) :
    ∑ u, f u = (∑ a, ∑ c, ∑ k, f (.init a c k)) + ∑ ν, ∑ k, f (.new ν k) := by
  let e : Uid A U0 N U1 ≃ (Fin A × Fin A × Fin U0) ⊕ (N × Fin U1) :=
    { toFun := fun u => match u with
        | .init a c k => .inl (a, c, k)
        | .new ν k => .inr (ν, k)
      invFun := fun s => match s with
        | .inl p => .init p.1 p.2.1 p.2.2
        | .inr p => .new p.1 p.2
      left_inv := fun u => by cases u <;> rfl
      right_inv := fun s => by rcases s with ⟨a, c, k⟩ | ⟨ν, k⟩ <;> rfl }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl


def initN (n : Fin A → Fin A → Fin (U0 + 1)) (p : Fin (A + A')) : ℕ :=
  ∑ a, ∑ c, ((if Fin.castAdd A' a = p then (n a c).1 else 0) + if Fin.castAdd A' c = p then (n a c).1 else 0)

theorem card_fin_le (N c : ℕ) : ((univ : Finset (Fin N)).filter fun k => k.1 < c).card ≤ c := by
  calc _ ≤ (range c).card := by
        refine card_le_card_of_injOn (fun k => k.1) ?_ ?_
        · intro k hk
          exact mem_coe.2 (mem_range.2 (mem_filter.1 (mem_coe.1 hk)).2)
        · intro k _ k' _ hkk
          exact Fin.ext hkk
    _ = c := card_range c

theorem sum_fin_le (N c : ℕ) (p : Prop) [Decidable p] :
    (∑ k : Fin N, if p ∧ k.1 < c then 1 else 0) ≤ if p then c else 0 := by
  by_cases hp : p
  · simp only [hp, true_and, if_true]
    rw [← card_filter]
    exact card_fin_le N c
  · simp [hp]

open Classical in

theorem held_le_chan (M : Sys F (A + A') E) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (p : Fin (A + A')) :
    ((Plan.seenAt n o E : Finset (Uid A U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card ≤
      initN n p + ∑ ν : M.N, ∑ d : Bool, if M.np ν d = p then (o ν).1 + 1 else 0 := by
  have h1 : ((Plan.seenAt n o E : Finset (Uid A U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card ≤
      ∑ u : Uid A U0 M.N U1, ∑ d : Bool, if cparty M.np u d = p ∧ unum u < ucnt n o u then 1 else 0 := by
    rw [card_filter]
    refine (Finset.sum_le_sum fun u hu => ?_).trans (Finset.sum_le_sum_of_subset (subset_univ _))
    have h4 := mem_seen_iff.1 hu
    split_ifs with h3
    · rw [Fintype.sum_bool]
      rcases h3 with h3 | h3
      · have h5 : cparty M.np u false = p := h3.symm
        rw [if_pos (⟨h5, h4⟩ : cparty M.np u false = p ∧ unum u < ucnt n o u)]
        exact Nat.le_add_left _ _
      · have h5 : cparty M.np u true = p := h3.symm
        rw [if_pos (⟨h5, h4⟩ : cparty M.np u true = p ∧ unum u < ucnt n o u)]
        exact Nat.le_add_right _ _
    · exact Nat.zero_le _
  refine h1.trans ?_
  rw [sum_uid]
  refine add_le_add ?_ ?_
  · unfold initN
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
    rw [Finset.sum_comm, Fintype.sum_bool, Nat.add_comm]
    exact add_le_add (sum_fin_le U0 (n a c).1 (Fin.castAdd A' a = p)) (sum_fin_le U0 (n a c).1 (Fin.castAdd A' c = p))
  · refine Finset.sum_le_sum fun ν _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun d _ => sum_fin_le U1 ((o ν).1 + 1) (M.np ν d = p)

end Held

end Nc.G

namespace Nc.Tow

open Finset Nc.G


theorem sum_sub_le {κ : Type*} [Fintype κ] (p : κ → Prop) [Fintype {x // p x}] (f : κ → ℕ) :
    ∑ x : {x // p x}, f x.1 ≤ ∑ x, f x := by
  classical
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') (lhat : ℕ)
  (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1)

open Classical in

noncomputable def heldN (p : Fin (AA + A')) : ℕ :=
  ((Plan.seenAt n o (Fintype.card (Mv T R ch FL)) : Finset (Un R FL Pl U0 U1)).filter
    (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card


noncomputable def chanN (p : Fin (AA + A')) : ℕ := ∑ ν : (sys R FL Pl).N, ∑ d : Bool,
  if (sys R FL Pl).np ν d = p then 1 else 0

variable {R FL Pl lhat n o}

section

variable (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool),
    oo R FL Pl o ⟨.inl x, ν⟩ = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x))
  (hgL : ∀ l : LMv T FL, GoodL R ch FL (oo R FL Pl o) l (num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l)) ∧
    ∀ ν, num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ oo R FL Pl o ⟨.inr l, ν⟩)

include hr hb hgL in

theorem law_le (l : LMv T FL) (ν : (FL.L l.2.2.2).Cn) :
    oo R FL Pl o ⟨.inr l, ν⟩ ≤ FL.G₁ * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) := by
  have h1 := (hgL l).1
  unfold GoodL at h1
  set t := num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) with ht
  have h2 : (oo R FL Pl o ⟨.inr l, ν⟩) ^ 2 ≤ ∑ ν : (FL.L l.2.2.2).Cn, (oo R FL Pl o ⟨Sum.inr l, ν⟩) ^ 2 :=
    Finset.single_le_sum (f := fun ν : (FL.L l.2.2.2).Cn => (oo R FL Pl o ⟨Sum.inr l, ν⟩) ^ 2)
      (fun _ _ => Nat.zero_le _) (mem_univ ν)
  have h3 : (oo R FL Pl o ⟨.inr l, ν⟩) ^ 2 ≤ FL.G₁ * t ^ 2 := by
    refine h2.trans (le_trans ?_ h1)
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hr hb)
  have h4 : (oo R FL Pl o ⟨.inr l, ν⟩) ^ 2 ≤ (FL.G₁ * t) ^ 2 := by
    refine h3.trans ?_
    rw [mul_pow]
    refine Nat.mul_le_mul_right _ ?_
    rw [pow_two]
    exact Nat.le_mul_self _
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

include hr hb hgL in
open Classical in

theorem law_node (l : LMv T FL) (P : Nd T) : (∑ ν : (FL.L l.2.2.2).Cn, ∑ d : Bool,
    if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d))) = P then
      oo R FL Pl o ⟨.inr l, ν⟩ else 0) ≤ 2 * Fintype.card T.Nr * FL.G₁ *
    ∑ f : T.Fl, if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f) = P then
      num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) else 0 := by
  set t := num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) with ht
  set S := ∑ f : T.Fl, if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f) = P then t else 0 with hS
  have h5 : ∀ (ν : (FL.L l.2.2.2).Cn) (d : Bool),
      (if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d))) = P then
        oo R FL Pl o ⟨.inr l, ν⟩ else 0) ≤ FL.G₁ * S := by
    intro ν d
    split_ifs with hP
    · refine (law_le hr hb hgL l ν).trans (Nat.mul_le_mul_left _ ?_)
      refine le_trans ?_ (Finset.single_le_sum (f := fun f : T.Fl =>
        if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f) = P then t else 0) (fun _ _ => Nat.zero_le _)
        (mem_univ (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d))))
      simp only [hP, if_true]
      exact le_rfl
    · exact Nat.zero_le _
  calc _ ≤ ∑ _ν : (FL.L l.2.2.2).Cn, ∑ _d : Bool, FL.G₁ * S :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun d _ => h5 ν d
    _ = Fintype.card (FL.L l.2.2.2).Cn * (2 * (FL.G₁ * S)) := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, card_univ, card_univ, Fintype.card_bool]
    _ = _ := by
        rw [Fintype.card_congr (FL.cn l.2.2.2)]
        ring

include hr hb hgR hgL

open Classical in

theorem held_le (P : Nd T) : heldN R FL Pl n o (Pl.pt P) ≤ initN (A' := A') n (Pl.pt P) + chanN R FL Pl (Pl.pt P) +
    2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P +
    2 * Fintype.card T.Nr * FL.G₁ * NL R ch FL lhat (nn n) (oo R FL Pl o) P := by
  refine (held_le_chan (sys R FL Pl) n o (Pl.pt P)).trans ?_
  have h1 : (∑ ν : (sys R FL Pl).N, ∑ d : Bool, if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 + 1 else 0) =
      chanN R FL Pl (Pl.pt P) + ∑ ν : (sys R FL Pl).N, ∑ d : Bool,
        if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 else 0 := by
    unfold chanN
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> omega
  have h2 : (∑ ν : (sys R FL Pl).N, ∑ d : Bool, if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 else 0) =
      ∑ ν : NM R FL (ch := ch), ∑ d : Bool,
        if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo R FL Pl o ν else 0 := by
    rw [← Equiv.sum_comp (eN R FL Pl)]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun d _ => ?_
    have h3 : oo R FL Pl o (eN R FL Pl ν) = (o ν).1 := by
      unfold oo
      rw [Equiv.symm_apply_apply]
    rw [h3]
    refine if_congr ?_ rfl rfl
    rw [np_eq]
    exact Pl.pt.injective.eq_iff
  rw [h1, h2]
  have h4 : (∑ ν : NM R FL (ch := ch), ∑ d : Bool,
      if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo R FL Pl o ν else 0) ≤
      2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P +
      2 * Fintype.card T.Nr * FL.G₁ * NL R ch FL lhat (nn n) (oo R FL Pl o) P := by
    change (∑ ν : (Σ mv : Mv T R ch FL, (kindM R ch FL mv).Cn), ∑ d : Bool,
      if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo R FL Pl o ν else 0) ≤ _
    rw [Fintype.sum_sigma, Fintype.sum_sum_type]
    refine add_le_add ?_ ?_
    · -- relays
      have h5 : ∀ x : {x : RM T m AA // okR T R ch x}, (∑ ν : Bool, ∑ d : Bool,
          if tri T R ch x.1 (if d then (if ν then 2 else 1) else (if ν then 1 else 0)) = P then
            oo R FL Pl o ⟨.inl x, ν⟩ else 0) ≤
          2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 else 0 := by
        intro x
        have h6 : nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x) := by
          unfold nR
          rw [dif_pos x.2]
        rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fin.sum_univ_three, h6]
        simp only [hgR, if_true, Bool.false_eq_true, if_false]
        split_ifs <;> omega
      have h7 : (∑ x : {x : RM T m AA // okR T R ch x}, 2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then
          nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 else 0) ≤ 2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P := by
        rw [← Finset.mul_sum]
        refine Nat.mul_le_mul_left _ ?_
        exact sum_sub_le (fun x => okR T R ch x) fun x => ∑ q : Fin 3, if tri T R ch x q = P then
          nR R ch FL lhat (nn n) (oo R FL Pl o) x else 0
      refine le_trans (Finset.sum_le_sum fun x _ => ?_) h7
      refine le_trans (le_of_eq ?_) (h5 x)
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun d _ => ?_
      cases ν <;> cases d <;> rfl
    · -- laws
      unfold NL
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => law_node hr hb hgL l P
  omega

end

end Nc.Tow
end
/- Source module Nc.Tow.Ever6. -/
section
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G

section Tree

variable {h b D J r AA : ℕ} {T : Tower h b D J r} {hh : 0 < h} {Lf : ∀ j, T.Ed j → ℕ}


noncomputable def chF (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) : ∀ j, T.X j → ℕ
  | 0, _ => 0
  | j + 1, c => chs hh Lf j c

end Tree

section Ever

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
  {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool),
    oo R FL Pl o ⟨.inl x, ν⟩ = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x))
  (hgL : ∀ l : LMv T FL, GoodL R ch FL (oo R FL Pl o) l (num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l)) ∧
    ∀ ν, num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ oo R FL Pl o ⟨.inr l, ν⟩)
  (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f)

variable (R ch FL Pl lhat n o) in

noncomputable abbrev LfO : ∀ j, T.Ed j → ℕ := ldL R ch FL lhat (nn n) (oo R FL Pl o)

variable (ch) in
open Classical in

noncomputable def isB (P : Nd T) : ℕ := if ∃ a, P = nd T 0 (Nat.zero_le _) (ch a) then 1 else 0

include hh hr hb hgR in
open Classical in
theorem NR_onN (P : Nd T) : NR R ch FL lhat (nn n) (oo R FL Pl o) P ≤ isB ch P * (2 * m * lhat) +
    onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
      (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  rcases nd_cases P with rfl | ⟨j, hj, c, rfl⟩
  · exact (NR_none hh hr hb hgR).trans (Nat.le_add_left _ _)
  · rw [onN_nd]
    cases j with
    | zero =>
      refine (NR_zero hh hr hb hgR c).trans (add_le_add ?_ ?_)
      · unfold isB
        by_cases hc : ∃ a, ch a = c
        · obtain ⟨a, rfl⟩ := hc
          rw [if_pos ⟨a, rfl⟩, if_pos ⟨a, rfl⟩, Nat.one_mul]
        · rw [if_neg hc]
          exact Nat.zero_le _
      · change 7 * fb (LfO R ch FL Pl lhat n o) 0 c ≤ 8 * fb (LfO R ch FL Pl lhat n o) 0 c +
          3 * chF hh (LfO R ch FL Pl lhat n o) 0 c
        omega
    | succ j =>
      refine (NR_succ hh hr hb hgR hj c).trans (le_trans (le_of_eq ?_) (Nat.le_add_left _ _))
      rfl

include hh hr hb hgL hnr in
open Classical in
theorem NL_onN (P : Nd T) : NL R ch FL lhat (nn n) (oo R FL Pl o) P ≤ Fintype.card FL.Di *
    onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
      (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  rcases nd_cases P with rfl | ⟨j, hj, c, rfl⟩
  · rw [NL_none]
    exact Nat.zero_le _
  · rw [onN_nd]
    cases j with
    | zero =>
      rw [NL_zero]
      exact Nat.zero_le _
    | succ j =>
      refine (NL_succ hh hr hb hgL hnr hj c).trans (Nat.mul_le_mul_left _ ?_)
      change fb (LfO R ch FL Pl lhat n o) (j + 1) c ≤ 8 * fb (LfO R ch FL Pl lhat n o) (j + 1) c +
        3 * chF hh (LfO R ch FL Pl lhat n o) (j + 1) c
      omega

open Classical in
theorem initN_le {ℓf : ℕ} (P : Nd T) (hP : ∀ a, P = nd T 0 (Nat.zero_le _) (ch a) →
    ∑ c, ((n a c).1 + (n c a).1) ≤ ℓf) : initN (A' := A') n (Pl.pt P) ≤ isB ch P * ℓf := by
  unfold isB
  split_ifs with hB
  · obtain ⟨a, rfl⟩ := hB
    rw [Nat.one_mul]
    refine le_trans (le_of_eq ?_) (hP a rfl)
    rw [Pl.pt_base]
    unfold initN
    have h1 : ∀ a' c : Fin AA, (if Fin.castAdd A' a' = Fin.castAdd A' a then (n a' c).1 else 0) =
        if a' = a then (n a c).1 else 0 := by
      intro a' c
      by_cases ha : a' = a
      · subst ha; simp
      · rw [if_neg fun he => ha (Fin.castAdd_injective _ _ he), if_neg ha]
    have h2 : ∀ a' c : Fin AA, (if Fin.castAdd A' c = Fin.castAdd A' a then (n a' c).1 else 0) =
        if c = a then (n a' a).1 else 0 := by
      intro a' c
      by_cases ha : c = a
      · subst ha; simp
      · rw [if_neg fun he => ha (Fin.castAdd_injective _ _ he), if_neg ha]
    simp only [h1, h2, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    unfold initN
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    have hne : ∀ a, Fin.castAdd A' a ≠ Pl.pt P := by
      intro a ha
      rw [← Pl.pt_base] at ha
      exact hB ⟨a, (Pl.pt.injective ha).symm⟩
    rw [if_neg (hne a), if_neg (hne c), Nat.add_zero]

end Ever

end Nc.Tow
end
/- Source module Nc.Tow.Ever7. -/
section
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
  {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}


noncomputable def eR (R : Routes T m Uu) {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') :
    (sys R FL Pl).R ≃ Σ mv : Mv T R ch FL, (kindM R ch FL mv).Ro :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Ro) (eE R FL)

variable (R ch FL Pl lhat n o) in

noncomputable def padR (r' : (sys R FL Pl).R) : ℕ :=
  (1 + Fintype.card (((sys R FL Pl).kind r'.1).SlAt r'.2)) * num R ch FL lhat (nn n) (oo R FL Pl o) (eE R FL r'.1)

open Classical in

theorem pads_node {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm) (P : Nd T) :
    (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) ≤
      2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P + (1 + Sm) * NL R ch FL lhat (nn n) (oo R FL Pl o) P := by
  have h1 : (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) =
      ∑ y : (Σ mv : Mv T R ch FL, (kindM R ch FL mv).Ro), if partM R ch FL y.1 y.2 = P then
        (1 + Fintype.card ((kindM R ch FL y.1).SlAt y.2)) * num R ch FL lhat (nn n) (oo R FL Pl o) y.1 else 0 := by
    rw [← Equiv.sum_comp (eR R FL Pl)]
    refine Finset.sum_congr rfl fun r' _ => if_congr ?_ rfl rfl
    exact Pl.pt.injective.eq_iff
  rw [h1, Fintype.sum_sigma, Fintype.sum_sum_type]
  refine add_le_add ?_ ?_
  · have h7 : (∑ x : {x : RM T m AA // okR T R ch x}, 2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then
        nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 else 0) ≤ 2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P := by
      rw [← Finset.mul_sum]
      refine Nat.mul_le_mul_left _ ?_
      exact sum_sub_le (fun x => okR T R ch x) fun x => ∑ q : Fin 3, if tri T R ch x q = P then
        nR R ch FL lhat (nn n) (oo R FL Pl o) x else 0
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) h7
    rw [Finset.mul_sum]
    have h6 : nR R ch FL lhat (nn n) (oo R FL Pl o) x.1 = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x) := by
      unfold nR
      rw [dif_pos x.2]
    have h2 : ∀ (q : (relay F).Ro) (inst : Fintype ((relay F).SlAt q)), @Fintype.card _ inst ≤ 1 := fun q inst => by
      refine (Fintype.card_le_of_injective (Subtype.val : (relay F).SlAt q → Unit) Subtype.val_injective).trans ?_
      exact le_of_eq Fintype.card_unit
    rw [h6]
    refine Finset.sum_le_sum (ι := (relay F).Ro) fun q _ => ?_
    by_cases hq : partM R ch FL (.inl x) q = P
    · rw [if_pos hq, if_pos (show tri T R ch x.1 q = P from hq)]
      refine Nat.mul_le_mul_right _ ?_
      exact Nat.add_le_add_left (h2 q _) 1
    · rw [if_neg hq]
      exact Nat.zero_le _
  · unfold NL
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum, ← Equiv.sum_comp (FL.ro l.2.2.2)]
    refine Finset.sum_le_sum (ι := (FL.L l.2.2.2).Ro) fun p _ => ?_
    change (if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p)) = P then _ else 0) ≤ _
    have h2 : ∀ (inst : Fintype ((FL.L l.2.2.2).SlAt p)), @Fintype.card _ inst ≤ Sm := fun inst =>
      (Fintype.card_le_of_injective (Subtype.val : (FL.L l.2.2.2).SlAt p → (FL.L l.2.2.2).Sl)
        Subtype.val_injective).trans (hSm _)
    split_ifs
    · exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (h2 _) 1)
    · exact le_rfl

open Classical in


theorem held_node_le (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
    (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool),
      oo R FL Pl o ⟨.inl x, ν⟩ = num R ch FL lhat (nn n) (oo R FL Pl o) (.inl x))
    (hgL : ∀ l : LMv T FL, GoodL R ch FL (oo R FL Pl o) l (num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l)) ∧
      ∀ ν, num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ oo R FL Pl o ⟨.inr l, ν⟩)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm) {ℓf : ℕ}
    (P : Nd T) (hini : ∀ a, P = nd T 0 (Nat.zero_le _) (ch a) → ∑ c, ((n a c).1 + (n c a).1) ≤ ℓf) :
    heldN R FL Pl n o (Pl.pt P) +
      (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) ≤
      isB ch P * (ℓf + 8 * m * lhat) + chanN R FL Pl (Pl.pt P) +
        (4 + (2 * Fintype.card T.Nr * FL.G₁ + 1 + Sm) * Fintype.card FL.Di) *
          onN (fun j x => 8 * fb (LfO R ch FL Pl lhat n o) j x + 3 * chF hh (LfO R ch FL Pl lhat n o) j x)
            (∑ e : T.Ed J, LfO R ch FL Pl lhat n o J e) P := by
  set Lf := LfO R ch FL Pl lhat n o with hLf
  set f : ∀ j, T.X j → ℕ := fun j x => 8 * fb Lf j x + 3 * chF hh Lf j x with hf
  set f0 := ∑ e : T.Ed J, Lf J e with hf0
  set c1 := 2 * Fintype.card T.Nr * FL.G₁ with hc1
  have a1 : heldN R FL Pl n o (Pl.pt P) ≤ initN (A' := A') n (Pl.pt P) + chanN R FL Pl (Pl.pt P) +
      2 * NR R ch FL lhat (nn n) (oo R FL Pl o) P + c1 * NL R ch FL lhat (nn n) (oo R FL Pl o) P :=
    held_le hr hb hgR hgL P
  have a2 := pads_node (R := R) (Pl := Pl) (lhat := lhat) (n := n) (o := o) hSm P
  have a3 : NR R ch FL lhat (nn n) (oo R FL Pl o) P ≤ isB ch P * (2 * m * lhat) + onN f f0 P :=
    NR_onN hh hr hb hgR P
  have a4 : NL R ch FL lhat (nn n) (oo R FL Pl o) P ≤ Fintype.card FL.Di * onN f f0 P :=
    NL_onN hh hr hb hgL hnr P
  have a5 := initN_le (Pl := Pl) (n := n) (ℓf := ℓf) P hini
  generalize NR R ch FL lhat (nn n) (oo R FL Pl o) P = NRv at a1 a2 a3
  generalize NL R ch FL lhat (nn n) (oo R FL Pl o) P = NLv at a1 a2 a4
  have a6 : c1 * NLv ≤ c1 * (Fintype.card FL.Di * onN f f0 P) := Nat.mul_le_mul_left _ a4
  have a7 : (1 + Sm) * NLv ≤ (1 + Sm) * (Fintype.card FL.Di * onN f f0 P) := Nat.mul_le_mul_left _ a4
  have e1 : (4 + (c1 + 1 + Sm) * Fintype.card FL.Di) * onN f f0 P = 4 * onN f f0 P +
      c1 * (Fintype.card FL.Di * onN f f0 P) + (1 + Sm) * (Fintype.card FL.Di * onN f f0 P) := by ring
  have e2 : isB ch P * (ℓf + 8 * m * lhat) = isB ch P * ℓf + 4 * (isB ch P * (2 * m * lhat)) := by ring
  rw [e1, e2]
  generalize (∑ r' : (sys R FL Pl).R, if (sys R FL Pl).rp r' = Pl.pt P then padR R ch FL Pl lhat n o r' else 0) = pv
    at a2 ⊢
  generalize heldN R FL Pl n o (Pl.pt P) = hv at a1 ⊢
  generalize initN (A' := A') n (Pl.pt P) = iv at a1 a5
  generalize chanN R FL Pl (Pl.pt P) = cv at a1 ⊢
  generalize onN f f0 P = ov at a3 a6 a7 ⊢
  generalize c1 * (Fintype.card FL.Di * ov) = x1 at a6 ⊢
  generalize (1 + Sm) * (Fintype.card FL.Di * ov) = x2 at a7 ⊢
  generalize c1 * NLv = x3 at a1 a6
  generalize (1 + Sm) * NLv = x4 at a2 a7
  generalize isB ch P * ℓf = x5 at a5 ⊢
  generalize isB ch P * (2 * m * lhat) = x6 at a3 ⊢
  omega

end Nc.Tow
end
/- Source module Nc.Tow.PlaceE. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset

variable {h b D J r AA : ℕ}


def baseNd (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) : Fin AA ↪ Nd T where
  toFun a := nd T 0 (Nat.zero_le _) (ch a)
  inj' a c hac := ch.injective (nd_inj.1 hac)


def extra (T : Tower h b D J r) (AA : ℕ) : ℕ := Fintype.card (Nd T) - AA


theorem exists_place (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) : Nonempty (Place T ch (extra T AA)) := by
  classical
  have hle : AA ≤ Fintype.card (Nd T) := by
    have := Fintype.card_le_of_embedding (baseNd T ch)
    rwa [Fintype.card_fin] at this
  -- the base nodes and the others
  let S : Finset (Nd T) := univ.map (baseNd T ch)
  have hS : S.card = AA := by rw [card_map, card_univ, Fintype.card_fin]
  have hc : Fintype.card {ν : Nd T // ν ∉ S} = extra T AA := by
    rw [Fintype.card_subtype_compl (fun ν => ν ∈ S), Fintype.card_coe, hS]
    rfl
  let e1 : {ν : Nd T // ν ∈ S} ≃ Fin AA :=
    (Equiv.ofBijective (fun a : Fin AA => (⟨baseNd T ch a, mem_map_of_mem _ (mem_univ a)⟩ : {ν : Nd T // ν ∈ S})) (by
      constructor
      · intro a c hac
        exact (baseNd T ch).injective (congrArg Subtype.val hac)
      · rintro ⟨ν, hν⟩
        obtain ⟨a, -, ha⟩ := mem_map.1 hν
        exact ⟨a, Subtype.ext ha⟩)).symm
  let e2 : {ν : Nd T // ν ∉ S} ≃ Fin (extra T AA) := Fintype.equivFinOfCardEq hc
  let e : Nd T ≃ Fin (AA + extra T AA) :=
    (Equiv.sumCompl (fun ν => ν ∈ S)).symm.trans ((Equiv.sumCongr e1 e2).trans finSumFinEquiv)
  refine ⟨⟨e, fun a => ?_⟩⟩
  have hmem : baseNd T ch a ∈ S := mem_map_of_mem _ (mem_univ a)
  have h1 : (Equiv.sumCompl (fun ν => ν ∈ S)).symm (baseNd T ch a) = Sum.inl ⟨baseNd T ch a, hmem⟩ :=
    Equiv.sumCompl_symm_apply_of_pos hmem
  have h2 : e1 ⟨baseNd T ch a, hmem⟩ = a := by
    rw [Equiv.symm_apply_eq]
    rfl
  change finSumFinEquiv ((Equiv.sumCongr e1 e2) ((Equiv.sumCompl (fun ν => ν ∈ S)).symm (baseNd T ch a))) = _
  rw [h1, Equiv.sumCongr_apply, Sum.map_inl, h2, finSumFinEquiv_apply_left]

end Nc.Tow
end
/- Source module Nc.Tow.Cst. -/
section
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G
open NS1 (lg)

variable {F : Type} [CommRing F] {h b D J r m Uu : ℕ} {T : Tower h b D J r}


def kapB (c m X lh : ℕ) : ℕ := c * (m * X * (lh + 2 * X ^ 2))


def capB (c m X lh U0 : ℕ) : ℕ := U0 + 2 + 3 * c * kapB c m X lh

section

variable {FL : FlagLaws F T} {laws : List (Law F)} {c p q U0 : ℕ} {ρ : ℝ} (hC : TCst FL laws c ρ p q)
include hC

theorem TCst.D_two : 2 ≤ D := by
  have h1 := hC.two
  have h2 := hC.ρ_lt
  have h3 := hC.ρ_pos
  by_contra hcon
  have h4 : D ≤ 1 := by omega
  have h5 : (D : ℝ) ≤ 1 := by exact_mod_cast h4
  nlinarith

theorem TCst.X_pos : 0 < Fintype.card (T.X 0) := by
  have hD := hC.D_two
  have h1 := Tower.card_X_le (T := T) (by omega : 0 < D) J le_rfl
  have := hC.bot_pos
  omega

theorem TCst.c_pos : 1 ≤ c := hC.h_pos.trans_le hC.h_le

theorem kbar_kapB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    kbar FL Uu AA lh ≤ (kapB c m (Fintype.card (T.X 0)) lh : ℕ) := by
  refine (kbar_le hm hUu hAA hC.X_pos hC.b_pos).trans ?_
  unfold kapB
  push_cast
  exact mul_le_mul_of_nonneg_right hC.cst (by positivity)

theorem capN_capB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    capN FL U0 Uu AA lh ≤ capB c m (Fintype.card (T.X 0)) lh U0 := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  unfold capN capB
  refine Nat.add_le_add_left (Nat.ceil_le.2 ?_) _
  push_cast
  have hb : (b : ℝ) ≤ c := by exact_mod_cast hC.b_le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  calc 3 * (b : ℝ) * kbar FL Uu AA lh ≤ 3 * c * kbar FL Uu AA lh := by gcongr
    _ ≤ _ := by gcongr

theorem YhN_le {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    YhN FL Uu AA lh ρ ≤ 2 * c * kapB c m (Fintype.card (T.X 0)) lh * c := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  unfold YhN
  refine Nat.ceil_le.2 ?_
  push_cast
  have hρ : 0 < 1 - ρ := by have := hC.ρ_lt; linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hC.h_pos
  have hs : √(h : ℝ) ≤ c := by
    have h2 : √(h : ℝ) ≤ h := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    exact h2.trans (by exact_mod_cast hC.h_le)
  have hi := hC.inv
  have hi0 : 0 ≤ 1 / (1 - ρ) := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg (h : ℝ)
  calc 2 * √(h : ℝ) * kbar FL Uu AA lh / (1 - ρ) = 2 * √(h : ℝ) * kbar FL Uu AA lh * (1 / (1 - ρ)) := by ring
    _ ≤ 2 * c * kbar FL Uu AA lh * (1 / (1 - ρ)) := by gcongr
    _ ≤ 2 * c * (kapB c m (Fintype.card (T.X 0)) lh : ℕ) * (1 / (1 - ρ)) := by gcongr
    _ ≤ _ := by gcongr

theorem BhN_le {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    BhN FL Uu AA lh ρ ^ q * Fintype.card (T.X 0) ^ p ≤ (2 * c * kapB c m (Fintype.card (T.X 0)) lh) ^ q := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  have h2 := BhN_pow_le (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh) hC.b_pos hC.h_pos hC.bD hC.ρ_pos hC.bot_pos
    hC.pq hC.pow
  have hh : (h : ℝ) ≤ c := by exact_mod_cast hC.h_le
  have h3 : (2 * (h : ℝ)) ^ q * kbar FL Uu AA lh ^ q ≤
      (2 * (c : ℝ)) ^ q * ((kapB c m (Fintype.card (T.X 0)) lh : ℕ) : ℝ) ^ q := by
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    gcongr
  have h4 := h2.trans h3
  rw [← mul_pow] at h4
  exact_mod_cast h4

end


theorem card_Tg_le {V : ℕ} (hD : 0 < D) (hb : 0 < b) (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V)
    {AA : ℕ} (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hfl : Fintype.card (Sym2 T.Fl) ≤ V) :
    Fintype.card (Tg T m AA) ≤ 12 * V ^ 5 := by
  rw [Fintype.card_congr (tgEquiv T m AA), Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_sigma]
  have h1 : ∑ j : Fin (J + 1), Fintype.card (T.Ed j) ≤ 2 * V ^ 4 := by
    calc _ ≤ ∑ _j : Fin (J + 1), V * V * V := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (Tower.card_ed_le hD (Nat.le_of_lt_succ j.2)).trans ?_
          gcongr
      _ = (J + 1) * (V * V * V) := by simp
      _ ≤ (2 * V) * (V * V * V) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * V ^ 4 := by ring
  have h2 := (card_RM_le (T := T) (m := m) (AA := AA) hD).trans
    (rmN_le (X0 := Fintype.card (T.X 0)) hV hh hr hm hJ hAA hX)
  have h3 : ∑ j : Fin J, Fintype.card (Σ i : Fin h, T.V (j + 1) i × Sym2 T.Fl) ≤ V ^ 4 := by
    calc _ ≤ ∑ _j : Fin J, V * (V * V) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Fintype.card_sigma]
          calc _ ≤ ∑ _i : Fin h, V * V := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Fintype.card_prod]
                exact Nat.mul_le_mul ((Tower.card_V_le hD hb j.2 i).trans hX) hfl
            _ = h * (V * V) := by simp
            _ ≤ V * (V * V) := Nat.mul_le_mul_right _ hh
      _ = J * (V * (V * V)) := by simp
      _ ≤ V * (V * (V * V)) := Nat.mul_le_mul_right _ hJ
      _ = V ^ 4 := by ring
  have h4 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h5 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ hV
  omega

section Numbers


theorem two_pow_le {h b D J r : ℕ} {T : Tower h b D J r} (hD : 2 ≤ D) (hX : 0 < Fintype.card (T.X J)) :
    2 ^ J ≤ Fintype.card (T.X 0) := by
  have key : ∀ n ≤ J, 2 ^ n * Fintype.card (T.X n) ≤ Fintype.card (T.X 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      refine le_trans ?_ (ih (by omega))
      rw [T.card_X n (by omega), pow_succ, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD)
  refine le_trans ?_ (key J le_rfl)
  exact Nat.le_mul_of_pos_right _ hX

theorem depth_le {J X c K : ℕ} (hJ : 2 ^ J ≤ X) (hX : X ≤ c * (2 * K)) : J + 1 ≤ (2 * c + 1) * lg K := by
  have hl : 1 ≤ lg K := Nat.succ_le_succ (Nat.zero_le _)
  have h1 : K < 2 ^ lg K := Nat.lt_pow_succ_log_self (by norm_num) K
  have h2 : 2 * c < 2 ^ (2 * c) := Nat.lt_two_pow_self
  have h3 : 2 ^ J < 2 ^ (2 * c + lg K) := by
    calc 2 ^ J ≤ c * (2 * K) := hJ.trans hX
      _ = 2 * c * K := by ring
      _ < 2 ^ (2 * c) * 2 ^ lg K := Nat.mul_lt_mul'' h2 h1
      _ = _ := (pow_add _ _ _).symm
  have h4 : J < 2 * c + lg K := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have h5 : 2 * c ≤ 2 * c * lg K := Nat.le_mul_of_pos_right _ hl
  have e : (2 * c + 1) * lg K = 2 * c * lg K + lg K := by ring
  omega

theorem m_le {c m J K : ℕ} (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg K) : m ≤ c * ((2 * c + 1) ^ 7 * lg K ^ 7) := by
  refine hm.trans (Nat.mul_le_mul_left _ ?_)
  rw [← mul_pow]
  exact Nat.pow_le_pow_left hJ 7

end Numbers

end Nc.Tow
end
/- Source module Paper.Tree. -/
section
set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (ee)
open NS1 (lg)


noncomputable def flagMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    (FL : FlagLaws A T) : FlagLaws R T where
  Di := FL.Di
  L d := lawMap f (FL.L d)
  ro := FL.ro
  cn := FL.cn
  ends := FL.ends
  lam_pos := FL.lam_pos
  nonempty := FL.nonempty
  a₁ := FL.a₁
  a₁_pos := FL.a₁_pos
  C₁ := FL.C₁
  C₁_nonneg := FL.C₁_nonneg
  G₁ := FL.G₁
  G₁_le := FL.G₁_le
  L1 := FL.L1
  L2 := FL.L2

theorem TCst_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    {FL : FlagLaws A T} {laws : List (G.Law A)} {c p q : ℕ} {ρ : ℝ} (hC : TCst FL laws c ρ p q) :
    TCst (flagMap f FL) (laws.map (lawMap f)) c ρ p q where
  r_pos := hC.r_pos
  b_pos := hC.b_pos
  h_pos := hC.h_pos
  bD := hC.bD
  ρ_pos := hC.ρ_pos
  ρ_lt := hC.ρ_lt
  gain := hC.gain
  two := hC.two
  near := hC.near
  h_le := hC.h_le
  b_le := hC.b_le
  r_le := hC.r_le
  nr_le := hC.nr_le
  g_le := hC.g_le
  di_le := hC.di_le
  fl_le := hC.fl_le
  sl_le := hC.sl_le
  bot := hC.bot
  bot_pos := hC.bot_pos
  cst := hC.cst
  inv := hC.inv
  pq := hC.pq
  pow := hC.pow
  mem d := List.mem_map.2 ⟨_, hC.mem d, rfl⟩
  len L hL := by
    obtain ⟨L', h1, rfl⟩ := List.mem_map.1 hL
    exact ⟨⟨(hC.len L' h1).1.len_le⟩, (hC.len L' h1).2⟩

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












section Build

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') {ρ : ℝ} {lhat : ℕ}


def ndStage : Nd T → ℕ
  | none => J + 1
  | some s => s.1.1


noncomputable def ndPar (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) : Nd T → Nd T
  | none => none
  | some s => parN hh Lf s.1.1 s.2

theorem ndStage_par (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) {ν : Nd T} (hν : ν ≠ none) :
    ndStage (ndPar hh Lf ν) = ndStage ν + 1 := by
  rcases ν with _ | ⟨j, c⟩
  · exact absurd rfl hν
  · show ndStage (parN hh Lf j.1 c) = j.1 + 1
    unfold parN
    split_ifs with hj
    · rfl
    · have := j.2
      show J + 1 = j.1 + 1
      omega

theorem card_ndChildren (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] {ν : Nd T} (hν : ν ≠ none) :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = ν).card ≤ b := by
  rcases nd_cases ν with rfl | ⟨i, hi, c', rfl⟩
  · exact absurd rfl hν
  rcases i with _ | j
  · refine le_of_eq_of_le (card_eq_zero.2 (filter_false_of_mem fun μ _ hμ => ?_)) (Nat.zero_le _)
    have := ndStage_par hh Lf hμ.1
    rw [hμ.2] at this
    exact absurd this.symm (Nat.succ_ne_zero _)
  · refine le_trans ?_ (card_children (hh := hh) (Lf := Lf) (j := j) (by omega) c')
    refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X j => nd T j (by omega) c))
    intro μ hμ
    obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
    have hs := ndStage_par hh Lf hμ1
    rw [hμ2] at hs
    rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
    · exact absurd rfl hμ1
    have e : i = j := by
      simp only [ndStage, nd] at hs
      omega
    subst e
    refine mem_image.2 ⟨c, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    have h2 : parN hh Lf i c = nd T (i + 1) hi c' := hμ2
    unfold parN at h2
    rw [dif_pos hi, nd_inj] at h2
    exact h2

theorem card_ndRoot (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = none).card ≤ Fintype.card (T.X J) := by
  rw [← card_univ (α := T.X J)]
  refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X J => nd T J le_rfl c))
  intro μ hμ
  obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
  rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
  · exact absurd rfl hμ1
  have h2 : parN hh Lf i c = none := hμ2
  unfold parN at h2
  split_ifs at h2 with hi
  · exact absurd h2 nd_ne_none
  · have e : i = J := by omega
    subst e
    exact mem_image.2 ⟨c, mem_univ _, rfl⟩

theorem ndStage_eq_top {ν : Nd T} : ndStage ν = J + 1 ↔ ν = none := by
  rcases ν with _ | ⟨j, c⟩
  · simp [ndStage]
  · have := j.2
    simp [ndStage]
    omega


noncomputable def treePar (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (p : Fin (AA + A')) : Fin (AA + A') :=
  Pl.pt (ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Pl.pt.symm p))


noncomputable def treeUp (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (p : Fin (AA + A')) : ℕ :=
  onN (fb (lev (load R ch FL N (nn n) (oo R FL Pl o)))) 0 (Pl.pt.symm p)

variable {R FL Pl}

theorem valid_of (n : Fin AA → Fin AA → Fin (N + 1)) (h : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) : Valid N (nn n) := by
  intro a
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) (h a)
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl


theorem cur_tree (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (plan R FL Pl N N U1).good n o x)
    {u : Un R FL Pl N U1} (hu : u ∈ (plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))
    (hd : u ∉ deadU R FL Pl N o) (hloop : hold0 (sys R FL Pl).np u ≠ hold1 (sys R FL Pl).np u) :
    ∃ s : Σ j : Fin (J + 1), T.X j, u ∈ AsU R FL Pl N n o s ∧
      s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
  classical
  have hr := hH.r_pos
  have hb := hH.b_pos
  have hh := hH.h_pos
  have hp : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨hseen, hal⟩ := cur_end hr hb hh hu
  cases u with
  | init a c kk =>
    exfalso
    have hkn := mem_seen_init.1 hseen
    have hdone : tgB T R ch a c kk = .done := hal ⟨hv, hkn⟩
    have hne : a ≠ c := fun e => by
      subst e
      exact hloop rfl
    unfold tgB at hdone
    rw [if_neg hne] at hdone
    split_ifs at hdone with hs
    exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := gam T ch a kk) (s := 0)
      (R.pl_pos (fun e => hne (ch.injective e)) _)).1 hdone
  | new ν kk =>
    have hko := mem_seen_new.1 hseen
    have halv : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) = (o ν).1 := by
      rw [alv_good _ (hp _)]
      unfold oo
      rw [Equiv.symm_apply_apply]
    have hlt : kk.1 < (o ν).1 := by
      by_contra hge
      refine hd (mem_image.2 ⟨ν, mem_univ _, ?_⟩)
      rw [Fin.le_def] at hko
      have e : kk = o ν := Fin.ext (by omega)
      rw [e]
    have hA : AlU R FL Pl N n o (Uid.new ν kk : Un R FL Pl N U1) := by
      change kk.1 < alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν)
      rw [halv]
      exact hlt
    have hdone : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = .done := hal hA
    have e0 : hold0 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 false)) :=
      np_eq R FL Pl ν false
    have e1 : hold1 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 true)) :=
      np_eq R FL Pl ν true
    rw [e0, e1]
    have hmem : ∀ s, IsCh R ch FL (eN R FL Pl ν) s → (Uid.new ν kk : Un R FL Pl N U1) ∈ AsU R FL Pl N n o s :=
      fun s hs => mem_AsU_new.2 ⟨hA, hs⟩
    have hal' : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≠ 0 := by omega
    revert hdone hal' hmem
    generalize eN R FL Pl ν = w
    intro hdone hmem hal'
    rcases w with ⟨⟨x, hx⟩ | l, β⟩
    · have hnum : num R ch FL N (nn n) (oo R FL Pl o) (.inl ⟨x, hx⟩) ≠ 0 := by
        have := alv_le_num (lhat := N) (n := nn n) (o := oo R FL Pl o) (FL := FL) hr hb ⟨x, hx⟩ β
        omega
      obtain ⟨j, hj, c, h1, h2⟩ := done_hold hr hb hh hx (β := β) hdone hnum
      refine ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩, hmem _ ⟨⟨x, hx⟩, β, rfl, hdone, h1⟩, ?_⟩
      have h3 : s(partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β false),
          partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β true)) =
          s(nd T j hj c, parN hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) j c) := h2
      have h4 := congrArg (Sym2.map Pl.pt) h3
      simp only [Sym2.map_mk] at h4
      rw [h4, treePar, Equiv.symm_apply_apply]
      rfl
    · simp [tgM] at hdone


theorem layers_le_seen (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hg : ∀ x, (plan R FL Pl N N U1).good n o x) (p : Fin (AA + A')) :
    ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      (plan R FL Pl N N U1).num n o r'.1 ≤
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  classical
  have key : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      ∃ ν : (sys R FL Pl).N, ν.1 = r'.1 ∧ (∃ d, (sys R FL Pl).np ν d = p) ∧
        (plan R FL Pl N N U1).num n o r'.1 ≤ (o ν).1 := by
    rintro ⟨x, ro⟩ hr'
    obtain ⟨-, hrp, hlaw⟩ := mem_filter.1 hr'
    have hch : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro : (kindM R ch FL mv).Ro,
        GoodMv R ch FL N (nn n) (oo R FL Pl o) mv →
        ∃ ν : (kindM R ch FL mv).Cn, (∃ d, (kindM R ch FL mv).cnEnd ν d = ro) ∧
          num R ch FL N (nn n) (oo R FL Pl o) mv ≤ oo R FL Pl o ⟨mv, ν⟩ := by
      rintro (y | l) hl ro hgood
      · simp at hl
      obtain ⟨ν, hν⟩ := hH.near (FL.ro l.2.2.2 ro)
      refine ⟨(FL.cn l.2.2.2).symm ν, ?_, hgood.2 _⟩
      have h1 := FL.ends l.2.2.2 ((FL.cn l.2.2.2).symm ν)
      rw [Equiv.apply_symm_apply] at h1
      have h2 : FL.ro l.2.2.2 ro ∈ s(T.cN ν, T.dN ν) := by
        rcases hν with hν | hν <;> simp [hν]
      rw [← h1, Sym2.mem_iff] at h2
      rcases h2 with h2 | h2
      · exact ⟨false, ((FL.ro l.2.2.2).injective h2).symm⟩
      · exact ⟨true, ((FL.ro l.2.2.2).injective h2).symm⟩
    obtain ⟨ν, ⟨d, hd⟩, hle⟩ := hch (eE R FL x) hlaw ro (hg x)
    refine ⟨⟨x, ν⟩, rfl, ⟨d, ?_⟩, ?_⟩
    · rw [← hrp]
      exact congrArg (fun z => (sys R FL Pl).rp ⟨x, z⟩) hd
    · have e : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      unfold oo at hle
      rw [e] at hle
      exact hle
  choose ν hν1 hν2 hν3 using key
  let Fr : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      Finset (Un R FL Pl N U1) := fun r' hr' =>
    (univ.filter fun k : Fin U1 => k.1 < (plan R FL Pl N N U1).num n o r'.1).image (Uid.new (ν r' hr'))
  rw [← Finset.sum_attach]
  calc _ = ∑ q ∈ (univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach, (Fr q.1 q.2).card := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [card_image_of_injective _ (fun k k' e => (Uid.new.inj e).2), card_fin_lt']
        exact (hν3 q.1 q.2).trans (o _).2.le
    _ = ((univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach.biUnion fun q => Fr q.1 q.2).card := by
        rw [card_biUnion]
        intro q _ q' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu hu'
        obtain ⟨k, -, rfl⟩ := mem_image.1 hu
        obtain ⟨k', -, e⟩ := mem_image.1 hu'
        apply hne
        have e1 : (ν q'.1 q'.2).1 = (ν q.1 q.2).1 := congrArg Sigma.fst (Uid.new.inj e).1
        rw [hν1, hν1] at e1
        obtain ⟨⟨x, ro⟩, hq⟩ := q
        obtain ⟨⟨x', ro'⟩, hq'⟩ := q'
        simp only at e1
        subst e1
        have a1 := (mem_filter.1 hq).2.1
        have a2 := (mem_filter.1 hq').2.1
        obtain rfl : ro = ro' := (sys R FL Pl).inj x' (a1.trans a2.symm)
        rfl
    _ ≤ _ := by
        refine card_le_card fun u hu => ?_
        obtain ⟨q, -, hu⟩ := mem_biUnion.1 hu
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hu
        refine mem_filter.2 ⟨mem_seen_new.2 ?_, ?_⟩
        · rw [Fin.le_def]
          have := (mem_filter.1 hk).2
          have := hν3 q.1 q.2
          omega
        · obtain ⟨d, hd⟩ := hν2 q.1 q.2
          cases d
          · exact Or.inl hd.symm
          · exact Or.inr hd.symm

end Build

section Good

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}


theorem thm_tree_poss_good (hℓ : 0 < ℓ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (x : Fin (Fintype.card (Mv T R ch FL))) (hp : (Tow.plan R FL Pl N N U1).Poss n o ℓ x) :
    (Tow.plan R FL Pl N N U1).good n o x := by
  refine poss_good hℓ ?_
  obtain ⟨ι, hι⟩ := hp
  refine ⟨ι, fun ν => ?_⟩
  have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  unfold oo
  rw [h1]
  exact hι ν

end Good

section Program

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
variable {Inp ι : Type} {Dd Y p TM : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}


theorem tree_slp (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y TM) (hh : 0 < h) (hb : 0 < b)
    (hS : SlpN inp p H) (hn : ∀ a c, (fun x => ((nI x a c : Fin (U0 + 1)) : ℕ)) ∈ H)
    (ho : ∀ ν, (fun x => ((oI x ν : Fin U1) : ℕ)) ∈ H) (lhat : ℕ) :
    ∃ H', SlpN inp (p + Y ^ 16) H' ∧ Units nI oI lhat TM H' ∧
      HostOk hh (fun x => load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x))) H' ∧
      ∀ (j : ℕ) (_ : j ≤ J) (c : T.X j), (fun x => fb (lev (load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)))) j c) ∈ H' := by
  have hR : Rng (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) U0 U1 := rng
  have hS0 : SY inp Y p 0 H := by
    unfold SY
    rw [Nat.zero_mul, Nat.add_zero]
    exact hS
  have hb0 : Base (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) H := ⟨hn, fun ν => ho _⟩
  obtain ⟨H1, s1, u1, f1⟩ := after_stage hA hB hR hb hS0 hb0 (lhat := lhat)
  obtain ⟨H2, s2, u2, f2⟩ := units_stage hA hB hB2 s1 f1
  obtain ⟨H3, s3, u3, f3⟩ := host_stage hh (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB s2
    (fun j i => u2 (f1.isMin j i))
  obtain ⟨H4, s4, u4, f4⟩ := fb_stage (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB
    (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s3 (fun τ => u3 (u2 (f1.load τ)))
  refine ⟨H4, ?_, (f2.weaken u3).weaken u4, fun j hj c c' => u4 (f3 j hj c c'), f4⟩
  refine SlpN.le hA.zero_lt ?_ s4
  have h3 := hA.three
  have h4 : 0 + 11 + 8 * Y + 9 + 1 + 1 ≤ Y ^ 4 := by
    have e1 : Y ^ 4 = Y ^ 3 * Y := by ring
    have e2 : 3 ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left h3 3
    have e3 : 3 ^ 3 * Y ≤ Y ^ 3 * Y := Nat.mul_le_mul_right _ e2
    omega
  have h5 : (0 + 11 + 8 * Y + 9 + 1 + 1) * Y ^ 12 ≤ Y ^ 16 := by
    calc _ ≤ Y ^ 4 * Y ^ 12 := Nat.mul_le_mul_right _ h4
      _ = Y ^ 16 := by ring
  exact Nat.add_le_add_left h5 p


theorem par_computed {U0' : ℕ} {n' : Inp → Fin AA → Fin AA → Fin (U0' + 1)} {o' : Inp → (sys R FL Pl).N → Fin U1}
    (hh : 0 < h) (hH : HostOk hh (fun x => load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x))) H) (a q : Fin (AA + A')) :
    (ind fun x => treePar R FL Pl hh (n' x) (o' x) a = q) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
  classical
  have hconst : ∀ P : Prop, (ind fun _ : Inp => P) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
    intro P
    by_cases hP : P
    · refine Or.inr (Or.inr (funext fun x => ?_))
      exact ind_true (P := fun _ : Inp => P) hP
    · refine Or.inr (Or.inl (funext fun x => ?_))
      exact ind_false (P := fun _ : Inp => P) hP
  rcases nd_cases (Pl.pt.symm a) with e | ⟨j, hj, c, e⟩
  · simp only [treePar, e, ndPar]
    exact hconst _
  simp only [treePar, e]
  by_cases hjJ : j < J
  · rcases nd_cases (Pl.pt.symm q) with eq | ⟨i, hi, c', eq⟩
    · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
        intro x hx
        have := congrArg Pl.pt.symm hx
        rw [Equiv.symm_apply_apply, eq] at this
        simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)] at this
        exact absurd this (Option.some_ne_none _)
      rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => False from funext fun x => eq_false (this x)]
      exact hconst _
    · by_cases hij : i = j + 1
      · subst hij
        refine Or.inl ?_
        have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
            fun x => hostj hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) c = c' := by
          funext x
          rw [← Equiv.eq_symm_apply, eq]
          simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)]
          simp
        rw [e2]
        exact hH j hjJ c c'
      · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
          intro x hx
          have := congrArg Pl.pt.symm hx
          rw [Equiv.symm_apply_apply, eq] at this
          have h1 := congrArg ndStage this
          rw [ndStage_par hh _ nd_ne_none] at h1
          exact hij h1.symm
        rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
          fun _ => False from funext fun x => eq_false (this x)]
        exact hconst _
  · have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => Pl.pt none = q := by
      funext x
      simp only [ndPar, nd, parN, dif_neg (show ¬ j + 1 ≤ J by omega)]
    rw [e2]
    exact hconst _

end Program

section Numbers

theorem lg_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ lg M := by
  unfold lg
  have := Nat.log_pos (b := 2) (n := M) (by norm_num) hM
  omega


theorem const_mul_pow_le {L : ℕ} (hL : 2 ≤ L) {k e C : ℕ} (h : k + e ≤ C) : k * L ^ e ≤ L ^ C := by
  calc k * L ^ e ≤ L ^ k * L ^ e :=
        Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hL k))
    _ = L ^ (k + e) := (pow_add _ _ _).symm
    _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) h


def cKap (c : ℕ) : ℕ := 2 * c * (c * (c * (2 * c + 1) ^ 7 * c * (1 + 2 * c ^ 2)))

theorem kapB_tree {c m X M J N : ℕ} (hX : X ≤ c * M) (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg M) :
    2 * c * kapB c m X N ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) := by
  have h1 : N + 2 * X ^ 2 ≤ (1 + 2 * c ^ 2) * (N + M ^ 2) := by
    have : X ^ 2 ≤ (c * M) ^ 2 := Nat.pow_le_pow_left hX 2
    nlinarith
  unfold kapB
  calc 2 * c * (c * (m * X * (N + 2 * X ^ 2))) ≤
      2 * c * (c * (c * ((2 * c + 1) ^ 7 * lg M ^ 7) * (c * M) * ((1 + 2 * c ^ 2) * (N + M ^ 2)))) := by
        have := m_le hm hJ
        gcongr
    _ = _ := by unfold cKap; ring


theorem gain_rpow {B A M X q : ℕ} (hq : 0 < q) (hM : 0 < M) (hX : M ≤ X) (h : B ^ q * X ^ 1 ≤ A ^ q) :
    (B : ℝ) ≤ (A : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ((B : ℝ) * (M : ℝ) ^ (1 / (q : ℝ))) ^ q ≤ (A : ℝ) ^ q := by
    rw [mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (1 / (q : ℝ))) q, ← Real.rpow_mul hM0.le,
      one_div_mul_cancel (by exact_mod_cast hq.ne'), Real.rpow_one]
    have h2 : B ^ q * M ≤ A ^ q := (Nat.mul_le_mul_left _ (by rwa [pow_one])).trans h
    exact_mod_cast h2
  have h3 := le_of_pow_le_pow_left₀ hq.ne' (Nat.cast_nonneg A) h1
  rw [Real.rpow_neg hM0.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h3


theorem const_pow_le {c Z a C : ℕ} (hZ : 2 ≤ Z) (h : (c + 4) * a ≤ C) : ((c + 3) * Z) ^ a ≤ Z ^ C := by
  calc ((c + 3) * Z) ^ a ≤ (Z ^ (c + 3) * Z) ^ a := by
        gcongr
        exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hZ _)
    _ = Z ^ ((c + 4) * a) := by rw [← pow_succ, ← pow_mul]
    _ ≤ Z ^ C := Nat.pow_le_pow_right (by omega) h

end Numbers

section Lemmas

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ c : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {ρ : ℝ}


theorem tree_nums {c M N X J m : ℕ} (hc : 1 ≤ c) (hM : 2 ≤ M) (hN : 1 ≤ N) (hX : X ≤ c * M) (hJ : J + 1 ≤ X)
    (hm : m ≤ c * (J + 1) ^ 7) :
    c ≤ ((c + 3) * M) ^ 9 ∧ m ≤ ((c + 3) * M) ^ 9 ∧ X ≤ ((c + 3) * M) ^ 9 ∧ M ≤ ((c + 3) * M) ^ 9 ∧
      ((c + 3) * M) ^ 9 ≤ ((c + 3) * (M * N)) ^ 30 ∧ N ≤ ((c + 3) * (M * N)) ^ 30 ∧
      capB c m X N N * (c + c) + 1 ≤ ((c + 3) * (M * N)) ^ 30 := by
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = (c + 3) * M := ⟨_, rfl⟩
  rw [← hG, ← hG0]
  have hG0G : G0 ≤ G := by rw [hG0, hG]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hN)
  have hXG : X ≤ G0 := by rw [hG0]; exact hX.trans (Nat.mul_le_mul_right _ (by omega))
  have hcG : c + 3 ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hMG : M ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hNG : N ≤ G := by
    rw [hG]
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < M)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have q : ∀ a a', a ≤ a' → G0 ^ a ≤ G0 ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have p : ∀ a a', a ≤ a' → G ^ a ≤ G ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have hG9 : G0 ≤ G0 ^ 9 := Nat.le_self_pow (by norm_num) _
  have hG30 : G ≤ G ^ 30 := Nat.le_self_pow (by norm_num) _
  have hm8 : m ≤ G0 ^ 8 := by
    calc m ≤ c * (J + 1) ^ 7 := hm
      _ ≤ G0 * G0 ^ 7 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (hJ.trans hXG) 7)
      _ = G0 ^ 8 := by ring
  refine ⟨by omega, hm8.trans (q 8 9 (by norm_num)), by omega, by omega,
    (Nat.pow_le_pow_left hG0G 9).trans (p 9 30 (by norm_num)), by omega, ?_⟩
  have hm8' : m ≤ G ^ 8 := hm8.trans (Nat.pow_le_pow_left hG0G 8)
  have h1 : kapB c m X N ≤ G ^ 15 := by
    unfold kapB
    calc c * (m * X * (N + 2 * X ^ 2)) ≤ G * (G ^ 8 * G * (G + G * G ^ 2)) := by
          gcongr <;> omega
      _ = G ^ 11 + G ^ 13 := by ring
      _ ≤ G ^ 13 + G ^ 13 := Nat.add_le_add_right (p 11 13 (by norm_num)) _
      _ = 2 * G ^ 13 := by ring
      _ ≤ G * G ^ 13 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 14 := by ring
      _ ≤ G ^ 15 := p 14 15 (by norm_num)
  have h2 : capB c m X N N ≤ G ^ 18 := by
    unfold capB
    have e1 : G ≤ G ^ 17 := Nat.le_self_pow (by norm_num) _
    calc N + 2 + 3 * c * kapB c m X N ≤ G + G + G * G * G ^ 15 := by gcongr <;> omega
      _ = G + G + G ^ 17 := by ring
      _ ≤ G ^ 17 + G ^ 17 + G ^ 17 := by omega
      _ = 3 * G ^ 17 := by ring
      _ ≤ G * G ^ 17 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 18 := by ring
  calc capB c m X N N * (c + c) + 1 ≤ G ^ 18 * (G + G) + G ^ 19 := by
        gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by omega)
    _ = 3 * G ^ 19 := by ring
    _ ≤ G * G ^ 19 := Nat.mul_le_mul_right _ (by omega)
    _ = G ^ 20 := by ring
    _ ≤ G ^ 30 := p 20 30 (by norm_num)

open Classical in

theorem card_treeChildren (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (q : Fin (AA + A')) :
    (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = q).card ≤
      (if q = Pl.pt none then Fintype.card (T.X J) else b) := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective q
  have h1 : (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = Pl.pt ν).card ≤
      (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) μ = ν).card := by
    refine card_le_card_of_injOn Pl.pt.symm ?_ Pl.pt.symm.injective.injOn
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 (mem_coe.1 hp)
    refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, fun e => h1 ?_, Pl.pt.injective h2⟩)
    rw [← Equiv.apply_symm_apply Pl.pt p, e]
  by_cases hν : ν = none
  · subst hν
    rw [if_pos rfl]
    exact h1.trans (card_ndRoot _ _)
  · rw [if_neg fun e => hν (Pl.pt.injective e)]
    exact h1.trans (card_ndChildren _ _ hν)

open Classical in

theorem tree_node_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card ≤ (c + 1) * BhN FL Uu AA N ρ := by
  let S := (univ : Finset (Σ j : Fin (J + 1), T.X j)).filter fun s =>
    Pl.pt (some s) = p ∨ treePar R FL Pl hH.h_pos n o (Pl.pt (some s)) = p
  refine le_trans (card_le_card (t := S.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu4⟩ := mem_filter.1 hu1
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu1
    obtain ⟨s, hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    refine mem_biUnion.2 ⟨s, mem_filter.2 ⟨mem_univ _, ?_⟩, hs1⟩
    have h2 : p ∈ s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
      rw [← hs2, Sym2.mem_iff]
      exact hu2
    rw [Sym2.mem_iff] at h2
    exact h2.imp Eq.symm Eq.symm
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => (card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans
    (fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two _ (Nat.le_of_lt_succ s.1.2) _)).trans ?_)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  calc S.card ≤ ({p} ∪ univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p : Finset _).card := by
        refine card_le_card_of_injOn (fun s => Pl.pt (some s)) ?_ (fun s _ s' _ e => Option.some.inj (Pl.pt.injective e))
        intro s hs
        rcases (mem_filter.1 (mem_coe.1 hs)).2 with h3 | h3
        · exact mem_coe.2 (mem_union_left _ (mem_singleton.2 h3))
        · exact mem_coe.2 (mem_union_right _ (mem_filter.2
            ⟨mem_univ _, fun e => Option.some_ne_none s (Pl.pt.injective e), h3⟩))
    _ ≤ 1 + (univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p).card :=
        (card_union_le _ _).trans (by simp)
    _ ≤ c + 1 := by
        have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
        split_ifs at this <;> omega

open Classical in

theorem tree_total_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) :
    (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).card ≤
      YhN FL Uu AA N ρ := by
  refine le_trans (card_le_card (t := univ.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s, hs1, -⟩ := cur_tree hH hv hg hu1 hu3 hu4
    exact mem_biUnion.2 ⟨s, mem_univ _, hs1⟩
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans ?_)
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two

open Classical in

theorem tree_between (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)} (hv : Valid N (nn n))
    {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {p : Fin (AA + A')}
    (hp : p ≠ Pl.pt none) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (fun u => s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(p, treePar R FL Pl hH.h_pos n o p))).card ≤ treeUp R FL Pl n o p := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective p
  rcases ν with _ | q
  · exact absurd rfl hp
  refine (card_le_card (t := AsU R FL Pl N n o q) fun u hu => ?_).trans ?_
  · obtain ⟨hu, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s', hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    have he := hs2.symm.trans hu2
    rcases Sym2.eq_iff.1 he with ⟨e1, -⟩ | ⟨e1, e2⟩
    · rwa [← Option.some.inj (Pl.pt.injective e1)]
    · exfalso
      simp only [treePar, Equiv.symm_apply_apply] at e1 e2
      have a1 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none q)
      have a2 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none s')
      rw [← Pl.pt.injective e1] at a1
      rw [Pl.pt.injective e2] at a2
      omega
  · refine (card_AsU hH.r_pos hH.b_pos hH.h_pos q).trans (le_of_eq ?_)
    simp only [treeUp, Equiv.symm_apply_apply]
    rfl

open Classical in

theorem tree_up_node (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    treeUp R FL Pl n o p + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p),
      treeUp R FL Pl n o q ≤ (c + 1) * BhN FL Uu AA N ρ := by
  have h1 : ∀ q, treeUp R FL Pl n o q ≤ BhN FL Uu AA N ρ := fun q => by
    rcases nd_cases (Pl.pt.symm q) with e | ⟨j, hj, x, e⟩
    · simp [treeUp, e, onN]
    · simp only [treeUp, e, onN_nd]
      exact fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two j hj x
  rw [add_mul, one_mul, add_comm]
  refine Nat.add_le_add ((Finset.sum_le_sum fun q _ => h1 q).trans ?_) (h1 p)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
  split_ifs at this <;> omega


theorem tree_up_total (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) :
    ∑ p, treeUp R FL Pl n o p ≤ YhN FL Uu AA N ρ := by
  rw [← Equiv.sum_comp Pl.pt]
  simp only [treeUp, Equiv.symm_apply_apply]
  rw [Fintype.sum_option]
  simp only [onN, Nat.zero_add]
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two


theorem onN_le_up (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (P : Nd T) :
    onN (fun j x => 8 * fb (LfO R ch FL Pl N n o) j x + 3 * chF hh (LfO R ch FL Pl N n o) j x)
        (∑ e : T.Ed J, LfO R ch FL Pl N n o J e) P ≤
      8 * (treeUp R FL Pl n o (Pl.pt P) + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q) := by
  classical
  have kids : ∀ (j : ℕ) (hj : j ≤ J) (s : Finset (T.X j)),
      (∀ x ∈ s, parN hh (LfO R ch FL Pl N n o) j x = P) →
      ∑ x ∈ s, fb (LfO R ch FL Pl N n o) j x ≤ ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q := by
    intro j hj s hs
    have e1 : ∀ x, treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := fun x => by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [← Finset.sum_congr rfl fun x _ => e1 x,
      ← Finset.sum_image (f := treeUp R FL Pl n o) (g := fun x => Pl.pt (nd T j hj x))
        (fun x _ x' _ e => nd_inj.1 (Pl.pt.injective e))]
    refine Finset.sum_le_sum_of_subset fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hq
    refine mem_filter.2 ⟨mem_univ _, fun e => nd_ne_none (Pl.pt.injective e), ?_⟩
    simp only [treePar, Equiv.symm_apply_apply]
    exact congrArg Pl.pt (hs x hx)
  rcases nd_cases P with rfl | ⟨j, hj, x, rfl⟩
  · have h1 := kids J le_rfl univ fun x _ => by
      unfold parN
      rw [dif_neg (by omega)]
    have h2 := T.sum_bet (LfO R ch FL Pl N n o J)
    have h3 : ∑ x, fb (LfO R ch FL Pl N n o) J x = ∑ x, T.bet (LfO R ch FL Pl N n o J) x := rfl
    simp only [onN]
    omega
  · rw [onN_nd]
    have e1 : treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [e1]
    rcases j with _ | j
    · simp only [chF]
      omega
    · have h1 : chF hh (LfO R ch FL Pl N n o) (j + 1) x ≤ _ :=
        le_trans (le_of_eq (by rw [chF, chs, Finset.sum_filter]))
          (kids j (by omega) (univ.filter fun y => hostj hh (LfO R ch FL Pl N n o) y = x) fun y hy => by
            unfold parN
            rw [dif_pos hj, (mem_filter.1 hy).2])
      omega

open Classical in




theorem thm_tree_copies (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) {o : (sys R FL Pl).N → Fin U1}
    (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm)
    (p : Fin (AA + A')) :
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
        (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card +
        ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p),
          (1 + Fintype.card (((sys R FL Pl).kind r'.1).SlAt r'.2)) * (Tow.plan R FL Pl N N U1).num n o r'.1 ≤
      (4 + (2 * Fintype.card T.Nr * FL.G₁ + 1 + Sm) * Fintype.card FL.Di) * 8 * (treeUp R FL Pl n o p +
          ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p), treeUp R FL Pl n o q) +
        (if (p : ℕ) < AA then (1 + 8 * m) * N else 0) +
        2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  have hgd : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨P, rfl⟩ := Pl.pt.surjective p
  have h0 := held_node_le (R := R) (Pl := Pl) (lhat := N) (n := n) (o := o) hH.h_pos hH.r_pos hH.b_pos
    (fun x ν => hgd (.inl x) ν) (fun l => hgd (.inr l)) hH.near hSm (ℓf := N) P (fun a _ => hv a)
  have h2 : isB ch P * (N + 8 * m * N) ≤ if ((Pl.pt P : Fin (AA + A')) : ℕ) < AA then (1 + 8 * m) * N else 0 := by
    unfold isB
    split_ifs with e1 e2 e2
    · exact le_of_eq (by ring)
    · obtain ⟨a, rfl⟩ := e1
      exact absurd (by rw [Pl.pt_base]; exact a.2) e2
    · simp
    · simp
  have h3 : chanN R FL Pl (Pl.pt P) ≤
      2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P))).card := by
    unfold deadU chanN
    rw [Finset.filter_image, card_image_of_injective _ (fun ν ν' e => (Uid.new.inj e).1), card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [Fintype.sum_bool]
    by_cases e : Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P)
        (Uid.new ν (o ν) : Un R FL Pl N U1)
    · rw [if_pos e]
      split_ifs <;> omega
    · rw [if_neg e, if_neg fun h => e (Or.inr h.symm), if_neg fun h => e (Or.inl h.symm)]
      exact Nat.zero_le _
  have h4 := onN_le_up (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o P
  rw [Finset.sum_filter]
  refine le_trans h0 ?_
  calc _ ≤ _ + _ + _ := Nat.add_le_add (Nat.add_le_add h2 h3) (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

open Classical in

theorem tree_value (hH : THypR FL ρ) (hℓ : 1 ≤ ℓ) {cap : ℕ} (hcap : capN FL N Uu AA N ≤ cap)
    (hlen : ∀ d, (FL.L d).Le c ∧ (FL.L d).lam ≤ c) (hc : 1 ≤ c) (hU1 : U1 = cap * (c + c) + 1)
    {n : Fin AA → Fin AA → Fin (N + 1)} (tab : ∀ a, NodeTable F (fun a c => (n a c).1) ℓ a) :
    netValue tab = ∑ o : (sys R FL Pl).N → Fin U1, if ∀ x, (Tow.plan R FL Pl N N U1).good n o x then
      ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
        ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))), ∏ p,
        groupVal (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) none
          (Plan.seenAt n o (Fintype.card (Mv T R ch FL)))
          ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL))) id
          (fun a => partyTab (Tow.plan R FL Pl N N U1) n o (startTab (sys R FL Pl) U1 n tab a) a) p w
      else 0 := by
  have hok : (Tow.plan R FL Pl N N U1).Ok (capN FL N Uu AA N) :=
    plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
  have hgood : ∀ n o x, (Tow.plan R FL Pl N N U1).Poss n o ℓ x → (Tow.plan R FL Pl N N U1).good n o x :=
    fun n o x => thm_tree_poss_good hℓ n o x
  have hkl : ∀ x, ((sys R FL Pl).kind x).Le c ∧ ((sys R FL Pl).kind x).lam ≤ c := by
    intro x
    change (kindM R ch FL (eE R FL x)).Le c ∧ (kindM R ch FL (eE R FL x)).lam ≤ c
    rcases eE R FL x with y | l
    · exact ⟨⟨fun _ _ => hc⟩, Nat.zero_le _⟩
    · exact hlen _
  have hU1' : ∀ x, capN FL N Uu AA N * (c + ((sys R FL Pl).kind x).lam) + 1 ≤ U1 := by
    intro x
    rw [hU1]
    exact Nat.add_le_add_right (Nat.mul_le_mul hcap (Nat.add_le_add_left (hkl x).2 c)) 1
  have hU0' : 0 < U1 := by omega
  rw [← posVal_start (S := sys R FL Pl) (U1 := U1) tab,
    Paper.thm_tree_moves hok hℓ hgood (m := fun _ => c) (fun x => (hkl x).1) hU0' hU1' n
      (startTab (sys R FL Pl) U1 n tab) (fun a y y' h => startTab_congr tab a h) (fun a y h => startTab_ne_none tab a y h)]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x
  swap
  · rw [if_neg hg, if_neg hg]
  rw [if_pos hg, if_pos hg, posVal_groups _ _ _ _ _ id]

open Classical in

theorem tree_computed (hH : THypR FL ρ) {V : ℕ} (hV : 3 ≤ V) (hm : m ≤ V) (hJ : J + 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V)
    (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hdd : Fintype.card FL.Di ≤ V) (hbV : b ≤ V)
    (hfl : Fintype.card (Sym2 T.Fl) ≤ V) (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ V) (hN : N ≤ V) (hU1 : U1 ≤ V)
    (hD : 0 < D) :
    ∃ (steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
        (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin ((20 * V ^ 9) ^ 4))
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → ℕ)),
      steps ≤ 3 * (20 * V ^ 9) ^ 16 ∧ Fintype.card (Nd T) ≤ 20 * V ^ 9 ∧ Fintype.card (Mv T R ch FL) ≤ 20 * V ^ 9 ∧
      Fintype.card (Un R FL Pl N U1) ≤ 20 * V ^ 9 ∧
      (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
      (∀ p q, (ind fun x => treePar R FL Pl hH.h_pos x.1 x.2 p = q) ∈ H) ∧
      (∀ u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cur x.1 x.2 (Fintype.card (Mv T R ch FL))) ∈ H) ∧
      (∀ z u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cons x.1 x.2 z) ∈ H) ∧
      (∀ y, (fun x => (Tow.plan R FL Pl N N U1).num x.1 x.2 y) ∈ H) ∧
      (∀ p, (fun x => treeUp R FL Pl x.1 x.2 p) ∈ H) ∧
      ∀ y, (ind fun x => (Tow.plan R FL Pl N N U1).good x.1 x.2 y) ∈ H := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := N) (U1 := U1) hD
    hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX hdd hbV hS hN hU1
  have n7 := card_Tg_le (T := T) (m := m) (AA := AA) hD hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX
    hfl
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 20 * V ^ 9 := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ a, a ≤ 9 → V ^ a ≤ V ^ 9 := fun a ha => Nat.pow_le_pow_right (by omega) ha
  have p2 := pw 2 (by omega)
  have p5 := pw 5 (by omega)
  have p6 := pw 6 (by omega)
  have p7 := pw 7 (by omega)
  have p1 : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
  have hA : Alph (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hNM : Fintype.card (NM R FL (ch := ch)) = Fintype.card (sys R FL Pl).N := Fintype.card_congr (eN R FL Pl).symm
  have hZM : Fintype.card (ZM R FL (ch := ch)) = Fintype.card (sys R FL Pl).Z := Fintype.card_congr (eZ R FL Pl).symm
  have hWb : Wb R ch FL N U1 = Fintype.card (Un R FL Pl N U1) := by
    rw [card_Un]
    unfold Wb
    rw [hNM]
  have hAA2 : AA * AA ≤ V ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hAA hAA
  have hBd : Bnd R ch FL N U1 Y := {
    aa := by omega
    w := by rw [hWb]; omega
    nm := by rw [hNM]; omega
    mv := by omega
    tg := by omega
    nd := by omega
    fl := by omega
    di := by omega
    h := by omega
    j := by omega
    t := by unfold tend; omega
    tt := by
      rw [hWb]
      have h1 : b * Fintype.card (Sym2 T.Fl) * Fintype.card (Un R FL Pl N U1) ≤ V * V * (18 * V ^ 7) := by gcongr
      have h2 : V * V * (18 * V ^ 7) = 18 * V ^ 9 := by ring
      omega }
  have hB2 : Bnd2 R FL Pl N U1 Y 0 := {
    zm := by rw [hZM]; omega
    un := by omega
    tm := Nat.zero_le _ }
  have hYY : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  let inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
      (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin (Y ^ 4) := fun i x => match i with
    | .inl q => ⟨(x.1 q.1 q.2).1, by have := (x.1 q.1 q.2).2; omega⟩
    | .inr ν => ⟨(x.2 ν).1, by have := (x.2 ν).2; omega⟩
  obtain ⟨H', s1, f1, g1, e1⟩ := tree_slp (R := R) (FL := FL) (Pl := Pl) hA hBd hB2 hH.h_pos hH.b_pos
    (SlpN.inputs hA.zero_lt inp) (nI := fun x => x.1) (oI := fun x => x.2) (fun a b => ⟨.inl (a, b), rfl⟩)
    (fun ν => ⟨.inr ν, rfl⟩) N
  have s2 := (s1.snoc (fun _ => ⟨0, hA.zero_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))).snoc
    (fun _ => ⟨1, hA.one_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))
  refine ⟨_, inp, _, ?_, by omega, by omega, by omega, fun _ _ _ => rfl, fun _ _ => rfl, s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : Fintype.card ((Fin AA × Fin AA) ⊕ (sys R FL Pl).N) = AA * AA + Fintype.card (sys R FL Pl).N := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [e0]
    have : Y ≤ Y ^ 16 := Nat.le_self_pow (by norm_num) _
    omega
  · intro p q
    have key := par_computed (R := R) (FL := FL) (Pl := Pl) (U0' := N) (H := H') (n' := fun x => x.1) (o' := fun x => x.2)
      hH.h_pos g1 p q
    rcases key with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact fun u => Or.inr (Or.inr (f1.cur u))
  · exact fun z u => Or.inr (Or.inr (f1.cons (eZ R FL Pl z) u))
  · exact fun y => Or.inr (Or.inr (f1.num (eE R FL y)))
  · intro p
    unfold treeUp
    rcases nd_cases (Pl.pt.symm p) with e | ⟨j, hj, c, e⟩
    · simp only [e, onN]
      exact Or.inr (Or.inl rfl)
    · simp only [e, onN_nd]
      exact Or.inr (Or.inr (e1 j hj c))
  · exact fun y => Or.inr (Or.inr (f1.good (eE R FL y)))




end Lemmas



section Thm

variable {F : Type} [CommRing F] {h b D J m Uu AA N M ℓ : ℕ} {T : Tower h b D J 1}


def cTree (c : ℕ) : ℕ := (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 + (4 + (2 * c * c + 1 + c) * c) * 8 +
  (1 + 8 * (c * (2 * c + 1) ^ 7))

open Classical in

theorem exists_thinTrees (R : Routes T m Uu) (FL : FlagLaws F T) {laws : List (G.Law F)} {c q : ℕ} {ρ : ℝ}
    (hC : TCst FL laws c ρ 1 q) {C : ℕ} (hC0 : cTree c ≤ C) (hm1 : 1 ≤ m)
    (hm : m ≤ c * (J + 1) ^ 7) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hM : 2 ≤ M)
    (hX1 : M ≤ Fintype.card (T.X 0)) (hX2 : Fintype.card (T.X 0) ≤ c * M) (hAA : AA ≤ M) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) :
    Nonempty (ThinTrees F laws AA N ℓ M b FL.G₁ C (1 / (q : ℝ))) := by
  classical
  obtain ⟨hCc, hC8, hC9⟩ : (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 ≤ C ∧ (4 + (2 * c * c + 1 + c) * c) * 8 ≤ C ∧
      1 + 8 * (c * (2 * c + 1) ^ 7) + 7 ≤ C := by unfold cTree at hC0; omega
  have hH := hC.toTHypR
  have hc := hC.c_pos
  have hl := lg_two hM
  have hJX := two_pow_le (T := T) hC.D_two hC.bot_pos
  have hdep : J + 1 ≤ (2 * c + 1) * lg M := depth_le hJX (hX2.trans (Nat.mul_le_mul_left _ (by omega)))
  have hJ1 : J + 1 ≤ Fintype.card (T.X 0) := Nat.succ_le_of_lt ((Nat.lt_two_pow_self (n := J)).trans_le hJX)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := tree_nums (N := N) hc hM hN hX2 hJ1 hm
  have hAX : AA ≤ Fintype.card (T.X 0) := hAA.trans hX1
  obtain ⟨ch⟩ := Function.Embedding.nonempty_of_card_le (α := Fin AA) (β := T.X 0) (by rwa [Fintype.card_fin])
  obtain ⟨Pl⟩ := exists_place T ch
  have hkap := kapB_tree (N := N) hX2 hm hdep
  obtain ⟨U1, hU1⟩ : ∃ U1, U1 = capB c m (Fintype.card (T.X 0)) N N * (c + c) + 1 := ⟨_, rfl⟩
  rw [← hU1] at a7
  obtain ⟨W, hW⟩ : ∃ W, W = ((c + 3) * M) ^ 9 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = ((c + 3) * (M * N)) ^ 30 := ⟨_, rfl⟩
  rw [← hW] at a1 a2 a3 a4 a5
  rw [← hV] at a5 a6 a7
  have hcV : c ≤ V := a1.trans a5
  have hMN : 2 ≤ M * N := le_trans hM (Nat.le_mul_of_pos_right _ hN)
  -- loads
  have hq : 0 < q := by have := hC.pq; omega
  have hBh : (BhN FL Uu AA N ρ : ℝ) ≤ ((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) *
      (N + (M : ℝ) ^ 2) := by
    refine (gain_rpow hq (by omega) hX1 (BhN_le (lh := N) hC hm1 hUu hAX)).trans ?_
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    calc ((2 * c * kapB c m (Fintype.card (T.X 0)) N : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) ≤
        ((cKap c * (lg M ^ 7 * M * (N + M ^ 2)) : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkap) (Real.rpow_nonneg hM0.le _)
      _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]
          push_cast
          ring
  have hnode : (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
    have h3 : (c + 1) * (cKap c * lg M ^ 7) ≤ lg M ^ C := by
      rw [← mul_assoc]
      refine const_mul_pow_le hl ?_
      calc (c + 1) * cKap c + 7 ≤ (2 * c + 1) * cKap c + 7 := by gcongr; omega
        _ ≤ C := by rw [mul_comm (2 * c + 1)]; omega
    calc (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
        ((c + 1 : ℕ) : ℝ) * (((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2)) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left hBh (Nat.cast_nonneg _)
      _ = (((c + 1) * (cKap c * lg M ^ 7) : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
          push_cast; ring
      _ ≤ _ := by gcongr
  have htot : YhN FL Uu AA N ρ ≤ lg M ^ C * M * (N + M ^ 2) := by
    have h1 := YhN_le (lh := N) hC hm1 hUu hAX
    have h2 : cKap c * c * lg M ^ 7 ≤ lg M ^ C := const_mul_pow_le hl (by
      have : cKap c * c ≤ cKap c * (2 * c + 1) := Nat.mul_le_mul_left _ (by omega)
      omega)
    calc YhN FL Uu AA N ρ ≤ 2 * c * kapB c m (Fintype.card (T.X 0)) N * c := h1
      _ ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) * c := Nat.mul_le_mul_right _ hkap
      _ = cKap c * c * lg M ^ 7 * M * (N + M ^ 2) := by ring
      _ ≤ _ := by gcongr
  have hne : ∀ p, p ≠ Pl.pt none → Pl.pt.symm p ≠ none := fun p hp e => hp (by
    rw [← Equiv.apply_symm_apply Pl.pt p, e])
  have hV3 : 3 ≤ V := hV ▸ (le_trans (Nat.le_add_left 3 c)
    (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))).trans (Nat.le_self_pow (by norm_num) _)
  obtain ⟨steps, inp, H, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := tree_computed (R := R) (FL := FL)
    (Pl := Pl) (U1 := U1) (N := N) hH (V := V) hV3 (by omega) (by omega) (hC.h_le.trans hcV) (hC.r_le.trans hcV)
    (by omega) (by omega) (hC.di_le.trans hcV) (hC.b_le.trans hcV) (hC.fl_le.trans hcV)
    (fun d => (hC.sl_le d).trans hcV) a6 a7 (by have := hC.D_two; omega)
  refine ⟨{
    A' := extra T AA
    E := Fintype.card (Mv T R ch FL)
    U1 := U1
    sys := sys R FL Pl
    plan := Tow.plan R FL Pl N N U1
    stage := fun p => ndStage (Pl.pt.symm p)
    depth := J + 1
    root := Pl.pt none
    par := treePar R FL Pl hH.h_pos
    dead := deadU R FL Pl N
    isLaw := fun x => (eE R FL x).isRight
    depth_le := hdep.trans ((le_of_eq (by rw [pow_one])).trans (const_mul_pow_le hl (show 2 * c + 1 + 1 ≤ C by omega)))
    stage_le := fun p => ?_
    stage_given := fun a => by rw [← Pl.pt_base, Equiv.symm_apply_apply]; rfl
    stage_root := fun p => by rw [ndStage_eq_top, Equiv.symm_apply_eq]
    stage_par := fun n o p hp => by
      rw [treePar, Equiv.symm_apply_apply]
      exact ndStage_par _ _ (hne p hp)
    children_le := fun n o x hx => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o x
      rwa [if_neg hx] at this
    root_children_le := fun n o => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o (Pl.pt none)
      rw [if_pos rfl] at this
      exact this.trans (hC.bot.trans (by omega))
    dead_le := fun o => ?_
    kinds := fun x => ?_
    law_stage := fun r' hr' => ?_
    U1_pos := by rw [hU1]; exact Nat.succ_pos _
    cap := capN FL N Uu AA N
    ok := plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
    up := treeUp R FL Pl
    good_iff := fun n o x => ?_
    poss_good := fun n o x hp => thm_tree_poss_good hℓ n o x hp
    edge := fun n hv o hg u hu => ?_
    node_le := fun n hv o hg p => ?_
    total_le := fun n hv o hg => ?_
    between_le := fun n hv o hg p hp => tree_between hH (valid_of n hv) hg hp
    up_node := fun n hv o hg p => ?_
    up_total := fun n hv o hg => ?_
    copies_le := fun n hv o hg p => ?_
    layers_le := fun n o hg p => layers_le_seen hH n o hg p
    value := fun n hv tab => tree_value hH hℓ (capN_capB hC hm1 hUu hAX) (fun d => hC.len _ (hC.mem d)) hc hU1 tab
    computed := ?_ }⟩
  · rcases Pl.pt.symm p with _ | ⟨j, x⟩
    · exact le_rfl
    · exact Nat.le_of_lt (show j.1 < J + 1 from j.2)
  · obtain ⟨n1', -⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := 0) (U1 := 0)
      (show 0 < D by have := hC.D_two; omega) hC.b_pos (show 1 ≤ W by omega) (hC.h_le.trans a1) (hC.r_le.trans a1) a2
      (show J ≤ W by omega) (show AA ≤ W by omega) a3 (hC.di_le.trans a1) (hC.b_le.trans a1)
      (fun d => (hC.sl_le d).trans a1) (Nat.zero_le _) (Nat.zero_le _)
    refine (card_image_le.trans (le_of_eq card_univ)).trans (n1'.trans ?_)
    rw [hW, ← pow_mul]
    calc 17 * ((c + 3) * M) ^ (9 * 6) ≤ ((c + 3) * M) ^ 3 * ((c + 3) * M) ^ (9 * 6) := by
          refine Nat.mul_le_mul_right _ ?_
          have := Nat.pow_le_pow_left (le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M by omega))) 3
          omega
      _ = ((c + 3) * M) ^ 57 := by rw [← pow_add]
      _ ≤ M ^ C := const_pow_le hM (by omega)
  · change if (eE R FL x).isRight = true then kindM R ch FL (eE R FL x) ∈ laws else kindM R ch FL (eE R FL x) = relay F
    rcases eE R FL x with y | l
    · simp [kindM]
    · simp only [Sum.isRight_inr, if_true]
      exact hC.mem _
  · change 0 < ndStage (Pl.pt.symm (Pl.pt (partM R ch FL (eE R FL r'.1) r'.2)))
    rw [Equiv.symm_apply_apply]
    have key : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro, 0 < ndStage (partM R ch FL mv ro) := by
      rintro (y | l) hl ro
      · simp at hl
      · exact Nat.succ_pos _
    exact key _ hr' _
  · have e : ∀ ν : (kindM R ch FL (eE R FL x)).Cn, oo R FL Pl o ⟨eE R FL x, ν⟩ = (o ⟨x, ν⟩ : ℕ) := fun ν => by
      unfold oo
      have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [h1]
    change GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ↔ if (eE R FL x).isRight = true then
      b * ∑ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val ^ 2 ≤
          FL.G₁ * num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ^ 2 ∧
        ∀ ν : (kindM R ch FL (eE R FL x)).Cn, num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ≤ (o ⟨x, ν⟩ : ℕ)
      else ∀ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val = num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x)
    simp only [← e]
    clear e
    generalize eE R FL x = mv
    rcases mv with y | l
    · exact Iff.rfl
    · simp only [Sum.isRight_inr, if_true, GoodMv, GoodL, Nat.one_mul]
      rfl
  · obtain ⟨hu, hl'⟩ := mem_filter.1 hu
    obtain ⟨hu, hd⟩ := mem_sdiff.1 hu
    obtain ⟨s, -, hs⟩ := cur_tree hH (valid_of n hv) hg hu hd hl'
    exact ⟨_, fun e => Option.some_ne_none s (Pl.pt.injective e), hs⟩
  · -- the units at one node
    exact (Nat.cast_le.2 (tree_node_le (R := R) (FL := FL) (Pl := Pl) hH (valid_of n hv) hg hC.b_le hC.bot p)).trans hnode
  · -- all units
    exact (tree_total_le hH (valid_of n hv) hg).trans htot
  · exact (Nat.cast_le.2 (tree_up_node hH n o hC.b_le hC.bot p)).trans hnode
  · exact (tree_up_total hH n o).trans htot
  · -- copies
    refine (thm_tree_copies (R := R) (FL := FL) (Pl := Pl) hH hv hg hC.sl_le p).trans ?_
    refine Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ?_) ?_) (Nat.mul_le_mul_right _ (by omega))
    · refine le_trans ?_ hC8
      have a1 := hC.nr_le
      have a2 := hC.g_le
      have a3 := hC.di_le
      gcongr
    · split_ifs
      · refine Nat.mul_le_mul_right _ ?_
        have h1 : 1 ≤ lg M ^ 7 := Nat.one_le_pow _ _ (by omega)
        calc 1 + 8 * m ≤ lg M ^ 7 + 8 * (c * ((2 * c + 1) ^ 7 * lg M ^ 7)) :=
              Nat.add_le_add h1 (Nat.mul_le_mul_left _ (m_le hm hdep))
          _ = (1 + 8 * (c * (2 * c + 1) ^ 7)) * lg M ^ 7 := by ring
          _ ≤ lg M ^ C := const_mul_pow_le hl hC9
      · exact le_rfl
  · -- the program
    have hpow : ∀ e, e ≤ 200000 → ((c + 3) * (M * N)) ^ e ≤ (M * N) ^ C := fun e he =>
      const_pow_le hMN ((Nat.mul_le_mul_left _ he).trans (by omega))
    have hG3 : 3 ≤ (c + 3) * (M * N) :=
      le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))
    obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
    rw [← hG] at hV hpow hG3
    have hYG : 20 * V ^ 9 ≤ G ^ 273 := by
      rw [hV, ← pow_mul]
      calc 20 * G ^ (30 * 9) ≤ G ^ 3 * G ^ (30 * 9) := Nat.mul_le_mul_right _ (by
            have := Nat.pow_le_pow_left hG3 3; omega)
        _ = G ^ 273 := by rw [← pow_add]
    have hyp : 20 * V ^ 9 ≤ (M * N) ^ C := hYG.trans (hpow 273 (by norm_num))
    refine ⟨_, steps, inp, H, ?_, ?_, ?_, b2.trans hyp, ?_, b3.trans hyp, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
    · refine (Nat.pow_le_pow_left hYG 4).trans ?_
      rw [← pow_mul]
      exact hpow _ (by norm_num)
    · refine b0.trans ?_
      calc 3 * (20 * V ^ 9) ^ 16 ≤ G * (G ^ 273) ^ 16 := Nat.mul_le_mul hG3 (Nat.pow_le_pow_left hYG 16)
        _ = G ^ 4369 := by rw [← pow_mul, ← pow_succ']
        _ ≤ _ := hpow _ (by norm_num)
    · rw [card_party Pl]
      exact b1.trans hyp
    · refine a7.trans (le_trans ?_ hyp)
      have : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
      omega


















theorem thm_tree {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R] (M AA N ℓ : ℕ), 2 ≤ M → AA ≤ M → 1 ≤ N → 1 ≤ ℓ →
      Nonempty (ThinTrees R (((univ : Finset VL.Di).toList.map VL.L).map (lawMap (algebraMap A R))) AA N ℓ M
        (2 ^ ee h) (goodBound VL.C₁ VL.a₁) C (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ))) := by
  have he : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ ((2 ^ ee h : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by norm_num) he
    linarith
  obtain ⟨c, hc⟩ := ValiantBorder.lawTowers
    { VL with
      G₁ := goodBound VL.C₁ VL.a₁
      G₁_le := Nat.floor_le (by have := VL.C₁_nonneg; positivity)
      L2 := fun d i => (VL.L2 d i).trans (Nat.le_floor VL.G₁_le) } h3 (by linarith) htwo
  refine ⟨cTree c, fun R _ _ M AA N ℓ hM hAA hN hℓ => ?_⟩
  obtain ⟨J, m, Uu, T, Rt, FL, hG, hC, hX1, hX2, hm1, hm2, hUu⟩ := hc M (by omega)
  have e : Real.logb 2 ((2 ^ ee h : ℕ) : ℝ) = (ee h : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simp only [] at hG
  rw [e, ← hG]
  exact exists_thinTrees Rt (flagMap (algebraMap A R) FL) (TCst_map _ hC) le_rfl hm1 hm2 hUu hM hX1 hX2 hAA hN hℓ

end Thm

end Paper
end

open Finset Nc Nc.Tow Nc.Vp Paper
open Nc.Tower (ee)
theorem solution {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R] (M AA N ℓ : ℕ), 2 ≤ M → AA ≤ M → 1 ≤ N → 1 ≤ ℓ →
      Nonempty (ThinTrees R (((univ : Finset VL.Di).toList.map VL.L).map (lawMap (algebraMap A R))) AA N ℓ M
        (2 ^ ee h) (goodBound VL.C₁ VL.a₁) C (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ))) := Paper.thm_tree VL h3 hgain
