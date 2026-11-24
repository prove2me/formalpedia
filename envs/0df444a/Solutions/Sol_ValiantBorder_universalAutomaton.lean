-- Prove2me | solution 1 for ValiantBorder.universalAutomaton
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:08:05.260938+00:00
-- url     : https://prove2.me/submissions/32b153c5-a928-46fe-894c-779979e06a58

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_tapeAutomata

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026).
Source: `anthropics/formal-math`, revision
11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/Paper/{Universal,UniversalSteps,CircuitPhi,Circuit}.lean`.
The construction uses the weighted universal automaton, its tape semantics and the grid representation of its run polynomial.
Apache-2.0. -/

/-! Source module: Nc.Tape.Rep -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Linear representations of series on words

A series is a function `List Ω → F`. A linear representation of dimension `n` gives the value of the series
at a word as (row vector) · (product of matrices, one for each letter) · (column vector). Sums, products and
stars (over non-empty factors) of represented series are represented, and dimensions add up.
-/

namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- A series on words. -/
abbrev Series (F Ω : Type*) := List Ω → F

namespace Series

/-- The Cauchy product. -/
def mul (f g : Series F Ω) : Series F Ω := fun o =>
  ∑ k ∈ range (o.length + 1), f (o.take k) * g (o.drop k)

/-- The unit: 1 at the empty word. -/
def one : Series F Ω := fun o => if o = [] then 1 else 0

/-- The star over non-empty factors: the sum over all ways to cut the word into non-empty factors. -/
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

/-- A linear representation with state space `Q`. -/
structure Rep (F Ω Q : Type*) where
  /-- initial weights -/
  lam : Q → F
  /-- transition weights -/
  mu : Ω → Matrix Q Q F
  /-- final weights -/
  gam : Q → F

namespace Rep

variable {Q Q₁ Q₂ : Type*} [Fintype Q] [Fintype Q₁] [Fintype Q₂]

/-- The weights from a state to acceptance along a word. -/
def tail (r : Rep F Ω Q) : List Ω → Q → F
  | [] => r.gam
  | a :: o => r.mu a *ᵥ tail r o

/-- The series of a representation. -/
def series (r : Rep F Ω Q) : Series F Ω := fun o => r.lam ⬝ᵥ r.tail o

/-- Sum of two series. -/
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

/-- Product of two series. -/
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

/-- Star of a series (over non-empty factors). -/
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

/-! Source module: Nc.Tape.Rat -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Rational series of bounded dimension
-/

set_option linter.unusedSimpArgs false

namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- The series has a linear representation of dimension at most `n`. -/
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

/-- The series of one letter. -/
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

/-- Normal form: one initial and one final state; the same values at non-empty words. -/
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

/-! Source module: Nc.Tape.Hat -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Series on several channels

Letters are pairs (channel, letter). `hat f v` is the sum of the series `f` over all words whose projections
to the channels are the words `v z`. Products of series become convolutions.
-/

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

/-- The words with given projections. -/
noncomputable def fib (v : Z → List Γ) : Finset (List (Z × Γ)) :=
  (show {o : List (Z × Γ) | proj o = v}.Finite from
    (List.finite_length_eq (Z × Γ) (∑ z, (v z).length)).subset (by
      rintro o rfl
      exact (sum_length_proj o).symm)).toFinset

theorem mem_fib {v : Z → List Γ} {o : List (Z × Γ)} : o ∈ fib v ↔ proj o = v := by
  simp [fib]

/-- The sum of a series over the words with given projections. -/
noncomputable def hat (f : Series F (Z × Γ)) (v : Z → List Γ) : F := ∑ o ∈ fib v, f o

/-- All ways to cut the words on the channels into two parts. -/
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

/-- The part of a series at non-empty words. -/
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

/-- The recursion for the star. -/
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

/-! Source module: Nc.Tape.Loop -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Words, loops, and phases on disjoint channels
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The series of one word. -/
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

/-- The body of a loop: one of finitely many words, with weights. -/
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

/-! Source module: Nc.Tape.Task -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Tasks

A program is a series on the channels "side b of tape s" and "input j". Its value at an input is the sum,
over all contents of the tapes, of the weight of the program at these contents (the same word on both sides
of every tape).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

/-- The words on the channels for given contents of the tapes and given inputs. -/
def tup (W : S → List Γ) (u : J → List Γ) : Ch S J → List Γ
  | .tp s _ => W s
  | .inp j => u j

/-- The contents of total length at most `t`. -/
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

/-- The value of a program, with contents of total length at most `t`. -/
noncomputable def val (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : F :=
  ∑ W ∈ contents S Γ t, hat P (tup W u)

/-- All contents that contribute have total length at most `t`. -/
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

/-! Source module: Nc.Sort.Runs -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Programs given by their structured runs

A series on channels is described by a family of runs: every run emits words on the channels and has a weight.
The sum of the series over all words with given projections is the sum of the weights of the runs that emit
these projections.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The series is described by runs with emissions em and weights wt. -/
def IsRuns (P : Series F (Z × Γ)) {X : Type*} (em : X → Z → List Γ) (wt : X → F) : Prop :=
  ∀ v, ∃ R : Finset X, (∀ x, x ∈ R ↔ em x = v) ∧ hat P v = ∑ x ∈ R, wt x

/-- There is a series of dimension at most n with these runs. -/
def Runs (n : ℕ) {X : Type*} (em : X → Z → List Γ) (wt : X → F) : Prop :=
  ∃ P : Series F (Z × Γ), RatLe n P ∧ IsRuns P em wt

theorem IsRuns.exists_run {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {v : Z → List Γ} (hv : hat P v ≠ 0) : ∃ x, em x = v ∧ wt x ≠ 0 := by
  obtain ⟨R, h1, h2⟩ := h v
  rw [h2] at hv
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨x, (h1 x).1 hx, hne⟩

theorem IsRuns.of_fib {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {v : Z → List Γ} (R : Finset X) (hR : ∀ x, x ∈ R ↔ em x = v) :
    hat P v = ∑ x ∈ R, wt x := by
  obtain ⟨R', h1, h2⟩ := h v
  have : R' = R := by ext x; rw [h1, hR]
  rw [h2, this]

theorem IsRuns.mul {f g : Series F (Z × Γ)} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : IsRuns f em wt) (hg : IsRuns g em' wt') :
    IsRuns (Series.mul f g) (fun (x : X × Y) z => em x.1 z ++ em' x.2 z) (fun x => wt x.1 * wt' x.2) := by
  classical
  intro v
  choose Rf hf1 hf2 using hf
  choose Rg hg1 hg2 using hg
  refine ⟨(anti v).biUnion fun p => Rf p.1 ×ˢ Rg p.2, ?_, ?_⟩
  · rintro ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, hf1, hg1, mem_anti]
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      funext z
      rw [h1, h2, hp z]
    · intro h
      exact ⟨(em x, em' y), fun z => congrFun h z, rfl, rfl⟩
  · rw [hat_mul, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [hf2, hg2, Finset.sum_mul_sum, Finset.sum_product]
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨x, y⟩ h h'
      rw [Finset.mem_product, hf1, hg1] at h h'
      exact hpq (Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))

theorem IsRuns.sum {ι : Type*} [Fintype ι] {X : ι → Type*} {P : ι → Series F (Z × Γ)}
    {em : ∀ i, X i → Z → List Γ} {wt : ∀ i, X i → F} (h : ∀ i, IsRuns (P i) (em i) (wt i)) :
    IsRuns (∑ i, P i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  intro v
  choose R h1 h2 using h
  refine ⟨univ.sigma fun i => R i v, ?_, ?_⟩
  · rintro ⟨i, x⟩
    simp [h1]
  · rw [hat_sum, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => h2 i v

theorem IsRuns.congr {P : Series F (Z × Γ)} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (h : IsRuns P em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) : IsRuns P em' wt' := by
  intro v
  obtain ⟨R, g1, g2⟩ := h v
  refine ⟨R.map e.symm.toEmbedding, fun y => ?_, ?_⟩
  · simp only [Finset.mem_map_equiv, Equiv.symm_symm, g1]
    have : em (e y) = em' y := funext fun z => h1 y z
    rw [this]
  · rw [g2, Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← h2]
    simp

theorem IsRuns.one : IsRuns (Series.one : Series F (Z × Γ)) (fun (_ : Unit) _ => []) (fun _ => 1) := by
  classical
  intro v
  refine ⟨if v = fun _ => [] then {()} else ∅, ?_, ?_⟩
  · intro x
    by_cases h : v = fun _ => []
    · simp [h]
    · simp [h, Ne.symm h]
  · rw [hat_one]
    split_ifs <;> simp

/-- The star: the runs are the lists of runs. -/
theorem IsRuns.kstar {f : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (hf : IsRuns f em wt) (hne : ∀ x, em x ≠ fun _ => []) :
    IsRuns (Series.kstar f) (fun (l : List X) z => l.flatMap fun x => em x z)
      (fun l => (l.map wt).prod) := by
  classical
  intro v
  induction hn : ∑ z, (v z).length using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    choose Rf hf1 hf2 using hf
    have hlt : ∀ p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []), ∑ z, (p.2 z).length < n := by
      intro p hp
      rw [Finset.mem_filter, mem_anti] at hp
      have e : n = ∑ z, (p.1 z).length + ∑ z, (p.2 z).length := by
        rw [← hn, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun z _ => by rw [← hp.1 z, List.length_append]
      have : 0 < ∑ z, (p.1 z).length := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        apply hp.2
        funext z
        exact List.length_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 h0 z (Finset.mem_univ z))
      omega
    have ih' : ∀ p, ∃ R : Finset (List X), p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []) →
        (∀ l, l ∈ R ↔ (fun z => l.flatMap fun x => em x z) = p.2) ∧
        hat (Series.kstar f) p.2 = ∑ l ∈ R, (l.map wt).prod := by
      intro p
      by_cases hp : p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => [])
      · obtain ⟨R, h1, h2⟩ := ih _ (hlt p hp) p.2 rfl
        exact ⟨R, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨∅, fun h => absurd h hp⟩
    choose Rs hRs using ih'
    let A := (anti v).filter (fun p => p.1 ≠ fun _ => [])
    let B : Finset (X × List X) := A.biUnion fun p => Rf p.1 ×ˢ Rs p
    have hB : ∀ x l, (x, l) ∈ B ↔ (fun z => em x z ++ l.flatMap fun x => em x z) = v := by
      intro x l
      simp only [B, Finset.mem_biUnion, Finset.mem_product]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        rw [hf1] at h1
        rw [(hRs p hp).1] at h2
        have := (mem_anti.1 (Finset.mem_filter.1 hp).1)
        funext z
        rw [← this z, h1]
        exact congrArg _ (congrFun h2 z)
      · intro h
        have hp : (em x, fun z => l.flatMap fun x => em x z) ∈ A := by
          rw [Finset.mem_filter, mem_anti]
          exact ⟨fun z => congrFun h z, hne x⟩
        exact ⟨_, hp, (hf1 _ _).2 rfl, ((hRs _ hp).1 _).2 rfl⟩
    let C : Finset (List X) := B.map ⟨fun p => p.1 :: p.2, by rintro ⟨a, b⟩ ⟨c, d⟩ h; simpa using h⟩
    have hC : ∀ l, l ∈ C ↔ l ≠ [] ∧ (fun z => l.flatMap fun x => em x z) = v := by
      intro l
      simp only [C, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.exists]
      constructor
      · rintro ⟨x, l', h, rfl⟩
        exact ⟨by simp, by rw [hB] at h; exact h⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil h1
        exact ⟨x, l', (hB _ _).2 (by simpa using h2), rfl⟩
    refine ⟨(if v = fun _ => [] then {[]} else ∅) ∪ C, ?_, ?_⟩
    · intro l
      rw [Finset.mem_union, hC]
      by_cases hl : l = []
      · subst hl
        by_cases h : v = fun _ => []
        · simp [h]
        · simp [h, Ne.symm h]
      · by_cases h : v = fun _ => []
        · simp [h, hl]
        · simp [h, hl]
    · rw [Finset.sum_union]
      · rw [hat_kstar]
        congr 1
        · split_ifs <;> simp
        · simp only [C, Finset.sum_map, Function.Embedding.coeFn_mk, List.map_cons, List.prod_cons]
          simp only [B]
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun p hp => ?_
            rw [hf2, (hRs p hp).2, Finset.sum_mul_sum, Finset.sum_product]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              (List.prod_cons (l := j.map wt) (a := wt i)).symm
          · intro p hp q hq hpq
            rw [Function.onFun, Finset.disjoint_left]
            rintro ⟨x, y⟩ h h'
            rw [Finset.mem_product, hf1] at h h'
            rw [(hRs p hp).1] at h
            rw [(hRs q hq).1] at h'
            exact hpq (Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))
      · rw [Finset.disjoint_left]
        intro l hl hl'
        rw [hC] at hl'
        split_ifs at hl <;> simp at hl
        exact hl'.1 hl

/-- The word on the channels, channel by channel. -/
noncomputable def chanWord (w : Z → List Γ) : List (Z × Γ) :=
  (univ : Finset Z).toList.flatMap fun z => (w z).map fun a => (z, a)

theorem proj_flatMap {ι : Type*} (l : List ι) (g : ι → List (Z × Γ)) (z : Z) :
    proj (l.flatMap g) z = l.flatMap fun i => proj (g i) z := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, proj_append, ih]

theorem proj_map_mk (z z' : Z) (w : List Γ) :
    proj (w.map fun a => (z, a)) z' = if z = z' then w else [] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, proj_cons, ih]
    split_ifs <;> rfl

theorem flatMap_ite_eq {ι β : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (i : ι) (hi : i ∈ l)
    (g : ι → List β) : (l.flatMap fun j => if j = i then g j else []) = g i := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hl
    by_cases h : a = i
    · subst h
      have : (l.flatMap fun j => if j = a then g j else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro j hj
        rw [if_neg]
        rintro rfl
        exact hl.1 hj
      simp [this]
    · rw [if_neg h, List.nil_append]
      exact ih hl.2 (by simpa [Ne.symm h] using hi)

theorem proj_chanWord (w : Z → List Γ) : proj (chanWord w) = w := by
  funext z
  rw [chanWord, proj_flatMap]
  have : (fun i => proj ((w i).map fun a => (i, a)) z) = fun i => if i = z then w i else [] := by
    funext i; rw [proj_map_mk]
  rw [this]
  exact flatMap_ite_eq _ (Finset.nodup_toList _) z (by simp) w

theorem length_chanWord (w : Z → List Γ) : (chanWord w).length = ∑ z, (w z).length := by
  rw [← sum_length_proj, proj_chanWord]

namespace Runs

theorem mono {n m : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F} (h : Runs n em wt) (hm : n ≤ m) :
    Runs m em wt := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.mono hm, h2⟩

theorem congr {n : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (h : Runs n em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) : Runs n em' wt' := by
  obtain ⟨P, g1, g2⟩ := h
  exact ⟨P, g1, g2.congr e h1 h2⟩

theorem mul {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (fun (x : X × Y) z => em x.1 z ++ em' x.2 z) (fun x => wt x.1 * wt' x.2) := by
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  exact ⟨_, g1.mul g3, g2.mul g4⟩

theorem sum {ι : Type*} [Fintype ι] {n : ι → ℕ} {X : ι → Type*} {em : ∀ i, X i → Z → List Γ}
    {wt : ∀ i, X i → F} (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  choose P h1 h2 using h
  exact ⟨∑ i, P i, RatLe.sum _ _ _ fun i _ => h1 i, IsRuns.sum h2⟩

theorem add {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (Sum.elim em em') (Sum.elim wt wt') := by
  classical
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  refine ⟨P + Q, g1.add g3, fun v => ?_⟩
  obtain ⟨R, h1, h2⟩ := g2 v
  obtain ⟨R', h3, h4⟩ := g4 v
  refine ⟨R.disjSum R', ?_, ?_⟩
  · rintro (x | x)
    · simp [h1]
    · simp [h3]
  · rw [hat_add, h2, h4, Finset.sum_disjSum]
    simp

theorem kstar {n : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F} (hf : Runs n em wt)
    (hne : ∀ x, ∃ z, em x z ≠ []) :
    Runs (n + 1) (fun (l : List X) z => l.flatMap fun x => em x z) (fun l => (l.map wt).prod) := by
  obtain ⟨P, g1, g2⟩ := hf
  refine ⟨_, g1.kstar, g2.kstar fun x h => ?_⟩
  obtain ⟨z, hz⟩ := hne x
  exact hz (congrFun h z)

theorem one : Runs 1 (fun (_ : Unit) (_ : Z) => ([] : List Γ)) (fun _ => (1 : F)) :=
  ⟨_, RatLe.one, IsRuns.one⟩

/-- One of finitely many families of words, with weights. -/
theorem pick {κ : Type*} [Fintype κ] (w : κ → Z → List Γ) (c : κ → F) :
    Runs (∑ k, (2 * ∑ z, (w k z).length + 1)) w c := by
  classical
  refine ⟨Series.body (fun k => chanWord (w k)) c, ?_, fun v => ?_⟩
  · have := RatLe.body (F := F) (fun k => chanWord (w k)) c
    simpa only [length_chanWord] using this
  · refine ⟨univ.filter fun k => w k = v, by simp, ?_⟩
    rw [hat_body, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [proj_chanWord]
    by_cases h : w k = v
    · simp [h]
    · simp [h, Ne.symm h]

/-- Fixed words. -/
theorem const (w : Z → List Γ) :
    Runs (2 * ∑ z, (w z).length + 1) (fun (_ : Unit) => w) (fun _ => (1 : F)) := by
  have := pick (F := F) (fun _ : Unit => w) (fun _ => 1)
  simpa using this

/-- A sequence of choices. -/
theorem pi {k : ℕ} {n : Fin k → ℕ} {X : Fin k → Type*} {em : ∀ i, X i → Z → List Γ}
    {wt : ∀ i, X i → F} (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i + 1) (fun (x : ∀ i, X i) z => (List.ofFn fun i => em i (x i) z).flatten)
      (fun x => ∏ i, wt i (x i)) := by
  induction k with
  | zero =>
    refine Runs.mono (n := 1) ((one (F := F) (Z := Z) (Γ := Γ)).congr
      ⟨fun _ => (), fun _ i => i.elim0, fun x => ?_, fun _ => rfl⟩ ?_ ?_) (by omega)
    · funext i; exact i.elim0
    · intro y z; simp
    · intro y; simp
  | succ k ih =>
    have h1 := (h 0).mul (ih (n := fun i => n i.succ) (X := fun i => X i.succ) (em := fun i => em i.succ)
      (wt := fun i => wt i.succ) fun i => h i.succ)
    refine (h1.congr (Fin.consEquiv X).symm ?_ ?_).mono ?_
    · intro y z
      simp [Fin.consEquiv, List.ofFn_succ, Fin.tail]
    · intro y
      simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]
    · rw [Fin.sum_univ_succ]; omega

end Runs

end Nc
end

/-! Source module: Nc.Sort.RunVal -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The value of a program given by its runs
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J] {X : Type*}

/-- The run puts the same word on both sides of every tape, and the inputs are u. -/
def Mt (em : X → Ch S J → List Γ) (u : J → List Γ) (x : X) : Prop :=
  (∀ s, em x (.tp s false) = em x (.tp s true)) ∧ ∀ j, em x (.inp j) = u j

theorem Mt.eq_tup {em : X → Ch S J → List Γ} {u : J → List Γ} {x : X} (h : Mt em u x) :
    em x = tup (fun s => em x (.tp s true)) u := by
  funext z
  match z with
  | .tp s false => exact h.1 s
  | .tp s true => rfl
  | .inp j => exact h.2 j

theorem Mt.of_tup {em : X → Ch S J → List Γ} {u : J → List Γ} {x : X} {W : S → List Γ}
    (h : em x = tup W u) : Mt em u x ∧ (fun s => em x (.tp s true)) = W := by
  refine ⟨⟨fun s => ?_, fun j => ?_⟩, ?_⟩
  · rw [h]; rfl
  · rw [h]; rfl
  · funext s; rw [h]; rfl

theorem IsRuns.val_eq {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) (t : ℕ) (u : J → List Γ) (R : Finset X)
    (hR : ∀ x, x ∈ R ↔ Mt em u x ∧ ∑ s, (em x (.tp s true)).length ≤ t) :
    val t P u = ∑ x ∈ R, wt x := by
  classical
  rw [val, ← Finset.sum_fiberwise_of_maps_to (s := R) (t := contents S Γ t)
    (g := fun x s => em x (.tp s true))]
  · refine Finset.sum_congr rfl fun W hW => ?_
    refine h.of_fib _ fun x => ?_
    rw [Finset.mem_filter, hR]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h1.eq_tup, h3]
    · intro h1
      obtain ⟨h2, h3⟩ := Mt.of_tup h1
      refine ⟨⟨h2, ?_⟩, h3⟩
      rw [mem_contents, ← h3] at hW
      exact hW
  · intro x hx
    rw [mem_contents]
    exact ((hR x).1 hx).2

theorem IsRuns.exists_mt {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {u : J → List Γ} {W : S → List Γ} (hW : hat P (tup W u) ≠ 0) :
    ∃ x, Mt em u x ∧ (fun s => em x (.tp s true)) = W := by
  obtain ⟨x, hx, -⟩ := h.exists_run hW
  exact ⟨x, Mt.of_tup hx⟩

theorem IsRuns.bdd {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {u : J → List Γ} {t : ℕ}
    (ht : ∀ x, Mt em u x → ∑ s, (em x (.tp s true)).length ≤ t) : Bdd t P u := by
  intro W hW
  obtain ⟨x, hx, rfl⟩ := h.exists_mt hW
  exact ht x hx

end Nc
end

/-! Source module: Nc.Sort.Words -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Words on several channels; codes; choices of letters
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

section Codes

variable {κ Γ : Type*}

theorem flatMap_inj {f : κ → List Γ} (hne : ∀ a, f a ≠ [])
    (hf : ∀ a b u v, f a ++ u = f b ++ v → a = b) :
    Function.Injective fun l : List κ => l.flatMap f := by
  intro l
  induction l with
  | nil =>
    rintro (_ | ⟨b, l'⟩) h
    · rfl
    · simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h.symm).1 (hne b)
  | cons a l ih =>
    rintro (_ | ⟨b, l'⟩) h
    · simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h).1 (hne a)
    · simp only [List.flatMap_cons] at h
      obtain rfl := hf a b _ _ h
      rw [ih (List.append_cancel_left h)]

theorem flatten_ofFn_single {k : ℕ} (i : Fin k) (w : Fin k → List Γ) (h : ∀ j, j ≠ i → w j = []) :
    (List.ofFn w).flatten = w i := by
  have h1 : (List.ofFn w).flatten = (List.finRange k).flatMap fun j => if j = i then w j else [] := by
    rw [List.ofFn_eq_map, ← List.flatMap_def]
    refine List.flatMap_congr fun j _ => ?_
    by_cases e : j = i
    · simp [e]
    · simp [e, h j e]
  rw [h1]
  exact flatMap_ite_eq _ (List.nodup_finRange k) i (List.mem_finRange i) w

theorem flatten_ofFn_nil {k : ℕ} (w : Fin k → List Γ) (h : ∀ j, w j = []) : (List.ofFn w).flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
  exact h j

end Codes

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The word w on every channel of zs. -/
def on (zs : Finset Z) (w : List Γ) : Z → List Γ := fun z => if z ∈ zs then w else []

theorem on_append (zs : Finset Z) (w w' : List Γ) (z : Z) : on zs w z ++ on zs w' z = on zs (w ++ w') z := by
  unfold on; split_ifs <;> simp

theorem flatMap_on {κ : Type*} (zs : Finset Z) (f : κ → List Γ) (l : List κ) (z : Z) :
    (l.flatMap fun k => on zs (f k) z) = on zs (l.flatMap f) z := by
  unfold on
  split_ifs
  · rfl
  · simp

theorem sum_on (zs : Finset Z) (w : List Γ) : ∑ z, (on zs w z).length = zs.card * w.length := by
  unfold on
  simp only [apply_ite List.length, List.length_nil]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]

namespace Runs

/-- Choose a letter and write it on the channels of zs. -/
theorem letter {κ : Type*} [Fintype κ] (zs : Finset Z) (f : κ → Γ) (c : κ → F) :
    Runs (Fintype.card κ * (2 * zs.card + 1)) (fun k => on zs [f k]) c := by
  refine (pick (fun k => on zs [f k]) c).mono ?_
  simp [sum_on]

/-- A fixed word on the channels of zs. -/
theorem word (zs : Finset Z) (w : List Γ) :
    Runs (2 * (zs.card * w.length) + 1) (fun _ : Unit => on zs w) (fun _ => (1 : F)) := by
  refine (const (on zs w)).mono ?_
  rw [sum_on]

end Runs

end Nc
end

/-! Source module: Nc.Uni.Alpha -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Letters and tapes of the universal program; loops over letters
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

section Star

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- Any word over a set of letters, written on the channels of zs. -/
theorem Runs.wordstar {κ : Type*} [Fintype κ] (zs : Finset Z) (hz : zs.Nonempty) (f : κ → Γ) :
    Runs (Fintype.card κ * (2 * zs.card + 1) + 1) (fun l : List κ => on zs (l.map f)) (fun _ => (1 : F)) := by
  obtain ⟨z₀, hz₀⟩ := hz
  have h := (Runs.letter (F := F) zs f fun _ => 1).kstar fun k => ⟨z₀, by simp [on, hz₀]⟩
  refine h.congr (Equiv.refl _) (fun l z => ?_) fun l => by simp
  rw [Equiv.refl_apply, flatMap_on]
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih, List.map_cons]; rfl

end Star

end Nc

namespace Nc.Uni

/-- Letters: bits, end of a word, modes, kinds of records, columns of records, mark, end of a record, flags, end of a
block. -/
inductive Sy (M K : Type) where
  | bit (x : Bool)
  | semi
  | md (m : M)
  | kd (k : K)
  | col (c : Fin 4 → Bool)
  | mark
  | dot
  | flag (f : Bool)
  | bar
  deriving DecidableEq, Fintype

/-- Letters of records. -/
abbrev Bl (K : Type) := K ⊕ (Fin 4 → Bool)

variable {M K : Type}

/-- Letters of records as letters. -/
def be : Bl K → Sy M K
  | .inl k => .kd k
  | .inr c => .col c

/-- Letters of records and the mark. -/
def ol : Option (Bl K) → Sy M K
  | none => .mark
  | some b => be b

theorem ol_inj : Function.Injective (ol : Option (Bl K) → Sy M K) := by
  rintro (_ | (a | a)) (_ | (b | b)) h <;> simp [ol, be] at h <;> simp [h]

theorem ol_ne_dot (o : Option (Bl K)) : (ol o : Sy M K) ≠ .dot := by
  rcases o with _ | (a | a) <;> simp [ol, be]

theorem ol_ne_bar (o : Option (Bl K)) : (ol o : Sy M K) ≠ .bar := by
  rcases o with _ | (a | a) <;> simp [ol, be]

/-- Tapes: registers, modes, counter, fresh addresses, lookups, the list, buckets, copies. -/
inductive Tp (K : Type) where
  | rg (i : Fin 5)
  | md
  | cp
  | fr
  | lk
  | ls
  | bk (b : Bl K)
  | cm (k : Bool)
  deriving DecidableEq, Fintype

/-- Channels. -/
abbrev Zc (K : Type) := Ch (Tp K) Unit

end Nc.Uni
end

/-! Source module: Nc.Uni.SortU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sorting loop
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- The list tape, read. -/
abbrev lsT : Zc K := .tp .ls true
/-- The list tape, written. -/
abbrev lsF : Zc K := .tp .ls false

/-- A record on the list: flag, letters and mark, end. -/
def rw' (f : Bool) (w : List (Option (Bl K))) : List (Sy M K) := .flag f :: (w.map ol ++ [.dot])

/-- Letters other than the end of a block. -/
abbrev NB (M K : Type) := {γ : Sy M K // γ ≠ .bar}

/-- Rounds of the distribution: flag, first letter, the others. -/
abbrev Dr (K : Type) := Bool × Bl K × List (Option (Bl K))

/-- Emissions of a round of the distribution. -/
def emDr (d : Dr K) : Zc K → List (Sy M K) := fun z =>
  on {lsT} (rw' d.1 (some d.2.1 :: d.2.2)) z ++ on {.tp (.bk d.2.1) false} (rw' d.1 (d.2.2 ++ [some d.2.1])) z

theorem runs_dr : Runs (Fintype.card (Bl K) * (10 + 3 + (Fintype.card (Option (Bl K)) * 5 + 1) + 7))
    (emDr : Dr K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := Runs.sum (F := A) fun b : Bl K =>
    (((Runs.letter (F := A) (Z := Zc K) {lsT, .tp (.bk b) false} (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.word (F := A) {lsT} [(be b : Sy M K)])).mul
    (Runs.wordstar (F := A) {lsT, .tp (.bk b) false} ⟨lsT, by simp⟩ (ol : Option (Bl K) → Sy M K))).mul
    (Runs.const (F := A) fun z : Zc K => on {lsT} [(Sy.dot : Sy M K)] z ++ on {.tp (.bk b) false} [be b, Sy.dot] z)
  refine (h.congr ⟨fun d => ⟨d.2.1, (((d.1, ()), d.2.2), ())⟩, fun y => (y.2.1.1.1, y.1, y.2.1.2), fun d => rfl,
    fun y => rfl⟩ (fun d z => ?_) fun d => by simp).mono ?_
  · obtain ⟨f, b, w⟩ := d
    simp only [Equiv.coe_fn_mk, emDr, rw']
    by_cases h1 : z = lsT
    · subst h1
      simp [on, ol]
    · by_cases h2 : z = .tp (.bk b) false
      · subst h2
        simp [on, ol]
      · simp [on, h1, h2]
  · have hc : ∀ b : Bl K, ({lsT, .tp (.bk b) false} : Finset (Zc K)).card = 2 := fun b => Finset.card_pair (by simp)
    simp only [hc, List.length_append, Finset.sum_add_distrib, sum_on]
    simp
    ring_nf
    omega

/-- The channels where a pass of the distribution ends a block. -/
def barSet : Finset (Zc K) := insert lsT (univ.image fun b : Bl K => (.tp (.bk b) false : Zc K))

/-- Runs of a pass. -/
abbrev Ps (M K : Type) := List (Dr K) × (Bl K → List (NB M K))

/-- The letters of records, in some order. -/
noncomputable def bsl (K : Type) [Fintype K] [DecidableEq K] : List (Bl K) := List.ofFn (Fintype.equivFin (Bl K)).symm

theorem mem_bsl (b : Bl K) : b ∈ bsl K := by
  rw [bsl, List.mem_ofFn]
  exact ⟨Fintype.equivFin (Bl K) b, by simp⟩

theorem bsl_nodup : (bsl K).Nodup := by
  rw [bsl, List.nodup_ofFn]
  exact Equiv.injective _

/-- Emissions of the collection. -/
noncomputable def emCo (m : Bl K → List (NB M K)) : Zc K → List (Sy M K) := fun z =>
  (List.ofFn fun i => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) z ++
    on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z).flatten ++ on {lsF} [Sy.bar] z

theorem runs_co : Runs (Fintype.card (Bl K) * (Fintype.card (Sy M K) * 5 + 1 + 3) + 1 + 3)
    (emCo : (Bl K → List (NB M K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h0 : ∀ i : Fin (Fintype.card (Bl K)), Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
      (fun (w : List (NB M K)) (z : Zc K) => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
        (w.map Subtype.val) z ++ on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z)
      (fun _ => (1 : A)) := by
    intro i
    have h1 := (Runs.wordstar (F := A) (Z := Zc K) {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ⟨lsF, by simp⟩ (Subtype.val : NB M K → Sy M K)).mul
      (Runs.word (F := A) (Z := Zc K) {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)])
    refine (h1.congr ⟨fun w => (w, ()), Prod.fst, fun w => rfl, fun y => rfl⟩ (fun w z => rfl) fun w => by simp).mono ?_
    have hc : ({.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF} : Finset (Zc K)).card = 2 :=
      Finset.card_pair (by simp)
    have hs : Fintype.card (NB M K) ≤ Fintype.card (Sy M K) := Fintype.card_subtype_le _
    rw [hc, Finset.card_singleton, List.length_singleton]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hs) 1) (by norm_num)
  have h := (Runs.pi h0).mul (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr ⟨fun m => ((fun i => m ((Fintype.equivFin (Bl K)).symm i)), ()),
    fun y b => y.1 (Fintype.equivFin (Bl K) b), fun m => by simp, fun y => by simp⟩ (fun m z => rfl) fun m => ?_).mono ?_
  · simp
  · simp

/-- Emissions of a pass. -/
noncomputable def emPs (p : Ps M K) : Zc K → List (Sy M K) := fun z =>
  (p.1.flatMap fun d => emDr d z) ++ (on barSet [Sy.bar] z ++ emCo p.2 z)

/-- Dimension of a pass. -/
def dimPs (m k : ℕ) : ℕ := (k * (10 + 3 + ((k + 1) * 5 + 1) + 7) + 1) + ((2 * (k + 1) + 1) + (k * (m * 5 + 1 + 3) + 1 + 3))

theorem emDr_ne (d : Dr K) : ∃ z, (emDr d : Zc K → List (Sy M K)) z ≠ [] := ⟨lsT, by simp [emDr, on, rw']⟩

theorem card_barSet : (barSet : Finset (Zc K)).card ≤ Fintype.card (Bl K) + 1 := by
  unfold barSet
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  exact Finset.card_image_le

theorem runs_ps : Runs (dimPs (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
    (emPs : Ps M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := ((runs_dr (A := A) (M := M) (K := K)).kstar fun d => emDr_ne d).mul
    ((Runs.word (F := A) (Z := Zc K) barSet [(Sy.bar : Sy M K)]).mul (runs_co (A := A) (M := M) (K := K)))
  refine (h.congr ⟨fun p => (p.1, (), p.2), fun y => (y.1, y.2.2), fun p => rfl, fun y => rfl⟩ (fun p z => rfl)
    fun p => ?_).mono ?_
  · simp
  · have := card_barSet (K := K)
    unfold dimPs
    rw [Fintype.card_option]
    simp only [List.length_singleton, mul_one]
    omega

/-- Emissions of the last reading: the marks are in front and are dropped. -/
def emFi (l : List (Bool × List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  (l.flatMap fun d => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) ++ on {lsT} [Sy.bar] z

theorem runs_fi : Runs (14 + 3 + (Fintype.card (Bl K) * 7 + 1) + 7 + 1 + 3)
    (emFi : List (Bool × List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({lsT, .tp (.cm false) false, .tp (.cm true) false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have h1 := (((Runs.letter (F := A) (Z := Zc K) {lsT, .tp (.cm false) false, .tp (.cm true) false}
      (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.word (F := A) {lsT} [(Sy.mark : Sy M K)])).mul
    (Runs.wordstar (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false} ⟨lsT, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.word (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false} [(Sy.dot : Sy M K)])
  have h2 := h1.congr (em' := fun (d : Bool × List (Bl K)) z => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) (wt' := fun _ => 1)
    ⟨fun d => (((d.1, ()), d.2), ()), fun y => (y.1.1.1, y.1.2), fun d => rfl, fun y => rfl⟩ (fun d z => by
      obtain ⟨f, w⟩ := d
      have hw : (w.map some).map (ol : Option (Bl K) → Sy M K) = w.map be := by
        rw [List.map_map]; rfl
      simp only [Equiv.coe_fn_mk, rw', List.map_cons, hw]
      by_cases h1 : z = lsT
      · subst h1
        simp [on, ol]
      · by_cases h2 : z = .tp (.cm false) false
        · subst h2
          simp [on]
        · by_cases h3 : z = .tp (.cm true) false
          · subst h3
            simp [on]
          · simp [on, h1, h2, h3]) (fun d => by simp)
  have h3 := (h2.kstar fun d => ⟨lsT, by simp [on, rw']⟩).mul (Runs.word (F := A) (Z := Zc K) {lsT} [(Sy.bar : Sy M K)])
  refine (h3.congr ⟨fun l => (l, ()), Prod.fst, fun l => rfl, fun y => rfl⟩ (fun l z => rfl) fun l => by simp).mono ?_
  rw [hc]
  simp

end Nc.Uni
end

/-! Source module: Nc.Sort.Radix -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Radix sort and the check of neighbours

Records are pairs of a flag (false: entry of the table, true: lookup) and a key of n letters. After one pass
for every letter, records with equal keys are neighbours, in the original order. So every lookup has the key of
an entry of the table before it if and only if, after sorting, every lookup has the same key as the record
before it.
-/

set_option linter.unusedSectionVars false

namespace Nc.Sort

variable {n : ℕ} {B : Type*} [DecidableEq B]

/-- A record: a flag and a key. -/
abbrev Rc (n : ℕ) (B : Type*) := Bool × (Fin n → B)

/-- One pass: distribute by letter j, collect. -/
def pass (bs : List B) (j : Fin n) (l : List (Rc n B)) : List (Rc n B) :=
  bs.flatMap fun b => l.filter fun r => r.2 j = b

/-- The list after the first j passes. -/
def srt (bs : List B) (l : List (Rc n B)) : ℕ → List (Rc n B)
  | 0 => l
  | j + 1 => if h : j < n then pass bs ⟨j, h⟩ (srt bs l j) else srt bs l j

/-- The keys of length j, in the order of the sort. -/
def keys (bs : List B) : ℕ → List (List B)
  | 0 => [[]]
  | j + 1 => bs.flatMap fun b => (keys bs j).map fun k => k ++ [b]

theorem mem_keys {bs : List B} (hbs : ∀ b, b ∈ bs) (j : ℕ) (k : List B) : k ∈ keys bs j ↔ k.length = j := by
  induction j generalizing k with
  | zero => simp [keys]
  | succ j ih =>
    simp only [keys, List.mem_flatMap, List.mem_map, ih]
    constructor
    · rintro ⟨b, -, k, rfl, rfl⟩
      simp
    · intro h
      rcases List.eq_nil_or_concat k with rfl | ⟨k', b, rfl⟩
      · simp at h
      · exact ⟨b, hbs b, k', by simpa using h, by simp⟩

theorem keys_nodup {bs : List B} (hn : bs.Nodup) (j : ℕ) : (keys bs j).Nodup := by
  induction j with
  | zero => simp [keys]
  | succ j ih =>
    rw [keys, List.nodup_flatMap]
    refine ⟨fun b _ => ih.map fun a b h => by simpa using h, ?_⟩
    refine List.Pairwise.imp ?_ hn
    intro b b' hne
    rw [Function.onFun, List.disjoint_left]
    intro k hk hk'
    simp only [List.mem_map] at hk hk'
    obtain ⟨a, -, rfl⟩ := hk
    obtain ⟨a', -, h⟩ := hk'
    have := List.append_inj' h rfl
    simp at this
    exact hne this.2.symm

theorem srt_eq (bs : List B) (l : List (Rc n B)) (j : ℕ) (hj : j ≤ n) :
    srt bs l j = (keys bs j).flatMap fun k => l.filter fun r => (List.ofFn r.2).take j = k := by
  induction j with
  | zero => simp [srt, keys]
  | succ j ih =>
    have hlt : j < n := hj
    rw [srt, dif_pos hlt, ih hlt.le, pass, keys, List.flatMap_assoc]
    refine List.flatMap_congr fun b _ => ?_
    rw [List.filter_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun k hk => ?_
    rw [List.filter_filter]
    refine List.filter_congr fun r _ => ?_
    have h1 : (List.ofFn r.2).take (j + 1) = (List.ofFn r.2).take j ++ [r.2 ⟨j, hlt⟩] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hlt)]
      simp
    rw [h1]
    by_cases e1 : (List.ofFn r.2).take j = k
    · subst e1; simp
    · have : ¬ ((List.ofFn r.2).take j ++ [r.2 ⟨j, hlt⟩] = k ++ [b]) := by
        intro h
        exact e1 (List.append_inj' h rfl).1
      simp [e1, this]

/-- The check of neighbours. -/
def chk : Option (Fin n → B) → List (Rc n B) → Prop
  | _, [] => True
  | p, r :: l => (r.1 = false ∨ p = some r.2) ∧ chk (some r.2) l

/-- The first record of the list is an entry of the table. -/
def headOk : List (Rc n B) → Prop
  | [] => True
  | r :: _ => r.1 = false

theorem chk_same (k : Fin n → B) (g l : List (Rc n B)) (hg : ∀ r ∈ g, r.2 = k) :
    chk (some k) (g ++ l) ↔ chk (some k) l := by
  induction g with
  | nil => rfl
  | cons r g ih =>
    have : r.2 = k := hg r (by simp)
    rw [List.cons_append, chk, this]
    simp [ih fun r hr => hg r (by simp [hr])]

theorem chk_groups (K : List (Fin n → B)) (hK : K.Nodup) (g : (Fin n → B) → List (Rc n B))
    (hg : ∀ k, ∀ r ∈ g k, r.2 = k) (p : Option (Fin n → B)) (hp : ∀ k ∈ K, p ≠ some k) :
    chk p (K.flatMap g) ↔ ∀ k ∈ K, headOk (g k) := by
  induction K generalizing p with
  | nil => simp [chk]
  | cons k K ih =>
    rw [List.nodup_cons] at hK
    rw [List.flatMap_cons, List.forall_mem_cons]
    rcases hgk : g k with _ | ⟨r, g'⟩
    · rw [List.nil_append, ih hK.2 p fun k' hk' => hp k' (by simp [hk'])]
      simp [headOk]
    · have hr : r.2 = k := hg k r (by simp [hgk])
      have hpk := hp k (by simp)
      rw [List.cons_append, chk, hr, chk_same k _ _ fun r' hr' => hg k r' (by simp [hgk, hr']),
        ih hK.2 (some k) fun k' hk' h => hK.1 (by
          have := Option.some_injective _ h
          rwa [this])]
      simp [headOk, hpk]

theorem flatMap_pmap_eq {α β γ : Type*} {P : α → Prop} (f : ∀ a, P a → β) (g : β → List γ)
    (g' : α → List γ) (l : List α) (H : ∀ a ∈ l, P a) (h : ∀ a (ha : P a), g (f a ha) = g' a) :
    (l.pmap f H).flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.pmap_cons, List.flatMap_cons, List.flatMap_cons, h, ih]

theorem chk_srt {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (l : List (Rc n B)) :
    chk none (srt bs l n) ↔ ∀ k, headOk (l.filter fun r => r.2 = k) := by
  have e : srt bs l n = ((keys bs n).pmap (fun k (hk : k.length = n) => fun i : Fin n => k.get (i.cast hk.symm))
      fun k hk => (mem_keys hbs n k).1 hk).flatMap fun k => l.filter fun r => r.2 = k := by
    rw [srt_eq bs l n le_rfl]
    symm
    refine flatMap_pmap_eq _ _ _ _ _ fun k hk => List.filter_congr fun r _ => ?_
    have : r.2 = (fun i : Fin n => k.get (i.cast hk.symm)) ↔ (List.ofFn r.2).take n = k := by
      rw [List.take_of_length_le (by simp)]
      subst hk
      constructor
      · intro h
        rw [h]
        exact List.ofFn_get k
      · intro h
        funext i
        have h2 : (List.ofFn r.2).get (i.cast (by simp)) = r.2 i := by simp
        rw [← h2, List.get_of_eq h]
        rfl
    simp only [this]
  rw [e, chk_groups]
  · constructor
    · intro h k
      refine h k ?_
      rw [List.mem_pmap]
      refine ⟨List.ofFn k, (mem_keys hbs _ _).2 (by simp), ?_⟩
      funext i
      simp
    · intro h k _
      exact h k
  · refine List.Nodup.pmap ?_ (keys_nodup hn n)
    intro a ha b hb h
    refine List.ext_get (by rw [ha, hb]) fun i h1 h2 => ?_
    have := congrFun h ⟨i, ha ▸ h1⟩
    simpa using this
  · intro k r hr
    simpa using (List.mem_filter.1 hr).2
  · intro k _
    simp

/-- First the table, then the lookups: the check succeeds if and only if every lookup is in the table. -/
theorem chk_table {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (T L : List (Fin n → B)) :
    chk none (srt bs (T.map (fun x => (false, x)) ++ L.map fun x => (true, x)) n) ↔ ∀ x ∈ L, x ∈ T := by
  rw [chk_srt hbs hn]
  have h1 : ∀ k, (T.map (fun x => ((false, x) : Rc n B)) ++ L.map fun x => (true, x)).filter
      (fun r => r.2 = k) = (T.filter (· = k)).map (fun x => (false, x)) ++
        (L.filter (· = k)).map fun x => (true, x) := by
    intro k
    rw [List.filter_append, List.filter_map, List.filter_map]
    rfl
  simp only [h1]
  constructor
  · intro h x hx
    have := h x
    by_contra hT
    have e : T.filter (· = x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp only [decide_eq_true_eq]
      rintro rfl
      exact hT ha
    have hx' : x ∈ L.filter (· = x) := by simp [hx]
    rw [e] at this
    rcases hL : L.filter (· = x) with _ | ⟨a, l⟩
    · rw [hL] at hx'; simp at hx'
    · rw [hL] at this
      simp [headOk] at this
  · intro h k
    rcases hT : T.filter (· = k) with _ | ⟨a, l⟩
    · have : L.filter (· = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [decide_eq_true_eq]
        rintro rfl
        have := h a ha
        have h2 : a ∈ T.filter (· = a) := by simp [this]
        rw [hT] at h2
        simp at h2
      simp [this, headOk]
    · simp [headOk]

theorem sum_filter [Fintype B] (j : Fin n) (l : List (Rc n B)) :
    ∑ b, (l.filter fun r => r.2 j = b).length = l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have : ∀ b, ((r :: l).filter fun r => r.2 j = b).length =
        (if r.2 j = b then 1 else 0) + (l.filter fun r => r.2 j = b).length := by
      intro b
      rw [List.filter_cons]
      by_cases h : r.2 j = b
      · simp [h, add_comm]
      · simp [h]
    simp only [this, Finset.sum_add_distrib, ih]
    simp [add_comm]

theorem length_pass [Fintype B] {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (j : Fin n)
    (l : List (Rc n B)) : (pass bs j l).length = l.length := by
  rw [pass, List.length_flatMap, ← List.sum_toFinset _ hn]
  have : bs.toFinset = Finset.univ := by ext b; simp [hbs]
  rw [this, sum_filter]

theorem length_srt [Fintype B] {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup)
    (l : List (Rc n B)) (j : ℕ) : (srt bs l j).length = l.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [srt]
    split_ifs with h
    · rw [length_pass hbs hn, ih]
    · exact ih

end Nc.Sort
end

/-! Source module: Nc.Uni.CmpU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The comparison of neighbours
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

section Pure

variable {κ : Type*}

/-- The check of neighbours. -/
def chkG : Option κ → List (Bool × κ) → Prop
  | _, [] => True
  | p, r :: l => (r.1 = false ∨ p = some r.2) ∧ chkG (some r.2) l

theorem chkG_map {n : ℕ} {B κ : Type*} (φ : (Fin n → B) → κ) (hφ : Function.Injective φ)
    (p : Option (Fin n → B)) (l : List (Sort.Rc n B)) :
    chkG (p.map φ) (l.map fun r => (r.1, φ r.2)) ↔ Sort.chk p l := by
  induction l generalizing p with
  | nil => simp [chkG, Sort.chk]
  | cons r l ih =>
    rw [List.map_cons, chkG, Sort.chk]
    have h1 := ih (some r.2)
    rw [Option.map_some] at h1
    rw [h1]
    refine and_congr (or_congr Iff.rfl ?_) Iff.rfl
    rcases p with _ | q
    · simp
    · simp [hφ.eq_iff]

/-- Rounds of the comparison. -/
abbrev RdG (κ : Type*) := ((Bool × κ) × κ) ⊕ (Bool × κ)

/-- The record read on the second copy. -/
def RdG.fst : RdG κ → Bool × κ
  | .inl (r, _) => r
  | .inr r => r

/-- The record read on the first copy: the next one. -/
def RdG.snd : RdG κ → Bool × κ
  | .inl (_, x) => (false, x)
  | .inr r => (true, r.2)

theorem RdG.ext {d d' : RdG κ} (h1 : d.fst = d'.fst) (h2 : d.snd = d'.snd) : d = d' := by
  rcases d with ⟨r, x⟩ | r <;> rcases d' with ⟨r', x'⟩ | r' <;> simp_all [RdG.fst, RdG.snd]

theorem RdG.exists_iff (r r' : Bool × κ) :
    (∃ d : RdG κ, d.fst = r ∧ d.snd = r') ↔ (r'.1 = false ∨ some r.2 = some r'.2) := by
  constructor
  · rintro ⟨⟨r, x⟩ | r, rfl, rfl⟩ <;> simp [RdG.fst, RdG.snd]
  · rcases r' with ⟨f, x⟩
    rintro (h | h)
    · simp only at h
      subst h
      exact ⟨.inl (r, x), rfl, rfl⟩
    · simp only [Option.some.injEq] at h
      subst h
      cases f
      · exact ⟨.inl (r, r.2), rfl, rfl⟩
      · exact ⟨.inr r, rfl, rfl⟩

theorem cmpG_iff (r : Bool × κ) (l : List (Bool × κ)) :
    (∃ (ds : List (RdG κ)) (r' : Bool × κ), ds.map RdG.snd = l ∧ ds.map RdG.fst ++ [r'] = r :: l) ↔
      chkG (some r.2) l := by
  induction l generalizing r with
  | nil =>
    simp only [chkG, iff_true]
    exact ⟨[], r, rfl, rfl⟩
  | cons a l ih =>
    rw [chkG, ← ih, ← RdG.exists_iff]
    constructor
    · rintro ⟨_ | ⟨d, ds⟩, r', h1, h2⟩
      · simp at h1
      · simp only [List.map_cons, List.cons.injEq, List.cons_append] at h1 h2
        exact ⟨⟨d, h2.1, h1.1⟩, ds, r', h1.2, h2.2⟩
    · rintro ⟨⟨d, h1, h2⟩, ds, r', h3, h4⟩
      exact ⟨d :: ds, r', by simp [h2, h3], by simp [h1, h4]⟩

/-- Runs of the comparison. -/
abbrev XG (κ : Type*) := κ × List (RdG κ) × (Bool × κ)

/-- The list read on the first copy. -/
def PlG (y : XG κ) : List (Bool × κ) := (false, y.1) :: y.2.1.map RdG.snd

/-- The list read on the second copy. -/
def QlG (y : XG κ) : List (Bool × κ) := y.2.1.map RdG.fst ++ [y.2.2]

theorem exists_cmpG {l : List (Bool × κ)} (hl : l ≠ []) : (∃ y : XG κ, PlG y = l ∧ QlG y = l) ↔ chkG none l := by
  obtain ⟨r, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [chkG, ← cmpG_iff]
  constructor
  · rintro ⟨⟨x, ds, r'⟩, h1, h2⟩
    simp only [PlG, List.cons.injEq] at h1
    obtain ⟨rfl, h1⟩ := h1
    exact ⟨Or.inl rfl, ds, r', h1, h2⟩
  · rintro ⟨h, ds, r', h1, h2⟩
    have h : r.1 = false := by simpa using h
    obtain ⟨f, x⟩ := r
    simp only at h
    subst h
    exact ⟨(x, ds, r'), by simp [PlG, h1], h2⟩

theorem cmpG_unique {y y' : XG κ} (h1 : PlG y = PlG y') (h2 : QlG y = QlG y') : y = y' := by
  obtain ⟨x, ds, r⟩ := y
  obtain ⟨x', ds', r'⟩ := y'
  simp only [PlG, List.cons.injEq, Prod.mk.injEq, true_and] at h1
  simp only [QlG] at h2
  obtain ⟨rfl, h1⟩ := h1
  have hl : ds.length = ds'.length := by simpa using congrArg List.length h1
  obtain ⟨h4, h3⟩ := List.append_inj h2 (by simpa using hl)
  obtain rfl : r = r' := by simpa using h3
  obtain rfl : ds = ds' := by
    clear h3 h2
    induction ds generalizing ds' with
    | nil => simpa using hl.symm
    | cons d ds ih =>
      rcases ds' with _ | ⟨d', ds'⟩
      · simp at hl
      · simp only [List.map_cons, List.cons.injEq] at h1 h4
        rw [RdG.ext h4.1 h1.1, ih ds' h1.2 (by simpa using hl) h4.2]
  rfl

end Pure

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- Records without marks. -/
abbrev Rk (K : Type) := Bool × List (Bl K)

/-- The word of a record without mark. -/
def rk (r : Rk K) : List (Sy M K) := rw' r.1 (r.2.map some)

theorem rk_eq (r : Rk K) : (rk r : List (Sy M K)) = .flag r.1 :: (r.2.map be ++ [.dot]) := by
  rw [rk, rw', List.map_map]; rfl

/-- The first copy. -/
abbrev cP : Zc K := .tp (.cm false) true
/-- The second copy. -/
abbrev cQ : Zc K := .tp (.cm true) true

theorem runs_rk (zs : Finset (Zc K)) (hz : zs.Nonempty) :
    Runs (2 * (2 * zs.card + 1) + (Fintype.card (Bl K) * (2 * zs.card + 1) + 1) + (2 * zs.card + 1))
      (fun r : Rk K => on zs (rk r : List (Sy M K))) (fun _ => (1 : A)) := by
  have h := ((Runs.letter (F := A) zs (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.wordstar (F := A) zs hz (be : Bl K → Sy M K))).mul (Runs.word (F := A) zs [(Sy.dot : Sy M K)])
  refine (h.congr ⟨fun r => ((r.1, r.2), ()), fun y => (y.1.1, y.1.2), fun r => rfl, fun y => rfl⟩ (fun r z => ?_)
    fun r => ?_).mono ?_
  · simp only [Equiv.coe_fn_mk, on_append, rk_eq]
    rfl
  · simp
  · simp

/-- Emissions of a round. -/
def emRd (d : RdG (List (Bl K))) : Zc K → List (Sy M K) := fun z => on {cP} (rk d.snd) z ++ on {cQ} (rk d.fst) z

theorem runs_rdG : Runs ((9 + (Fintype.card (Bl K) * 3 + 1) + (3 + (Fintype.card (Bl K) * 3 + 1) + 3)) +
    (6 + 3 + (Fintype.card (Bl K) * 5 + 1) + 5)) (emRd : RdG (List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hpq : (cP : Zc K) ≠ cQ := by simp
  have h1 := (runs_rk (A := A) (M := M) (K := K) {cQ} ⟨cQ, by simp⟩).mul
    (((Runs.word (F := A) (Z := Zc K) {cP} [(Sy.flag false : Sy M K)]).mul
    (Runs.wordstar (F := A) {cP} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.word (F := A) {cP} [(Sy.dot : Sy M K)]))
  have h2 := (((Runs.letter (F := A) (Z := Zc K) {cQ} (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
    (Runs.word (F := A) {cP} [(Sy.flag true : Sy M K)])).mul
    (Runs.wordstar (F := A) {cP, cQ} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.word (F := A) {cP, cQ} [(Sy.dot : Sy M K)])
  refine ((h1.add h2).congr ⟨Sum.map (fun y => (y.1, (((), y.2), ()))) (fun y => (((y.1, ()), y.2), ())),
    Sum.map (fun y => (y.1, y.2.1.2)) (fun y => (y.1.1.1, y.1.2)), fun y => ?_, fun y => ?_⟩
    (fun y z => ?_) fun y => ?_).mono ?_
  · rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl
  · rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl
  · rcases y with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.elim_inl, emRd, RdG.fst, RdG.snd, rk_eq]
      by_cases hz : z = cP
      · subst hz; simp [on]
      · simp [on, hz]
    · simp only [Equiv.coe_fn_mk, Sum.map_inr, Sum.elim_inr, emRd, RdG.fst, RdG.snd, rk_eq]
      by_cases hz : z = cP
      · subst hz; simp [on]
      · by_cases hz' : z = cQ
        · subst hz'; simp [on]
        · simp [on, hz, hz']
  · rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> simp
  · rw [Finset.card_pair hpq]
    simp
    omega

/-- Emissions of the comparison. -/
def emCm (y : XG (List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  on {cP} ((PlG y).flatMap rk) z ++ on {cQ} ((QlG y).flatMap rk) z

/-- Dimension of the comparison. -/
def dimCm (k : ℕ) : ℕ := (3 + (k * 3 + 1) + 3) +
  ((((9 + (k * 3 + 1) + (3 + (k * 3 + 1) + 3)) + (6 + 3 + (k * 5 + 1) + 5)) + 1) + (6 + (k * 3 + 1) + 3))

theorem runs_cm : Runs (dimCm (Fintype.card (Bl K)))
    (emCm : XG (List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hk := (runs_rdG (A := A) (M := M) (K := K)).kstar fun d => ⟨cP, by simp [emRd, on, rk_eq]⟩
  have h := (((Runs.word (F := A) (Z := Zc K) {cP} [(Sy.flag false : Sy M K)]).mul
    (Runs.wordstar (F := A) {cP} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.word (F := A) {cP} [(Sy.dot : Sy M K)])).mul
    (hk.mul (runs_rk (A := A) (M := M) (K := K) {cQ} ⟨cQ, by simp⟩))
  refine (h.congr ⟨fun y => ((((), y.1), ()), y.2), fun y => (y.1.1.2, y.2), fun y => rfl, fun y => rfl⟩
    (fun y z => ?_) fun y => ?_).mono ?_
  · obtain ⟨w, ds, r⟩ := y
    simp only [Equiv.coe_fn_mk, emCm, PlG, QlG]
    by_cases hz : z = cP
    · subst hz
      simp [on, emRd, rk_eq, List.flatMap_map]
    · by_cases hz' : z = cQ
      · subst hz'
        simp [on, emRd, rk_eq, List.flatMap_map]
      · simp [on, emRd, hz, hz']
  · simp
  · unfold dimCm
    simp

end Nc.Uni
end

/-! Source module: Nc.Uni.SpecU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sorting loop: specification
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

section Blocks

variable {Γ : Type*}

/-- Words without the letter a, followed by a, are cut in one way. -/
theorem cut_inj {a : Γ} {w w' x x' : List Γ} (hw : a ∉ w) (hw' : a ∉ w') (h : w ++ a :: x = w' ++ a :: x') :
    w = w' ∧ x = x' := by
  induction w generalizing w' with
  | nil =>
    rcases w' with _ | ⟨b, w'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw'
  | cons b w ih =>
    rcases w' with _ | ⟨b', w'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw
    · simp only [List.cons_append, List.cons.injEq, List.mem_cons, not_or] at h hw hw'
      obtain ⟨h1, h2⟩ := ih hw.2 hw'.2 h.2
      exact ⟨by rw [h.1, h1], h2⟩

/-- Words, each followed by the letter a. -/
def blocks (a : Γ) (ws : List (List Γ)) : List Γ := ws.flatMap fun w => w ++ [a]

theorem blocks_cons (a : Γ) (w : List Γ) (ws : List (List Γ)) : blocks a (w :: ws) = w ++ a :: blocks a ws := by
  simp [blocks]

theorem blocks_append (a : Γ) (ws ws' : List (List Γ)) : blocks a (ws ++ ws') = blocks a ws ++ blocks a ws' := by
  simp [blocks]

theorem blocks_inj {a : Γ} {ws ws' : List (List Γ)} (h : ∀ w ∈ ws, a ∉ w) (h' : ∀ w ∈ ws', a ∉ w)
    (e : blocks a ws = blocks a ws') : ws = ws' := by
  induction ws generalizing ws' with
  | nil =>
    rcases ws' with _ | ⟨w', ws'⟩
    · rfl
    · rw [blocks_cons] at e
      simp [blocks] at e
  | cons w ws ih =>
    rcases ws' with _ | ⟨w', ws'⟩
    · rw [blocks_cons] at e
      simp [blocks] at e
    · rw [blocks_cons, blocks_cons] at e
      obtain ⟨h1, h2⟩ := cut_inj (h w (by simp)) (h' w' (by simp)) e
      rw [h1, ih (fun w hw => h w (by simp [hw])) (fun w hw => h' w (by simp [hw])) h2]

theorem length_blocks (a : Γ) (ws : List (List Γ)) : (blocks a ws).length = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [blocks_cons, List.length_append, List.length_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    omega

end Blocks

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

theorem rw'_inj {f f' : Bool} {w w' : List (Option (Bl K))} {u v : List (Sy M K)}
    (h : rw' f w ++ u = rw' f' w' ++ v) : f = f' ∧ w = w' ∧ u = v := by
  simp only [rw', List.cons_append, List.cons.injEq, Sy.flag.injEq, List.append_assoc, List.singleton_append] at h
  obtain ⟨rfl, h⟩ := h
  have hd : ∀ w : List (Option (Bl K)), (Sy.dot : Sy M K) ∉ w.map ol := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨o, -, ho⟩ := hw
    exact ol_ne_dot o ho
  obtain ⟨h1, h2⟩ := cut_inj (hd w) (hd w') h
  exact ⟨rfl, List.map_injective_iff.2 ol_inj h1, h2⟩

/-- Lists of records. -/
def encW (l : List (Bool × List (Option (Bl K)))) : List (Sy M K) := l.flatMap fun r => rw' r.1 r.2

theorem encW_inj : Function.Injective (encW : List (Bool × List (Option (Bl K))) → List (Sy M K)) := by
  refine flatMap_inj (fun r => by simp [rw']) ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ u v h
  obtain ⟨rfl, rfl, -⟩ := rw'_inj h
  rfl

theorem bar_rw' (f : Bool) (w : List (Option (Bl K))) : (Sy.bar : Sy M K) ∉ rw' f w := by
  simp only [rw', List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false, not_or]
  refine ⟨by simp, ?_, by simp⟩
  rintro ⟨o, -, ho⟩
  exact ol_ne_bar o ho

theorem bar_encW (l : List (Bool × List (Option (Bl K)))) : (Sy.bar : Sy M K) ∉ encW l := by
  rw [encW, List.mem_flatMap]
  rintro ⟨r, -, h⟩
  exact bar_rw' _ _ h

/-- What a pass of the distribution reads. -/
def dIn (d : List (Dr K)) : List (Bool × List (Option (Bl K))) := d.map fun d => (d.1, some d.2.1 :: d.2.2)

/-- What it writes to the bucket b. -/
def dOut (b : Bl K) (d : List (Dr K)) : List (Bool × List (Option (Bl K))) :=
  (d.filter fun d => d.2.1 = b).map fun d => (d.1, d.2.2 ++ [some d.2.1])

/-- What the last reading reads. -/
def fIn (l : List (Rk K)) : List (Bool × List (Option (Bl K))) := l.map fun r => (r.1, none :: r.2.map some)

/-- What it writes. -/
def fOut (l : List (Rk K)) : List (Bool × List (Option (Bl K))) := l.map fun r => (r.1, r.2.map some)

/-- What a collection writes. -/
noncomputable def cOut (m : Bl K → List (NB M K)) : List (Sy M K) := ((bsl K).flatMap m).map Subtype.val

/-- Runs of the sort. -/
abbrev XU (M K : Type) := List (Ps M K) × List (Rk K) × XG (List (Bl K))

/-- Emissions of the sort. -/
noncomputable def emU (x : XU M K) : Zc K → List (Sy M K) := fun z =>
  (x.1.flatMap fun p => emPs p z) ++ (emFi x.2.1 z ++ emCm x.2.2 z)

/-- Dimension of the sort. -/
def dimU (m k : ℕ) : ℕ := (dimPs m k + 1) + ((14 + 3 + (k * 7 + 1) + 7 + 1 + 3) + dimCm k)

theorem runs_U : Runs (dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
    (emU : XU M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := ((runs_ps (A := A) (M := M) (K := K)).kstar fun p => ⟨lsT, by
    intro h
    have := congrArg List.length h
    simp [emPs, on, barSet] at this⟩).mul ((runs_fi (A := A) (M := M) (K := K)).mul (runs_cm (A := A) (M := M) (K := K)))
  refine h.congr (Equiv.refl _) (fun y z => rfl) fun y => ?_
  simp

section Values

theorem mem_barSet_lsT : (lsT : Zc K) ∈ barSet := by simp [barSet]

theorem mem_barSet_bk (b : Bl K) : (.tp (.bk b) false : Zc K) ∈ barSet := by simp [barSet]

theorem not_barSet {z : Zc K} (h1 : z ≠ lsT) (h2 : ∀ b, z ≠ .tp (.bk b) false) : z ∉ barSet := by
  simp only [barSet, mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
  exact ⟨h1, fun b e => h2 b e.symm⟩

theorem emCo_lsF (m : Bl K → List (NB M K)) : emCo m lsF = cOut m ++ [Sy.bar] := by
  unfold emCo cOut
  have h1 : ∀ i : Fin (Fintype.card (Bl K)), on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) (lsF : Zc K) ++
      on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)] lsF =
      (m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val := by
    intro i
    simp [on]
  simp only [h1]
  rw [bsl, List.map_flatMap, List.flatMap_def, List.map_ofFn]
  simp only [on, mem_singleton, if_true]
  rfl

theorem emCo_bk_true (m : Bl K → List (NB M K)) (b : Bl K) :
    emCo m (.tp (.bk b) true) = (m b).map Subtype.val ++ [Sy.bar] := by
  unfold emCo
  rw [flatten_ofFn_single (Fintype.equivFin (Bl K) b)]
  · simp [on]
  · intro k hk
    have : b ≠ (Fintype.equivFin (Bl K)).symm k := by
      rintro rfl
      simp at hk
    simp [on, this]

theorem emCo_other (m : Bl K → List (NB M K)) {z : Zc K} (h1 : z ≠ lsF) (h2 : ∀ b, z ≠ .tp (.bk b) true) :
    emCo m z = [] := by
  unfold emCo
  rw [flatten_ofFn_nil]
  · simp [on, h1]
  · intro i
    simp [on, h1, h2]

theorem emPs_lsT (p : Ps M K) : emPs p lsT = encW (dIn p.1) ++ [Sy.bar] := by
  have h1 : emCo p.2 (lsT : Zc K) = [] := emCo_other _ (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d lsT : List (Sy M K)) = rw' d.1 (some d.2.1 :: d.2.2) := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [h1]
  simp only [h2, on, mem_barSet_lsT, if_true, List.append_nil]
  rw [encW, dIn, List.flatMap_map]

theorem emPs_lsF (p : Ps M K) : emPs p lsF = cOut p.2 ++ [Sy.bar] := by
  have h1 : (lsF : Zc K) ∉ barSet := not_barSet (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d lsF : List (Sy M K)) = [] := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [emCo_lsF]
  simp [h2, on, h1]

theorem emPs_bk_false (p : Ps M K) (b : Bl K) : emPs p (.tp (.bk b) false) = encW (dOut b p.1) ++ [Sy.bar] := by
  have h1 : emCo p.2 (.tp (.bk b) false : Zc K) = [] := emCo_other _ (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d (.tp (.bk b) false) : List (Sy M K)) =
      if d.2.1 = b then rw' d.1 (d.2.2 ++ [some d.2.1]) else [] := by
    intro d
    by_cases h : d.2.1 = b
    · subst h; simp [emDr, on]
    · simp [emDr, on, h, Ne.symm h]
  have h3 : ∀ l : List (Dr K), (l.flatMap fun d => (if d.2.1 = b then rw' d.1 (d.2.2 ++ [some d.2.1]) else [] : List (Sy M K))) =
      (l.filter fun d => d.2.1 = b).flatMap fun d => rw' d.1 (d.2.2 ++ [some d.2.1]) := by
    intro l
    induction l with
    | nil => rfl
    | cons d l ih =>
      rw [List.flatMap_cons, ih, List.filter_cons]
      by_cases h : d.2.1 = b <;> simp [h]
  unfold emPs
  rw [h1]
  simp only [h2, on, mem_barSet_bk, if_true, List.append_nil]
  rw [h3, encW, dOut, List.flatMap_map]

theorem emPs_bk_true (p : Ps M K) (b : Bl K) : emPs p (.tp (.bk b) true) = (p.2 b).map Subtype.val ++ [Sy.bar] := by
  have h1 : (.tp (.bk b) true : Zc K) ∉ barSet := not_barSet (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d (.tp (.bk b) true) : List (Sy M K)) = [] := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [emCo_bk_true]
  simp [h2, on, h1]

theorem emPs_other (p : Ps M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF) (h3 : ∀ b s, z ≠ .tp (.bk b) s) : emPs p z = [] := by
  have e1 : emCo p.2 z = [] := emCo_other _ h2 fun b => h3 b true
  have e2 : ∀ d : Dr K, (emDr d z : List (Sy M K)) = [] := by
    intro d; simp [emDr, on, h1, h3]
  have e3 : z ∉ (barSet : Finset (Zc K)) := not_barSet h1 fun b => h3 b false
  unfold emPs
  rw [e1]
  simp [e2, on, e3]

theorem emFi_lsT (l : List (Rk K)) : (emFi l lsT : List (Sy M K)) = encW (fIn l) ++ [Sy.bar] := by
  simp [emFi, on, encW, fIn, List.flatMap_map]

theorem emFi_cm (l : List (Rk K)) (k : Bool) : (emFi l (.tp (.cm k) false) : List (Sy M K)) = encW (fOut l) := by
  cases k <;> simp [emFi, on, encW, fOut, List.flatMap_map]

theorem emFi_other (l : List (Rk K)) {z : Zc K} (h1 : z ≠ lsT) (h2 : ∀ k, z ≠ .tp (.cm k) false) :
    (emFi l z : List (Sy M K)) = [] := by
  simp [emFi, on, h1, h2]

theorem rk_flatMap (l : List (Rk K)) : (l.flatMap rk : List (Sy M K)) = encW (fOut l) := by
  rw [encW, fOut, List.flatMap_map]; rfl

theorem emCm_true (y : XG (List (Bl K))) (k : Bool) :
    (emCm y (.tp (.cm k) true) : List (Sy M K)) = encW (fOut (if k then QlG y else PlG y)) := by
  cases k <;> simp [emCm, on, ← rk_flatMap]

theorem emCm_other (y : XG (List (Bl K))) {z : Zc K} (h : ∀ k, z ≠ .tp (.cm k) true) :
    (emCm y z : List (Sy M K)) = [] := by
  simp [emCm, on, h]

theorem emU_lsT (x : XU M K) : emU x lsT = blocks Sy.bar (x.1.map (fun p => encW (dIn p.1)) ++ [encW (fIn x.2.1)]) := by
  unfold emU
  rw [emFi_lsT, emCm_other _ (by simp), blocks_append]
  simp only [emPs_lsT]
  simp [blocks, List.flatMap_map]

theorem emU_lsF (x : XU M K) : emU x lsF = blocks Sy.bar (x.1.map fun p => cOut p.2) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_lsF]
  simp [blocks, List.flatMap_map]

theorem emU_bk_false (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) false) = blocks Sy.bar (x.1.map fun p => encW (dOut b p.1)) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_bk_false]
  simp [blocks, List.flatMap_map]

theorem emU_bk_true (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) true) = blocks Sy.bar (x.1.map fun p => (p.2 b).map Subtype.val) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_bk_true]
  simp [blocks, List.flatMap_map]

theorem emU_cm_false (x : XU M K) (k : Bool) : emU x (.tp (.cm k) false) = encW (fOut x.2.1) := by
  have h : ∀ p : Ps M K, emPs p (.tp (.cm k) false) = [] := fun p => emPs_other p (by simp) (by simp) (by simp)
  unfold emU
  rw [emFi_cm, emCm_other _ (by simp)]
  simp [h]

theorem emU_cm_true (x : XU M K) (k : Bool) :
    emU x (.tp (.cm k) true) = encW (fOut (if k then QlG x.2.2 else PlG x.2.2)) := by
  have h : ∀ p : Ps M K, emPs p (.tp (.cm k) true) = [] := fun p => emPs_other p (by simp) (by simp) (by simp)
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_true]
  simp [h]

theorem emU_other (x : XU M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF) (h3 : ∀ b s, z ≠ .tp (.bk b) s)
    (h4 : ∀ k s, z ≠ .tp (.cm k) s) : emU x z = [] := by
  have h : ∀ p : Ps M K, emPs p z = [] := fun p => emPs_other p h1 h2 h3
  unfold emU
  rw [emFi_other _ h1 (fun k => h4 k false), emCm_other _ (fun k => h4 k true)]
  simp [h]

end Values

end Nc.Uni
end

/-! Source module: Nc.Uni.SpecU2 -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sorting loop: the number of passes is forced
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset Nc.Sort

variable {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {n : ℕ}

/-- The letters of a key after j rotations, without the first one. -/
def rst (j : ℕ) (x : Fin n → Bl K) : List (Option (Bl K)) :=
  ((List.ofFn x).drop (j + 1)).map some ++ none :: ((List.ofFn x).take j).map some

/-- The letters of a key after j rotations. -/
def rot (j : ℕ) (x : Fin n → Bl K) : List (Option (Bl K)) :=
  ((List.ofFn x).drop j).map some ++ none :: ((List.ofFn x).take j).map some

theorem rot_cons {j : ℕ} (hj : j < n) (x : Fin n → Bl K) : rot j x = some (x ⟨j, hj⟩) :: rst j x := by
  rw [rot, rst, List.drop_eq_getElem_cons (by simpa using hj)]
  simp

theorem rot_succ {j : ℕ} (hj : j < n) (x : Fin n → Bl K) : rot (j + 1) x = rst j x ++ [some (x ⟨j, hj⟩)] := by
  rw [rot, rst, List.take_succ_eq_append_getElem (by simpa using hj)]
  simp

theorem rot_zero (x : Fin n → Bl K) : rot 0 x = (List.ofFn x).map some ++ [none] := by simp [rot]

theorem rot_last (x : Fin n → Bl K) : rot n x = none :: (List.ofFn x).map some := by
  rw [rot, List.drop_of_length_le (by simp), List.take_of_length_le (by simp)]
  rfl

/-- The records after j rotations. -/
def recs (j : ℕ) (l : List (Rc n (Bl K))) : List (Bool × List (Option (Bl K))) := l.map fun r => (r.1, rot j r.2)

/-- The rounds of the distribution in pass j. -/
def dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) : List (Dr K) := l.map fun r => (r.1, r.2 ⟨j, hj⟩, rst j r.2)

theorem dIn_dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) : dIn (dl j hj l) = recs j l := by
  rw [dIn, dl, recs, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp, rot_cons hj]

theorem dOut_dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) (b : Bl K) :
    dOut b (dl j hj l) = recs (j + 1) (l.filter fun r => r.2 ⟨j, hj⟩ = b) := by
  rw [dOut, dl, recs, List.filter_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp, rot_succ hj]

theorem dIn_inj : Function.Injective (dIn : List (Dr K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, b, w⟩ ⟨f', b', w'⟩ h
  simp only [Prod.mk.injEq, List.cons.injEq, Option.some.injEq] at h
  rw [h.1, h.2.1, h.2.2]

theorem fIn_inj : Function.Injective (fIn : List (Rk K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ h
  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
  rw [h.1, List.map_injective_iff.2 (Option.some_injective _) h.2]

theorem fOut_inj : Function.Injective (fOut : List (Rk K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ h
  simp only [Prod.mk.injEq] at h
  rw [h.1, List.map_injective_iff.2 (Option.some_injective _) h.2]

/-- A word without the letter bar. -/
def toNB (w : List (Sy M K)) (h : Sy.bar ∉ w) : List (NB M K) := w.attachWith _ fun _ hγ e => h (e ▸ hγ)

theorem toNB_val (w : List (Sy M K)) (h : Sy.bar ∉ w) : (toNB w h).map Subtype.val = w := by
  rw [toNB, List.attachWith_map_subtype_val]

theorem nb_inj : Function.Injective (List.map (Subtype.val : NB M K → Sy M K)) :=
  List.map_injective_iff.2 Subtype.val_injective

/-- The pass j. -/
def cps (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) : Ps M K :=
  (dl j hj l, fun b => toNB (encW (dOut b (dl j hj l))) (bar_encW _))

theorem cOut_cps (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) :
    cOut (cps (M := M) j hj l).2 = encW (recs (j + 1) (Sort.pass (bsl K) ⟨j, hj⟩ l)) := by
  rw [cOut, List.map_flatMap]
  simp only [cps, toNB_val, dOut_dl]
  rw [Sort.pass, recs, List.map_flatMap, encW, List.flatMap_assoc]
  rfl

/-- All passes from j on. -/
noncomputable def canon (l : List (Rc n (Bl K))) : ℕ → ℕ → List (Ps M K)
  | 0, _ => []
  | k + 1, j => if hj : j < n then cps j hj (srt (bsl K) l j) :: canon l k (j + 1) else []

/-- The list in the end. -/
noncomputable def finL (l : List (Rc n (Bl K))) : List (Rk K) := (srt (bsl K) l n).map fun r => (r.1, List.ofFn r.2)

theorem recs_last (l : List (Rc n (Bl K))) : recs n (srt (bsl K) l n) = fIn (finL l) := by
  rw [recs, fIn, finL, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp, rot_last]

theorem srt_ne_nil {l : List (Rc n (Bl K))} (hl : l ≠ []) (j : ℕ) : srt (bsl K) l j ≠ [] := by
  intro h
  have h1 := length_srt (B := Bl K) mem_bsl bsl_nodup l j
  rw [h] at h1
  exact hl (List.length_eq_zero_iff.1 h1.symm)

theorem bar_cOut (m : Bl K → List (NB M K)) : (Sy.bar : Sy M K) ∉ cOut m := by
  rw [cOut, List.mem_map]
  rintro ⟨γ, -, h⟩
  exact γ.2 h

/-- The conditions on the passes and the last reading determine them. -/
theorem passes_iff {l : List (Rc n (Bl K))} (hl : l ≠ []) (k j : ℕ) (hjk : j + k = n) (ps : List (Ps M K))
    (fin : List (Rk K)) :
    ((encW (recs j (srt (bsl K) l j)) :: ps.map fun p => cOut p.2) =
        (ps.map fun p => encW (dIn p.1)) ++ [encW (fIn fin)] ∧
      ∀ p ∈ ps, ∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val) ↔ ps = canon l k j ∧ fin = finL l := by
  induction k generalizing j ps with
  | zero =>
    obtain rfl : j = n := by omega
    rw [recs_last]
    rcases ps with _ | ⟨p, ps⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true, canon, true_and]
      constructor
      · rintro ⟨h, -⟩
        exact (fIn_inj (encW_inj h)).symm
      · rintro rfl
        exact ⟨rfl, by simp⟩
    · simp only [canon, reduceCtorEq, false_and, iff_false]
      rintro ⟨h, -⟩
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have h1 := encW_inj h.1
      have hne : srt (bsl K) l j ≠ [] := srt_ne_nil hl j
      rw [finL] at h1
      obtain ⟨r, l', hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr] at h1
      rcases hp : p.1 with _ | ⟨d, d'⟩
      · rw [hp] at h1
        simp [fIn, dIn] at h1
      · rw [hp] at h1
        simp [fIn, dIn] at h1
  | succ k ih =>
    have hj : j < n := by omega
    have hne : srt (bsl K) l j ≠ [] := srt_ne_nil hl j
    rw [canon, dif_pos hj]
    rcases ps with _ | ⟨p, ps⟩
    · simp only [reduceCtorEq, false_and, iff_false]
      rintro ⟨h, -⟩
      simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
      have h1 := encW_inj h
      obtain ⟨r, l', hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr, recs, List.map_cons, rot_cons hj] at h1
      rcases fin with _ | ⟨d, d'⟩
      · simp [fIn] at h1
      · simp [fIn] at h1
    · have hs : srt (bsl K) l (j + 1) = Sort.pass (bsl K) ⟨j, hj⟩ (srt (bsl K) l j) := by rw [srt, dif_pos hj]
      have key : (encW (recs j (srt (bsl K) l j)) : List (Sy M K)) = encW (dIn p.1) → (∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val) →
          p = cps j hj (srt (bsl K) l j) := by
        intro h1 h2
        have h3 : p.1 = dl j hj (srt (bsl K) l j) := by
          have := encW_inj h1
          rw [← dIn_dl j hj] at this
          exact (dIn_inj this).symm
        refine Prod.ext h3 ?_
        funext b
        apply nb_inj
        rw [← h2 b, h3]
        exact (toNB_val _ (bar_encW _)).symm
      constructor
      · rintro ⟨h, h2⟩
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
        have hp := key h.1 fun b => h2 p (by simp) b
        subst hp
        rw [cOut_cps, ← hs] at h
        obtain ⟨h3, h4⟩ := (ih (j + 1) (by omega) ps).1 ⟨h.2, fun q hq => h2 q (by simp [hq])⟩
        exact ⟨by rw [h3], h4⟩
      · rintro ⟨h, h2⟩
        rw [List.cons.injEq] at h
        obtain ⟨rfl, h3⟩ := h
        obtain ⟨h4, h5⟩ := (ih (j + 1) (by omega) ps).2 ⟨h3, h2⟩
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, List.cons_append, List.cons.injEq]
          refine ⟨?_, ?_⟩
          · rw [cps, dIn_dl]
          · rw [cOut_cps, ← hs]
            exact h4
        · intro q hq b
          rw [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact (toNB_val _ (bar_encW _)).symm
          · exact h5 q hq b

/-- The run of the sort is matched on its tapes; w is the block that is on the list before. -/
structure IMU (x : XU M K) (w : List (Sy M K)) : Prop where
  ls : w ++ Sy.bar :: emU x lsF = emU x lsT
  bk : ∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true)
  cm : ∀ k, emU x (.tp (.cm k) false) = emU x (.tp (.cm k) true)

theorem imu_iff {l : List (Rc n (Bl K))} (hl : l ≠ []) (x : XU M K) :
    IMU x (encW (recs 0 l)) ↔ x.1 = canon l n 0 ∧ x.2.1 = finL l ∧ PlG x.2.2 = finL l ∧ QlG x.2.2 = finL l := by
  have h0 := passes_iff hl n 0 (by omega) x.1 x.2.1
  rw [show srt (bsl K) l 0 = l from rfl] at h0
  have e1 : (encW (recs 0 l) ++ Sy.bar :: emU x lsF = emU x lsT) ↔
      (encW (recs 0 l) :: x.1.map fun p => cOut p.2) = (x.1.map fun p => encW (dIn p.1)) ++ [encW (fIn x.2.1)] := by
    rw [emU_lsF, emU_lsT, ← blocks_cons]
    constructor
    · intro h
      refine blocks_inj ?_ ?_ h
      · intro w hw
        rw [List.mem_cons, List.mem_map] at hw
        rcases hw with rfl | ⟨p, -, rfl⟩
        · exact bar_encW _
        · exact bar_cOut _
      · intro w hw
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
        rcases hw with ⟨p, -, rfl⟩ | rfl <;> exact bar_encW _
    · intro h
      rw [h]
  have e2 : (∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true)) ↔
      ∀ p ∈ x.1, ∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val := by
    have e3 : ∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true) ↔
        ∀ p ∈ x.1, encW (dOut b p.1) = (p.2 b).map Subtype.val := by
      intro b
      rw [emU_bk_false, emU_bk_true]
      constructor
      · intro h p hp
        have h2 := blocks_inj (by
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨p, -, rfl⟩ := hw
          exact bar_encW _) (by
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨p, -, rfl⟩ := hw
          rw [List.mem_map]
          rintro ⟨γ, -, h⟩
          exact γ.2 h) h
        exact List.map_inj_left.1 h2 p hp
      · intro h
        rw [List.map_congr_left h]
    exact ⟨fun h p hp b => (e3 b).1 (h b) p hp, fun h b => (e3 b).2 fun p hp => h p hp b⟩
  have e4 : (∀ k, emU x (.tp (.cm k) false) = emU x (.tp (.cm k) true)) ↔ x.2.1 = PlG x.2.2 ∧ x.2.1 = QlG x.2.2 := by
    simp only [emU_cm_false, emU_cm_true]
    constructor
    · intro h
      exact ⟨fOut_inj (encW_inj (h false)), fOut_inj (encW_inj (h true))⟩
    · rintro ⟨h1, h2⟩ k
      cases k
      · simp only [Bool.false_eq_true, if_false]; rw [h1]
      · simp only [if_true]; rw [h2]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a1, a2⟩ := h0.1 ⟨e1.1 h1, e2.1 h2⟩
    obtain ⟨a3, a4⟩ := e4.1 h3
    exact ⟨a1, a2, by rw [← a3, a2], by rw [← a4, a2]⟩
  · rintro ⟨a1, a2, a3, a4⟩
    obtain ⟨b1, b2⟩ := h0.2 ⟨a1, a2⟩
    exact ⟨e1.2 b1, e2.2 b2, e4.2 ⟨by rw [a2, a3], by rw [a2, a4]⟩⟩

theorem imu_unique {l : List (Rc n (Bl K))} (hl : l ≠ []) {x x' : XU M K} (h : IMU x (encW (recs 0 l)))
    (h' : IMU x' (encW (recs 0 l))) : x = x' := by
  rw [imu_iff hl] at h h'
  refine Prod.ext (h.1.trans h'.1.symm) (Prod.ext (h.2.1.trans h'.2.1.symm) ?_)
  exact cmpG_unique (h.2.2.1.trans h'.2.2.1.symm) (h.2.2.2.trans h'.2.2.2.symm)

theorem imu_exists {l : List (Rc n (Bl K))} (hl : l ≠ []) :
    (∃ x : XU M K, IMU x (encW (recs 0 l))) ↔ chk none (srt (bsl K) l n) := by
  have hne : finL l ≠ [] := by
    rw [finL, Ne, List.map_eq_nil_iff]
    exact srt_ne_nil hl n
  have h1 : chkG none (finL l) ↔ chk none (srt (bsl K) l n) := by
    have := chkG_map (List.ofFn : (Fin n → Bl K) → List (Bl K)) List.ofFn_injective none (srt (bsl K) l n)
    rwa [Option.map_none] at this
  rw [← h1, ← exists_cmpG hne]
  constructor
  · rintro ⟨x, h⟩
    rw [imu_iff hl] at h
    exact ⟨x.2.2, h.2.2.1, h.2.2.2⟩
  · rintro ⟨y, h2, h3⟩
    refine ⟨(canon l n 0, finL l, y), ?_⟩
    rw [imu_iff hl]
    exact ⟨rfl, rfl, h2, h3⟩

/-- First the table, then the lookups: there is a run if and only if every lookup is in the table. -/
theorem imu_table (T L : List (Fin n → Bl K)) (hT : T ≠ []) :
    (∃ x : XU M K, IMU x (encW (recs 0 (T.map (fun x => (false, x)) ++ L.map fun x => (true, x))))) ↔
      ∀ x ∈ L, x ∈ T := by
  rw [imu_exists (by simp [hT])]
  exact chk_table mem_bsl bsl_nodup T L

end Nc.Uni
end

/-! Source module: Nc.Uni.PM -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Pointer machines

Every step loads one record and allocates one record, at the next address.
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

/-- A pointer machine with modes M, kinds of records K, weights in A. The variables of a step are: the 5 registers,
the 3 fields of the record that is loaded, the new address. -/
structure Mach (A M K : Type*) where
  /-- rules -/
  Rl : Type
  [fR : Fintype Rl]
  [dR : DecidableEq Rl]
  /-- mode before -/
  src : Rl → M
  /-- mode after -/
  dst : Rl → M
  /-- the bit that is read from the input -/
  rd : Rl → Option Bool
  /-- kind of the record that is loaded -/
  lk : Rl → K
  /-- the register with its address -/
  la : Rl → Fin 5
  /-- kind of the record that is allocated -/
  ak : Rl → K
  /-- its fields -/
  af : Rl → Fin 3 → Fin 9
  /-- the registers after the step -/
  dr : Rl → Fin 5 → Fin 9
  /-- weight -/
  wt : Rl → A
  /-- first mode -/
  m0 : M
  /-- last mode -/
  mh : M
  /-- kind of the record with address 0 -/
  kN : K

attribute [instance] Mach.fR Mach.dR

variable {A M K : Type*} (P : Mach A M K)

/-- A register as a variable. -/
def rv (i : Fin 5) : Fin 9 := ⟨i.1, by omega⟩

/-- Records: kind, address, fields. -/
abbrev Rec (K : Type*) := K × (Fin 4 → ℕ)

namespace Mach

/-- A step: a rule and the values of the variables. -/
abbrev Step := P.Rl × (Fin 9 → ℕ)

variable {P}

/-- The record that is loaded. -/
def ld (st : P.Step) : Rec K := (P.lk st.1, ![st.2 (rv (P.la st.1)), st.2 5, st.2 6, st.2 7])

/-- The record that is allocated. -/
def al (st : P.Step) : Rec K :=
  (P.ak st.1, ![st.2 8, st.2 (P.af st.1 0), st.2 (P.af st.1 1), st.2 (P.af st.1 2)])

/-- The weight of a list of steps. -/
def wts [CommMonoid A] (tr : List P.Step) : A := (tr.map fun st => P.wt st.1).prod

variable (P)

/-- States. -/
structure State where
  /-- mode -/
  mode : M
  /-- registers -/
  regs : Fin 5 → ℕ
  /-- records -/
  heap : List (Rec K)
  /-- last address -/
  n : ℕ
  /-- the rest of the input -/
  inp : List Bool

variable {P}

/-- A step is possible. -/
structure Fire (σ : State (M := M) (K := K)) (st : P.Step) : Prop where
  src : P.src st.1 = σ.mode
  regs : ∀ i, st.2 (rv i) = σ.regs i
  fresh : st.2 8 = σ.n + 1
  load : ld st ∈ σ.heap
  read : (P.rd st.1).toList <+: σ.inp

/-- The state after a step. -/
def nxt (σ : State (M := M) (K := K)) (st : P.Step) : State (M := M) (K := K) where
  mode := P.dst st.1
  regs i := st.2 (P.dr st.1 i)
  heap := σ.heap ++ [al st]
  n := σ.n + 1
  inp := σ.inp.drop (P.rd st.1).toList.length

variable (P) in
/-- Accepting runs. -/
def Seq : State (M := M) (K := K) → List P.Step → Prop
  | σ, [] => σ.mode = P.mh ∧ σ.inp = []
  | σ, st :: tr => Fire σ st ∧ Seq (nxt σ st) tr

/-- Runs that are checked globally: loads may refer to any record. -/
structure GV (σ : State (M := M) (K := K)) (tr : List P.Step) : Prop where
  modes : σ.mode :: tr.map (fun st => P.dst st.1) = tr.map (fun st => P.src st.1) ++ [P.mh]
  regs : ∀ i, ∃ fin, σ.regs i :: tr.map (fun st => st.2 (P.dr st.1 i)) = tr.map (fun st => st.2 (rv i)) ++ [fin]
  fresh : tr.map (fun st => st.2 8) = (List.range tr.length).map fun j => σ.n + 1 + j
  read : (tr.flatMap fun st => (P.rd st.1).toList) = σ.inp
  load : ∀ st ∈ tr, ld st ∈ σ.heap ++ tr.map al

/-- The heap is closed. -/
structure Closed (σ : State (M := M) (K := K)) : Prop where
  le : ∀ c ∈ σ.heap, ∀ i, c.2 i ≤ σ.n
  ex : ∀ j ≤ σ.n, ∃ c ∈ σ.heap, c.2 0 = j
  reg : ∀ i, σ.regs i ≤ σ.n

theorem env_cases (p : Fin 9 → Prop) (h : ∀ i : Fin 5, p (rv i)) (h5 : p 5) (h6 : p 6) (h7 : p 7) (h8 : p 8) :
    ∀ i, p i := by
  intro i
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

theorem Closed.env {σ : State (M := M) (K := K)} (hσ : Closed σ) {st : P.Step} (hf : Fire σ st) :
    ∀ i, st.2 i ≤ σ.n + 1 := by
  have hl := hσ.le _ hf.load
  refine env_cases _ (fun i => ?_) ?_ ?_ ?_ ?_
  · rw [hf.regs]
    exact (hσ.reg i).trans (Nat.le_succ _)
  · exact (hl 1).trans (Nat.le_succ _)
  · exact (hl 2).trans (Nat.le_succ _)
  · exact (hl 3).trans (Nat.le_succ _)
  · exact hf.fresh.le

theorem Closed.nxt {σ : State (M := M) (K := K)} (hσ : Closed σ) {st : P.Step} (hf : Fire σ st) :
    Closed (Mach.nxt σ st) := by
  have he := hσ.env hf
  constructor
  · intro c hc i
    simp only [Mach.nxt, List.mem_append, List.mem_singleton] at hc ⊢
    rcases hc with hc | rfl
    · exact (hσ.le c hc i).trans (Nat.le_succ _)
    · have h4 : ∀ i : Fin 4, (al st).2 i ≤ σ.n + 1 := by
        intro i
        fin_cases i
        · exact he _
        · exact he _
        · exact he _
        · exact he _
      exact h4 i
  · intro j hj
    simp only [Mach.nxt] at hj ⊢
    rcases Nat.lt_or_ge σ.n j with h | h
    · refine ⟨al st, by simp, ?_⟩
      have : (al st).2 0 = st.2 8 := rfl
      rw [this, hf.fresh]
      omega
    · obtain ⟨c, hc, h0⟩ := hσ.ex j h
      exact ⟨c, by simp [hc], h0⟩
  · intro i
    exact he _

/-- The global check is the same as the check step by step, if the heap is closed. -/
theorem gv_iff {σ : State (M := M) (K := K)} (hσ : Closed σ) (tr : List P.Step) : GV σ tr ↔ Seq P σ tr := by
  induction tr generalizing σ with
  | nil =>
    constructor
    · rintro ⟨h1, -, -, h4, -⟩
      exact ⟨by simpa using h1, by simpa using h4.symm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by simp [h1], fun i => ⟨σ.regs i, rfl⟩, rfl, by simp [h2], by simp⟩
  | cons st tr ih =>
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h1
      have hr : ∀ i, σ.regs i = st.2 (rv i) ∧ ∃ fin, st.2 (P.dr st.1 i) :: tr.map (fun st => st.2 (P.dr st.1 i)) =
          tr.map (fun st => st.2 (rv i)) ++ [fin] := by
        intro i
        obtain ⟨fin, hfin⟩ := h2 i
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hfin
        exact ⟨hfin.1, fin, hfin.2⟩
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.cons.injEq, List.map_map] at h3
      have hfr : ∀ st' ∈ tr, σ.n + 1 < st'.2 8 := by
        intro st' hst
        have hm : st'.2 8 ∈ tr.map fun st => st.2 8 := List.mem_map.2 ⟨st', hst, rfl⟩
        rw [h3.2, List.mem_map] at hm
        obtain ⟨j, -, hj⟩ := hm
        simp only [Function.comp] at hj
        omega
      have hload : ld st ∈ σ.heap := by
        have hm := h5 st (by simp)
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hm
        · exfalso
          have ha : (ld st).2 0 ≤ σ.n := by
            have : (ld st).2 0 = st.2 (rv (P.la st.1)) := rfl
            rw [this, ← (hr _).1]
            exact hσ.reg _
          rw [List.map_cons, List.mem_cons, List.mem_map] at hm
          rcases hm with e | ⟨st', hst, e⟩
          · have h0 : (ld st).2 0 = (al st).2 0 := by rw [e]
            have h8 : (al st).2 0 = st.2 8 := rfl
            have := h3.1
            omega
          · have h0 : (ld st).2 0 = (al st').2 0 := by rw [e]
            have h8 : (al st').2 0 = st'.2 8 := rfl
            have := hfr st' hst
            omega
      have hf : Fire σ st := by
        refine ⟨h1.1.symm, fun i => (hr i).1.symm, by simpa using h3.1, hload, ?_⟩
        rw [← h4, List.flatMap_cons]
        exact List.prefix_append _ _
      refine ⟨hf, (ih (hσ.nxt hf)).1 ⟨h1.2, fun i => (hr i).2, ?_, ?_, ?_⟩⟩
      · rw [h3.2]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · simp only [Mach.nxt]
        rw [← h4, List.flatMap_cons, List.drop_left]
      · intro st' hst
        have hm := h5 st' (by simp [hst])
        simp only [Mach.nxt]
        rw [List.map_cons] at hm
        simpa using hm
    · rintro ⟨hf, h⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := (ih (hσ.nxt hf)).2 h
      refine ⟨?_, fun i => ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨hf.src.symm, h1⟩
      · obtain ⟨fin, hfin⟩ := h2 i
        refine ⟨fin, ?_⟩
        simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨(hf.regs i).symm, hfin⟩
      · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.cons.injEq, List.map_map]
        refine ⟨hf.fresh, ?_⟩
        rw [h3]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · rw [List.flatMap_cons, h4]
        simp only [Mach.nxt]
        obtain ⟨rest, hrest⟩ := hf.read
        rw [← hrest, List.drop_left]
      · intro st' hst
        rw [List.mem_cons] at hst
        rw [List.map_cons]
        rcases hst with rfl | hst
        · exact List.mem_append_left _ hf.load
        · have := h5 st' hst
          simp only [Mach.nxt] at this
          simpa using this

/-- All values of the variables are at most the number of steps. -/
theorem Seq.le {σ : State (M := M) (K := K)} (hσ : Closed σ) {tr : List P.Step} (h : Seq P σ tr) :
    ∀ st ∈ tr, ∀ i, st.2 i ≤ σ.n + tr.length := by
  induction tr generalizing σ with
  | nil => simp
  | cons st tr ih =>
    obtain ⟨hf, h⟩ := h
    intro st' hst i
    rw [List.mem_cons] at hst
    rw [List.length_cons]
    rcases hst with rfl | hst
    · have := hσ.env hf i
      omega
    · have := ih (hσ.nxt hf) h st' hst i
      simp only [Mach.nxt] at this
      omega

variable [CommRing A]

variable (P) in
/-- The accepting runs from a state are finitely many; their weights have the sum S, their lengths are at most B. -/
def SumTo {A M K : Type*} [CommRing A] (P : Mach A M K) (σ : State (M := M) (K := K)) (S : A) (B : ℤ) : Prop :=
  ∃ R : Finset (List P.Step), (∀ tr, tr ∈ R ↔ Seq P σ tr) ∧ ∑ tr ∈ R, wts tr = S ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B

theorem SumTo.mono {σ : State (M := M) (K := K)} {S : A} {B B' : ℤ} (h : SumTo P σ S B) (hB : B ≤ B') : SumTo P σ S B' := by
  obtain ⟨R, h1, h2, h3⟩ := h
  exact ⟨R, h1, h2, fun tr htr => (h3 tr htr).trans hB⟩

/-- The end. -/
theorem SumTo.halt {σ : State (M := M) (K := K)} (hm : σ.mode = P.mh) (hi : σ.inp = []) (hP : ∀ r, P.src r ≠ P.mh) :
    SumTo P σ 1 0 := by
  classical
  refine ⟨{[]}, fun tr => ?_, by simp [wts], by simp⟩
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨hm, hi⟩
  · intro h
    rcases tr with _ | ⟨st, tr⟩
    · rfl
    · exact absurd (h.1.src.trans hm) (hP _)

/-- One step: finitely many possibilities. -/
theorem SumTo.fin {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (F : Finset P.Step) (hF : ∀ st, st ∈ F ↔ Fire σ st)
    (S : P.Step → A) (B : ℤ) (h : ∀ st ∈ F, SumTo P (nxt σ st) (S st) B) :
    SumTo P σ (∑ st ∈ F, P.wt st.1 * S st) (B + 1) := by
  classical
  have h' : ∀ st, ∃ R : Finset (List P.Step), st ∈ F → (∀ tr, tr ∈ R ↔ Seq P (nxt σ st) tr) ∧
      ∑ tr ∈ R, wts tr = S st ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B := by
    intro st
    by_cases hst : st ∈ F
    · obtain ⟨R, hR⟩ := h st hst
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h => absurd h hst⟩
  choose R hR using h'
  refine ⟨F.biUnion fun st => (R st).image fun tr => st :: tr, fun tr => ?_, ?_, ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨st, hst, tr, htr, rfl⟩
      exact ⟨(hF st).1 hst, ((hR st hst).1 tr).1 htr⟩
    · intro htr
      rcases tr with _ | ⟨st, tr⟩
      · exact absurd htr.1 hm
      · have hst := (hF st).2 htr.1
        exact ⟨st, hst, tr, ((hR st hst).1 tr).2 htr.2, rfl⟩
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun st hst => ?_
      rw [Finset.sum_image (by intro x _ y _ e; simpa using e), ← (hR st hst).2.1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun tr _ => by simp [wts]
    · intro st _ st' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro tr h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨t1, -, rfl⟩ := h1
      obtain ⟨t2, -, e⟩ := h2
      exact hne (List.cons.inj e).1.symm
  · intro tr htr
    simp only [Finset.mem_biUnion, Finset.mem_image] at htr
    obtain ⟨st, hst, tr, htr, rfl⟩ := htr
    have := (hR st hst).2.2 tr htr
    rw [List.length_cons]
    push_cast
    omega

/-- No step. -/
theorem SumTo.none {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (h : ∀ st : P.Step, ¬ Fire σ st) (B : ℤ) :
    SumTo P σ 0 B := by
  have h1 := SumTo.fin hm (∅ : Finset P.Step) (by simpa using h) (fun _ => 0) 0 (by simp)
  refine ⟨∅, ?_, by simp, by simp⟩
  obtain ⟨R, hR, -, -⟩ := h1
  intro tr
  simp only [Finset.notMem_empty, false_iff]
  intro htr
  rcases tr with _ | ⟨st, tr⟩
  · exact hm htr.1
  · exact h st htr.1

/-- Exactly one step. -/
theorem SumTo.one {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (st : P.Step) (hst : ∀ st', Fire σ st' ↔ st' = st)
    {S : A} {B : ℤ} (h : SumTo P (nxt σ st) S B) : SumTo P σ (P.wt st.1 * S) (B + 1) := by
  have h1 := SumTo.fin hm {st} (fun st' => by rw [Finset.mem_singleton, hst]) (fun _ => S) B (by
    intro st' hst'
    rw [Finset.mem_singleton] at hst'
    subst hst'
    exact h)
  simpa using h1

/-- Exactly two steps. -/
theorem SumTo.two {σ : State (M := M) (K := K)} (hm : σ.mode ≠ P.mh) (st st₁ : P.Step) (hne : st ≠ st₁)
    (hst : ∀ st', Fire σ st' ↔ st' = st ∨ st' = st₁) {S S₁ : A} {B : ℤ} (h : SumTo P (nxt σ st) S B)
    (h₁ : SumTo P (nxt σ st₁) S₁ B) : SumTo P σ (P.wt st.1 * S + P.wt st₁.1 * S₁) (B + 1) := by
  classical
  have h1 := SumTo.fin hm {st, st₁} (fun st' => by rw [Finset.mem_insert, Finset.mem_singleton, hst])
    (fun st' => if st' = st then S else S₁) B (by
    intro st' hst'
    rw [Finset.mem_insert, Finset.mem_singleton] at hst'
    rcases hst' with rfl | rfl
    · rw [if_pos rfl]; exact h
    · rw [if_neg hne.symm]; exact h₁)
  rw [Finset.sum_pair hne, if_pos rfl, if_neg hne.symm] at h1
  exact h1

end Mach

end Nc.Uni
end

/-! Source module: Nc.Uni.Prog -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# A tape program that simulates a pointer machine
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- A word of bits, ended. -/
def bw (w : List Bool) : List (Sy M K) := w.map .bit ++ [.semi]

/-- The content of a record: kind and columns. -/
def cont (κ : K) (cs : List (Fin 4 → Bool)) : List (Bl K) := .inl κ :: cs.map .inr

/-- A record, as it is written. -/
def rec' (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) : List (Sy M K) := rw' f ((cont κ cs).map some ++ [none])

theorem rec'_eq (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) :
    (rec' f κ cs : List (Sy M K)) = .flag f :: .kd κ :: (cs.map .col ++ [.mark, .dot]) := by
  simp [rec', rw', cont, ol, be, List.map_map, Function.comp_def]

/-- A side of a tape. -/
abbrev tp (s : Tp K) (b : Bool) : Zc K := .tp s b

/-- The sides of all register tapes. -/
def rgs (b : Bool) : Finset (Zc K) := univ.image fun i => tp (.rg i) b

theorem mem_rgs (b : Bool) (z : Zc K) : z ∈ rgs b ↔ ∃ i, z = tp (.rg i) b := by
  simp [rgs, eq_comm]

theorem card_rgs (b : Bool) : (rgs b : Finset (Zc K)).card = 5 := by
  rw [rgs, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  simpa using h

/-- Loops with a fixed body. -/
theorem runs_rep (w : Zc K → List (Sy M K)) (hw : ∃ z, w z ≠ []) :
    Runs (2 * ∑ z, (w z).length + 1 + 1) (fun (l : List Unit) z => l.flatMap fun _ => w z) (fun _ => (1 : A)) := by
  have h := (Runs.const (F := A) w).kstar fun _ => hw
  exact h.congr (Equiv.refl _) (fun l z => rfl) fun l => by simp

/-- The three words of a round of the counter. -/
def cn (r : List Bool × List Unit) : List Bool := r.1 ++ false :: List.replicate r.2.length true

/-- The next number. -/
def cn1 (r : List Bool × List Unit) : List Bool := r.1 ++ true :: List.replicate r.2.length false

/-- Emissions of a round of the counter. -/
def emCt (r : List Bool × List Unit) : Zc K → List (Sy M K) := fun z =>
  on {tp .cp true, tp .fr false} (bw (cn r)) z ++ on {tp .cp false} (bw (cn1 r)) z

theorem flatMap_unit {γ : Type*} (l : List Unit) (a : γ) : (l.flatMap fun _ => [a]) = List.replicate l.length a := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, ih]; rfl

theorem runs_ct : Runs 60 (emCt : List Bool × List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({tp .cp true, tp .fr false, tp .cp false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have hc2 : ({tp .cp true, tp .fr false} : Finset (Zc K)).card = 2 := Finset.card_pair (by simp)
  have h1 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false} ⟨tp .cp true, by simp⟩
    (fun b : Bool => (Sy.bit b : Sy M K))
  have h2 := Runs.const (F := A) fun z : Zc K => on {tp .cp true, tp .fr false} [(Sy.bit false : Sy M K)] z ++
    on {tp .cp false} [Sy.bit true] z
  have h3 := runs_rep (A := A) (fun z : Zc K => on {tp .cp true, tp .fr false} [(Sy.bit true : Sy M K)] z ++
    on {tp .cp false} [Sy.bit false] z) ⟨tp .cp false, by simp [on]⟩
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false} [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr ⟨fun r => (((r.1, ()), r.2), ()), fun y => (y.1.1.1, y.1.2), fun r => rfl,
    fun y => rfl⟩ (fun r z => ?_) fun r => ?_).mono ?_
  · obtain ⟨w, l⟩ := r
    simp only [Equiv.coe_fn_mk, emCt, cn, cn1, bw]
    by_cases hz1 : z = tp .cp true
    · subst hz1
      simp [on, flatMap_unit]
    · by_cases hz2 : z = tp .fr false
      · subst hz2
        simp [on, flatMap_unit]
      · by_cases hz3 : z = tp .cp false
        · subst hz3
          simp [on, flatMap_unit]
        · simp [on, hz1, hz2, hz3]
  · simp
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, hc2]
    simp

/-- The first words: registers 0, counter 1. -/
def i0 (l : List Unit) : List Bool := List.replicate (l.length + 1) false

/-- The first address. -/
def i1 (l : List Unit) : List Bool := List.replicate l.length false ++ [true]

/-- Emissions at the start. -/
def emIn (m0 : M) (kN : K) (l : List Unit) : Zc K → List (Sy M K) := fun z =>
  on (rgs false) (bw (i0 l)) z ++ on {tp .cp false} (bw (i1 l)) z ++
    on {lsF} (rec' false kN (List.replicate (l.length + 1) fun _ => false)) z ++ on {tp .md false} [.md m0] z

theorem runs_in (m0 : M) (kN : K) : Runs 80 (emIn m0 kN : List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := Runs.const (F := A) fun z : Zc K => on {lsF} [(Sy.flag false : Sy M K), .kd kN] z ++ on {tp .md false} [.md m0] z
  have h2 := runs_rep (A := A) (fun z : Zc K => on (insert (tp .cp false) (rgs false)) [(Sy.bit false : Sy M K)] z ++
    on {lsF} [.col fun _ => false] z) ⟨lsF, by simp [on, mem_rgs]⟩
  have h3 := Runs.const (F := A) fun z : Zc K => on (rgs false) [(Sy.bit false : Sy M K), .semi] z ++
    on {tp .cp false} [.bit true, .semi] z ++ on {lsF} [.col fun _ => false, .mark, .dot] z
  refine (((h1.mul h2).mul h3).congr ⟨fun l => (((), l), ()), fun y => y.1.2, fun l => rfl, fun y => rfl⟩
    (fun l z => ?_) fun l => ?_).mono ?_
  · simp only [Equiv.coe_fn_mk, emIn, i0, i1, bw, rec'_eq]
    by_cases hz1 : z ∈ rgs false
    · obtain ⟨i, rfl⟩ := (mem_rgs _ _).1 hz1
      simp [on, mem_rgs, flatMap_unit, List.replicate_succ']
    · by_cases hz2 : z = tp .cp false
      · subst hz2
        simp [on, mem_rgs, flatMap_unit]
      · by_cases hz3 : z = lsF
        · subst hz3
          simp [on, mem_rgs, flatMap_unit, List.replicate_succ']
        · simp [on, hz1, hz2, hz3]
  · simp
  · have hc : (insert (tp .cp false) (rgs false) : Finset (Zc K)).card = 6 := by
      rw [Finset.card_insert_of_notMem (by simp [mem_rgs]), card_rgs]
    simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, card_rgs]
    simp

section Steps

variable (P : Mach A M K)

/-- A column of the variables of all bits. -/
def cw (w : List (Fin 9 → Bool)) (i : Fin 9) : List Bool := w.map fun v => v i

/-- The columns of the record that is loaded. -/
def ldc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) := w.map fun v => ![v (rv (P.la r)), v 5, v 6, v 7]

/-- The columns of the record that is allocated. -/
def alc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) :=
  w.map fun v => ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]

/-- What a step writes on a register tape. -/
def rgw (s : Bool) (r : P.Rl) (w : List (Fin 9 → Bool)) (i : Fin 5) : List Bool :=
  if s then cw w (rv i) else cw w (P.dr r i)

/-- Emissions of a step. -/
def emSt (x : P.Rl × List (Fin 9 → Bool)) : Zc K → List (Sy M K)
  | .tp (.rg i) s => bw (rgw P s x.1 x.2 i)
  | .tp .md s => [.md (if s then P.src x.1 else P.dst x.1)]
  | .tp .cp _ => []
  | .tp .fr s => if s then bw (cw x.2 8) else []
  | .tp .lk s => if s then [] else rec' true (P.lk x.1) (ldc P x.1 x.2)
  | .tp .ls s => if s then [] else rec' false (P.ak x.1) (alc P x.1 x.2)
  | .tp (.bk _) _ => []
  | .tp (.cm _) _ => []
  | .inp _ => (P.rd x.1).toList.map .bit

/-- Before the columns. -/
def st0 (r : P.Rl) : Zc K → List (Sy M K)
  | .tp .md s => [.md (if s then P.src r else P.dst r)]
  | .tp .lk s => if s then [] else [.flag true, .kd (P.lk r)]
  | .tp .ls s => if s then [] else [.flag false, .kd (P.ak r)]
  | .inp _ => (P.rd r).toList.map .bit
  | _ => []

/-- A column. -/
def st1 (r : P.Rl) (v : Fin 9 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => [.bit (if s then v (rv i) else v (P.dr r i))]
  | .tp .fr s => if s then [.bit (v 8)] else []
  | .tp .lk s => if s then [] else [.col ![v (rv (P.la r)), v 5, v 6, v 7]]
  | .tp .ls s => if s then [] else [.col ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]]
  | _ => []

/-- After the columns. -/
def st2 : Zc K → List (Sy M K)
  | .tp (.rg _) _ => [.semi]
  | .tp .fr s => if s then [.semi] else []
  | .tp .lk s => if s then [] else [.mark, .dot]
  | .tp .ls s => if s then [] else [.mark, .dot]
  | _ => []

theorem flatMap_single' {α β : Type*} (l : List α) (f : α → β) : (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem flatMap_nil' {α β : Type*} (l : List α) : (l.flatMap fun _ => ([] : List β)) = [] := by simp

theorem emSt_eq (x : P.Rl × List (Fin 9 → Bool)) (z : Zc K) :
    st0 P x.1 z ++ (x.2.flatMap (fun v => st1 P x.1 v z) ++ st2 z) = emSt P x z := by
  obtain ⟨r, w⟩ := x
  match z with
  | .tp (.rg i) s =>
    simp only [st0, st1, st2, emSt, flatMap_single', rgw, bw, List.nil_append, cw]
    cases s <;> simp [List.map_map, Function.comp_def]
  | .tp .md s => simp [st0, st1, st2, emSt]
  | .tp .cp s => simp [st0, st1, st2, emSt]
  | .tp .fr s =>
    cases s
    · simp [st0, st1, st2, emSt]
    · simp [st0, st1, st2, emSt, flatMap_single', bw, cw, List.map_map, Function.comp_def]
  | .tp .lk s =>
    cases s
    · simp [st0, st1, st2, emSt, flatMap_single', rec'_eq, ldc, List.map_map, Function.comp_def]
    · simp [st0, st1, st2, emSt]
  | .tp .ls s =>
    cases s
    · simp [st0, st1, st2, emSt, flatMap_single', rec'_eq, alc, List.map_map, Function.comp_def]
    · simp [st0, st1, st2, emSt]
  | .tp (.bk b) s => simp [st0, st1, st2, emSt]
  | .tp (.cm k) s => simp [st0, st1, st2, emSt]
  | .inp j => simp [st0, st1, st2, emSt]

theorem st1_ne (r : P.Rl) (v : Fin 9 → Bool) : ∃ z, st1 P r v z ≠ [] := ⟨tp .fr true, by simp [st1]⟩

/-- Dimension of a step. -/
def dimSt : ℕ := ∑ r : P.Rl, (2 * ∑ z, (st0 P r z).length + 1 +
  ((∑ v : Fin 9 → Bool, (2 * ∑ z, (st1 P r v z).length + 1)) + 1 + (2 * ∑ z, ((st2 z : List (Sy M K))).length + 1)))

theorem runs_st : Runs (dimSt P) (emSt P : P.Rl × List (Fin 9 → Bool) → Zc K → List (Sy M K)) (fun x => P.wt x.1) := by
  have h := Runs.sum (F := A) fun r : P.Rl =>
    (Runs.pick (F := A) (fun _ : Unit => st0 P r) fun _ => P.wt r).mul
    (((Runs.pick (F := A) (fun v : Fin 9 → Bool => st1 P r v) fun _ => 1).kstar fun v => st1_ne P r v).mul
    (Runs.const (F := A) (st2 : Zc K → List (Sy M K))))
  refine (h.congr ⟨fun x => ⟨x.1, ((), x.2, ())⟩, fun y => (y.1, y.2.2.1), fun x => rfl, fun y => rfl⟩ (fun x z => ?_)
    fun x => ?_).mono ?_
  · simp only [Equiv.coe_fn_mk]
    exact emSt_eq P x z
  · simp
  · unfold dimSt
    refine Finset.sum_le_sum fun r _ => ?_
    simp

end Steps

/-- Emissions at the end. -/
def emEd (mh : M) (x : List (Fin 5 → Bool) × List Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then bw (x.1.map fun v => v i) else []
  | .tp .md s => if s then [.md mh] else []
  | .tp .cp s => if s then bw (true :: x.2) else []
  | _ => []

/-- Emissions at the end, the registers. -/
def ed1 (v : Fin 5 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then [.bit (v i)] else []
  | _ => []

theorem runs_ed (mh : M) : Runs ((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30)
    (emEd mh : List (Fin 5 → Bool) × List Bool → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := (Runs.pick (F := A) (fun v : Fin 5 → Bool => (ed1 v : Zc K → List (Sy M K))) fun _ => 1).kstar
    fun v => ⟨tp (.rg 0) true, by simp [ed1]⟩
  have h2 := Runs.const (F := A) fun z : Zc K => on (rgs true) [(Sy.semi : Sy M K)] z ++
    on {tp .md true} [.md mh] z ++ on {tp .cp true} [.bit true] z
  have h3 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true} ⟨tp .cp true, by simp⟩ (fun b : Bool => (Sy.bit b : Sy M K))
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true} [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr ⟨fun x => (((x.1, ()), x.2), ()), fun y => (y.1.1.1, y.1.2), fun r => rfl,
    fun y => rfl⟩ (fun x z => ?_) fun x => ?_).mono ?_
  · obtain ⟨w, u⟩ := x
    simp only [Equiv.coe_fn_mk]
    match z with
    | .tp (.rg i) s =>
      cases s
      · simp [ed1, emEd, on, mem_rgs]
      · simp [ed1, emEd, on, mem_rgs, flatMap_single', bw, List.map_map, Function.comp_def]
    | .tp .md s => cases s <;> simp [ed1, emEd, on, mem_rgs]
    | .tp .cp s => cases s <;> simp [ed1, emEd, on, mem_rgs, bw]
    | .tp .fr s => simp [ed1, emEd, on, mem_rgs]
    | .tp .lk s => simp [ed1, emEd, on, mem_rgs]
    | .tp .ls s => simp [ed1, emEd, on, mem_rgs]
    | .tp (.bk b) s => simp [ed1, emEd, on, mem_rgs]
    | .tp (.cm k) s => simp [ed1, emEd, on, mem_rgs]
    | .inp j => simp [ed1, emEd, on, mem_rgs]
  · simp
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, card_rgs]
    simp

/-- Emissions of the phase that appends the lookups to the list. -/
def emAp (w : List (Sy M K)) : Zc K → List (Sy M K) := fun z => on {tp .lk true, lsF} w z ++ on {lsF} [.bar] z

theorem runs_ap : Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
    (emAp : List (Sy M K) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({tp .lk true, lsF} : Finset (Zc K)).card = 2 := Finset.card_pair (by simp)
  have h := (Runs.wordstar (F := A) (Z := Zc K) {tp .lk true, lsF} ⟨lsF, by simp⟩ (fun γ : Sy M K => γ)).mul
    (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr ⟨fun w => (w, ()), Prod.fst, fun w => rfl, fun y => rfl⟩ (fun w z => ?_) fun w => ?_).mono ?_
  · simp [emAp]
  · simp
  · rw [hc]
    simp

/-- Runs of the program. -/
abbrev XP (P : Mach A M K) := List Unit × List (List Bool × List Unit) × List (P.Rl × List (Fin 9 → Bool)) ×
  (List (Fin 5 → Bool) × List Bool) × List (Sy M K) × XU M K

variable (P : Mach A M K)

/-- Emissions of the program. -/
noncomputable def emX (x : XP P) : Zc K → List (Sy M K) := fun z =>
  emIn P.m0 P.kN x.1 z ++ ((x.2.1.flatMap fun r => emCt r z) ++ ((x.2.2.1.flatMap fun s => emSt P s z) ++
    (emEd P.mh x.2.2.2.1 z ++ (emAp x.2.2.2.2.1 z ++ emU x.2.2.2.2.2 z))))

/-- Dimension of the program. -/
noncomputable def dimX : ℕ := 80 + ((60 + 1) + ((dimSt P + 1) +
  (((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30) +
    ((Fintype.card (Sy M K) * 5 + 1 + 3) + dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K))))))

theorem emSt_ne (x : P.Rl × List (Fin 9 → Bool)) : ∃ z, emSt P x z ≠ [] := ⟨tp .md true, by simp [emSt]⟩

theorem runs_X : Runs (dimX P) (emX P : XP P → Zc K → List (Sy M K)) (fun x => (x.2.2.1.map fun s => P.wt s.1).prod) := by
  have h := (runs_in (A := A) (M := M) (K := K) P.m0 P.kN).mul
    (((runs_ct (A := A) (M := M) (K := K)).kstar fun r => ⟨tp .cp true, by simp [emCt, on, bw]⟩).mul
    (((runs_st P).kstar fun s => emSt_ne P s).mul ((runs_ed (A := A) (M := M) (K := K) P.mh).mul
    ((runs_ap (A := A) (M := M) (K := K)).mul (runs_U (A := A) (M := M) (K := K))))))
  refine h.congr (Equiv.refl _) (fun x z => rfl) fun x => ?_
  simp

end Nc.Uni
end

/-! Source module: Nc.Uni.Bin -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Binary numbers, the first bit is the highest
-/

namespace Nc.Uni

/-- The value of a word of bits. -/
def bv : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 2 ^ w.length else 0) + bv w

theorem bv_lt (w : List Bool) : bv w < 2 ^ w.length := by
  induction w with
  | nil => simp [bv]
  | cons b w ih =>
    simp only [bv, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem bv_inj {w w' : List Bool} (h : w.length = w'.length) (e : bv w = bv w') : w = w' := by
  induction w generalizing w' with
  | nil => exact (List.length_eq_zero_iff.1 h.symm).symm
  | cons b w ih =>
    rcases w' with _ | ⟨b', w'⟩
    · simp at h
    · have hl : w.length = w'.length := by simpa using h
      have h1 := bv_lt w
      have h2 := bv_lt w'
      simp only [bv, hl] at e
      rw [hl] at h1
      have hb : b = b' := by
        cases b <;> cases b' <;> simp at e ⊢ <;> omega
      subst hb
      have : bv w = bv w' := by omega
      rw [ih hl this]

/-- The word of L bits of a number. -/
def bin : ℕ → ℕ → List Bool
  | 0, _ => []
  | L + 1, n => decide (2 ^ L ≤ n) :: bin L (if 2 ^ L ≤ n then n - 2 ^ L else n)

theorem length_bin (L n : ℕ) : (bin L n).length = L := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih => rw [bin, List.length_cons, ih]

theorem bv_bin {L n : ℕ} (h : n < 2 ^ L) : bv (bin L n) = n := by
  induction L generalizing n with
  | zero =>
    simp at h
    simp [bin, bv, h]
  | succ L ih =>
    rw [bin, bv, length_bin]
    rw [pow_succ] at h
    by_cases hn : 2 ^ L ≤ n
    · simp only [hn, decide_true, if_true]
      rw [ih (by omega)]
      omega
    · simp only [hn, decide_false, Bool.false_eq_true, if_false]
      rw [ih (by omega)]
      omega

theorem bin_bv (w : List Bool) : bin w.length (bv w) = w :=
  bv_inj (length_bin _ _) (bv_bin (bv_lt w))

theorem bv_append (u v : List Bool) : bv (u ++ v) = bv u * 2 ^ v.length + bv v := by
  induction u with
  | nil => simp [bv]
  | cons b u ih =>
    rw [List.cons_append, bv, bv, ih, List.length_append, pow_add]
    split_ifs <;> ring

theorem bv_false (k : ℕ) : bv (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bv, ih]

theorem bv_true (k : ℕ) : bv (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bv, List.length_replicate, if_pos rfl, pow_succ]
    omega

/-- The successor of a word. -/
theorem bv_succ (u : List Bool) (k : ℕ) :
    bv (u ++ true :: List.replicate k false) = bv (u ++ false :: List.replicate k true) + 1 := by
  have h := bv_true k
  rw [bv_append, bv_append, bv, bv, bv_false]
  simp only [if_true, Bool.false_eq_true, if_false, List.length_cons, List.length_replicate]
  omega

/-- A word that has a successor ends with 0 1 ⋯ 1. -/
theorem exists_cut {w : List Bool} (h : bv w + 1 < 2 ^ w.length) :
    ∃ u k, w = u ++ false :: List.replicate k true := by
  induction w using List.reverseRecOn with
  | nil => simp [bv] at h
  | append_singleton w b ih =>
    cases b
    · exact ⟨w, 0, rfl⟩
    · rw [bv_append, List.length_append, pow_add] at h
      simp only [bv, List.length_nil, List.length_singleton, pow_zero, pow_one, if_true] at h
      obtain ⟨u, k, rfl⟩ := ih (by omega)
      refine ⟨u, k + 1, ?_⟩
      rw [List.replicate_succ', List.append_assoc]
      rfl

theorem cut_unique {u u' : List Bool} {k k' : ℕ}
    (h : u ++ false :: List.replicate k true = u' ++ false :: List.replicate k' true) : u = u' ∧ k = k' := by
  have h1 := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] at h1
  have key : ∀ (k k' : ℕ) (a b : List Bool), List.replicate k true ++ false :: a = List.replicate k' true ++ false :: b →
      k = k' ∧ a = b := by
    intro k
    induction k with
    | zero =>
      intro k' a b e
      cases k' with
      | zero => simpa using e
      | succ k' => simp [List.replicate_succ] at e
    | succ k ih =>
      intro k' a b e
      cases k' with
      | zero => simp [List.replicate_succ] at e
      | succ k' =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at e
        obtain ⟨h2, h3⟩ := ih k' a b e
        exact ⟨by rw [h2], h3⟩
  obtain ⟨h2, h3⟩ := key k k' _ _ h1
  exact ⟨List.reverse_injective h3, h2⟩

end Nc.Uni
end

/-! Source module: Nc.Uni.Vals -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# What the program writes on the tapes; matched runs
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] (P : Mach A M K)

/-- Words of bits, one after the other. -/
def bws (ws : List (List Bool)) : List (Sy M K) := ws.flatMap bw

theorem bws_cons (w : List Bool) (ws : List (List Bool)) : (bws (w :: ws) : List (Sy M K)) = bw w ++ bws ws := rfl

theorem bw_inj {w w' : List Bool} {u v : List (Sy M K)} (h : bw w ++ u = bw w' ++ v) : w = w' ∧ u = v := by
  simp only [bw, List.append_assoc, List.singleton_append] at h
  have hs : ∀ w : List Bool, (Sy.semi : Sy M K) ∉ w.map .bit := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨b, -, hb⟩ := hw
    exact absurd hb (by simp)
  obtain ⟨h1, h2⟩ := cut_inj (hs w) (hs w') h
  exact ⟨List.map_injective_iff.2 (fun a b e => by simpa using e) h1, h2⟩

theorem bws_inj : Function.Injective (bws : List (List Bool) → List (Sy M K)) := by
  refine flatMap_inj (fun w => by simp [bw]) ?_
  intro w w' u v h
  exact (bw_inj h).1

/-- The contents of the records, with the mark. -/
def oc (c : List (Bl K)) : List (Option (Bl K)) := c.map some ++ [none]

theorem encW_append (l l' : List (Bool × List (Option (Bl K)))) : (encW (l ++ l') : List (Sy M K)) = encW l ++ encW l' := by
  simp [encW]

theorem encW_cons (r : Bool × List (Option (Bl K))) (l : List (Bool × List (Option (Bl K)))) :
    (encW (r :: l) : List (Sy M K)) = rw' r.1 r.2 ++ encW l := rfl

variable {P}

/-- The records that are defined. -/
def dfs (x : XP P) : List (List (Bl K)) :=
  cont P.kN (List.replicate (x.1.length + 1) fun _ => false) :: x.2.2.1.map fun s => cont (P.ak s.1) (alc P s.1 s.2)

/-- The records that are looked up. -/
def lks (x : XP P) : List (List (Bl K)) := x.2.2.1.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)

theorem emX_rg_true (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) true) = bws (x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i]) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.rg i) true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.rg i) true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp (.rg i) true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, rgw, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_rg_false (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) false) = bws (i0 x.1 :: x.2.2.1.map fun s => cw s.2 (P.dr s.1 i)) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.rg i) false) : List (Sy M K)) = bw (i0 l) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.rg i) false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp (.rg i) false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, rgw, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_md_true (x : XP P) : emX P x (tp .md true) = (x.2.2.1.map (fun s => P.src s.1) ++ [P.mh]).map .md := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .md true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .md true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .md true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_single', List.map_map, Function.comp_def]

theorem emX_md_false (x : XP P) : emX P x (tp .md false) = (P.m0 :: x.2.2.1.map fun s => P.dst s.1).map .md := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .md false) : List (Sy M K)) = [.md P.m0] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .md false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .md false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_single', List.map_map, Function.comp_def]

theorem emX_cp_true (x : XP P) : emX P x (tp .cp true) = bws (x.2.1.map cn ++ [true :: x.2.2.2.1.2]) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .cp true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .cp true) : List (Sy M K)) = bw (cn r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .cp true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_cp_false (x : XP P) : emX P x (tp .cp false) = bws (i1 x.1 :: x.2.1.map cn1) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .cp false) : List (Sy M K)) = bw (i1 l) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .cp false) : List (Sy M K)) = bw (cn1 r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .cp false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_fr_true (x : XP P) : emX P x (tp .fr true) = bws (x.2.2.1.map fun s => cw s.2 8) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .fr true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .fr true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .fr true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_fr_false (x : XP P) : emX P x (tp .fr false) = bws (x.2.1.map cn) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .fr false) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .fr false) : List (Sy M K)) = bw (cn r) := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .fr false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, bws, List.flatMap_map]

theorem emX_lk_true (x : XP P) : emX P x (tp .lk true) = x.2.2.2.2.1 := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .lk true) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .lk true) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .lk true) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_lk_false (x : XP P) : emX P x (tp .lk false) = encW ((lks x).map fun c => (true, oc c)) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp .lk false) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp .lk false) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (tp .lk false) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, encW, lks, List.flatMap_map, oc, rec']

theorem emX_ls_true (x : XP P) : emX P x lsT = emU x.2.2.2.2.2 lsT := by
  have h1 : ∀ l, (emIn P.m0 P.kN l lsT : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r lsT : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_ls_false (x : XP P) :
    emX P x lsF = encW ((dfs x).map fun c => (false, oc c)) ++ (x.2.2.2.2.1 ++ .bar :: emU x.2.2.2.2.2 lsF) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l lsF : List (Sy M K)) =
      rec' false P.kN (List.replicate (l.length + 1) fun _ => false) := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r lsF : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, encW, dfs, List.flatMap_map, oc, rec']

theorem emX_bk (x : XP P) (b : Bl K) (s : Bool) : emX P x (tp (.bk b) s) = emU x.2.2.2.2.2 (tp (.bk b) s) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.bk b) s) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.bk b) s) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_cm (x : XP P) (k s : Bool) : emX P x (tp (.cm k) s) = emU x.2.2.2.2.2 (tp (.cm k) s) := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (tp (.cm k) s) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (tp (.cm k) s) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  unfold emX
  rw [h1]
  simp [h2, emSt, emEd, emAp, on, flatMap_nil']

theorem emX_inp (x : XP P) : emX P x (.inp ()) = (x.2.2.1.flatMap fun s => (P.rd s.1).toList).map .bit := by
  have h1 : ∀ l, (emIn P.m0 P.kN l (.inp ()) : List (Sy M K)) = [] := by
    intro l; simp [emIn, on, mem_rgs]
  have h2 : ∀ r, (emCt r (.inp ()) : List (Sy M K)) = [] := by
    intro r; simp [emCt, on]
  have h3 : emU x.2.2.2.2.2 (.inp ()) = [] := emU_other _ (by simp) (by simp) (by simp) (by simp)
  unfold emX
  rw [h1, h3]
  simp [h2, emSt, emEd, emAp, on, List.map_flatMap]

/-- The conditions for a matched run. -/
structure MX (x : XP P) (bits : List Bool) : Prop where
  rg : ∀ i, i0 x.1 :: x.2.2.1.map (fun s => cw s.2 (P.dr s.1 i)) =
    x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i]
  md : P.m0 :: x.2.2.1.map (fun s => P.dst s.1) = x.2.2.1.map (fun s => P.src s.1) ++ [P.mh]
  cp : i1 x.1 :: x.2.1.map cn1 = x.2.1.map cn ++ [true :: x.2.2.2.1.2]
  fr : x.2.1.map cn = x.2.2.1.map fun s => cw s.2 8
  lk : x.2.2.2.2.1 = encW ((lks x).map fun c => (true, oc c))
  ls : IMU x.2.2.2.2.2 (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
  inp : (x.2.2.1.flatMap fun s => (P.rd s.1).toList) = bits

theorem mt_X (x : XP P) (bits : List Bool) :
    Mt (emX P) (fun _ => bits.map .bit) x ↔ MX x bits := by
  have hmd : Function.Injective (Sy.md : M → Sy M K) := fun a b e => by simpa using e
  have hbit : Function.Injective (Sy.bit : Bool → Sy M K) := fun a b e => by simpa using e
  constructor
  · rintro ⟨h1, h2⟩
    have hlk : x.2.2.2.2.1 = encW ((lks x).map fun c => (true, oc c)) := by
      have := h1 .lk
      rw [emX_lk_false, emX_lk_true] at this
      exact this.symm
    refine ⟨fun i => ?_, ?_, ?_, ?_, hlk, ⟨?_, fun b => ?_, fun k => ?_⟩, ?_⟩
    · have := h1 (.rg i)
      rw [emX_rg_false, emX_rg_true] at this
      exact bws_inj this
    · have := h1 .md
      rw [emX_md_false, emX_md_true] at this
      exact List.map_injective_iff.2 hmd this
    · have := h1 .cp
      rw [emX_cp_false, emX_cp_true] at this
      exact bws_inj this
    · have := h1 .fr
      rw [emX_fr_false, emX_fr_true] at this
      exact bws_inj this
    · have := h1 .ls
      rw [emX_ls_false, emX_ls_true, hlk, ← List.append_assoc, ← encW_append] at this
      exact this
    · have := h1 (.bk b)
      rw [emX_bk, emX_bk] at this
      exact this
    · have := h1 (.cm k)
      rw [emX_cm, emX_cm] at this
      exact this
    · have := h2 ()
      rw [emX_inp] at this
      exact List.map_injective_iff.2 hbit this
  · rintro ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, h9⟩
    refine ⟨?_, ?_⟩
    · intro s
      cases s with
      | rg i => rw [emX_rg_false, emX_rg_true, h1]
      | md => rw [emX_md_false, emX_md_true, h2]
      | cp => rw [emX_cp_false, emX_cp_true, h3]
      | fr => rw [emX_fr_false, emX_fr_true, h4]
      | lk => rw [emX_lk_false, emX_lk_true, h5]
      | ls => rw [emX_ls_false, emX_ls_true, h5, ← List.append_assoc, ← encW_append, h6]
      | bk b => rw [emX_bk, emX_bk, h7]
      | cm k => rw [emX_cm, emX_cm, h8]
    · rintro ⟨⟩
      rw [emX_inp, h9]

end Nc.Uni
end

/-! Source module: Nc.Uni.Trace -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Matched runs are runs of the pointer machine
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

section Columns

theorem cols_ext {q : ℕ} {c c' : List (Fin (q + 1) → Bool)} (h : ∀ j, c.map (fun v => v j) = c'.map fun v => v j) : c = c' := by
  have hl : c.length = c'.length := by simpa using congrArg List.length (h 0)
  refine List.ext_getElem hl fun i h1 h2 => ?_
  funext j
  have := h j
  have h3 : (c.map fun v => v j)[i]'(by simpa using h1) = (c'.map fun v => v j)[i]'(by simpa using h2) := by
    simp only [this]
  simpa using h3

/-- The columns of numbers of L bits. -/
def unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : List (Fin q → Bool) :=
  List.ofFn fun t : Fin L => fun j => (bin L (a j)).get (t.cast (length_bin L (a j)).symm)

theorem length_unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : (unb L a).length = L := by simp [unb]

theorem unb_proj (L : ℕ) {q : ℕ} (a : Fin q → ℕ) (j : Fin q) : (unb L a).map (fun v => v j) = bin L (a j) := by
  refine List.ext_getElem (by simp [length_unb, length_bin]) fun i h1 h2 => ?_
  simp [unb]

/-- A list of columns is given by numbers. -/
theorem unb_bv {q : ℕ} (w : List (Fin (q + 1) → Bool)) : unb w.length (fun j => bv (w.map fun v => v j)) = w := by
  refine cols_ext fun j => ?_
  rw [unb_proj]
  have := bin_bv (w.map fun v => v j)
  rwa [List.length_map] at this

theorem bin_zero (L : ℕ) : bin L 0 = List.replicate L false := by
  have := bin_bv (List.replicate L false)
  rwa [List.length_replicate, bv_false] at this

end Columns

section Chains

theorem chain_len {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool) (h : a :: l.map f = l.map g ++ [b])
    (hfg : ∀ r ∈ l, (f r).length = (g r).length) : (∀ r ∈ l, (g r).length = a.length) ∧ b.length = a.length := by
  induction l generalizing a with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨by simp, by rw [h]⟩
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (by simp [hr])
    have h3 : (f r).length = a.length := by rw [hfg r (by simp), h.1]
    refine ⟨fun r' hr' => ?_, by rw [h2, h3]⟩
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · rw [h.1]
    · rw [h1 r' hr', h3]

theorem chain_val {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool) (h : a :: l.map f = l.map g ++ [b])
    (hfg : ∀ r ∈ l, bv (f r) = bv (g r) + 1) :
    l.map (fun r => bv (g r)) = (List.range l.length).map (fun j => bv a + j) ∧ bv b = bv a + l.length := by
  induction l generalizing a with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨rfl, by rw [h]; rfl⟩
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (by simp [hr])
    have h3 : bv (f r) = bv a + 1 := by rw [hfg r (by simp), h.1]
    rw [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, h1, h2, h3, h.1]
    refine ⟨?_, by omega⟩
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp]
    omega

end Chains

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

/-- A step with numbers. -/
def nst (s : P.Rl × List (Fin 9 → Bool)) : P.Step := (s.1, fun i => bv (cw s.2 i))

variable (P) in
/-- The first state. -/
def σi (bits : List Bool) : Mach.State (M := M) (K := K) := ⟨P.m0, fun _ => 0, [(P.kN, ![0, 0, 0, 0])], 0, bits⟩

/-- The content of a record of numbers. -/
def cN (L : ℕ) (ρ : Rec K) : List (Bl K) := cont ρ.1 (unb L ρ.2)

theorem length_cN (L : ℕ) (ρ : Rec K) : (cN L ρ).length = L + 1 := by simp [cN, cont, length_unb]

/-- The key of a record of numbers. -/
def kyN (L : ℕ) (ρ : Rec K) : Fin (L + 1) → Bl K := fun i => (cN L ρ).get (i.cast (length_cN L ρ).symm)

theorem ofFn_kyN (L : ℕ) (ρ : Rec K) : List.ofFn (kyN L ρ) = cN L ρ := by
  refine List.ext_getElem (by rw [List.length_ofFn, length_cN]) fun i h1 h2 => ?_
  rw [List.getElem_ofFn]
  rfl

theorem kyN_inj {L : ℕ} {ρ ρ' : Rec K} (h : ∀ j, ρ.2 j < 2 ^ L) (h' : ∀ j, ρ'.2 j < 2 ^ L) (e : kyN L ρ = kyN L ρ') :
    ρ = ρ' := by
  have h1 : cN L ρ = cN L ρ' := by rw [← ofFn_kyN, ← ofFn_kyN, e]
  simp only [cN, cont, List.cons.injEq, Sum.inl.injEq] at h1
  have h2 := List.map_injective_iff.2 Sum.inr_injective h1.2
  refine Prod.ext h1.1 ?_
  funext j
  have h3 := congrArg (List.map fun v : Fin 4 → Bool => v j) h2
  rw [unb_proj, unb_proj] at h3
  rw [← bv_bin (h j), ← bv_bin (h' j), h3]

theorem length_cn (r : List Bool × List Unit) : (cn1 r).length = (cn r).length := by simp [cn, cn1]

theorem bv_cn (r : List Bool × List Unit) : bv (cn1 r) = bv (cn r) + 1 := bv_succ _ _

theorem bv_i1 (l : List Unit) : bv (i1 l) = 1 := by
  rw [i1, bv_append, bv_false]
  simp [bv]

theorem length_i1 (l : List Unit) : (i1 l).length = l.length + 1 := by simp [i1]

theorem length_i0 (l : List Unit) : (i0 l).length = l.length + 1 := by simp [i0]

theorem bv_i0 (l : List Unit) : bv (i0 l) = 0 := bv_false _

theorem alc_eq {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)} (hl : s.2.length = L) :
    alc P s.1 s.2 = unb L (Mach.al (nst s)).2 := by
  have key : ∀ i, cw s.2 i = bin L (bv (cw s.2 i)) := by
    intro i
    have := bin_bv (cw s.2 i)
    rw [cw, List.length_map, hl] at this
    exact this.symm
  refine cols_ext fun j => ?_
  rw [unb_proj, alc, List.map_map]
  fin_cases j
  · exact key 8
  · exact key _
  · exact key _
  · exact key _

theorem ldc_eq {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)} (hl : s.2.length = L) :
    ldc P s.1 s.2 = unb L (Mach.ld (nst s)).2 := by
  have key : ∀ i, cw s.2 i = bin L (bv (cw s.2 i)) := by
    intro i
    have := bin_bv (cw s.2 i)
    rw [cw, List.length_map, hl] at this
    exact this.symm
  refine cols_ext fun j => ?_
  rw [unb_proj, ldc, List.map_map]
  fin_cases j
  · exact key _
  · exact key 5
  · exact key 6
  · exact key 7

section Facts

variable {x : XP P} {bits : List Bool} (hx : MX x bits)

include hx

theorem MX.len_cn : (∀ r ∈ x.2.1, (cn r).length = x.1.length + 1) ∧ x.2.2.2.1.2.length + 1 = x.1.length + 1 := by
  have := chain_len x.2.1 cn1 cn _ _ hx.cp fun r _ => length_cn r
  rw [length_i1] at this
  exact ⟨this.1, by simpa using this.2⟩

theorem MX.len : ∀ s ∈ x.2.2.1, s.2.length = x.1.length + 1 := by
  intro s hs
  have h1 : cw s.2 8 ∈ x.2.1.map cn := by
    rw [hx.fr]
    exact List.mem_map.2 ⟨s, hs, rfl⟩
  obtain ⟨r, hr, e⟩ := List.mem_map.1 h1
  have h2 := hx.len_cn.1 r hr
  rw [e] at h2
  simpa [cw] using h2

theorem MX.length_eq : x.2.1.length = x.2.2.1.length := by
  have := congrArg List.length hx.fr
  simpa using this

theorem MX.vals : x.2.2.1.map (fun s => bv (cw s.2 8)) = (List.range x.2.2.1.length).map (fun j => 1 + j) ∧
    bv (true :: x.2.2.2.1.2) = 1 + x.2.2.1.length := by
  have h1 := chain_val x.2.1 cn1 cn _ _ hx.cp fun r _ => bv_cn r
  rw [bv_i1, hx.length_eq] at h1
  refine ⟨?_, h1.2⟩
  rw [← h1.1]
  have h2 := congrArg (List.map bv) hx.fr
  rw [List.map_map, List.map_map] at h2
  exact h2.symm

theorem MX.size_eq : Nat.size (x.2.2.1.length + 1) = x.1.length + 1 := by
  have h1 := hx.vals.2
  have h2 := hx.len_cn.2
  have h3 := bv_lt x.2.2.2.1.2
  simp only [bv, if_true] at h1
  have e : x.2.2.2.1.2.length = x.1.length := by omega
  rw [e] at h1 h3
  refine le_antisymm ?_ ?_
  · rw [Nat.size_le, pow_succ]
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    omega

end Facts

/-- The records of numbers that are defined. -/
def dfN (tr : List P.Step) : List (Rec K) := (P.kN, ![0, 0, 0, 0]) :: tr.map Mach.al

/-- The list that is sorted. -/
def lsN (L : ℕ) (tr : List P.Step) : List (Sort.Rc (L + 1) (Bl K)) :=
  ((dfN tr).map (kyN L)).map (fun k => (false, k)) ++ ((tr.map Mach.ld).map (kyN L)).map fun k => (true, k)

theorem recs_lsN (L : ℕ) (tr : List P.Step) : recs 0 (lsN L tr) =
    ((dfN tr).map (cN L)).map (fun c => (false, oc c)) ++ ((tr.map Mach.ld).map (cN L)).map fun c => (true, oc c) := by
  simp only [recs, lsN, List.map_append, List.map_map, Function.comp_def, rot_zero, ofFn_kyN, oc]

theorem lsN_ne (L : ℕ) (tr : List P.Step) : lsN L tr ≠ [] := by simp [lsN, dfN]

theorem unb_zero (L : ℕ) : unb L ![0, 0, 0, 0] = List.replicate L fun _ : Fin 4 => false := by
  refine cols_ext fun j => ?_
  rw [unb_proj, List.map_replicate]
  have : (![0, 0, 0, 0] : Fin 4 → ℕ) j = 0 := by fin_cases j <;> rfl
  rw [this, bin_zero]

theorem block_of {x : XP P} (hx : ∀ s ∈ x.2.2.1, s.2.length = x.1.length + 1) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.1.length + 1) (x.2.2.1.map nst)) := by
  rw [recs_lsN]
  congr 1
  · congr 1
    rw [dfs, dfN, List.map_cons, List.map_map, List.map_map]
    congr 1
    · rw [cN, unb_zero]
    · refine List.map_congr_left fun s hs => ?_
      simp only [Function.comp, cN]
      rw [← alc_eq (hx s hs)]
      rfl
  · congr 1
    rw [lks, List.map_map, List.map_map]
    refine List.map_congr_left fun s hs => ?_
    simp only [Function.comp, cN]
    rw [← ldc_eq (hx s hs)]
    rfl

theorem MX.block {x : XP P} {bits : List Bool} (hx : MX x bits) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.1.length + 1) (x.2.2.1.map nst)) := block_of hx.len

theorem nst_lt {x : XP P} {bits : List Bool} (hx : MX x bits) {s : P.Rl × List (Fin 9 → Bool)} (hs : s ∈ x.2.2.1) (i : Fin 9) :
    (nst s).2 i < 2 ^ (x.1.length + 1) := by
  have := bv_lt (cw s.2 i)
  rw [cw, List.length_map, hx.len s hs] at this
  exact this

theorem four_lt {a b c d n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) (j : Fin 4) : (![a, b, c, d] : Fin 4 → ℕ) j < n := by
  fin_cases j <;> assumption

/-- **A matched run is a run of the machine.** -/
theorem MX.gv {x : XP P} {bits : List Bool} (hx : MX x bits) : Mach.GV (σi P bits) (x.2.2.1.map nst) := by
  refine ⟨?_, fun i => ⟨bv (x.2.2.2.1.1.map fun v => v i), ?_⟩, ?_, ?_, ?_⟩
  · rw [List.map_map, List.map_map]
    exact hx.md
  · have := congrArg (List.map bv) (hx.rg i)
    rw [List.map_cons, List.map_append, List.map_map, List.map_map, bv_i0] at this
    rw [List.map_map, List.map_map]
    exact this
  · rw [List.map_map, List.length_map]
    refine hx.vals.1.trans ?_
    exact List.map_congr_left fun j _ => by simp [σi]
  · rw [List.flatMap_map]
    exact hx.inp
  · have h1 := hx.ls
    rw [hx.block] at h1
    have h2 := (imu_table (M := M) ((dfN (x.2.2.1.map nst)).map (kyN (x.1.length + 1)))
      (((x.2.2.1.map nst).map Mach.ld).map (kyN (x.1.length + 1))) (by simp [dfN])).1 ⟨_, h1⟩
    intro st hst
    have h3 := h2 (kyN (x.1.length + 1) (Mach.ld st)) (List.mem_map.2 ⟨_, List.mem_map.2 ⟨st, hst, rfl⟩, rfl⟩)
    obtain ⟨ρ, hρ, e⟩ := List.mem_map.1 h3
    have hst' := hst
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst'
    have hb1 : ∀ j, (Mach.ld (nst s)).2 j < 2 ^ (x.1.length + 1) :=
      four_lt (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _)
    have hb2 : ∀ j, ρ.2 j < 2 ^ (x.1.length + 1) := by
      rw [dfN, List.mem_cons, List.mem_map] at hρ
      rcases hρ with rfl | ⟨st', hst', rfl⟩
      · exact four_lt (by positivity) (by positivity) (by positivity) (by positivity)
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hst'
        exact four_lt (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _)
    rw [← kyN_inj hb2 hb1 e]
    exact hρ

theorem unit_list {l l' : List Unit} (h : l.length = l'.length) : l = l' :=
  List.ext_getElem h fun _ _ _ => rfl

/-- The run is determined by the run of the machine. -/
theorem MX.unique {x x' : XP P} {bits : List Bool} (hx : MX x bits) (hx' : MX x' bits)
    (e : x.2.2.1.map nst = x'.2.2.1.map nst) : x = x' := by
  have hT : x.2.2.1.length = x'.2.2.1.length := by simpa using congrArg List.length e
  have hL : x.1.length = x'.1.length := by
    have h1 := hx.size_eq
    have h2 := hx'.size_eq
    rw [hT] at h1
    omega
  have e1 : x.1 = x'.1 := unit_list hL
  have e3 : x.2.2.1 = x'.2.2.1 := by
    refine List.ext_getElem hT fun i h1 h2 => ?_
    have h3 : (x.2.2.1.map nst)[i]'(by simpa using h1) = (x'.2.2.1.map nst)[i]'(by simpa using h2) := by
      simp only [e]
    simp only [List.getElem_map] at h3
    have l1 := hx.len _ (List.getElem_mem h1)
    have l2 := hx'.len _ (List.getElem_mem h2)
    have h4 := congrArg Prod.fst h3
    have h5 := congrArg Prod.snd h3
    refine Prod.ext h4 ?_
    have h6 := unb_bv (x.2.2.1[i]).2
    have h7 := unb_bv (x'.2.2.1[i]).2
    rw [← h6, ← h7, l1, l2, hL]
    congr 1
  have e2 : x.2.1 = x'.2.1 := by
    have h1 : x.2.1.map cn = x'.2.1.map cn := by rw [hx.fr, hx'.fr, e3]
    refine List.map_injective_iff.2 ?_ h1
    rintro ⟨u, k⟩ ⟨u', k'⟩ h
    obtain ⟨a1, a2⟩ := cut_unique h
    exact Prod.ext a1 (unit_list a2)
  have e4 : x.2.2.2.1 = x'.2.2.2.1 := by
    refine Prod.ext (cols_ext fun i => ?_) ?_
    · have h1 := hx.rg i
      have h2 := hx'.rg i
      rw [e1, e3] at h1
      have h3 := h1.symm.trans h2
      simpa using List.append_cancel_left h3
    · have h1 := hx.cp
      have h2 := hx'.cp
      rw [e1, e2] at h1
      have h3 := h1.symm.trans h2
      simpa using List.append_cancel_left h3
  have e5 : x.2.2.2.2.1 = x'.2.2.2.2.1 := by
    rw [hx.lk, hx'.lk, lks, lks, e3]
  have e6 : x.2.2.2.2.2 = x'.2.2.2.2.2 := by
    have h1 := hx.ls
    have h2 := hx'.ls
    rw [hx.block] at h1
    rw [hx'.block] at h2
    rw [e1, e3] at h1
    exact imu_unique (lsN_ne _ _) h1 h2
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 (Prod.ext e4 (Prod.ext e5 e6))))

end Nc.Uni
end

/-! Source module: Nc.Uni.Exist -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Every run of the machine is a matched run
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

theorem bin_of {L : ℕ} {w : List Bool} (hl : w.length = L) : w = bin L (bv w) := by
  have := bin_bv w
  rw [hl] at this
  exact this.symm

theorem exists_MX {tr : List P.Step} {bits : List Bool} (hgv : Mach.GV (σi P bits) tr)
    (hle : ∀ st ∈ tr, ∀ i, st.2 i ≤ tr.length) : ∃ x : XP P, MX x bits ∧ x.2.2.1.map nst = tr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hgv
  obtain ⟨k, hk⟩ : ∃ k, Nat.size (tr.length + 1) = k + 1 := by
    have : 0 < Nat.size (tr.length + 1) := Nat.size_pos.2 (by omega)
    exact ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
  set L := k + 1 with hL
  have hT1 : tr.length + 1 < 2 ^ L := by
    rw [← hk]
    exact Nat.lt_size_self _
  have hT2 : 2 ^ k ≤ tr.length + 1 := by
    rw [← Nat.lt_size, hk]
    omega
  have hlt : ∀ st ∈ tr, ∀ i, st.2 i < 2 ^ L := fun st hst i => lt_of_le_of_lt (hle st hst i) (by omega)
  have hct : ∀ j, ∃ r : List Bool × List Unit, j < tr.length → cn r = bin L (j + 1) := by
    intro j
    by_cases hj : j < tr.length
    · obtain ⟨u, m, e⟩ := exists_cut (w := bin L (j + 1)) (by
        rw [bv_bin (by omega), length_bin]
        omega)
      refine ⟨(u, List.replicate m ()), fun _ => ?_⟩
      rw [e, cn, List.length_replicate]
    · exact ⟨([], []), fun h => absurd h hj⟩
  choose ct hct using hct
  choose fin hfin using h2
  let l0 : List Unit := List.replicate k ()
  let cts : List (List Bool × List Unit) := (List.range tr.length).map ct
  let sts : List (P.Rl × List (Fin 9 → Bool)) := tr.map fun st => (st.1, unb L st.2)
  let ed : List (Fin 5 → Bool) × List Bool := (unb L fin, (bin L (tr.length + 1)).tail)
  have hnst : ∀ st ∈ tr, nst (P := P) (st.1, unb L st.2) = st := by
    intro st hst
    refine Prod.ext rfl ?_
    funext i
    simp only [nst, cw]
    rw [unb_proj, bv_bin (hlt st hst i)]
  have hmap : sts.map nst = tr := by
    simp only [sts, List.map_map]
    conv_rhs => rw [← List.map_id tr]
    exact List.map_congr_left fun st hst => hnst st hst
  have hlen : ∀ s ∈ sts, s.2.length = l0.length + 1 := by
    intro s hs
    obtain ⟨st, -, rfl⟩ := List.mem_map.1 hs
    simp [l0, length_unb, hL]
  let lkw : List (Sy M K) := encW ((sts.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)).map fun c => (true, oc c))
  have hxu : ∃ xu : XU M K, IMU xu (encW (recs 0 (lsN L tr))) := by
    refine (imu_table (M := M) ((dfN tr).map (kyN L)) ((tr.map Mach.ld).map (kyN L)) (by simp [dfN])).2 ?_
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hy
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hρ
    have h6 := h5 st hst
    refine List.mem_map.2 ⟨Mach.ld st, ?_, rfl⟩
    rw [dfN]
    simpa [σi] using h6
  obtain ⟨xu, hxu⟩ := hxu
  let x : XP P := (l0, cts, sts, ed, lkw, xu)
  have hl0 : l0.length + 1 = L := by simp [l0, hL]
  have hcts : cts.map cn = (List.range tr.length).map fun j => bin L (j + 1) := by
    simp only [cts, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    exact hct j (List.mem_range.1 hj)
  have hcts1 : cts.map cn1 = (List.range tr.length).map fun j => bin L (j + 2) := by
    simp only [cts, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have e := hct j (List.mem_range.1 hj)
    have hj' := List.mem_range.1 hj
    simp only [Function.comp]
    rw [bin_of (L := L) (w := cn1 (ct j)) (by rw [length_cn, e, length_bin]), bv_cn, e, bv_bin (by omega)]
  refine ⟨x, ⟨fun i => ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩, hmap⟩
  · have h6 := congrArg (List.map (bin L)) (hfin i)
    rw [List.map_cons, List.map_append, List.map_map, List.map_map] at h6
    have e0 : i0 l0 = bin L 0 := by rw [bin_zero, i0, hl0]
    change i0 l0 :: sts.map (fun s => cw s.2 (P.dr s.1 i)) = sts.map (fun s => cw s.2 (rv i)) ++ [(unb L fin).map fun v => v i]
    rw [e0, unb_proj]
    simp only [sts, List.map_map]
    have a1 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 (P.dr s.1 i)) ∘ fun st : P.Step => (st.1, unb L st.2)) =
        bin L ∘ fun st => st.2 (P.dr st.1 i) := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    have a2 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 (rv i)) ∘ fun st : P.Step => (st.1, unb L st.2)) =
        bin L ∘ fun st => st.2 (rv i) := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    rw [a1, a2]
    exact h6
  · change P.m0 :: sts.map (fun s => P.dst s.1) = sts.map (fun s => P.src s.1) ++ [P.mh]
    simp only [sts, List.map_map]
    exact h1
  · change i1 l0 :: cts.map cn1 = cts.map cn ++ [true :: (bin L (tr.length + 1)).tail]
    have e1 : i1 l0 = bin L 1 := by
      rw [bin_of (L := L) (w := i1 l0) (by rw [length_i1, hl0]), bv_i1]
    have e2 : true :: (bin L (tr.length + 1)).tail = bin L (tr.length + 1) := by
      rw [hL, bin, List.tail_cons]
      simp [hT2]
    rw [e1, e2, hcts, hcts1]
    have e3 : ((List.range tr.length).map fun j => bin L (j + 1)) ++ [bin L (tr.length + 1)] =
        (List.range (tr.length + 1)).map fun j => bin L (j + 1) := by
      rw [List.range_succ, List.map_append]
      rfl
    rw [e3, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  · change cts.map cn = sts.map fun s => cw s.2 8
    rw [hcts]
    have h6 := congrArg (List.map (bin L)) h3
    rw [List.map_map, List.map_map] at h6
    simp only [sts, List.map_map]
    have a1 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 8) ∘ fun st : P.Step => (st.1, unb L st.2)) =
        bin L ∘ fun st => st.2 8 := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    rw [a1, h6]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp, σi]
    congr 1
    omega
  · have hb := block_of (x := x) hlen
    change IMU xu (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
    rw [hb]
    change IMU xu (encW (recs 0 (lsN (l0.length + 1) (sts.map nst))))
    rw [hl0, hmap]
    exact hxu
  · change (sts.flatMap fun s => (P.rd s.1).toList) = bits
    simp only [sts, List.flatMap_map]
    exact h4

end Nc.Uni
end

/-! Source module: Nc.Uni.LenU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The lengths of the tapes
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset Nc.Sort

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

theorem sum_Tp (f : Tp K → ℕ) : ∑ s, f s = (∑ i, f (.rg i)) + f .md + f .cp + f .fr + f .lk + f .ls + (∑ b, f (.bk b)) +
    ∑ k, f (.cm k) := by
  let e : Tp K ≃ (Fin 5 ⊕ (Bl K ⊕ Bool)) ⊕ Fin 5 :=
    { toFun := fun s => match s with
        | .rg i => .inl (.inl i)
        | .bk b => .inl (.inr (.inl b))
        | .cm k => .inl (.inr (.inr k))
        | .md => .inr 0
        | .cp => .inr 1
        | .fr => .inr 2
        | .lk => .inr 3
        | .ls => .inr 4
      invFun := fun y => match y with
        | .inl (.inl i) => .rg i
        | .inl (.inr (.inl b)) => .bk b
        | .inl (.inr (.inr k)) => .cm k
        | .inr 0 => .md
        | .inr 1 => .cp
        | .inr 2 => .fr
        | .inr 3 => .lk
        | .inr 4 => .ls
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun y => by
        rcases y with (i | b | k) | j
        · rfl
        · rfl
        · rfl
        · fin_cases j <;> rfl }
  rw [← e.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_five (fun j => f (e.symm (.inr j)))]
  change (∑ i, f (.rg i)) + ((∑ b, f (.bk b)) + ∑ k, f (.cm k)) + (f .md + f .cp + f .fr + f .lk + f .ls) = _
  ring

theorem length_rw' (f : Bool) (w : List (Option (Bl K))) : (rw' f w : List (Sy M K)).length = w.length + 2 := by
  simp [rw']

theorem length_encW {l : List (Bool × List (Option (Bl K)))} {n : ℕ} (h : ∀ r ∈ l, r.2.length = n) :
    (encW l : List (Sy M K)).length = l.length * (n + 2) := by
  induction l with
  | nil => simp [encW]
  | cons r l ih =>
    rw [encW_cons, List.length_append, length_rw', h r (by simp), ih fun r hr => h r (by simp [hr]), List.length_cons]
    ring

theorem length_rot {n : ℕ} {j : ℕ} (hj : j ≤ n) (x : Fin n → Bl K) : (rot j x).length = n + 1 := by
  simp [rot]
  omega

theorem length_encW_recs {n : ℕ} {j : ℕ} (hj : j ≤ n) (l : List (Rc n (Bl K))) :
    (encW (recs j l) : List (Sy M K)).length = l.length * (n + 3) := by
  rw [length_encW (n := n + 1)]
  · simp [recs]
  · intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr
    exact length_rot hj _

theorem canon_length {n : ℕ} (l : List (Rc n (Bl K))) (k j : ℕ) (hjk : j + k = n) :
    (canon l k j : List (Ps M K)).length = k ∧ ∀ p ∈ (canon l k j : List (Ps M K)),
      (encW (dIn p.1) : List (Sy M K)).length = l.length * (n + 3) ∧
        ∑ b, ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length = l.length * (n + 3) := by
  induction k generalizing j with
  | zero => simp [canon]
  | succ k ih =>
    have hj : j < n := by omega
    obtain ⟨h1, h2⟩ := ih (j + 1) (by omega)
    have hl : (srt (bsl K) l j).length = l.length := length_srt mem_bsl bsl_nodup l j
    rw [canon, dif_pos hj]
    refine ⟨by rw [List.length_cons, h1], ?_⟩
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · constructor
      · rw [cps, dIn_dl, length_encW_recs hj.le, hl]
      · have h3 : ∀ b, (((cps j hj (srt (bsl K) l j) : Ps M K).2 b).map (Subtype.val : NB M K → Sy M K)).length =
            ((srt (bsl K) l j).filter fun r => r.2 ⟨j, hj⟩ = b).length * (n + 3) := by
          intro b
          have e : ((cps j hj (srt (bsl K) l j) : Ps M K).2 b).map (Subtype.val : NB M K → Sy M K) =
              encW (dOut b (dl j hj (srt (bsl K) l j))) := toNB_val _ (bar_encW _)
          rw [e, dOut_dl, length_encW_recs (by omega)]
        rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.sum_mul, Sort.sum_filter, hl]
    · exact h2 p hp

theorem sum_const_map {ι : Type*} (l : List ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ l, f i = c) : (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, h i (by simp), ih fun i hi => h i (by simp [hi]), List.length_cons]
    ring

/-- The lengths of the tapes of the sort. -/
theorem imu_length {n : ℕ} {l : List (Rc n (Bl K))} (hl : l ≠ []) {x : XU M K} (h : IMU x (encW (recs 0 l))) :
    (emU x lsT).length + ∑ b, (emU x (.tp (.bk b) true)).length + ∑ k, (emU x (.tp (.cm k) true)).length =
      (n + 1) * (l.length * (n + 3) + 1) + (n * (l.length * (n + 3)) + Fintype.card (Bl K) * n) + 2 * (l.length * (n + 2)) := by
  rw [imu_iff hl] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨c1, c2⟩ := canon_length (M := M) l n 0 (by omega)
  have hfin : (finL l).length = l.length := by
    rw [finL, List.length_map]
    exact length_srt mem_bsl bsl_nodup l n
  have hfin2 : ∀ r ∈ finL l, r.2.length = n := by
    intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr
    simp
  have hsum := sum_const_map (canon l n 0 : List (Ps M K))
    (List.length ∘ fun p : Ps M K => (encW (dIn p.1) : List (Sy M K))) (l.length * (n + 3)) (fun p hp => (c2 p hp).1)
  have e1 : (emU x lsT).length = (n + 1) * (l.length * (n + 3) + 1) := by
    rw [emU_lsT, length_blocks, h1, h2, ← recs_last, List.map_append, List.sum_append, List.map_map,
      hsum, c1, List.length_append, List.length_map, c1]
    simp only [List.map_cons, List.map_nil, List.sum_singleton, List.length_singleton]
    rw [length_encW_recs le_rfl]
    have : (srt (bsl K) l n).length = l.length := length_srt mem_bsl bsl_nodup l n
    rw [this]
    ring
  have e2 : ∑ b, (emU x (.tp (.bk b) true)).length = n * (l.length * (n + 3)) + Fintype.card (Bl K) * n := by
    have h5 : ∀ b, (emU x (.tp (.bk b) true)).length =
        (x.1.map fun p => ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum + n := by
      intro b
      rw [emU_bk_true, length_blocks, List.map_map, List.length_map, h1, c1]
      rfl
    rw [Finset.sum_congr rfl fun b _ => h5 b, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    have h6 : ∀ ps : List (Ps M K), ∑ b, (ps.map fun p => ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum =
        (ps.map fun p => ∑ b, ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum := by
      intro ps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [Finset.sum_add_distrib, ih]
    rw [h6, h1, sum_const_map _ _ (l.length * (n + 3)) (fun p hp => (c2 p hp).2), c1]
  have e3 : ∀ k, (emU x (.tp (.cm k) true)).length = l.length * (n + 2) := by
    intro k
    rw [emU_cm_true]
    have h7 : (if k then QlG x.2.2 else PlG x.2.2) = finL l := by
      cases k
      · simpa using h3
      · simpa using h4
    rw [h7, length_encW (n := n)]
    · rw [fOut, List.length_map, hfin]
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      simpa using hfin2 r' hr'
  rw [e1, e2, Finset.sum_congr rfl fun k _ => e3 k]
  simp

variable {P : Mach A M K}

theorem length_bws {ws : List (List Bool)} {n : ℕ} (h : ∀ w ∈ ws, w.length = n) :
    (bws ws : List (Sy M K)).length = ws.length * (n + 1) := by
  induction ws with
  | nil => simp [bws]
  | cons w ws ih =>
    rw [bws_cons, List.length_append, ih fun w hw => h w (by simp [hw]), List.length_cons]
    simp only [bw, List.length_append, List.length_map, List.length_singleton, h w (by simp)]
    ring

/-- The total length for T steps and L bits; b letters of records. -/
def tU (b T L : ℕ) : ℕ := 5 * ((T + 1) * (L + 1)) + (T + 1) + (T + 1) * (L + 1) + T * (L + 1) + T * (L + 4) +
  ((L + 2) * ((2 * T + 1) * (L + 4) + 1) + ((L + 1) * ((2 * T + 1) * (L + 4)) + b * (L + 1)) + 2 * ((2 * T + 1) * (L + 3)))

theorem MX.total {x : XP P} {bits : List Bool} (hx : MX x bits) :
    ∑ s, (emX P x (.tp s true)).length = tU (Fintype.card (Bl K)) x.2.2.1.length (x.1.length + 1) := by
  have hcw : ∀ s ∈ x.2.2.1, ∀ i, (cw s.2 i).length = x.1.length + 1 := by
    intro s hs i
    rw [cw, List.length_map, hx.len s hs]
  have hend : ∀ i : Fin 5, (x.2.2.2.1.1.map fun v => v i).length = x.1.length + 1 := by
    intro i
    have h1 := hx.rg i
    have h2 : ∀ w ∈ x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i], w.length = x.1.length + 1 := by
      rw [← h1]
      intro w hw
      rw [List.mem_cons, List.mem_map] at hw
      rcases hw with rfl | ⟨s, hs, rfl⟩
      · exact length_i0 _
      · exact hcw s hs _
    exact h2 _ (by simp)
  have e1 : ∀ i, (emX P x (.tp (.rg i) true)).length = (x.2.2.1.length + 1) * (x.1.length + 2) := by
    intro i
    rw [emX_rg_true, length_bws (n := x.1.length + 1)]
    · simp
    · intro w hw
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨s, hs, rfl⟩ | rfl
      · exact hcw s hs _
      · exact hend i
  have e2 : (emX P x (.tp .md true)).length = x.2.2.1.length + 1 := by
    rw [emX_md_true]
    simp
  have e3 : (emX P x (.tp .cp true)).length = (x.2.2.1.length + 1) * (x.1.length + 2) := by
    rw [emX_cp_true, length_bws (n := x.1.length + 1)]
    · simp [hx.length_eq]
    · intro w hw
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨r, hr, rfl⟩ | rfl
      · exact hx.len_cn.1 r hr
      · simpa using hx.len_cn.2
  have e4 : (emX P x (.tp .fr true)).length = x.2.2.1.length * (x.1.length + 2) := by
    rw [emX_fr_true, length_bws (n := x.1.length + 1)]
    · simp
    · intro w hw
      rw [List.mem_map] at hw
      obtain ⟨s, hs, rfl⟩ := hw
      exact hcw s hs _
  have e5 : (emX P x (.tp .lk true)).length = x.2.2.1.length * (x.1.length + 5) := by
    rw [emX_lk_true, hx.lk, length_encW (n := x.1.length + 3)]
    · simp [lks]
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
      simp [oc, cont, ldc, hx.len s hs]
  have hls := hx.ls
  rw [hx.block] at hls
  have e6 := imu_length (lsN_ne _ _) hls
  have hN : (lsN (x.1.length + 1) (x.2.2.1.map nst)).length = 2 * x.2.2.1.length + 1 := by
    simp [lsN, dfN]
    ring
  rw [hN] at e6
  have e7 : (emX P x (.tp .ls true)).length = (emU x.2.2.2.2.2 lsT).length := by rw [← emX_ls_true]
  have e8 : ∀ b, (emX P x (.tp (.bk b) true)).length = (emU x.2.2.2.2.2 (.tp (.bk b) true)).length := by
    intro b; rw [← emX_bk]
  have e9 : ∀ k, (emX P x (.tp (.cm k) true)).length = (emU x.2.2.2.2.2 (.tp (.cm k) true)).length := by
    intro k; rw [← emX_cm]
  rw [sum_Tp (fun s => (emX P x (.tp s true)).length), Finset.sum_congr rfl fun i _ => e1 i, e2, e3, e4, e5, e7,
    Finset.sum_congr rfl fun b _ => e8 b, Finset.sum_congr rfl fun k _ => e9 k]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold tU
  have e10 : ∀ a b c d e f g h' : ℕ, a + b + c + d + e + f + g + h' = a + b + c + d + e + (f + g + h') := by
    intros; omega
  rw [e10, e6]

end Nc.Uni
end

/-! Source module: NS1.Machine -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sum machines

Data are binary trees. A program is a formula of a small functional language; it is applied to a tree. A formula may
guess a bit, reject, multiply the weight of the run by a fixed constant `θ` of the ring `A` (named by a list of
bits), or by a constant that is *only named* (`mul`); the names are kept in the *bill* of the run. `run a b` applies
the program that is the value of `a` to the value of `b`. Every step costs 1.

`Ev θ F x l`: all runs of the formula `F` at the tree `x` stop, and `l` is the list of the accepting runs.
-/

namespace NS1
namespace Tree
@[simp] theorem hd_cons (a b : Tree) : (cons a b).hd = a := rfl
@[simp] theorem tl_cons (a b : Tree) : (cons a b).tl = b := rfl
@[simp] theorem hd_nil : nil.hd = nil := rfl
@[simp] theorem tl_nil : nil.tl = nil := rfl
@[simp] theorem len_num (k : ℕ) : (num k).len = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [num, len, ih]

theorem size_pos (x : Tree) : 0 < x.size := by cases x <;> simp [size]

@[simp] theorem path_ofBits (w : List Bool) : (ofBits w).path = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [ofBits, path, ih]
    cases b <;> simp [bit, one]

theorem bit_ne_nil {b : Bool} : bit b ≠ nil ↔ b = true := by cases b <;> simp [bit, one]

theorem size_ofBits (w : List Bool) : (ofBits w).size ≤ 4 * w.length + 1 := by
  induction w with
  | nil => simp [ofBits, size]
  | cons b w ih =>
    have : (bit b).size ≤ 3 := by cases b <;> simp [bit, one, size]
    simp only [ofBits, size, List.length_cons]
    omega

end Tree

open _root_.NS1.Tree

namespace Fm
theorem ofTree_code (F : Fm) : ofTree F.code = F := by
  induction F with
  | quote c => rw [code, ofTree]; rfl
  | id => rw [code, ofTree]; rfl
  | hd a ih => rw [code, ofTree]; simp [ih]
  | tl a ih => rw [code, ofTree]; simp [ih]
  | cons a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | ite a b c iha ihb ihc => rw [code, ofTree]; simp [iha, ihb, ihc]
  | run a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | guess => rw [code, ofTree]; simp
  | fail => rw [code, ofTree]; simp
  | theta a ih => rw [code, ofTree]; simp [ih]
  | mul a ih => rw [code, ofTree]; simp [ih]

end Fm

variable {A : Type} [CommRing A]

variable {θ : List Bool → A}
/-- The list of the accepting runs is determined. -/
theorem Ev.unique {F : Fm} {x : Tree} {l l' : List (Run A)} (h : Ev θ F x l) (h' : Ev θ F x l') : l = l' := by
  induction h generalizing l' with
  | quote c x => cases h'; rfl
  | id x => cases h'; rfl
  | hd _ ih => cases h' with | hd h => rw [ih h]
  | tl _ ih => cases h' with | tl h => rw [ih h]
  | cons _ _ iha ihb => cases h' with | cons ha hb => rw [iha ha, ihb hb]
  | ite _ _ _ iha ihb ihc =>
    cases h' with
    | ite ha hb hc =>
      obtain rfl := iha ha
      refine List.flatMap_congr fun r hr => ?_
      by_cases h : r.out = .nil
      · rw [ihc r hr h (hc r hr h)]
      · rw [ihb r hr h (hb r hr h)]
  | run _ _ _ iha ihb ih =>
    cases h' with
    | run ha hb h =>
      obtain rfl := iha ha
      obtain rfl := ihb hb
      refine List.flatMap_congr fun r hr => List.flatMap_congr fun s hs => ?_
      rw [ih r hr s hs (h r hr s hs)]
  | guess x => cases h'; rfl
  | fail x => cases h'; rfl
  | theta _ ih => cases h' with | theta h => rw [ih h]
  | mul _ ih => cases h' with | mul h => rw [ih h]

theorem Hl.ev {F : Fm} {x : Tree} (h : Hl θ F x) : Ev θ F x (evl θ F x) := by
  rw [evl, dif_pos h]
  exact h.choose_spec

theorem Ev.hl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : Hl θ F x := ⟨l, h⟩

theorem Ev.evl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : evl θ F x = l := h.hl.ev.unique h

theorem Ev.run' {a b : Fm} {x : Tree} {la lb : List (Run A)} (ha : Ev θ a x la) (hb : Ev θ b x lb)
    (h : ∀ r ∈ la, ∀ s ∈ lb, Hl θ (Fm.ofTree r.out) s.out) : Ev θ (.run a b) x
      (la.flatMap fun r => lb.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out) :=
  .run ha hb fun r hr s hs => (h r hr s hs).ev

/-- A run without guesses and weights. -/
def Dt (θ : List Bool → A) (F : Fm) (x o : Tree) (k : ℕ) : Prop := Ev θ F x [.det k o]

theorem Dt.quote (c x : Tree) : Dt θ (.quote c) x c 1 := Ev.quote c x

theorem Dt.id (x : Tree) : Dt θ .id x x 1 := Ev.id x

theorem Dt.hd {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.hd a) x o.hd (k + 1) := Ev.hd h

theorem Dt.tl {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.tl a) x o.tl (k + 1) := Ev.tl h

theorem Dt.cons {a b : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (hb : Dt θ b x p j) :
    Dt θ (.cons a b) x (.cons o p) (k + j + 1) := by
  have := Ev.cons ha hb
  simpa [Dt, Run.det, Run.seq, Run.tick] using this

/-- Weights and costs of runs after a step without guesses. -/
def Run.delay (k : ℕ) (r : Run A) : Run A := ⟨k + r.cost, r.th, r.bill, r.out⟩

theorem Ev.ite_true {a b c : Fm} {x o : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (c := c) (L := fun _ => l) ha (fun r _ _ => hb) (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd h ho)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.ite_false {a b c : Fm} {x : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (b := b) (L := fun _ => l) ha (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd rfl h) (fun r _ _ => hc)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.run_det {a b : Fm} {x p d : Tree} {k j : ℕ} {l : List (Run A)} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d l) : Ev θ (.run a b) x (l.map (Run.delay (k + j + 1))) := by
  have := Ev.run (L := fun _ _ => l) ha hb (fun r hr s hs => by
    simp only [List.mem_singleton] at hr hs
    subst hr hs
    exact h)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

/-- `let`: apply `body` to the value of `e`. -/
def lett (e body : Fm) : Fm := .run (.quote body.code) e

theorem Ev.lett {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ body s.out) : Ev θ (lett e body) x
      (le.flatMap fun s => (NS1.evl θ body s.out).map fun t => ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩) := by
  have := Ev.run' (Dt.quote (θ := θ) body.code x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Run.det, Fm.ofTree_code]
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  refine Eq.mp ?_ this
  unfold NS1.lett
  congr 1
  refine List.flatMap_congr fun s _ => ?_
  simp only [Run.det, Fm.ofTree_code]
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.seq, Run.tick, one_mul, List.nil_append, Run.mk.injEq, and_true]
  omega

end NS1
end

/-! Source module: NS1.Budget -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Budgets

A budget is a trie with numbers (in binary, lowest digit first) at its leaves; the leaves are named by the paths.
-/

namespace NS1

/-- Budgets. -/
inductive Bt where
  /-- no name -/
  | none
  /-- a name with a number -/
  | leaf (w : List Bool)
  /-- names that begin with 0, names that begin with 1 -/
  | node (l r : Bt)

/-- Subtract 1. -/
def decw : List Bool → Option (List Bool)
  | [] => Option.none
  | true :: w => some (false :: w)
  | false :: w => (decw w).map (true :: ·)

theorem length_decw {w w' : List Bool} (h : decw w = some w') : w'.length = w.length := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      rfl
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [ih hv]

namespace Bt

/-- Subtract 1 at a name. -/
def dec : List Bool → Bt → Option Bt
  | _, none => Option.none
  | [], leaf w => (decw w).map leaf
  | _ :: _, leaf _ => Option.none
  | [], node _ _ => Option.none
  | true :: p, node l r => (dec p r).map (node l)
  | false :: p, node l r => (dec p l).map fun l' => node l' r

/-- Subtract 1 at all names of a bill. -/
def decAll : List (List Bool) → Bt → Option Bt
  | [], t => some t
  | p :: b, t => (dec p t).bind (decAll b)

/-- All numbers are 0. -/
def zero : Bt → Bool
  | none => true
  | leaf w => w.all (! ·)
  | node l r => l.zero && r.zero

/-- A bound for the time to subtract 1. -/
def ht : Bt → ℕ
  | none => 0
  | leaf w => w.length + 1
  | node l r => max l.ht r.ht + 1

/-- The number of nodes and digits. -/
def nds : Bt → ℕ
  | none => 1
  | leaf w => w.length + 1
  | node l r => l.nds + r.nds + 1

/-- Budgets as trees. -/
def enc : Bt → Tree
  | none => .nil
  | leaf w => .cons .nil (.ofBits w)
  | node l r => .cons (.cons l.enc r.enc) .nil

theorem size_enc (t : Bt) : t.enc.size ≤ 4 * t.nds := by
  induction t with
  | none => simp [enc, Tree.size, nds]
  | leaf w =>
    have := Tree.size_ofBits w
    simp only [enc, Tree.size, nds]
    omega
  | node l r ihl ihr =>
    simp only [enc, Tree.size, nds]
    omega

theorem ht_dec {p : List Bool} {t t' : Bt} (h : dec p t = some t') : t'.ht = t.ht := by
  induction t generalizing p t' with
  | none => simp [dec] at h
  | leaf w =>
    cases p with
    | nil =>
      simp only [dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [ht, length_decw hv]
    | cons b p => simp [dec] at h
  | node l r ihl ihr =>
    cases p with
    | nil => simp [dec] at h
    | cons b p =>
      cases b with
      | true =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [ht, ihr hv]
      | false =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [ht, ihl hv]

theorem nds_dec {p : List Bool} {t t' : Bt} (h : dec p t = some t') : t'.nds = t.nds := by
  induction t generalizing p t' with
  | none => simp [dec] at h
  | leaf w =>
    cases p with
    | nil =>
      simp only [dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [nds, length_decw hv]
    | cons b p => simp [dec] at h
  | node l r ihl ihr =>
    cases p with
    | nil => simp [dec] at h
    | cons b p =>
      cases b with
      | true =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [nds, ihr hv]
      | false =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [nds, ihl hv]

theorem decAll_append (b b' : List (List Bool)) (t : Bt) : decAll (b ++ b') t = (decAll b t).bind (decAll b') := by
  induction b generalizing t with
  | nil => rfl
  | cons p b ih =>
    simp only [List.cons_append, decAll, Option.bind_assoc]
    congr 1
    funext t
    exact ih t

theorem ht_decAll {b : List (List Bool)} {t t' : Bt} (h : decAll b t = some t') : t'.ht = t.ht := by
  induction b generalizing t with
  | nil =>
    simp only [decAll, Option.some.injEq] at h
    rw [h]
  | cons p b ih =>
    simp only [decAll, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, h⟩ := h
    rw [ih h, ht_dec hs]

theorem nds_decAll {b : List (List Bool)} {t t' : Bt} (h : decAll b t = some t') : t'.nds = t.nds := by
  induction b generalizing t with
  | nil =>
    simp only [decAll, Option.some.injEq] at h
    rw [h]
  | cons p b ih =>
    simp only [decAll, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, h⟩ := h
    rw [ih h, nds_dec hs]

end Bt

end NS1
end

/-! Source module: NS1.Interp -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# An interpreter that counts the names of constants

`IF` is a formula of the language that evaluates formulas; instead of multiplying by a named constant it subtracts 1
from a budget. `WF` also checks that in the end the budgets are used up. These formulas are plain: they use no
named constants.
-/

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Dt.ite_true {a b c : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil) (hb : Dt θ b x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_true (c := c) ha ho hb

theorem Dt.ite_false {a b c : Fm} {x p : Tree} {k j : ℕ} (ha : Dt θ a x .nil k) (hc : Dt θ c x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_false (b := b) ha hc

theorem Dt.run {a b : Fm} {x p d o : Tree} {k j i : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Dt θ (Fm.ofTree p) d o i) : Dt θ (.run a b) x o (k + j + 1 + i) := Ev.run_det ha hb h

theorem Ev.ite_true_nil {a b c : Fm} {x o : Tree} {k : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x []) : Ev θ (.ite a b c) x [] := Ev.ite_true (c := c) ha ho hb

theorem Ev.ite_false_nil {a b c : Fm} {x : Tree} {k : ℕ} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x []) : Ev θ (.ite a b c) x [] := Ev.ite_false (b := b) ha hc

theorem Ev.run_nil {a b : Fm} {x p d : Tree} {k j : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d []) : Ev θ (.run a b) x [] := Ev.run_det ha hb h

theorem Ev.cons_nil_left {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x []) (hb : Ev θ b x l) :
    Ev θ (.cons a b) x [] := Ev.cons ha hb

theorem Ev.cons_nil_right {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x l) (hb : Ev θ b x []) :
    Ev θ (.cons a b) x [] := by
  have := Ev.cons ha hb
  have e : (l.flatMap fun r => ([] : List (Run A)).map fun s => (r.seq s).tick (.cons r.out s.out)) = [] :=
    List.flatMap_eq_nil_iff.2 fun _ _ => rfl
  rw [e] at this
  exact this

section Programs

/-- Subtract 1 from a number; the argument is (this program, the number). -/
def DW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) (.cons (.quote .nil) (.tl (.tl .id)))
    (.cons (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))) .fail

theorem DW_some {w w' : List Bool} (h : decw w = some w') :
    ∃ k ≤ 20 * w.length, Dt θ DW (.cons DW.code (ofBits w)) (ofBits w') k := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_true (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.cons (.quote _ _) (.tl (.tl (.id _)))))⟩
      simp only [List.length_cons]
      omega
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := ih hv
      have hd' : Dt θ (Fm.ofTree DW.code) (.cons DW.code (ofBits w)) (ofBits v) k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
        (.cons (.quote _ _) (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) hd')))⟩
      simp only [List.length_cons]
      omega

theorem DW_none {w : List Bool} (h : decw w = none) : Ev θ DW (.cons DW.code (ofBits w)) [] := by
  induction w with
  | nil => exact Ev.ite_false_nil (.tl (.id _)) (.fail _)
  | cons b w ih =>
    cases b with
    | true => simp [decw] at h
    | false =>
      simp only [decw, Option.map_eq_none_iff] at h
      refine Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ?_)))
      simp only [hd_cons, Fm.ofTree_code]
      exact ih h

/-- Subtract 1 in a budget; the argument is (this program, (the name, the budget)). -/
def DC : Fm :=
  .ite (.tl (.tl .id))
    (.ite (.hd (.tl (.tl .id)))
      (.ite (.hd (.tl .id))
        (.ite (.hd (.hd (.tl .id)))
          (.cons (.cons (.hd (.hd (.tl (.tl .id)))) (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.tl (.hd (.tl (.tl .id)))))))) (.quote .nil))
          (.cons (.cons (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.hd (.hd (.tl (.tl .id))))))) (.tl (.hd (.tl (.tl .id))))) (.quote .nil)))
        .fail)
      (.ite (.hd (.tl .id)) .fail
        (.cons (.quote .nil) (.run (.quote DW.code) (.cons (.quote DW.code) (.tl (.tl (.tl .id))))))))
    .fail

theorem DC_some {t t' : Bt} {x : Tree} (h : Bt.dec x.path t = some t') :
    ∃ k ≤ 60 * t.ht, Dt θ DC (.cons DC.code (.cons x t.enc)) t'.enc k := by
  induction t generalizing x t' with
  | none => simp [Bt.dec] at h
  | leaf w =>
    cases x with
    | cons a b => simp [path, Bt.dec] at h
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := DW_some (θ := θ) hv
      have hd' : Dt θ (Fm.ofTree DW.code) (.cons DW.code (ofBits w)) (ofBits v) k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.tl (.id _))))
        (Dt.ite_false (.hd (.tl (.id _))) (.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _)
          (.tl (.tl (.tl (.id _))))) hd'))))⟩
      simp only [Bt.ht]
      omega
  | node l r ihl ihr =>
    cases x with
    | nil => simp [path, Bt.dec] at h
    | cons a b =>
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihl hv
        have hd' : Dt θ (Fm.ofTree DC.code) (.cons DC.code (.cons b l.enc)) v.enc k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_false (.hd (.hd (.tl (.id _))))
            (.cons (.cons (.run (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _))))
              (.hd (.hd (.tl (.tl (.id _))))))) hd') (.tl (.hd (.tl (.tl (.id _)))))) (.quote _ _)))))⟩
        simp only [Bt.ht]
        omega
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihr hv
        have hd' : Dt θ (Fm.ofTree DC.code) (.cons DC.code (.cons b r.enc)) v.enc k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_true (.hd (.hd (.tl (.id _))))
            (by simpa using ha) (.cons (.cons (.hd (.hd (.tl (.tl (.id _))))) (.run (.hd (.id _)) (.cons (.hd (.id _))
              (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _))))))) hd')) (.quote _ _)))))⟩
        simp only [Bt.ht]
        omega

theorem DC_none {t : Bt} {x : Tree} (h : Bt.dec x.path t = none) : Ev θ DC (.cons DC.code (.cons x t.enc)) [] := by
  induction t generalizing x with
  | none => exact Ev.ite_false_nil (.tl (.tl (.id _))) (.fail _)
  | leaf w =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc]) (Ev.ite_false_nil (.hd (.tl (.tl (.id _)))) ?_)
    cases x with
    | cons a b => exact Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) (.fail _)
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_none_iff] at h
      refine Ev.ite_false_nil (.hd (.tl (.id _))) (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.quote _ _)
        (.cons (.quote _ _) (.tl (.tl (.tl (.id _))))) ?_))
      simp only [Fm.ofTree_code]
      exact DW_none h
  | node l r ihl ihr =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc]) (Ev.ite_true_nil (.hd (.tl (.tl (.id _))))
      (by simp [Bt.enc]) ?_)
    cases x with
    | nil => exact Ev.ite_false_nil (.hd (.tl (.id _))) (.fail _)
    | cons a b =>
      refine Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) ?_
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_none_iff] at h
        refine Ev.ite_false_nil (.hd (.hd (.tl (.id _)))) (Ev.cons_nil_left (Ev.cons_nil_left (Ev.run_nil (.hd (.id _))
          (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _)))) (.hd (.hd (.tl (.tl (.id _))))))) ?_)
          (Dt.tl (.hd (.tl (.tl (.id _)))))) (Dt.quote _ _))
        simp only [hd_cons, Fm.ofTree_code]
        exact ihl h
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_none_iff] at h
        refine Ev.ite_true_nil (.hd (.hd (.tl (.id _)))) (by simpa using ha) (Ev.cons_nil_left (Ev.cons_nil_right
          (Dt.hd (.hd (.tl (.tl (.id _))))) (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _))
          (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _))))))) ?_)) (Dt.quote _ _))
        simp only [hd_cons, Fm.ofTree_code]
        exact ihr h

/-- Check that a number is 0. -/
def AW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) .fail (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem AW_ev (w : List Bool) : ∃ k ≤ 20 * w.length + 5, ∃ o, Ev θ AW (.cons AW.code (ofBits w))
    (if w.all (! ·) then [.det k o] else []) := by
  induction w with
  | nil => exact ⟨_, by norm_num, _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | cons b w ih =>
    obtain ⟨k, hk, o, ih⟩ := ih
    cases b with
    | true =>
      refine ⟨0, Nat.zero_le _, .nil, ?_⟩
      simp only [List.all_cons, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
      exact Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_true_nil (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.fail _))
    | false =>
      simp only [List.all_cons, Bool.not_false, Bool.true_and]
      by_cases h : w.all (! ·)
      · simp only [h, if_true] at ih ⊢
        have ih' : Dt θ (Fm.ofTree AW.code) (.cons AW.code (ofBits w)) o k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, o, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
          (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ih'))⟩
        simp only [List.length_cons]
        omega
      · simp only [h] at ih ⊢
        refine ⟨0, Nat.zero_le _, .nil, ?_⟩
        refine Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_false_nil (.hd (.tl (.id _)))
          (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ?_))
        simp only [hd_cons, Fm.ofTree_code]
        exact ih

/-- Check that all numbers of a budget are 0. -/
def AZ : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id))
    (.cons (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))))
    (.run (.quote AW.code) (.cons (.quote AW.code) (.tl (.tl .id)))))
  (.quote .nil)

theorem AZ_ev (t : Bt) : ∃ k ≤ 40 * t.nds, ∃ o, Ev θ AZ (.cons AZ.code t.enc) (if t.zero then [.det k o] else []) := by
  induction t with
  | none => exact ⟨_, by simp [Bt.nds], _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | leaf w =>
    obtain ⟨k, hk, o, h⟩ := AW_ev (θ := θ) w
    simp only [Bt.zero]
    by_cases hz : w.all (! ·)
    · simp only [hz, if_true] at h ⊢
      have h' : Dt θ (Fm.ofTree AW.code) (.cons AW.code (ofBits w)) o k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, o, Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.id _)))
        (.run (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _)))) h'))⟩
      simp only [Bt.nds]
      omega
    · simp only [hz] at h ⊢
      refine ⟨0, Nat.zero_le _, .nil, ?_⟩
      refine Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc]) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _)))) ?_))
      simp only [Fm.ofTree_code]
      exact h
  | node l r ihl ihr =>
    obtain ⟨kl, hkl, ol, hl⟩ := ihl
    obtain ⟨kr, hkr, or, hr⟩ := ihr
    have el : Ev θ (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id))))) (.cons AZ.code (Bt.node l r).enc)
        ((if l.zero then [.det kl ol] else []).map (Run.delay 10)) := by
      refine Ev.run_det (k := 2) (j := 7) (.hd (.id _)) (.cons (.hd (.id _)) (.hd (.hd (.tl (.id _))))) ?_
      simp only [hd_cons, Fm.ofTree_code]
      exact hl
    have er : Ev θ (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))) (.cons AZ.code (Bt.node l r).enc)
        ((if r.zero then [.det kr or] else []).map (Run.delay 10)) := by
      refine Ev.run_det (k := 2) (j := 7) (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.hd (.tl (.id _))))) ?_
      simp only [hd_cons, Fm.ofTree_code]
      exact hr
    simp only [Bt.zero]
    by_cases hzl : l.zero
    · by_cases hzr : r.zero
      · simp only [hzl, hzr, if_true, Bool.and_self] at el er ⊢
        refine ⟨_, ?_, _, Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _)))
          (by simp [Bt.enc]) (Dt.cons (k := 10 + kl) (j := 10 + kr) el er))⟩
        simp only [Bt.nds]
        omega
      · simp only [hzl, hzr, if_true, if_false, Bool.and_false, Bool.false_eq_true, List.map_nil] at el er ⊢
        exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
          (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_right el er))⟩
    · simp only [hzl, if_false, Bool.false_and, Bool.false_eq_true, List.map_nil] at el er ⊢
      exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
        (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_left el er))⟩

end Programs

end NS1
end

/-! Source module: NS1.Eval -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The interpreter

`IF` at `(IF, (f, (x, t)))` simulates the formula `f` at `x` with the budgets `t`; its value is the value of the run
and the budgets that are left.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}

theorem forall₂_flatMap {R : α → β → Prop} {S : γ → δ → Prop} {l : List α} {l' : List β} {f : α → List γ}
    {g : β → List δ} (h : List.Forall₂ R l l') (hf : ∀ a ∈ l, ∀ b ∈ l', R a b → List.Forall₂ S (f a) (g b)) :
    List.Forall₂ S (l.flatMap f) (l'.flatMap g) := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append (hf _ List.mem_cons_self _ List.mem_cons_self hab) (ih fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem forall₂_exists {R : α → β → Prop} {l : List α} {l' : List β} (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) :
    ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- `let`, for lists that correspond to other lists. -/
theorem lett_rel {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le) {Q : List β}
    {R : Run A → β → Prop} (hR : List.Forall₂ R le Q) {Q2 : β → List γ} {R2 : Run A → γ → Prop}
    (h : ∀ s ∈ le, ∀ b ∈ Q, R s b → ∃ l2, Ev θ body s.out l2 ∧
      List.Forall₂ (fun t c => R2 ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩ c) l2 (Q2 b)) :
    ∃ l, Ev θ (lett e body) x l ∧ List.Forall₂ R2 l (Q.flatMap Q2) := by
  refine ⟨_, Ev.lett he fun s hs => ?_, forall₂_flatMap hR fun s hs b hb hsb => ?_⟩
  · obtain ⟨b, hb, hsb⟩ := forall₂_exists hR hs
    obtain ⟨l2, h2, -⟩ := h s hs b hb hsb
    exact h2.hl
  · obtain ⟨l2, h2, h3⟩ := h s hs b hb hsb
    rw [h2.evl, List.forall₂_map_left_iff]
    exact h3

end Rel

section Cases

/-- Choose by the length of the value of `b`. -/
def selF : List Fm → Fm → Fm
  | [], _ => .fail
  | c :: cs, b => .ite b (selF cs (.tl b)) c

theorem selF_ev {cs : List Fm} {b : Fm} {x o : Tree} {k : ℕ} (hb : Dt θ b x o k) {l : List (Run A)}
    (h : ∀ c, cs[o.len]? = some c → Ev θ c x l) (h0 : cs.length ≤ o.len → l = []) :
    ∃ k' ≤ cs.length * (k + cs.length + 1), Ev θ (selF cs b) x (l.map (Run.delay k')) := by
  induction cs generalizing b o k with
  | nil =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h0 (Nat.zero_le _)]
    exact .fail x
  | cons c cs ih =>
    cases o with
    | nil =>
      refine ⟨k + 1, ?_, Ev.ite_false hb (h c rfl)⟩
      simp only [List.length_cons]
      nlinarith
    | cons a o =>
      obtain ⟨k', hk', h'⟩ := ih (b := .tl b) (o := o) hb.tl (fun c hc => h c (by simpa [len] using hc))
        (fun hl => h0 (by simp only [List.length_cons, len]; omega))
      refine ⟨k + 1 + k', ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · have := Ev.ite_true (c := c) hb (by simp) h'
        rw [List.map_map] at this
        refine Eq.mp ?_ this
        congr 1
        refine List.map_congr_left fun r _ => ?_
        simp only [Run.delay, Function.comp_apply, Run.mk.injEq, and_true]
        omega

end Cases

section Code

/-- The formula in the environment. -/
def fF (b : Fm) : Fm := .hd (.tl b)
/-- The argument in the environment. -/
def fX (b : Fm) : Fm := .hd (.tl (.tl b))
/-- The budgets in the environment. -/
def fS (b : Fm) : Fm := .tl (.tl (.tl b))
/-- The opcode. -/
def fO (b : Fm) : Fm := .hd (fF b)
/-- The arguments of the formula. -/
def fA (b : Fm) : Fm := .tl (fF b)
/-- Recursive call. -/
def rec' (b a x s : Fm) : Fm := .run (.hd b) (.cons (.hd b) (.cons a (.cons x s)))

/-- First call, with the environment kept. -/
def call1 : Fm := .cons .id (rec' .id (.hd (fA .id)) (fX .id) (fS .id))

/-- Second call, with everything kept. -/
def call2 : Fm := .cons .id (rec' (.hd .id) (.tl (fA (.hd .id))) (fX (.hd .id)) (.tl (.tl .id)))

/-- The cases of the interpreter. -/
def caseL : List Fm := [
  -- quote
  .cons (fA .id) (fS .id),
  -- id
  .cons (fX .id) (fS .id),
  -- hd
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.hd (.hd .id)) (.tl .id)),
  -- tl
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.tl (.hd .id)) (.tl .id)),
  -- cons
  lett call1 (lett call2 (.cons (.cons (.hd (.tl (.hd .id))) (.hd (.tl .id))) (.tl (.tl .id)))),
  -- ite
  lett call1 (.ite (.hd (.tl .id))
    (rec' (.hd .id) (.hd (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))
    (rec' (.hd .id) (.tl (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))),
  -- run
  lett call1 (lett call2 (rec' (.hd (.hd .id)) (.hd (.tl (.hd .id))) (.hd (.tl .id)) (.tl (.tl .id)))),
  -- guess
  .cons .guess (fS .id),
  -- fail
  .fail,
  -- theta
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.theta (.hd .id)) (.tl .id)),
  -- mul
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.quote .nil) (.run (.quote DC.code) (.cons (.quote DC.code) .id)))
  ]

/-- The interpreter. -/
def IF : Fm := selF caseL (fO .id)

/-- The environment of the interpreter. -/
def env (f x : Tree) (t : Bt) : Tree := .cons IF.code (.cons f (.cons x t.enc))

theorem Dt.fX {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fX b) y x (k + 3) :=
  .hd (.tl (.tl h))

theorem Dt.fS {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fS b) y t.enc (k + 3) :=
  .tl (.tl (.tl h))

theorem Dt.fO {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fO b) y f.hd (k + 3) :=
  .hd (.hd (.tl h))

theorem Dt.fA {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fA b) y f.tl (k + 3) :=
  .tl (.hd (.tl h))

/-- A recursive call. -/
theorem rec_ev {b a x s : Fm} {y g z : Tree} {f' x' : Tree} {t t' : Bt} {kb ka kx ks : ℕ}
    (hb : Dt θ b y (env f' x' t') kb) (ha : Dt θ a y g ka) (hx : Dt θ x y z kx) (hs : Dt θ s y t.enc ks)
    {l : List (Run A)} (h : Ev θ IF (env g z t) l) :
    Ev θ (rec' b a x s) y (l.map (Run.delay (2 * kb + ka + kx + ks + 6))) := by
  have := Ev.run_det (Dt.hd hb) (.cons (.hd hb) (.cons ha (.cons hx hs))) (l := l) (by
    show Ev θ (Fm.ofTree IF.code) _ l
    rw [Fm.ofTree_code]
    exact h)
  refine Eq.mp ?_ this
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.delay, Run.mk.injEq, and_true]
  omega

/-- The runs that stay within the budgets, with what is left. -/
def simS (t : Bt) (l : List (Run A)) : List (Run A × Bt) :=
  l.filterMap fun r => (Bt.decAll r.bill t).map fun t' => (r, t')

theorem mem_simS {t : Bt} {l : List (Run A)} {q : Run A × Bt} (h : q ∈ simS t l) :
    q.1 ∈ l ∧ Bt.decAll q.1.bill t = some q.2 := by
  rw [simS, List.mem_filterMap] at h
  obtain ⟨r, hr, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨t', ht, rfl⟩ := h
  exact ⟨hr, ht⟩

theorem simS_map {t : Bt} {l : List (Run A)} {G : Run A → Run A} (h : ∀ r, (G r).bill = r.bill) :
    simS t (l.map G) = (simS t l).map fun q => (G q.1, q.2) := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [simS, List.map_cons, List.filterMap_cons, h] at ih ⊢
    cases Bt.decAll r.bill t with
    | none => exact ih
    | some t' =>
      simp only [Option.map_some, List.map_cons]
      rw [ih]

theorem simS_append {t : Bt} {l l' : List (Run A)} : simS t (l ++ l') = simS t l ++ simS t l' := by
  simp [simS]

theorem simS_flatMap {t : Bt} {la : List (Run A)} {L : Run A → List (Run A)} {G : Run A → Run A → Run A}
    (h : ∀ r s, (G r s).bill = r.bill ++ s.bill) : simS t (la.flatMap fun r => (L r).map (G r)) =
      (simS t la).flatMap fun q => (simS q.2 (L q.1)).map fun p => (G q.1 p.1, p.2) := by
  have one : ∀ (r : Run A) (l : List (Run A)), simS t (l.map (G r)) =
      ((Bt.decAll r.bill t).toList.map fun t' => (r, t')).flatMap fun q =>
        (simS q.2 l).map fun p => (G q.1 p.1, p.2) := by
    intro r l
    cases hd : Bt.decAll r.bill t with
    | none =>
      simp only [Option.toList_none, List.map_nil, List.flatMap_nil, simS, List.filterMap_map]
      rw [List.filterMap_eq_nil_iff]
      intro s _
      simp [h, Bt.decAll_append, hd]
    | some t' =>
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      induction l with
      | nil => rfl
      | cons s l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, h, Bt.decAll_append, hd, Option.bind_some] at ih ⊢
        cases Bt.decAll s.bill t' with
        | none => exact ih
        | some t'' =>
          simp only [Option.map_some, List.map_cons]
          rw [ih]
  induction la with
  | nil => rfl
  | cons r la ih =>
    rw [List.flatMap_cons, simS_append, ih, one]
    simp only [simS, List.filterMap_cons]
    cases Bt.decAll r.bill t with
    | none => simp
    | some t' => simp

end Code

end NS1
end

/-! Source module: NS1.EvalThm -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The interpreter is right
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Run.seq_assoc (r s t : Run A) : (r.seq s).seq t = r.seq (s.seq t) := by
  simp [Run.seq, add_assoc, mul_assoc, List.append_assoc]

theorem Fm.ofTree_cases (f : Tree) :
    (f.hd.len = 0 ∧ ofTree f = quote f.tl) ∨ (f.hd.len = 1 ∧ ofTree f = id) ∨
    (f.hd.len = 2 ∧ ofTree f = hd (ofTree f.tl)) ∨ (f.hd.len = 3 ∧ ofTree f = tl (ofTree f.tl)) ∨
    (f.hd.len = 4 ∧ ofTree f = cons (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 5 ∧ ofTree f = ite (ofTree f.tl.hd) (ofTree f.tl.tl.hd) (ofTree f.tl.tl.tl)) ∨
    (f.hd.len = 6 ∧ ofTree f = run (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 7 ∧ ofTree f = guess) ∨ ((f.hd.len = 8 ∨ 11 ≤ f.hd.len) ∧ ofTree f = fail) ∨
    (f.hd.len = 9 ∧ ofTree f = theta (ofTree f.tl)) ∨ (f.hd.len = 10 ∧ ofTree f = mul (ofTree f.tl)) := by
  cases f with
  | nil => left; exact ⟨rfl, by rw [ofTree]; rfl⟩
  | cons o a =>
    rw [ofTree]
    simp only [hd_cons, tl_cons]
    rcases hn : o.len with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp

/-- What the interpreter does in one run: `q` is a run of the formula and the budgets that are left. -/
structure RelJ (M j : ℕ) (r : Run A) (q : Run A × Bt) : Prop where
  th : r.th = q.1.th
  bill : r.bill = []
  out : r.out = .cons q.1.out q.2.enc
  cost : r.cost + j ≤ M * q.1.cost

/-- The bound for the overhead. -/
def MM (H : ℕ) : ℕ := 1000 + 100 * H

theorem IF_case {f x : Tree} {t : Bt} {c : Fm} (hc : caseL[f.hd.len]? = some c) {M : ℕ}
    {Q : List (Run A × Bt)} (h : ∃ l, Ev θ c (env f x t) l ∧ List.Forall₂ (RelJ M 300) l Q) :
    ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ M 0) l' Q := by
  obtain ⟨l, hl, hQ⟩ := h
  obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := l)
    (fun c' hc' => by
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      exact hl)
    (fun hlen => by
      rw [List.getElem?_eq_none hlen] at hc
      simp at hc)
  refine ⟨_, h', ?_⟩
  rw [List.forall₂_map_left_iff]
  have hk : k' ≤ 300 := hk'.trans (by simp [caseL])
  refine hQ.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
  have := hr.cost
  simp only [Run.delay]
  omega

/-- A call for a single value: `let r = IF(args)`. -/
theorem call0 {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) {body : Fm}
    {Q2 : Run A × Bt → List (Run A × Bt)}
    (hb : ∀ q ∈ simS t l, ∃ l2, Ev θ body (.cons q.1.out q.2.enc) l2 ∧ List.Forall₂ (fun s p => s.bill = [] ∧
      q.1.th * s.th = p.1.th ∧ s.out = .cons p.1.out p.2.enc ∧ M * q.1.cost + s.cost + 400 ≤ M * p.1.cost) l2 (Q2 q)) :
    ∃ l', Ev θ (lett (rec' .id (fA .id) (fX .id) (fS .id)) body) (env f x t) l' ∧
      List.Forall₂ (RelJ M 300) l' ((simS t l).flatMap Q2) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := rec_ev (Dt.id (env f x t)) (Dt.fA (Dt.id _)) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1
  refine lett_rel e (Q := simS t l) (R := fun s q => s.th = q.1.th ∧ s.bill = [] ∧ s.out = .cons q.1.out q.2.enc ∧
    s.cost ≤ M * q.1.cost + 30) ?_ ?_
  · rw [List.forall₂_map_left_iff]
    refine h1'.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
    have := hr.cost
    simp only [Run.delay]
    omega
  · rintro s - q hq ⟨e1, e2, e3, e4⟩
    obtain ⟨l2, h2, h2'⟩ := hb q hq
    rw [← e3] at h2
    refine ⟨l2, h2, h2'.imp fun u p hu => ?_⟩
    obtain ⟨f1, f2, f3, f4⟩ := hu
    refine ⟨?_, ?_, f3, ?_⟩
    · simp only [e1, f2]
    · simp only [e2, f1, List.append_nil]
    · simp only
      omega

theorem call1_rel {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.hd x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) :
    ∃ l', Ev θ call1 (env f x t) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (env f x t) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l' (simS t l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := Ev.cons (Dt.id (θ := θ) (env f x t))
    (rec_ev (Dt.id (env f x t)) (.hd (Dt.fA (Dt.id _))) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem call2_rel {f x o : Tree} {t t1 : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.tl x t1) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t1 l)) :
    ∃ l', Ev θ call2 (.cons (env f x t) (.cons o t1.enc)) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (.cons (env f x t) (.cons o t1.enc)) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l'
      (simS t1 l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have hb : Dt θ (.hd .id) (.cons (env f x t) (.cons o t1.enc)) (env f x t) 2 := .hd (.id _)
  have e := Ev.cons (Dt.id (θ := θ) (.cons (env f x t) (.cons o t1.enc)))
    (rec_ev hb (.tl (Dt.fA hb)) (Dt.fX hb) (t := t1) (.tl (.tl (Dt.id _))) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem flatMap_single {α β : Type*} (l : List α) (g : α → β) : (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **The interpreter is right.** -/
theorem interp {H : ℕ} {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) :
    ∀ f, Fm.ofTree f = F → ∀ t : Bt, t.ht ≤ H →
      ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ (MM H) 0) l' (simS t l) := by
  have hM : 1000 ≤ MM H := by unfold MM; omega
  induction h with
  | quote c x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fA .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fA (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | id x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fX .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | @hd a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.hd) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.hd (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @tl a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.tl) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.tl (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @cons a b x la lb ha hb iha ihb =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick (.cons r.out s.out)) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [← flatMap_single]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    rw [u3]
    refine ⟨_, Dt.cons (.cons (.hd (.tl (.hd (.id _)))) (.hd (.tl (.id _)))) (.tl (.tl (.id _))), .cons ⟨?_, ?_, rfl, ?_⟩ .nil⟩
    · simp [Run.det, Run.seq, Run.tick, s1, u1]
    · simp [Run.det, s2, u2]
    · simp only [Run.det, Run.seq, Run.tick]
      nlinarith
  | @ite a b c x la L ha hb hc iha ihb ihc =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    have hy : Dt θ (.hd .id) s.out (env f x t) 2 := by rw [s3]; exact .hd (.id _)
    have hv : Dt θ (.hd (.tl .id)) s.out q.1.out 3 := by rw [s3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) s.out q.2.enc 3 := by rw [s3]; exact .tl (.tl (.id _))
    by_cases hq0 : q.1.out = .nil
    · obtain ⟨l2, e2, r2⟩ := ihc q.1 (mem_simS hq).1 hq0 f.tl.tl.tl rfl q.2 hqt
      refine ⟨_, Ev.ite_false (hq0 ▸ hv) (rec_ev hy (.tl (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
    · obtain ⟨l2, e2, r2⟩ := ihb q.1 (mem_simS hq).1 hq0 f.tl.tl.hd rfl q.2 hqt
      refine ⟨_, Ev.ite_true hv hq0 (rec_ev hy (.hd (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
  | @run a b x la lb L ha hb hL iha ihb ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    have hlist : (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out) =
        la.flatMap fun r => (lb.flatMap fun s => (L r s).map fun t => s.seq t).map fun u => (r.seq u).tick u.out := by
      refine List.flatMap_congr fun r _ => ?_
      rw [List.map_flatMap]
      refine List.flatMap_congr fun s _ => ?_
      rw [List.map_map]
      refine List.map_congr_left fun u _ => ?_
      simp only [Function.comp_apply, Run.seq_assoc]
      rfl
    rw [hlist, simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [simS_flatMap (G := fun r s => r.seq s) (fun _ _ => rfl), List.map_flatMap]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    have hpt : p.2.ht ≤ H := (Bt.ht_decAll (mem_simS hp).2).trans_le hqt
    obtain ⟨l3, e3, r3⟩ := ih q.1 (mem_simS hq).1 p.1 (mem_simS hp).1 q.1.out rfl p.2 hpt
    have hy : Dt θ (.hd (.hd .id)) u.out (env f x t) 3 := by rw [u3]; exact .hd (.hd (.id _))
    have hf' : Dt θ (.hd (.tl (.hd .id))) u.out q.1.out 4 := by rw [u3]; exact .hd (.tl (.hd (.id _)))
    have hx : Dt θ (.hd (.tl .id)) u.out p.1.out 3 := by rw [u3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) u.out p.2.enc 3 := by rw [u3]; exact .tl (.tl (.id _))
    refine ⟨_, rec_ev hy hf' hx ht' e3, ?_⟩
    rw [List.forall₂_map_left_iff, List.map_map, List.forall₂_map_right_iff]
    refine r3.imp fun v w hv => ⟨?_, ?_, ?_, ?_⟩
    · simp [Run.delay, Run.seq, Run.tick, s1, u1, hv.th]
    · simp [Run.delay, s2, u2, hv.bill]
    · simp [Run.delay, Run.seq, Run.tick, hv.out]
    · have := hv.cost
      simp only [Run.delay, Run.seq, Run.tick, Function.comp_apply]
      nlinarith
  | guess x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons .guess (fS .id)) (by rw [h1]; rfl) ⟨_, Ev.cons (.guess _) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨?_, rfl, rfl, ?_⟩ (.cons ⟨?_, rfl, rfl, ?_⟩ .nil)
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
  | fail x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := [])
      (fun c' hc' => by
        rcases h1 with h1 | h1
        · rw [h1] at hc'
          obtain rfl := Option.some.inj hc'
          exact .fail _
        · rw [List.getElem?_eq_none (by simpa [caseL] using h1)] at hc'
          simp at hc')
      (fun _ => rfl)
    exact ⟨_, h', by simp [simS]⟩
  | @theta a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Ev.cons (Ev.theta (Dt.hd (.id _))) (Dt.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, ?_, rfl, ?_⟩ .nil
    · simp [Run.seq, Run.tick, Run.det]
    · simp only [Run.seq, Run.tick, Run.det]
      nlinarith
  | @mul a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    have hlist : simS t (l.map fun r => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)) =
        (simS t l).flatMap fun q => ((Bt.dec q.1.out.path q.2).map fun t' =>
          ((⟨q.1.cost + 1, q.1.th, q.1.bill ++ [q.1.out.path], .nil⟩ : Run A), t')).toList := by
      clear ih h
      induction l with
      | nil => rfl
      | cons r l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, Bt.decAll_append] at ih ⊢
        cases hd : Bt.decAll r.bill t with
        | none =>
          simp only [Option.bind_none, Option.map_none]
          exact ih
        | some t1 =>
          simp only [Option.bind_some, Bt.decAll, Option.map_some, List.flatMap_cons]
          cases hd2 : Bt.dec r.out.path t1 with
          | none =>
            simp only [Option.bind_none, Option.map_none, Option.toList_none, List.nil_append]
            exact ih
          | some t2 =>
            simp only [Option.bind_some, Option.map_some, Option.toList_some, List.singleton_append]
            rw [ih]
    rw [hlist]
    refine call0 (ih f.tl rfl t ht) fun q hq => ?_
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    cases hd : Bt.dec q.1.out.path q.2 with
    | none =>
      refine ⟨_, Ev.cons_nil_right (Dt.quote _ _) (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.id _)) ?_), .nil⟩
      rw [Fm.ofTree_code]
      exact DC_none hd
    | some t2 =>
      obtain ⟨k, hk, hdc⟩ := DC_some (θ := θ) hd
      refine ⟨_, Dt.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _) (.id _)) (i := k) ?_), .cons ⟨rfl, ?_, rfl, ?_⟩ .nil⟩
      · rw [Fm.ofTree_code]
        exact hdc
      · simp [Run.det]
      · simp only [Run.det]
        have : 60 * q.2.ht + 420 ≤ MM H := by unfold MM; omega
        nlinarith

end NS1
end

/-! Source module: NS1.Postpone -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Constants are postponed

`WF` applied to (program, (argument, budgets)) has, as plain weighted sum, the sum of the weights of the runs whose
names of constants are exactly the given budgets. Summed over all budgets with the powers of the constants this is
the value of the program.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT
/-- The constant with a given name (0 if there is none). -/
def lookup : KT R → List Bool → R
  | none, _ => 0
  | leaf c, [] => c
  | leaf _, _ :: _ => 0
  | node _ _, [] => 0
  | node _ r, true :: p => r.lookup p
  | node l _, false :: p => l.lookup p

/-- Numbers with `J` digits. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | J + 1 => [false, true].flatMap fun b => (words J).map (b :: ·)

/-- The value of a number. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * val w

/-- All budgets with `J` digits for the names of a trie, with the products of the powers of its constants. -/
def budg (J : ℕ) : KT R → List (Bt × R)
  | none => [(.none, 1)]
  | leaf c => (words J).map fun w => (.leaf w, c ^ val w)
  | node l r => (l.budg J).flatMap fun p => (r.budg J).map fun q => (.node p.1 q.1, p.2 * q.2)

end KT

/-- The bill uses up the budgets. -/
def ok (t : Bt) (b : List (List Bool)) : Bool := ((Bt.decAll b t).map Bt.zero).getD false

theorem ok_nil (t : Bt) : ok t [] = t.zero := rfl

theorem ok_cons (t : Bt) (p : List Bool) (b : List (List Bool)) :
    ok t (p :: b) = ((Bt.dec p t).map fun t' => ok t' b).getD false := by
  unfold ok
  simp only [Bt.decAll]
  cases Bt.dec p t <;> rfl

theorem all_not_iff (w : List Bool) : (w.all (! ·)) = true ↔ KT.val w = 0 := by
  induction w with
  | nil => simp [KT.val]
  | cons b w ih =>
    cases b with
    | true => simp [KT.val]
    | false => simp [KT.val, ← ih]

theorem decw_val (w : List Bool) : (decw w = none ∧ KT.val w = 0) ∨ ∃ w', decw w = some w' ∧ KT.val w = KT.val w' + 1 := by
  induction w with
  | nil => left; simp [decw, KT.val]
  | cons b w ih =>
    cases b with
    | true => right; exact ⟨false :: w, rfl, by simp [KT.val]; omega⟩
    | false =>
      rcases ih with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · left; simp [decw, h1, KT.val, h2]
      · right
        refine ⟨true :: w', by simp [decw, h1], ?_⟩
        simp only [KT.val, h2]
        simp
        omega

theorem ok_leaf (w : List Bool) (b : List (List Bool)) :
    ok (.leaf w) b = true ↔ (∀ p ∈ b, p = []) ∧ KT.val w = b.length := by
  induction b generalizing w with
  | nil =>
    rw [ok_nil, Bt.zero, all_not_iff]
    simp
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | cons a p => simp [Bt.dec]
    | nil =>
      rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · simp only [Bt.dec, h1, Option.map_none, Option.getD_none, Bool.false_eq_true, List.length_cons, false_iff]
        rintro ⟨-, h⟩
        omega
      · simp only [Bt.dec, h1, Option.map_some, Option.getD_some, ih, List.mem_cons, forall_eq_or_imp, true_and,
          List.length_cons]
        refine and_congr_right fun _ => ?_
        omega

/-- The names that begin with a given bit. -/
def part (a : Bool) (b : List (List Bool)) : List (List Bool) := b.filterMap fun p => match p with
  | [] => none
  | c :: p => if c = a then some p else none

theorem part_cons (a c : Bool) (p : List Bool) (b : List (List Bool)) :
    part a ((c :: p) :: b) = if c = a then p :: part a b else part a b := by
  unfold part
  by_cases h : c = a <;> simp [h]

theorem length_part_le (a : Bool) (b : List (List Bool)) : (part a b).length ≤ b.length :=
  List.length_filterMap_le _ _

theorem ok_node (l r : Bt) (b : List (List Bool)) :
    ok (.node l r) b = true ↔ [] ∉ b ∧ ok l (part false b) = true ∧ ok r (part true b) = true := by
  induction b generalizing l r with
  | nil => simp [ok_nil, part, Bt.zero]
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | nil => simp [Bt.dec]
    | cons a p =>
      cases a with
      | true =>
        rw [part_cons, part_cons, if_neg (by simp), if_pos rfl, ok_cons]
        cases h : Bt.dec p r with
        | none => simp [Bt.dec, h]
        | some r' => simp [Bt.dec, h, ih]
      | false =>
        rw [part_cons, part_cons, if_pos rfl, if_neg (by simp), ok_cons]
        cases h : Bt.dec p l with
        | none => simp [Bt.dec, h]
        | some l' => simp [Bt.dec, h, ih]

theorem ok_none (b : List (List Bool)) : ok .none b = true ↔ b = [] := by
  cases b with
  | nil => simp [ok_nil, Bt.zero]
  | cons p b => simp [ok_cons, Bt.dec]

theorem sum_words (J n : ℕ) (c : R) :
    ((KT.words J).map fun w => if KT.val w = n then c else 0).sum = if n < 2 ^ J then c else 0 := by
  induction J generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst h
      simp [KT.words, KT.val]
    · have h' : ¬ 0 = n := fun e => h e.symm
      simp [KT.words, KT.val, h, h']
  | succ J ih =>
    have e0 : ((KT.words J).map fun w => if KT.val (false :: w) = n then c else 0).sum =
        if n % 2 = 0 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 0
      · have : ∀ w, (KT.val (false :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (false :: w) = n) = False := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    have e1 : ((KT.words J).map fun w => if KT.val (true :: w) = n then c else 0).sum =
        if n % 2 = 1 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 1
      · have : ∀ w, (KT.val (true :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (true :: w) = n) = False := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map,
      List.sum_append, Function.comp_def]
    rw [e0, e1]
    by_cases hn : n < 2 ^ (J + 1)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, hn]
    · simp [hn]

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prod_lookup_node (l r : KT R) (b : List (List Bool)) : (b.map (KT.node l r).lookup).prod =
    if [] ∈ b then 0 else ((part false b).map l.lookup).prod * ((part true b).map r.lookup).prod := by
  induction b with
  | nil => simp [part]
  | cons p b ih =>
    cases p with
    | nil => simp [KT.lookup]
    | cons a p =>
      rw [List.map_cons, List.prod_cons, ih, part_cons, part_cons]
      cases a with
      | true =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.true_eq_false, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring
      | false =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.false_eq_true, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring

/-- **All budgets together.** -/
theorem sum_budg (J : ℕ) (K : KT R) (b : List (List Bool)) (hb : b.length < 2 ^ J) :
    ((K.budg J).map fun q => if ok q.1 b = true then q.2 else 0).sum = (b.map K.lookup).prod := by
  induction K generalizing b with
  | none =>
    simp only [KT.budg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ok_none]
    cases b with
    | nil => simp
    | cons p b => simp [KT.lookup]
  | leaf c =>
    simp only [KT.budg, List.map_map, Function.comp_def, ok_leaf]
    by_cases h : ∀ p ∈ b, p = []
    · have e1 : ((KT.words J).map fun w => if (∀ p ∈ b, p = []) ∧ KT.val w = b.length then c ^ KT.val w else 0) =
          (KT.words J).map fun w => if KT.val w = b.length then c ^ b.length else 0 := by
        refine List.map_congr_left fun w _ => ?_
        by_cases h2 : KT.val w = b.length
        · simp [h2, if_pos h]
        · simp [h2]
      rw [e1, sum_words, if_pos hb]
      have : b.map (KT.leaf c).lookup = List.replicate b.length c := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun x hx => ?_⟩
        rw [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [h p hp]
        rfl
      rw [this, List.prod_replicate]
    · simp only [h, false_and, if_false, List.map_const', List.sum_replicate, smul_zero]
      push Not at h
      obtain ⟨p, hp, hne⟩ := h
      symm
      apply List.prod_eq_zero
      rw [List.mem_map]
      refine ⟨p, hp, ?_⟩
      cases p with
      | nil => exact absurd rfl hne
      | cons a p => rfl
  | node l r ihl ihr =>
    have h1 := ihl (part false b) (lt_of_le_of_lt (length_part_le _ _) hb)
    have h2 := ihr (part true b) (lt_of_le_of_lt (length_part_le _ _) hb)
    rw [prod_lookup_node, ← h1, ← h2]
    simp only [KT.budg, sum_flatMap_map, List.map_map, Function.comp_def, ok_node]
    by_cases h : [] ∈ b
    · simp [h]
    · simp only [h, not_false_eq_true, true_and, if_false]
      rw [← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      by_cases h3 : ok p.1 (part false b) = true <;> by_cases h4 : ok q.1 (part true b) = true <;> simp [h3, h4]



/-- Apply a program; then check that the budgets are used up. The argument is (program, (argument, budgets)). -/
def WF : Fm := lett (.cons (.quote AZ.code) (.tl (lett (.cons (.quote IF.code) .id) IF))) AZ

theorem simS_cons (t : Bt) (r : Run A) (l : List (Run A)) :
    simS t (r :: l) = ((Bt.decAll r.bill t).map fun t' => (r, t')).toList ++ simS t l := by
  simp only [simS, List.filterMap_cons]
  cases Bt.decAll r.bill t <;> rfl

theorem map_simS (t : Bt) (l : List (Run A)) :
    ((simS t l).flatMap fun q => if q.2.zero then [q] else []).map (fun q => q.1.th) =
      (l.filter fun r => ok t r.bill).map Run.th := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [simS_cons, List.flatMap_append, List.map_append, ih, List.filter_cons]
    cases hd : Bt.decAll r.bill t with
    | none =>
      have : ok t r.bill = false := by rw [ok, hd]; rfl
      simp [this]
    | some t' =>
      have : ok t r.bill = t'.zero := by rw [ok, hd]; rfl
      rw [this]
      by_cases hz : t'.zero <;> simp [hz]

theorem sum_filter_th (t : Bt) (l : List (Run A)) :
    ((l.filter fun r => ok t r.bill).map Run.th).sum = (l.map fun r => if ok t r.bill = true then r.th else 0).sum := by
  induction l with
  | nil => rfl
  | cons r l ih => cases hr : ok t r.bill <;> simp [hr, ih]

/-- **Lemma 1, one bill**: `WF` is plain; it has the runs whose bill is the budget. -/
theorem WF_ev {H T : ℕ} {p d : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) d l) (hT : ∀ r ∈ l, r.cost ≤ T)
    {t : Bt} (ht : t.ht ≤ H) : ∃ l', Ev θ WF (.cons p (.cons d t.enc)) l' ∧
      (∀ r ∈ l', r.bill = [] ∧ r.cost ≤ MM H * T + 40 * t.nds + 40) ∧
      l'.map Run.th = (l.filter fun r => ok t r.bill).map Run.th := by
  obtain ⟨l1, e1, r1⟩ := interp h p rfl t ht
  -- the interpreter
  obtain ⟨l2, e2, r2⟩ := lett_rel (body := IF) (Dt.cons (.quote IF.code (.cons p (.cons d t.enc))) (.id _))
    (Q := [()]) (R := fun s _ => s = .det 3 (env p d t)) (.cons rfl .nil) (Q2 := fun _ => simS t l)
    (R2 := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.out = .cons q.1.out q.2.enc ∧ r.cost ≤ MM H * q.1.cost + 5)
    (by
      rintro s - - - rfl
      refine ⟨l1, e1, r1.imp fun r q hr => ⟨?_, ?_, hr.out, ?_⟩⟩
      · simp [Run.det, hr.th]
      · simp [Run.det, hr.bill]
      · have := hr.cost
        simp only [Run.det]
        omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at r2
  -- the check
  have e3 := Ev.cons (Dt.quote (θ := θ) AZ.code (.cons p (.cons d t.enc))) (Ev.tl e2)
  obtain ⟨l4, e4, r4⟩ := lett_rel (body := AZ) e3 (Q := simS t l)
    (R := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.out = .cons AZ.code q.2.enc ∧ r.cost ≤ MM H * q.1.cost + 10) (by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
      refine r2.imp fun r q hr => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.seq, Run.tick, Run.det, h2]
      · simp [Run.seq, Run.tick, Run.det, h3]
      · simp only [Run.seq, Run.tick, Run.det]
        omega) (Q2 := fun q => if q.2.zero then [q] else [])
    (R2 := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.cost ≤ MM H * q.1.cost + 40 * t.nds + 40) (by
      rintro s - q hq ⟨h1, h2, h3, h4⟩
      obtain ⟨k, hk, o, h5⟩ := AZ_ev (θ := θ) q.2
      rw [← h3] at h5
      refine ⟨_, h5, ?_⟩
      have hn : q.2.nds = t.nds := Bt.nds_decAll (mem_simS hq).2
      by_cases hz : q.2.zero
      · simp only [hz, if_true]
        refine .cons ⟨?_, ?_, ?_⟩ .nil
        · simp [Run.det, h1]
        · simp [Run.det, h2]
        · simp only [Run.det]
          omega
      · simp only [hz]
        exact .nil)
  refine ⟨l4, e4, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, h1, h2, h3⟩ := forall₂_exists r4 hr
    refine ⟨h2, h3.trans ?_⟩
    rw [List.mem_flatMap] at hq
    obtain ⟨q', hq', hq⟩ := hq
    have : q = q' := by
      split_ifs at hq
      · simpa using hq
      · simp at hq
    subst this
    have := hT _ (mem_simS hq').1
    have := Nat.mul_le_mul_left (MM H) this
    omega
  · rw [← map_simS]
    clear e4
    generalize ((simS t l).flatMap fun q => if q.2.zero then [q] else []) = Q at r4
    induction r4 with
    | nil => rfl
    | cons h _ ih => simp [h.1, ih]

variable [Algebra A R]

/-- **Lemma 1 (postponing).** The value of a list of runs is the sum, over all budgets, of the powers of the constants
times the sums of the weights of the runs that use up the budgets. -/
theorem val_eq_sum_budg {J : ℕ} {K : KT R} {κ : List Bool → R} {l : List (Run A)}
    (hJ : ∀ r ∈ l, r.bill.length < 2 ^ J) (hκ : ∀ r ∈ l, ∀ p ∈ r.bill, κ p = K.lookup p) :
    val κ l = ((K.budg J).map fun q =>
      q.2 * algebraMap A R (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum).sum := by
  induction l with
  | nil => simp [val]
  | cons r l ih =>
    have h1 := ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr)) fun r hr => hκ r (List.mem_cons_of_mem _ hr)
    have h2 := sum_budg J K r.bill (hJ r List.mem_cons_self)
    have h3 : (r.bill.map κ).prod = (r.bill.map K.lookup).prod := by
      congr 1
      exact List.map_congr_left fun p hp => hκ r List.mem_cons_self p hp
    have h4 : val κ (r :: l) = wt κ r + val κ l := by simp [val]
    rw [h4, h1, wt, h3, ← h2, ← List.sum_map_mul_left, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    congr 1
    by_cases h : ok q.1 r.bill = true
    · simp only [h, if_true]
      ring
    · simp [h]

end NS1
end

/-! Source module: NS1.Guess -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Guessing the budgets and multiplying by the powers of the constants
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- The constants `c, c², c⁴, …` (`n` of them); the names are `0, 10, 110, …`. -/
def comb (c : R) : ℕ → KT R
  | 0 => none
  | n + 1 => node (leaf c) (comb (c ^ 2) n)

/-- The powers `c ^ (2 ^ b)`, `b < B`, of all constants. -/
def expand (B : ℕ) : KT R → KT R
  | none => none
  | leaf c => comb c B
  | node l r => node (l.expand B) (r.expand B)

/-- Names of the constants. -/
def Leaf : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => p = []
  | node _ _, [] => False
  | node _ r, true :: p => r.Leaf p
  | node l _, false :: p => l.Leaf p

theorem Leaf.inB {K : KT R} {p : List Bool} (h : K.Leaf p) {b B : ℕ} (hb : b < B) : K.InB B (p ++ pw b) := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨b, hb, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem pw_succ (b : ℕ) : pw (b + 1) = true :: pw b := rfl

theorem combVal_pw (c : R) (b : ℕ) : combVal c (pw b) = c ^ 2 ^ b := by
  induction b generalizing c with
  | zero => simp [pw, combVal]
  | succ b ih => rw [pw_succ, combVal, ih, ← pow_mul, pow_succ' 2 b]

theorem Leaf.lk {K : KT R} {p : List Bool} (h : K.Leaf p) : ∃ c, ∀ i, K.lk (p ++ pw i) = c ^ 2 ^ i := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨c, fun i => combVal_pw c i⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem lookup_comb (c : R) {B b : ℕ} (h : b < B) : (comb c B).lookup (pw b) = combVal c (pw b) := by
  induction b generalizing c B with
  | zero =>
    cases B with
    | zero => omega
    | succ B => rfl
  | succ b ih =>
    cases B with
    | zero => omega
    | succ B =>
      rw [pw_succ, comb, lookup, combVal]
      exact ih _ (by omega)

theorem lookup_expand {B : ℕ} {K : KT R} {p : List Bool} (h : K.InB B p) : K.lk p = (K.expand B).lookup p := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    rw [expand, lookup_comb c hb, lk]
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem InB.mono {B B' : ℕ} (hB : B ≤ B') {K : KT R} {p : List Bool} (h : K.InB B p) : K.InB B' p := by
  induction K generalizing p with
  | none => exact h
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨b, lt_of_lt_of_le hb hB, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem nds_comb (c : R) (n : ℕ) : (comb c n).nds = 2 * n + 1 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [comb, nds, ih]; omega

theorem nds_pos (K : KT R) : 0 < K.nds := by cases K <;> simp [nds]

theorem nds_expand (B : ℕ) (K : KT R) : (K.expand B).nds ≤ K.nds * (2 * B + 1) := by
  induction K with
  | none => simp [expand, nds]
  | leaf c => simp [expand, nds, nds_comb]
  | node l r ihl ihr =>
    simp only [expand, nds]
    nlinarith

theorem ht_comb (c : R) (n : ℕ) : (comb c n).ht ≤ n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    have := ih (c ^ 2)
    simp only [comb, ht]
    omega

theorem ht_expand (B : ℕ) (K : KT R) : (K.expand B).ht ≤ K.ht + B := by
  induction K with
  | none => simp [expand, ht]
  | leaf c =>
    have := ht_comb c B
    simp only [expand, ht]
    omega
  | node l r ihl ihr =>
    simp only [expand, ht]
    omega

theorem length_words {J : ℕ} {w : List Bool} (h : w ∈ words J) : w.length = J := by
  induction J generalizing w with
  | zero => simp [words] at h; simp [h]
  | succ J ih =>
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, -, v, hv, rfl⟩ := h
    simp [ih hv]

theorem ht_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.ht ≤ K.ht + J + 1 := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.ht]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.ht, length_words hw, ht]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.ht, ht]
    omega

theorem nds_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.nds ≤ K.nds * (J + 1) := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.nds, nds]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.nds, length_words hw, nds]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.nds, nds]
    nlinarith

end KT

section Formulas

/-- Guess a bit; if it is 1, multiply by the constant with the name `p`. -/
def gbit (p : List Bool) : Fm := .ite .guess (.cons (.mul (.quote (ofBits p))) (.quote .nil)) (.quote .nil)

theorem gbit_ev (p : List Bool) (x : Tree) : Ev θ (gbit p) x [⟨3, 1, [], .nil⟩, ⟨6, 1, [p], one⟩] := by
  have h1 : Ev θ (.cons (.mul (.quote (ofBits p))) (.quote .nil)) x [⟨4, 1, [p], one⟩] := by
    have := Ev.cons (Ev.mul (Ev.quote (θ := θ) (ofBits p) x)) (Ev.quote .nil x)
    simpa [Run.det, Run.seq, Run.tick, one] using this
  have := Ev.ite (L := fun r => if r.out = .nil then [.det 1 .nil] else [⟨4, 1, [p], one⟩]) (Ev.guess (θ := θ) x)
    (b := .cons (.mul (.quote (ofBits p))) (.quote .nil)) (c := .quote .nil)
    (fun r _ h => by rw [if_neg h]; exact h1) (fun r _ h => by rw [if_pos h]; exact Ev.quote .nil x)
  simpa [Run.det, Run.seq, Run.tick, one, gbit] using this

/-- Guess the digits of a number; multiply by the powers of a constant. `ν i` is the exponent in the name that is
used for the power `2 ^ i`. -/
def gw (ν : ℕ → ℕ) (pre : List Bool) (b : ℕ) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | j, n + 1 => .cons (gbit (pre ++ KT.pw (ν (b + j)))) (gw ν pre b (j + 1) n)

/-- The budgets of the powers of a constant. -/
def gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | b, n + 1 => .cons (.cons (.cons (.quote .nil) (gw ν pre b 0 J)) (gcomb ν J pre (b + 1) n)) (.quote .nil)

/-- The budgets of all powers `2 ^ b`, `b < B`, of all constants. -/
def gt (ν : ℕ → ℕ) (J B : ℕ) : KT R → List Bool → Fm
  | .none, _ => .quote .nil
  | .leaf _, pre => gcomb ν J pre 0 B
  | .node l r, pre => .cons (.cons (gt ν J B l (pre ++ [false])) (gt ν J B r (pre ++ [true]))) (.quote .nil)

/-- A run that guesses a budget and multiplies by the powers of the constants. -/
structure RelG (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (q : Bt × R) : Prop where
  th : r.th = 1
  out : r.out = q.1.enc
  bill : (r.bill.map κ).prod = q.2
  names : ∀ p ∈ r.bill, P p
  cost : r.cost ≤ c

variable {κ : List Bool → R} {P : List Bool → Prop} {ν : ℕ → ℕ}

theorem gw_ev {pre : List Bool} {b : ℕ} {c : R} (x : Tree) {n j : ℕ}
    (h : ∀ i < j + n, κ (pre ++ KT.pw (ν (b + i))) = c ^ 2 ^ (b + i) ∧ P (pre ++ KT.pw (ν (b + i)))) :
    ∃ l, Ev θ (gw ν pre b j n) x l ∧ List.Forall₂ (fun r w => r.th = 1 ∧ r.out = ofBits w ∧
      (r.bill.map κ).prod = (c ^ 2 ^ (b + j)) ^ KT.val w ∧ (∀ p ∈ r.bill, P p) ∧ r.cost ≤ 8 * n + 1) l (KT.words n) := by
  induction n generalizing j with
  | zero => exact ⟨_, .quote .nil x, .cons ⟨rfl, rfl, by simp [Run.det, KT.val], by simp [Run.det], by simp [Run.det]⟩ .nil⟩
  | succ n ih =>
    obtain ⟨l, e, hl⟩ := ih (j := j + 1) (fun i hi => h i (by omega))
    obtain ⟨hκ, hP⟩ := h j (by omega)
    refine ⟨_, Ev.cons (gbit_ev _ x) e, ?_⟩
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.nil_append, h3, KT.val, Bool.false_eq_true, if_false, zero_add, ← pow_mul]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · simpa [Run.seq, Run.tick] using h4
      · simp only [Run.seq, Run.tick]
        omega
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.singleton_append, List.map_cons, List.prod_cons, h3, hκ, KT.val, if_true,
          ← pow_mul, ← pow_add]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · intro p hp
        simp only [Run.seq, Run.tick, List.singleton_append, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hP
        · exact h4 p hp
      · simp only [Run.seq, Run.tick]
        omega

theorem node_rel {f g : Fm} {x : Tree} {lf lg : List (Run A)} {Qf Qg : List (Bt × R)} {cf cg : ℕ}
    (hf : Ev θ f x lf) (hg : Ev θ g x lg) (rf : List.Forall₂ (RelG κ P cf) lf Qf)
    (rg : List.Forall₂ (RelG κ P cg) lg Qg) : ∃ l, Ev θ (.cons (.cons f g) (.quote .nil)) x l ∧
      List.Forall₂ (RelG κ P (cf + cg + 3)) l
        (Qf.flatMap fun p => Qg.map fun q => (Bt.node p.1 q.1, p.2 * q.2)) := by
  refine ⟨_, Ev.cons (Ev.cons hf hg) (Ev.quote .nil x), ?_⟩
  rw [List.flatMap_assoc]
  refine forall₂_flatMap rf fun r _ p _ hr => ?_
  have e : ((lg.map fun s => (r.seq s).tick (.cons r.out s.out)).flatMap fun u =>
      [Run.det 1 Tree.nil].map fun s => (u.seq s).tick (.cons u.out s.out)) =
      lg.map fun s => ((r.seq s).tick (.cons r.out s.out)).seq (.det 1 .nil) |>.tick (.cons (.cons r.out s.out) .nil) := by
    rw [List.flatMap_map]
    simp only [List.map_cons, List.map_nil]
    exact flatMap_single _ _
  rw [e, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine rg.imp fun s q hs => ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, hr.th, hs.th]
  · simp [Run.tick, hr.out, hs.out, Bt.enc]
  · simp [Run.seq, Run.tick, Run.det, hr.bill, hs.bill]
  · intro p hp
    simp only [Run.seq, Run.tick, Run.det, List.append_nil, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hr.names p hp
    · exact hs.names p hp
  · have h1 := hr.cost
    have h2 := hs.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

theorem gcomb_ev {J : ℕ} {pre : List Bool} {c : R} (x : Tree) {n b : ℕ}
    (h : ∀ i < b + n + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i))) :
    ∃ l, Ev θ (gcomb ν J pre b n) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * n + 1)) l ((KT.comb (c ^ 2 ^ b) n).budg J) := by
  induction n generalizing b with
  | zero =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩ <;> simp [Run.det]
  | succ n ih =>
    obtain ⟨lg, eg, rg⟩ := ih (b := b + 1) (fun i hi => h i (by omega))
    obtain ⟨lw, ew, rw'⟩ := gw_ev (θ := θ) (κ := κ) (P := P) (ν := ν) (pre := pre) (b := b) (c := c) x (n := J) (j := 0)
      (fun i hi => h (b + i) (by omega))
    have ef := Ev.cons (Ev.quote (θ := θ) .nil x) ew
    have rf : List.Forall₂ (RelG κ P (8 * J + 3)) ([Run.det 1 Tree.nil].flatMap fun r => lw.map fun s =>
        (r.seq s).tick (.cons r.out s.out)) ((KT.leaf (c ^ 2 ^ b)).budg J) := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, KT.budg]
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine rw'.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.tick, Run.det, h2, Bt.enc]
      · simpa [Run.seq, Run.tick, Run.det] using h3
      · simpa [Run.seq, Run.tick, Run.det] using h4
      · simp only [Run.seq, Run.tick, Run.det]
        omega
    obtain ⟨l, e, r⟩ := node_rel ef eg rf rg
    refine ⟨l, e, ?_⟩
    have hc : (c ^ 2 ^ b) ^ 2 = c ^ 2 ^ (b + 1) := by rw [← pow_mul, ← pow_succ]
    simp only [KT.comb, KT.budg, hc] at r ⊢
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    ring_nf
    omega

/-- Runs of `gt` = budgets. The hypothesis: the names that are used name the right powers. -/
theorem gt_ev {J B : ℕ} (x : Tree) (K : KT R) (pre : List Bool)
    (h : ∀ p, K.Leaf p → ∀ i < B + J,
      κ (pre ++ (p ++ KT.pw (ν i))) = K.lk (p ++ KT.pw i) ∧ P (pre ++ (p ++ KT.pw (ν i)))) :
    ∃ l, Ev θ (gt ν J B K pre) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * (K.expand B).nds)) l ((K.expand B).budg J) := by
  induction K generalizing pre with
  | none =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩
    · simp [Run.det]
    · simp [Run.det]
    · simp [Run.det, KT.expand, KT.nds]
  | leaf c =>
    have h' : ∀ i < B + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i)) := by
      intro i hi
      have := h [] rfl i hi
      simpa [KT.lk, KT.combVal_pw] using this
    obtain ⟨l, e, r⟩ := gcomb_ev (θ := θ) (J := J) (pre := pre) (c := c) x (n := B) (b := 0)
      (fun i hi => h' i (by omega))
    refine ⟨l, e, ?_⟩
    simp only [pow_zero, pow_one] at r
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    simp only [KT.expand, KT.nds_comb]
    nlinarith
  | node l r ihl ihr =>
    obtain ⟨ll, el, rl⟩ := ihl (pre ++ [false]) (fun p hp i hi => by
      have := h (false :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨lr, er, rr⟩ := ihr (pre ++ [true]) (fun p hp i hi => by
      have := h (true :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨l', e', r'⟩ := node_rel el er rl rr
    refine ⟨l', e', r'.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩⟩
    simp only [KT.expand, KT.nds]
    nlinarith

end Formulas

section Sizes

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [num, Tree.size, ih]; omega

theorem size_gw (ν : ℕ → ℕ) (pre : List Bool) (b N : ℕ) (n j : ℕ) (h : ∀ i < j + n, ν (b + i) ≤ N) :
    (gw ν pre b j n).code.size ≤ n * (4 * (pre.length + N) + 100) + 4 := by
  induction n generalizing j with
  | zero => simp [gw, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (j + 1) (fun i hi => h i (by omega))
    have h2 := size_ofBits (pre ++ KT.pw (ν (b + j)))
    have h3 := h j (by omega)
    simp only [KT.pw, List.length_append, List.length_replicate, List.length_singleton] at h2
    simp only [gw, gbit, Fm.code, Tree.size, size_num, KT.pw]
    nlinarith

theorem size_gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) (N : ℕ) (n b : ℕ) (h : ∀ i < b + n + J, ν i ≤ N) :
    (gcomb ν J pre b n).code.size ≤ n * ((J + 1) * (4 * (pre.length + N) + 100)) + 4 := by
  induction n generalizing b with
  | zero => simp [gcomb, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (b + 1) (fun i hi => h i (by omega))
    have h2 := size_gw ν pre b N J 0 (fun i hi => h _ (by omega))
    simp only [gcomb, Fm.code, Tree.size, size_num]
    nlinarith

theorem size_gt (ν : ℕ → ℕ) (J B : ℕ) (K : KT R) (pre : List Bool) (N : ℕ) (h : ∀ i < B + J, ν i ≤ N) :
    (gt ν J B K pre).code.size ≤ (K.expand B).nds * ((J + 1) * (4 * (pre.length + K.ht + N) + 100)) := by
  induction K generalizing pre with
  | none =>
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    nlinarith
  | leaf c =>
    have h1 := size_gcomb ν J pre N B 0 (fun i hi => h i (by omega))
    simp only [gt, KT.expand, KT.nds_comb, KT.ht, add_zero] at h1 ⊢
    refine h1.trans ?_
    have : 100 ≤ (J + 1) * (4 * (pre.length + N) + 100) := by nlinarith
    nlinarith
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    have e1 : (J + 1) * (4 * (pre.length + 1 + l.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_left l.ht r.ht
      omega
    have e2 : (J + 1) * (4 * (pre.length + 1 + r.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_right l.ht r.ht
      omega
    have e3 : 100 ≤ (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by nlinarith
    have e4 := h1.trans (Nat.mul_le_mul_left _ e1)
    have e5 := h2.trans (Nat.mul_le_mul_left _ e2)
    nlinarith

end Sizes

end NS1
end

/-! Source module: NS1.Step -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# One round

A program that guesses budgets, multiplies by the powers of the constants, forms a plain instance, cuts it into
pieces, and applies a given program to every piece.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R}

section Values

theorem wt_seq (r s : Run A) : wt κ (r.seq s) = wt κ r * wt κ s := by
  simp only [wt, Run.seq, map_mul, List.map_append, List.prod_append]
  ring

theorem wt_tick (r : Run A) (o : Tree) : wt κ (r.tick o) = wt κ r := rfl

theorem wt_delay (k : ℕ) (r : Run A) : wt κ (r.delay k) = wt κ r := rfl

theorem wt_det (k : ℕ) (o : Tree) : wt κ (Run.det k o : Run A) = 1 := by simp [wt, Run.det]

/-- Sums over runs, with a function of the value. -/
def sumF (κ : List Bool → R) (l : List (Run A)) (f : Tree → R) : R := (l.map fun r => wt κ r * f r.out).sum

theorem val_eq_sumF (l : List (Run A)) : val κ l = sumF κ l fun _ => 1 := by simp [val, sumF]

theorem sumF_delay (k : ℕ) (l : List (Run A)) (f : Tree → R) : sumF κ (l.map (Run.delay k)) f = sumF κ l f := by
  simp only [sumF, List.map_map]
  rfl

theorem sum_rel {β : Type*} {l : List (Run A)} {Q : List β} {c : β → R} {o : β → Tree} {f : Tree → R}
    (h : List.Forall₂ (fun r q => wt κ r = c q ∧ r.out = o q) l Q) :
    sumF κ l f = (Q.map fun q => c q * f (o q)).sum := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [sumF, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, h.1, h.2]

end Values

section App

/-- Apply a fixed program. -/
def app (p : Tree) (e : Fm) : Fm := .run (.quote p) e

theorem Ev.app {p x : Tree} {e : Fm} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ (Fm.ofTree p) s.out) : Ev θ (app p e) x
      (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out) := by
  have := Ev.run' (Dt.quote (θ := θ) p x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem sumF_app {p : Tree} {le : List (Run A)} {f : Tree → R} :
    sumF κ (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) f = sumF κ le fun o => sumF κ (NS1.evl θ (Fm.ofTree p) o) f := by
  simp only [sumF]
  rw [sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  show wt κ (((Run.det 1 p).seq s).seq t) * f t.out = wt κ s * (wt κ t * f t.out)
  rw [wt_seq, wt_seq, wt_det, one_mul, mul_assoc]

theorem mem_app {p : Tree} {le : List (Run A)} {u : Run A}
    (h : u ∈ le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) :
    ∃ s ∈ le, ∃ t ∈ NS1.evl θ (Fm.ofTree p) s.out, u.cost = s.cost + t.cost + 2 ∧ u.bill = s.bill ++ t.bill ∧
      u.out = t.out ∧ u.th = s.th * t.th := by
  rw [List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨s, hs, t, ht, ?_, ?_, rfl, ?_⟩
  · simp only [Run.seq, Run.tick, Run.det]
    omega
  · simp [Run.seq, Run.tick, Run.det]
  · simp [Run.seq, Run.tick, Run.det]

end App

section Loop

/-- Apply the program `D` to all trees of a list. The argument is (this program, the list). -/
def LP (D : Tree) : Fm := .ite (.tl .id)
  (.cons (.run (.quote D) (.hd (.tl .id))) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem LP_ev {D : Tree} {T : ℕ} {P : List Bool → Prop} (ys : Tree) (h : ∀ y ∈ ys.toList, Hl θ (Fm.ofTree D) y ∧
    ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ T ∧ ∀ p ∈ r.bill, P p) :
    ∃ l, Ev θ (LP D) (.cons (LP D).code ys) l ∧
      (∀ r ∈ l, r.cost ≤ (T + 30) * ys.toList.length + 10 ∧ ∀ p ∈ r.bill, P p) ∧
      val κ l = (ys.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := by
  induction ys with
  | nil =>
    refine ⟨_, Dt.ite_false (.tl (.id _)) (.quote _ _), ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp [Run.det]
    · simp [val, wt_det, toList]
  | cons a ys _ ih =>
    obtain ⟨lr, er, hr, vr⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨ha, ha'⟩ := h a List.mem_cons_self
    have e1 := Ev.run_det (Dt.quote (θ := θ) D (.cons (LP D).code (.cons a ys))) (.hd (.tl (.id _))) ha.ev
    have er' : Ev θ (Fm.ofTree (LP D).code) (.cons (LP D).code ys) lr := by rwa [Fm.ofTree_code]
    have e2 := Ev.run_det (Dt.hd (Dt.id (θ := θ) (.cons (LP D).code (.cons a ys)))) (.cons (.hd (.id _))
      (.tl (.tl (.id _)))) er'
    refine ⟨_, Ev.ite_true (.tl (.id _)) (by simp) (Ev.cons e1 e2), ?_, ?_⟩
    · intro r hr0
      simp only [List.mem_map, List.mem_flatMap] at hr0
      obtain ⟨_, ⟨_, ⟨r1, hr1, rfl⟩, ⟨_, ⟨r2, hr2, rfl⟩, rfl⟩⟩, rfl⟩ := hr0
      obtain ⟨c1, p1⟩ := ha' r1 hr1
      obtain ⟨c2, p2⟩ := hr r2 hr2
      refine ⟨?_, ?_⟩
      · simp only [Run.delay, Run.seq, Run.tick, toList, List.length_cons]
        nlinarith
      · intro p hp
        simp only [Run.delay, Run.seq, Run.tick, List.mem_append] at hp
        rcases hp with hp | hp
        · exact p1 p hp
        · exact p2 p hp
    · rw [val_eq_sumF, sumF_delay, toList, List.map_cons, List.prod_cons, ← vr]
      simp only [sumF, mul_one]
      rw [sum_flatMap_map, List.map_map]
      simp only [List.map_map, Function.comp_def, wt_tick, wt_seq, wt_delay]
      simp only [List.sum_map_mul_left]
      rw [List.sum_map_mul_right]
      rfl

end Loop

section Inst

/-- The plain instance for a program `p`, an argument `z` and budgets `t`. -/
def zq (p z : Tree) (t : Bt) : Tree := .cons WF.code (.cons p (.cons z t.enc))

/-- Form the plain instance: `fp` gives the program, `g` guesses the budgets. -/
def ZE (fp g : Fm) : Fm := .cons (.quote WF.code) (.cons fp (.cons .id g))

theorem ZE_ev {fp g : Fm} {p z : Tree} {k cg : ℕ} {P : List Bool → Prop} {lg : List (Run A)} {Q : List (Bt × R)}
    (hp : Dt θ fp z p k) (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q) :
    ∃ l, Ev θ (ZE fp g) z l ∧ List.Forall₂ (fun r q => wt κ r = q.2 ∧ r.out = zq p z q.1 ∧ (∀ n ∈ r.bill, P n) ∧
      r.cost ≤ cg + k + 5) l Q := by
  refine ⟨_, Ev.cons (Dt.quote _ _) (Ev.cons hp (Ev.cons (Dt.id _) hg)), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff]
  refine rg.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · rw [wt_tick, wt_seq, wt_tick, wt_seq, wt_tick, wt_seq, wt_det, wt_det, wt_det]
    simp [wt, hr.th, hr.bill]
  · simp [Run.tick, Run.det, hr.out, zq]
  · simpa [Run.seq, Run.tick, Run.det] using hr.names
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

/-- One round: guess budgets, multiply, form the plain instance, cut it with `G`, apply `D` to the pieces. -/
def stepF (D G p : Tree) (g : Fm) : Fm :=
  app (LP D).code (.cons (.quote (LP D).code) (app G (ZE (.quote p) g)))

theorem stepF_ev {D G p z : Tree} {g : Fm} {cg tG tD Ln : ℕ} {P : List Bool → Prop} {lg : List (Run A)}
    {Q : List (Bt × R)} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q)
    (hG : ∀ q ∈ Q, Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧
      r.cost ≤ tG ∧ r.out.toList.length ≤ Ln ∧ ∀ y ∈ r.out.toList, Hl θ (Fm.ofTree D) y ∧
        ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ tD ∧ ∀ n ∈ r.bill, P n) :
    ∃ l, Ev θ (stepF D G p g) z l ∧
      (∀ r ∈ l, r.cost ≤ cg + tG + (tD + 30) * Ln + 30 ∧ ∀ n ∈ r.bill, P n) ∧
      val κ l = (Q.map fun q => q.2 * sumF κ (evl θ (Fm.ofTree G) (zq p z q.1)) fun o =>
        (o.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod).sum := by
  obtain ⟨lZ, eZ, rZ⟩ := ZE_ev (Dt.quote p z) hg rg
  have hZ : ∀ s ∈ lZ, ∃ q ∈ Q, wt κ s = q.2 ∧ s.out = zq p z q.1 ∧ (∀ n ∈ s.bill, P n) ∧ s.cost ≤ cg + 1 + 5 :=
    fun s hs => forall₂_exists rZ hs
  have eG := Ev.app (p := G) eZ fun s hs => by
    obtain ⟨q, hq, -, h, -⟩ := hZ s hs
    rw [h]
    exact (hG q hq).1
  set lG := lZ.flatMap fun s => (evl θ (Fm.ofTree G) s.out).map fun t => ((Run.det 1 G).seq s).seq t |>.tick t.out
    with hlG
  have hmem : ∀ u ∈ lG, u.out.toList.length ≤ Ln ∧ (∀ y ∈ u.out.toList, Hl θ (Fm.ofTree D) y ∧
      ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ tD ∧ ∀ n ∈ r.bill, P n) ∧ u.cost ≤ cg + tG + 8 ∧ ∀ n ∈ u.bill, P n := by
    intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨q, hq, -, h4, h5, h6⟩ := hZ s hs
    rw [h4] at ht
    obtain ⟨g1, g2, g3, g4⟩ := (hG q hq).2 t ht
    refine ⟨by rw [h3]; exact g3, by rw [h3]; exact g4, by omega, ?_⟩
    rw [h2, g1, List.append_nil]
    exact h5
  have eC := Ev.cons (Dt.quote (θ := θ) (LP D).code z) eG
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at eC
  have hLP : ∀ u ∈ lG, ∃ l, Ev θ (LP D) (.cons (LP D).code u.out) l ∧
      (∀ r ∈ l, r.cost ≤ (tD + 30) * u.out.toList.length + 10 ∧ ∀ p ∈ r.bill, P p) ∧
      val κ l = (u.out.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := fun u hu =>
    LP_ev u.out (hmem u hu).2.1
  have eL := Ev.app (p := (LP D).code) eC fun s hs => by
    rw [List.mem_map] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Fm.ofTree_code]
    obtain ⟨l, hl, -⟩ := hLP u hu
    exact hl.hl
  refine ⟨_, eL, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hr
    rw [List.mem_map] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Fm.ofTree_code] at ht
    obtain ⟨l, hl, hl2, -⟩ := hLP u hu
    have ht' : t ∈ l := by
      have := hl.evl
      rw [← this]
      exact ht
    obtain ⟨m1, m2, m3, m4⟩ := hmem u hu
    obtain ⟨c1, p1⟩ := hl2 t ht'
    have := Nat.mul_le_mul_left (tD + 30) m1
    refine ⟨?_, ?_⟩
    · simp only [Run.seq, Run.tick, Run.det] at h1
      omega
    · intro n hn
      rw [h2] at hn
      simp only [Run.seq, Run.tick, Run.det, List.nil_append, List.mem_append] at hn
      rcases hn with hn | hn
      · exact m4 n hn
      · exact p1 n hn
  · rw [val_eq_sumF, sumF_app]
    have s1 : sumF κ (lG.map fun s => ((Run.det 1 (LP D).code).seq s).tick (.cons (Run.det 1 (LP D).code : Run A).out s.out))
        (fun o => sumF κ (evl θ (Fm.ofTree (LP D).code) o) fun _ => 1) =
        sumF κ lG fun o => (o.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := by
      simp only [sumF, List.map_map, Function.comp_def]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      obtain ⟨l, hl, -, hl3⟩ := hLP u hu
      rw [← hl3, wt_tick, wt_seq, wt_det, one_mul, Fm.ofTree_code]
      congr 1
      have e : (((Run.det 1 (LP D).code).seq u).tick (.cons (Run.det 1 (LP D).code : Run A).out u.out)).out =
          .cons (LP D).code u.out := rfl
      rw [e, hl.evl, val_eq_sumF, sumF]
    rw [s1, hlG, sumF_app]
    exact sum_rel (c := fun q : Bt × R => q.2) (o := fun q : Bt × R => zq p z q.1)
      (rZ.imp fun r q hr => ⟨hr.1, hr.2.1⟩)

end Inst

end NS1
end

/-! Source module: NS1.Accel -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Accelerators, the cut

Scales are `v ^ H` (`H = 16 / η`). `pv θ z` is the universal plain sum at `z = (program, argument)`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra A R]

/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into pieces of `v ^ H` steps. Its values
are lists of instances. -/
structure CutProg (θ : List Bool → A) (H v τ s : ℕ) (G : Tree) : Prop where
  size : G.size ≤ v ^ H
  list : ∀ z, z.size ≤ s → Hl θ (Fm.ofTree G) z ∧ ∀ r ∈ evl θ (Fm.ofTree G) z, r.bill = [] ∧ r.cost * v ^ 24 ≤ τ ∧
    r.out.toList.length * v ^ H ≤ τ * v ^ 2 ∧ ∀ y ∈ r.out.toList, y.size ≤ v ^ (H - 32)
  val : ∀ z, z.size ≤ s → Plain θ τ z →
    (∀ r ∈ evl θ (Fm.ofTree G) z, ∀ y ∈ r.out.toList, Plain θ (v ^ H) y) ∧
    pv θ z = ((evl θ (Fm.ofTree G) z).map fun r => r.th * (r.out.toList.map (pv θ)).prod).sum

/-- **Theorem C (the cut, at all scales)**, as a property of the ring and its constants. -/
def CutHyp (θ : List Bool → A) (H C₀ v₀ : ℕ) : Prop :=
  ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ →
    ∃ G, CutProg θ H v τ s G

/-- The program `D`, with the constants `K` and their powers `2 ^ b`, `b < B`, has the values of all universal plain
sums of `v ^ H` steps on instances of size `v ^ (H - 32)`, in `t` steps. -/
structure IsAccT (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧
    ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)

/-- The same, where runs have to stop only if the sum is plain. -/
structure IsPre (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → Hl θ (Fm.ofTree D) z ∧
    ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧ ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)

variable {θ : List Bool → A}

theorem IsAccT.pre {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) : IsPre θ H v t K B D :=
  ⟨fun z hz _ => h.run z hz, h.val⟩

theorem IsPre.mono {H v t t' : ℕ} {K : KT R} {B B' : ℕ} {D : Tree} (h : IsPre θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsPre θ H v t' K B' D :=
  ⟨fun z hz hp => ⟨(h.run z hz hp).1, fun r hr => ⟨((h.run z hz hp).2 r hr).1.trans ht, fun p hp' =>
    (((h.run z hz hp).2 r hr).2 p hp').mono hB⟩⟩, h.val⟩

theorem IsAccT.mono {H v t t' : ℕ} {K : KT R} {B B' : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsAccT θ H v t' K B' D :=
  ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1.trans ht, fun p hp' =>
    (((h.run z hz).2 r hr).2 p hp').mono hB⟩⟩, h.val⟩

/-- A run wants at most one constant a step. -/
theorem bill_le {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : ∀ r ∈ l, r.bill.length ≤ r.cost := by
  induction h with
  | quote c x => simp [Run.det]
  | id x => simp [Run.det]
  | hd _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Run.tick]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | tl _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Run.tick]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | cons _ _ iha ihb =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    have := iha r1 h1
    have := ihb r2 h2
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | ite _ _ _ iha ihb ihc =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    have := iha r1 h1
    have : r2.bill.length ≤ r2.cost := by
      by_cases h : r1.out = .nil
      · exact ihc r1 h1 h r2 h2
      · exact ihb r1 h1 h r2 h2
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | run _ _ _ iha ihb ih =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, r3, h3, rfl⟩ := hr
    have := iha r1 h1
    have := ihb r2 h2
    have := ih r1 h1 r2 h2 r3 h3
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | guess x => simp [Run.det]
  | fail x => simp
  | theta _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | mul _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.length_append,
      List.length_singleton]
    exact fun r hr => Nat.succ_le_succ (ih r hr)

/-- The universal program. -/
def UF : Fm := .run (.hd .id) (.tl .id)

theorem UF_ev {z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree z.hd) z.tl l) :
    Ev θ UF z (l.map (Run.delay 5)) := Ev.run_det (Dt.hd (Dt.id z)) (Dt.tl (Dt.id z)) h

theorem val_plain {κ : List Bool → R} {l : List (Run A)} (h : ∀ r ∈ l, r.bill = []) :
    val κ l = algebraMap A R (pval l) := by
  rw [val, pval, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  simp [wt, h r hr]

/-- The universal program is a program for the universal plain sums. -/
theorem UF_pre (θ : List Bool → A) (H v : ℕ) (K : KT R) (B : ℕ) : IsPre θ H v (v ^ H + 5) K B UF.code := by
  constructor
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl, List.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    obtain ⟨h1, h2⟩ := hp.2 s hs
    refine ⟨?_, ?_⟩
    · simp only [Run.delay]
      omega
    · simp [Run.delay, h1]
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code, e.evl, val_plain]
    · congr 1
      simp [pval, pv, Function.comp_def, Run.delay]
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      exact (hp.2 s hs).1

/-- The instances that arise from budgets are plain, and their sums are those of the runs that use up the budgets. -/
theorem zq_plain {p z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) z l) {T H τ : ℕ} (hT : ∀ r ∈ l, r.cost ≤ T)
    {t : Bt} (ht : t.ht ≤ H) (hτ : MM H * T + 40 * t.nds + 40 ≤ τ) : Plain θ τ (zq p z t) ∧
      pv θ (zq p z t) = (l.map fun r => if ok t r.bill = true then r.th else 0).sum ∧
      (evl θ (Fm.ofTree (zq p z t).hd) (zq p z t).tl).map Run.th = (l.filter fun r => ok t r.bill).map Run.th := by
  obtain ⟨l', e, h1, h2⟩ := WF_ev h hT ht
  have e' : Ev θ (Fm.ofTree (zq p z t).hd) (zq p z t).tl l' := by
    show Ev θ (Fm.ofTree WF.code) _ l'
    rw [Fm.ofTree_code]
    exact e
  refine ⟨⟨e'.hl, fun r hr => ?_⟩, ?_, by rw [e'.evl, h2]⟩
  · rw [e'.evl] at hr
    exact ⟨(h1 r hr).1, (h1 r hr).2.trans hτ⟩
  · rw [pv, e'.evl, pval, h2, sum_filter_th]

end NS1
end

/-! Source module: Nc.Uni.Rules -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The rules of the universal machine
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

/-- Kinds of records: nil, cons, garbage, frames. -/
inductive Kd where
  | N | C | G | HT | PE | PA | PB | HD | TL | CO1 | CO2 | IT | RU1 | RU2 | TH
  deriving DecidableEq

instance : Fintype Kd := ⟨{.N, .C, .G, .HT, .PE, .PA, .PB, .HD, .TL, .CO1, .CO2, .IT, .RU1, .RU2, .TH}, by
  intro x; cases x <;> simp⟩

/-- The prefixes of the names. -/
def pre (supp : Finset (List Bool)) : Finset (List Bool) := supp.biUnion fun q => q.inits.toFinset

theorem mem_pre {supp : Finset (List Bool)} {p : List Bool} : p ∈ pre supp ↔ ∃ q ∈ supp, p <+: q := by
  simp [pre]

/-- Prefixes of names. -/
abbrev Nm (supp : Finset (List Bool)) := {p : List Bool // p ∈ pre supp}

/-- Modes. -/
inductive Md (N : Type) where
  | S0 | S1 | S2 | P | PR | E | D (j : Fin 11) | K4 | K5 | K6 | R | H | T | I | I1 | I2 | TH (p : N) | TB (p : N) | Z
  deriving DecidableEq, Fintype

/-- Rules without names. -/
inductive Ra where
  | s0 | s1 | pr0 | pr1 | pa | pb | pe | s2 (b : Bool) | en | ec | dc (j : Fin 10) | d0 | d1 | d2 | d3 | d4 | d5 | d6
  | d7 (b : Bool) | d9 | k4 (b : Bool) | k5 (b : Bool) | k6 (b : Bool) | rhd | rtl | h (b : Bool) | t (b : Bool)
  | rco1 | rco2 | rit | ic | inn | i1 (b : Bool) | i2 (b : Bool) | rru1 | rru2 | rht
  deriving DecidableEq, Fintype

/-- Rules. -/
abbrev Ru (supp : Finset (List Bool)) := Ra ⊕ ({_u : Unit // [] ∈ pre supp} ⊕ (Nm supp ⊕ (Nm supp ⊕
  {x : Nm supp × Nm supp × Bool // x.2.1.1 = x.1.1 ++ [x.2.2]})))

/-- Cons or nil. -/
def kb (b : Bool) : Kd := if b then .C else .N

/-- The data of a rule. -/
structure RD (A N : Type) where
  src : Md N
  dst : Md N
  rd : Option Bool
  lk : Kd
  la : Fin 5
  ak : Kd
  af : Fin 3 → Fin 9
  dr : Fin 5 → Fin 9
  wt : A

variable {A : Type} [CommRing A] (θ : List Bool → A) (supp : Finset (List Bool))

/-- A rule without input and weight. -/
def rl {N : Type} (src dst : Md N) (lk : Kd) (la : Fin 5) (ak : Kd) (f0 f1 f2 : Fin 9) (d1 d2 d3 d4 : Fin 9) : RD A N :=
  ⟨src, dst, none, lk, la, ak, ![f0, f1, f2], ![0, d1, d2, d3, d4], 1⟩

/-- The rules without names. -/
def ruleA {N : Type} : Ra → RD A N
  | .s0 => rl .S0 .S1 .N 0 .HT 0 0 0 8 0 0 0
  | .s1 => rl .S1 .P .N 0 .PE 1 0 0 8 0 0 0
  | .pr0 => { (rl .P .PR .N 0 .G 0 0 0 0 1 0 0 : RD A N) with rd := some false }
  | .pr1 => { (rl .P .P .N 0 .PA 1 0 0 8 0 0 0 : RD A N) with rd := some true }
  | .pa => rl .PR .P .PA 2 .PB 1 5 0 8 0 0 0
  | .pb => rl .PR .PR .PB 2 .C 5 1 0 8 6 0 0
  | .pe => rl .PR .S2 .PE 2 .G 0 0 0 1 5 0 0
  | .s2 b => rl .S2 .E (kb b) 1 .G 0 0 0 5 6 2 0
  | .en => rl .E .R .N 1 .G 0 0 0 1 3 0 0
  | .ec => rl .E (.D 0) .C 1 .G 0 0 0 5 6 2 3
  | .dc j => rl (.D j.castSucc) (.D j.succ) .C 1 .G 0 0 0 6 2 3 4
  | .d0 => rl (.D 0) .R .N 1 .G 0 0 0 2 4 0 0
  | .d1 => rl (.D 1) .R .N 1 .G 0 0 0 3 4 0 0
  | .d2 => rl (.D 2) .E .N 1 .HD 4 0 0 2 3 8 0
  | .d3 => rl (.D 3) .E .N 1 .TL 4 0 0 2 3 8 0
  | .d4 => rl (.D 4) .K4 .N 1 .G 0 0 0 2 3 4 0
  | .d5 => rl (.D 5) .K5 .N 1 .G 0 0 0 2 3 4 0
  | .d6 => rl (.D 6) .K6 .N 1 .G 0 0 0 2 3 4 0
  | .d7 b => if b then rl (.D 7) .R .N 1 .C 0 0 0 8 4 0 0 else rl (.D 7) .R .N 1 .G 0 0 0 0 4 0 0
  | .d9 => rl (.D 9) .E .N 1 .TH 4 0 0 2 3 8 0
  | .k4 b => rl .K4 .E (kb b) 1 .CO1 6 2 3 5 2 8 0
  | .k5 b => rl .K5 .E (kb b) 1 .IT 6 2 3 5 2 8 0
  | .k6 b => rl .K6 .E (kb b) 1 .RU1 6 2 3 5 2 8 0
  | .rhd => rl .R .H .HD 2 .G 0 0 0 1 5 0 0
  | .rtl => rl .R .T .TL 2 .G 0 0 0 1 5 0 0
  | .h b => rl .H .R (kb b) 1 .G 0 0 0 5 2 0 0
  | .t b => rl .T .R (kb b) 1 .G 0 0 0 6 2 0 0
  | .rco1 => rl .R .E .CO1 2 .CO2 1 7 0 5 6 8 0
  | .rco2 => rl .R .R .CO2 2 .C 5 1 0 8 6 0 0
  | .rit => rl .R .I .IT 2 .G 0 0 0 1 5 6 7
  | .ic => rl .I .I1 .C 1 .G 0 0 0 2 3 4 0
  | .inn => rl .I .I2 .N 1 .G 0 0 0 2 3 4 0
  | .i1 b => rl .I1 .E (kb b) 1 .G 0 0 0 5 2 3 0
  | .i2 b => rl .I2 .E (kb b) 1 .G 0 0 0 6 2 3 0
  | .rru1 => rl .R .E .RU1 2 .RU2 1 7 0 5 6 8 0
  | .rru2 => rl .R .E .RU2 2 .G 0 0 0 5 1 6 0
  | .rht => rl .R .Z .HT 2 .G 0 0 0 0 0 0 0

/-- The rules. -/
def rule : Ru supp → RD A (Nm supp)
  | .inl r => ruleA r
  | .inr (.inl u) => rl .R (.TH ⟨[], u.2⟩) .TH 2 .G 0 0 0 1 5 0 0
  | .inr (.inr (.inl p)) => { (rl (.TH p) .R .N 1 .G 0 0 0 0 2 0 0 : RD A (Nm supp)) with wt := θ p.1 }
  | .inr (.inr (.inr (.inl p))) => rl (.TH p) (.TB p) .C 1 .G 0 0 0 5 6 2 0
  | .inr (.inr (.inr (.inr x))) => rl (.TB x.1.1) (.TH x.1.2.1) (kb x.1.2.2) 1 .G 0 0 0 2 3 0 0

/-- The universal machine. -/
noncomputable def UM : Mach A (Md (Nm supp)) Kd where
  Rl := Ru supp
  fR := Fintype.ofFinite _
  dR := Classical.decEq _
  src r := (rule θ supp r).src
  dst r := (rule θ supp r).dst
  rd r := (rule θ supp r).rd
  lk r := (rule θ supp r).lk
  la r := (rule θ supp r).la
  ak r := (rule θ supp r).ak
  af r := (rule θ supp r).af
  dr r := (rule θ supp r).dr
  wt r := (rule θ supp r).wt
  m0 := .S0
  mh := .Z
  kN := .N

/-- The register that is loaded depends on the mode only. -/
def laM {N : Type} : Md N → Fin 5
  | .S0 => 0
  | .S1 => 0
  | .P => 0
  | .PR => 2
  | .R => 2
  | _ => 1

theorem la_eq (r : Ru supp) : (rule θ supp r).la = laM (rule θ supp r).src := by
  rcases r with r | u | p | p | x
  · cases r <;> first | rfl | (rename_i b; cases b <;> rfl)
  all_goals rfl

end Nc.Uni
end

/-! Source module: Nc.Uni.Det -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal machine is deterministic but for the guesses and the input
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The rule for a mode and the kind of the record that is loaded. -/
def nextR (supp : Finset (List Bool)) : Md (Nm supp) → Kd → Option (Ru supp)
  | .S0, .N => some (.inl .s0)
  | .S1, .N => some (.inl .s1)
  | .PR, .PA => some (.inl .pa)
  | .PR, .PB => some (.inl .pb)
  | .PR, .PE => some (.inl .pe)
  | .S2, .C => some (.inl (.s2 true))
  | .S2, .N => some (.inl (.s2 false))
  | .E, .N => some (.inl .en)
  | .E, .C => some (.inl .ec)
  | .D j, .C => if h : j.1 < 10 then some (.inl (.dc ⟨j.1, h⟩)) else none
  | .D 0, .N => some (.inl .d0)
  | .D 1, .N => some (.inl .d1)
  | .D 2, .N => some (.inl .d2)
  | .D 3, .N => some (.inl .d3)
  | .D 4, .N => some (.inl .d4)
  | .D 5, .N => some (.inl .d5)
  | .D 6, .N => some (.inl .d6)
  | .D 9, .N => some (.inl .d9)
  | .K4, .C => some (.inl (.k4 true))
  | .K4, .N => some (.inl (.k4 false))
  | .K5, .C => some (.inl (.k5 true))
  | .K5, .N => some (.inl (.k5 false))
  | .K6, .C => some (.inl (.k6 true))
  | .K6, .N => some (.inl (.k6 false))
  | .R, .HD => some (.inl .rhd)
  | .R, .TL => some (.inl .rtl)
  | .R, .CO1 => some (.inl .rco1)
  | .R, .CO2 => some (.inl .rco2)
  | .R, .IT => some (.inl .rit)
  | .R, .RU1 => some (.inl .rru1)
  | .R, .RU2 => some (.inl .rru2)
  | .R, .HT => some (.inl .rht)
  | .R, .TH => if h : [] ∈ pre supp then some (.inr (.inl ⟨(), h⟩)) else none
  | .H, .C => some (.inl (.h true))
  | .H, .N => some (.inl (.h false))
  | .T, .C => some (.inl (.t true))
  | .T, .N => some (.inl (.t false))
  | .I, .C => some (.inl .ic)
  | .I, .N => some (.inl .inn)
  | .I1, .C => some (.inl (.i1 true))
  | .I1, .N => some (.inl (.i1 false))
  | .I2, .C => some (.inl (.i2 true))
  | .I2, .N => some (.inl (.i2 false))
  | .TH p, .N => some (.inr (.inr (.inl p)))
  | .TH p, .C => some (.inr (.inr (.inr (.inl p))))
  | .TB p, .C => if h : p.1 ++ [true] ∈ pre supp then some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, h⟩, true), rfl⟩)))) else none
  | .TB p, .N => if h : p.1 ++ [false] ∈ pre supp then some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, h⟩, false), rfl⟩)))) else none
  | _, _ => none

/-- The rules that are chosen by the input or by a guess. -/
def Sp (r : Ru supp) : Prop := r = .inl .pr0 ∨ r = .inl .pr1 ∨ ∃ b, r = .inl (.d7 b)

theorem nextR_of (r : Ru supp) (hr : ¬ Sp r) : nextR supp (rule θ supp r).src (rule θ supp r).lk = some r := by
  rcases r with r | u | p | p | x
  · cases r with
    | pr0 => exact absurd (Or.inl rfl) hr
    | pr1 => exact absurd (Or.inr (Or.inl rfl)) hr
    | d7 b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | s2 b => cases b <;> rfl
    | k4 b => cases b <;> rfl
    | k5 b => cases b <;> rfl
    | k6 b => cases b <;> rfl
    | h b => cases b <;> rfl
    | t b => cases b <;> rfl
    | i1 b => cases b <;> rfl
    | i2 b => cases b <;> rfl
    | dc j =>
      have : (j.castSucc : Fin 11).1 < 10 := j.2
      exact dif_pos this
    | _ => rfl
  · exact dif_pos u.2
  · rfl
  · rfl
  · obtain ⟨⟨p, p', b⟩, hx⟩ := x
    obtain ⟨p', hp'⟩ := p'
    simp only at hx
    subst hx
    cases b
    · exact dif_pos hp'
    · exact dif_pos hp'

theorem rd_of (r : Ru supp) (hr : ¬ Sp r) : (rule θ supp r).rd = none := by
  rcases r with r | u | p | p | x
  · cases r with
    | pr0 => exact absurd (Or.inl rfl) hr
    | pr1 => exact absurd (Or.inr (Or.inl rfl)) hr
    | d7 b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | _ => rfl
  all_goals rfl

theorem src_ne (r : Ru supp) : (rule θ supp r).src ≠ .Z := by
  rcases r with r | u | p | p | x
  · cases r with
    | d7 b => cases b <;> simp [rule, ruleA, rl]
    | _ => simp [rule, ruleA, rl]
  all_goals simp [rule, rl]

/-- States of the universal machine. -/
abbrev St (supp : Finset (List Bool)) := Mach.State (M := Md (Nm supp)) (K := Kd)

/-- A heap that can be used. -/
structure OKs (σ : St supp) : Prop where
  nil : ((.N, ![0, 0, 0, 0]) : Rec Kd) ∈ σ.heap
  le : ∀ c ∈ σ.heap, c.2 0 ≤ σ.n
  fn : ∀ c ∈ σ.heap, ∀ c' ∈ σ.heap, c.2 0 = c'.2 0 → c = c'
  r0 : σ.regs 0 = 0

/-- The values of the variables. -/
def envOf (σ : St supp) (p q s : ℕ) : Fin 9 → ℕ :=
  ![σ.regs 0, σ.regs 1, σ.regs 2, σ.regs 3, σ.regs 4, p, q, s, σ.n + 1]

/-- The state after a step. -/
noncomputable def nx (θ : List Bool → A) (σ : St supp) (r : Ru supp) (p q s : ℕ) : St supp :=
  Mach.nxt (P := UM θ supp) σ (r, envOf σ p q s)

theorem dr_zero (r : Ru supp) : (rule θ supp r).dr 0 = 0 := by
  rcases r with r | u | p | p | x
  · cases r with
    | d7 b => cases b <;> rfl
    | _ => rfl
  all_goals rfl

theorem OKs.nx {σ : St supp} (hσ : OKs σ) (r : Ru supp) (p q s : ℕ) : OKs (nx θ σ r p q s) := by
  have ha : (Mach.al (P := UM θ supp) (r, envOf σ p q s)).2 0 = σ.n + 1 := rfl
  constructor
  · exact List.mem_append_left _ hσ.nil
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hσ.le c hc).trans (Nat.le_succ _)
    · rw [List.mem_singleton] at hc
      subst hc
      exact ha.le
  · intro c hc c' hc' e
    rcases List.mem_append.1 hc with hc | hc <;> rcases List.mem_append.1 hc' with hc' | hc'
    · exact hσ.fn c hc c' hc' e
    · rw [List.mem_singleton] at hc'
      subst hc'
      have := hσ.le c hc
      omega
    · rw [List.mem_singleton] at hc
      subst hc
      have := hσ.le c' hc'
      omega
    · rw [List.mem_singleton] at hc hc'
      rw [hc, hc']
  · change envOf σ p q s ((rule θ supp r).dr 0) = 0
    rw [dr_zero]
    exact hσ.r0

theorem heap_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) : σ.heap ⊆ (nx θ σ r p q s).heap :=
  fun _ hc => List.mem_append_left _ hc

/-- The record that is allocated is in the heap. -/
theorem new_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) :
    ((rule θ supp r).ak, ![σ.n + 1, envOf σ p q s ((rule θ supp r).af 0), envOf σ p q s ((rule θ supp r).af 1),
      envOf σ p q s ((rule θ supp r).af 2)]) ∈ (nx θ σ r p q s).heap :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem inp_nx (σ : St supp) (r : Ru supp) (p q s : ℕ) :
    (nx θ σ r p q s).inp = σ.inp.drop (rule θ supp r).rd.toList.length := rfl

/-- The possible steps. -/
theorem fire_iff {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (st : (UM θ supp).Step) :
    Mach.Fire σ st ↔ (rule θ supp st.1).src = σ.mode ∧ (rule θ supp st.1).lk = κ ∧
      (rule θ supp st.1).rd.toList <+: σ.inp ∧ st.2 = envOf σ p q s := by
  have hla : ∀ r, (UM θ supp).la r = laM (rule θ supp r).src := fun r => la_eq θ supp r
  constructor
  · intro hf
    have hs : (rule θ supp st.1).src = σ.mode := hf.src
    have h0 : (Mach.ld st).2 0 = σ.regs (laM σ.mode) := by
      have : (Mach.ld st).2 0 = st.2 (rv ((UM θ supp).la st.1)) := rfl
      rw [this, hf.regs, hla, hs]
    have h1 := hσ.fn _ hf.load _ hrec h0
    have h2 := congrArg Prod.fst h1
    have h3 := fun i => congrFun (congrArg Prod.snd h1) i
    refine ⟨hs, h2, hf.read, ?_⟩
    funext i
    refine Mach.env_cases (fun i => st.2 i = envOf σ p q s i) (fun j => ?_) (h3 1) (h3 2) (h3 3) hf.fresh i
    rw [hf.regs]
    fin_cases j <;> rfl
  · rintro ⟨hs, hk, hr, he⟩
    have hregs : ∀ j, st.2 (rv j) = σ.regs j := by
      intro j
      rw [he]
      fin_cases j <;> rfl
    refine ⟨hs, hregs, by rw [he]; rfl, ?_, hr⟩
    have : Mach.ld st = (κ, ![σ.regs (laM σ.mode), p, q, s]) := by
      refine Prod.ext hk ?_
      have h0 : st.2 (rv ((UM θ supp).la st.1)) = σ.regs (laM σ.mode) := by rw [hregs, hla, hs]
      change ![st.2 (rv ((UM θ supp).la st.1)), st.2 5, st.2 6, st.2 7] = _
      rw [h0, he]
      rfl
    rw [this]
    exact hrec

/-- A step that is forced. -/
theorem sumTo_rule {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (r : Ru supp) (hr : nextR supp σ.mode κ = some r)
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hs : (rule θ supp r).src = σ.mode) (hk : (rule θ supp r).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ r p q s) S B) :
    Mach.SumTo (UM θ supp) σ ((rule θ supp r).wt * S) (B + 1) := by
  have hz : σ.mode ≠ (UM θ supp).mh := by
    rw [← hs]
    exact src_ne r
  have hsp : ∀ r' : Ru supp, (rule θ supp r').src = σ.mode → (rule θ supp r').lk = κ → ¬ Sp r' := by
    rintro r' h1 h2 (rfl | rfl | ⟨b, rfl⟩)
    · exact hm h1.symm
    · exact hm h1.symm
    · cases b
      · exact hd ⟨h1.symm, h2.symm⟩
      · exact hd ⟨h1.symm, h2.symm⟩
  refine Mach.SumTo.one hz (r, envOf σ p q s) (fun st' => ?_) h
  rw [fire_iff hσ hrec]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    have h5 := nextR_of (θ := θ) st'.1 (hsp _ h1 h2)
    rw [h1, h2, hr] at h5
    exact Prod.ext (Option.some_injective _ h5).symm h4
  · rintro rfl
    refine ⟨hs, hk, ?_, rfl⟩
    rw [rd_of r (hsp r hs hk)]
    exact List.nil_prefix

/-- No rule applies. -/
theorem sumTo_stuck {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (hr : nextR supp σ.mode κ = none)
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hz : σ.mode ≠ .Z) (B : ℤ) :
    Mach.SumTo (UM θ supp) σ 0 B := by
  refine Mach.SumTo.none hz (fun st hf => ?_) B
  rw [fire_iff hσ hrec] at hf
  obtain ⟨h1, h2, -, -⟩ := hf
  have hsp : ¬ Sp st.1 := by
    rintro (h | h | ⟨b, h⟩)
    · rw [h] at h1; exact hm h1.symm
    · rw [h] at h1; exact hm h1.symm
    · rw [h] at h1 h2
      cases b
      · exact hd ⟨h1.symm, h2.symm⟩
      · exact hd ⟨h1.symm, h2.symm⟩
  have h5 := nextR_of (θ := θ) st.1 hsp
  rw [h1, h2, hr] at h5
  exact absurd h5 (by simp)

end Nc.Uni
end

/-! Source module: Nc.Uni.EvalU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Trees in the heap, opcodes, names
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The address a represents the tree. -/
def Rep (H : List (Rec Kd)) : ℕ → Tree → Prop
  | a, .nil => a = 0
  | a, .cons t1 t2 => ∃ p q s, ((.C, ![a, p, q, s]) : Rec Kd) ∈ H ∧ Rep H p t1 ∧ Rep H q t2

theorem Rep.mono {H H' : List (Rec Kd)} (hH : H ⊆ H') {a : ℕ} {t : Tree} (h : Rep H a t) : Rep H' a t := by
  induction t generalizing a with
  | nil => exact h
  | cons t1 t2 ih1 ih2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, hH h1, ih1 h2, ih2 h3⟩

/-- The record at an address that represents a tree. -/
theorem Rep.load {σ : St supp} (hσ : OKs σ) {a : ℕ} {t : Tree} (h : Rep σ.heap a t) :
    ∃ p q s, ((kb (decide (t ≠ .nil)), ![a, p, q, s]) : Rec Kd) ∈ σ.heap ∧ Rep σ.heap p t.hd ∧ Rep σ.heap q t.tl := by
  cases t with
  | nil =>
    have h0 : a = 0 := h
    subst h0
    exact ⟨0, 0, 0, hσ.nil, rfl, rfl⟩
  | cons t1 t2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, h1, h2, h3⟩

/-- What happens when the value o is returned to the frame k. -/
def KS (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec Kd)) (k : ℕ) (inp : List Bool) (o : Tree) (S : A)
    (B : ℤ) : Prop :=
  ∀ (σ : St supp) (v : ℕ), OKs σ → σ.mode = .R → σ.regs 1 = v → σ.regs 2 = k → H ⊆ σ.heap → σ.inp = inp →
    Rep σ.heap v o → Mach.SumTo (UM θ supp) σ S B

theorem KS.heap {H H' : List (Rec Kd)} (hH : H ⊆ H') {k : ℕ} {inp : List Bool} {o : Tree} {S : A} {B : ℤ}
    (h : KS θ supp H k inp o S B) : KS θ supp H' k inp o S B :=
  fun σ v h1 h2 h3 h4 h5 h6 h7 => h σ v h1 h2 h3 h4 (fun _ hc => h5 (hH hc)) h6 h7

theorem wtA (r : Ra) : (ruleA r : RD A (Nm supp)).wt = 1 := by
  cases r with
  | d7 b => cases b <;> rfl
  | _ => rfl

/-- A forced step with a rule without names. -/
theorem sumTo_ruleA {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (r : Ra) (hr : nextR supp σ.mode κ = some (.inl r))
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hs : (ruleA r : RD A (Nm supp)).src = σ.mode)
    (hk : (ruleA r : RD A (Nm supp)).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S B) :
    Mach.SumTo (UM θ supp) σ S (B + 1) := by
  have h1 := sumTo_rule hσ hrec (.inl r) hr hm hd hs hk h
  have h2 : (rule θ supp (.inl r)).wt = 1 := wtA r
  rw [h2, one_mul] at h1
  exact h1

theorem rdA (r : Ra) (h : r ≠ .pr0) (h' : r ≠ .pr1) : (rule θ supp (.inl r)).rd = none := by
  cases r with
  | pr0 => exact absurd rfl h
  | pr1 => exact absurd rfl h'
  | d7 b => cases b <;> rfl
  | _ => rfl

theorem inpA (σ : St supp) (r : Ra) (h : r ≠ .pr0) (h' : r ≠ .pr1) (p q s : ℕ) : (nx θ σ (.inl r) p q s).inp = σ.inp := by
  rw [inp_nx, rdA r h h']
  rfl

/-- Reading the number of an opcode. -/
theorem dchain {S : A} {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : St supp) (po : ℕ), OKs σ → σ.mode = .D ⟨j, hj⟩ →
    σ.regs 1 = po → Rep σ.heap po o → ∀ (hl : j + o.len < 11),
    (∀ σ' : St supp, OKs σ' → σ'.mode = .D ⟨j + o.len, hl⟩ → σ'.regs 1 = 0 → σ'.regs 2 = σ.regs 2 →
      σ'.regs 3 = σ.regs 3 → σ'.regs 4 = σ.regs 4 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S B) →
    Mach.SumTo (UM θ supp) σ S (B + o.len) := by
  induction o with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl h
    have h0 : po = 0 := hr
    subst h0
    have := h σ hσ hm h1 rfl rfl rfl (fun _ hc => hc) rfl
    simpa [Tree.len] using this
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl h
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    have hl' : j + 1 + b.len < 11 := by
      simp only [Tree.len] at hl
      omega
    have hj' : j < 10 := by omega
    have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.C, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap
      rw [h1]
      exact hrec
    have h2 := ih (j + 1) (by omega) (nx θ σ (.inl (.dc ⟨j, hj'⟩)) p q s) q (hσ.nx _ _ _ _) rfl rfl
      (hq.mono (heap_nx σ _ _ _ _)) hl' (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => h σ' a1 (by
        rw [a2]
        congr 2
        simp only [Tree.len]
        omega) a3 (a4.trans rfl) (a5.trans rfl) (a6.trans rfl) (fun _ hc => a7 (heap_nx σ _ _ _ _ hc))
        (a8.trans (inpA σ _ (by simp) (by simp) _ _ _)))
    have h3 := sumTo_ruleA hσ hrec' (.dc ⟨j, hj'⟩) (by rw [hm]; exact dif_pos hj') (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl h2
    refine h3.mono ?_
    simp only [Tree.len]
    push_cast
    omega

/-- Numbers that are no opcodes. -/
theorem dstuck {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : St supp) (po : ℕ), OKs σ → σ.mode = .D ⟨j, hj⟩ →
    σ.regs 1 = po → Rep σ.heap po o → 11 ≤ j + o.len → Mach.SumTo (UM θ supp) σ 0 B := by
  induction o generalizing B with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl
    simp only [Tree.len] at hl
    omega
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    simp only [Tree.len] at hl
    have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.C, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap
      rw [h1]
      exact hrec
    by_cases hj' : j < 10
    · have h2 := ih (B := B - 1) (j + 1) (by omega) (nx θ σ (.inl (.dc ⟨j, hj'⟩)) p q s) q (hσ.nx _ _ _ _) rfl rfl
        (hq.mono (heap_nx σ _ _ _ _)) (by omega)
      have h3 := sumTo_ruleA hσ hrec' (.dc ⟨j, hj'⟩) (by rw [hm]; exact dif_pos hj') (by rw [hm]; simp) (by simp)
        (by rw [hm]; rfl) rfl h2
      exact h3.mono (by omega)
    · refine sumTo_stuck hσ hrec' ?_ (by rw [hm]; simp) (by simp) (by rw [hm]; simp) B
      rw [hm]
      exact dif_neg hj'

/-- From a formula to its opcode. -/
theorem toOp {S : A} {B : ℤ} {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .E) {o a : Tree}
    (hr : Rep σ.heap (σ.regs 1) (.cons o a)) (hl : o.len < 11)
    (h : ∀ σ' : St supp, OKs σ' → σ'.mode = .D ⟨o.len, hl⟩ → σ'.regs 1 = 0 → Rep σ'.heap (σ'.regs 2) a →
      σ'.regs 3 = σ.regs 2 → σ'.regs 4 = σ.regs 3 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp →
      Mach.SumTo (UM θ supp) σ' S B) : Mach.SumTo (UM θ supp) σ S (B + 11) := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := dchain (θ := θ) (S := S) (B := B) o 0 (by omega) (nx θ σ (.inl .ec) p q s) p (hσ.nx _ _ _ _) rfl rfl
    (hp.mono (heap_nx σ _ _ _ _)) (by omega) (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => by
      refine h σ' a1 (by rw [a2]; congr 2; omega) a3 ?_ (a5.trans rfl) (a6.trans rfl)
        (fun _ hc => a7 (heap_nx σ _ _ _ _ hc)) (a8.trans (inpA σ _ (by simp) (by simp) _ _ _))
      rw [a4]
      exact (hq.mono (heap_nx σ _ _ _ _)).mono a7)
  have h3 := sumTo_ruleA hσ hrec' .ec (by rw [hm]; rfl) (by rw [hm]; simp) (by simp) (by rw [hm]; rfl) rfl h2
  refine h3.mono ?_
  have : (o.len : ℤ) ≤ 10 := by exact_mod_cast Nat.le_of_lt_succ hl
  linarith

theorem noOp {B : ℤ} {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .E) {o a : Tree}
    (hr : Rep σ.heap (σ.regs 1) (.cons o a)) (hl : 11 ≤ o.len) : Mach.SumTo (UM θ supp) σ 0 B := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := dstuck (θ := θ) (B := B - 1) o 0 (by omega) (nx θ σ (.inl .ec) p q s) p (hσ.nx _ _ _ _) rfl rfl
    (hp.mono (heap_nx σ _ _ _ _)) (by omega)
  have h3 := sumTo_ruleA hσ hrec' .ec (by rw [hm]; rfl) (by rw [hm]; simp) (by simp) (by rw [hm]; rfl) rfl h2
  exact h3.mono (by omega)

/-- The bound for the lengths of names. -/
def Lm (supp : Finset (List Bool)) : ℕ := supp.sup List.length

theorem length_pre {p : List Bool} (hp : p ∈ pre supp) : p.length ≤ Lm supp := by
  obtain ⟨q, hq, h⟩ := mem_pre.1 hp
  exact h.length_le.trans (Finset.le_sup (f := List.length) hq)

theorem not_pre {p : List Bool} (hp : p ∉ pre supp) (hθ : ∀ q, q ∉ supp → θ q = 0) (w : List Bool) : θ (p ++ w) = 0 := by
  refine hθ _ fun h => hp (mem_pre.2 ⟨_, h, List.prefix_append _ _⟩)

/-- Reading a name. -/
theorem readName (hθ : ∀ q, q ∉ supp → θ q = 0) {S : A} {B : ℤ} (w : Tree) : ∀ (p : Nm supp) (σ : St supp), OKs σ →
    σ.mode = .TH p → Rep σ.heap (σ.regs 1) w → KS θ supp σ.heap (σ.regs 2) σ.inp .nil S B →
    Mach.SumTo (UM θ supp) σ (θ (p.1 ++ w.path) * S) (B + 1 + 2 * (Lm supp - p.1.length : ℕ)) := by
  induction w with
  | nil =>
    intro p σ hσ hm hr hk
    have h0 : σ.regs 1 = 0 := hr
    have hrec' : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
      rw [h0]
      exact hσ.nil
    have h2 := hk (nx θ σ (.inr (.inr (.inl p))) 0 0 0) 0 (hσ.nx _ _ _ _) rfl hσ.r0 rfl (heap_nx σ _ _ _ _) rfl rfl
    have h3 := sumTo_rule hσ hrec' (.inr (.inr (.inl p))) (by rw [hm]; rfl) (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; rfl) rfl h2
    have hw : (rule θ supp (.inr (.inr (.inl p)))).wt = θ p.1 := rfl
    rw [hw] at h3
    simp only [Tree.path, List.append_nil]
    refine h3.mono ?_
    have : (0 : ℤ) ≤ ((Lm supp - p.1.length : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  | cons a b _ ih =>
    intro p σ hσ hm hr hk
    obtain ⟨pa, pb, s, hrec, ha, hb⟩ := hr
    have hrec' : ((.C, ![σ.regs (laM σ.mode), pa, pb, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      exact hrec
    let σ1 := nx θ σ (.inr (.inr (.inr (.inl p)))) pa pb s
    have hσ1 : OKs σ1 := hσ.nx _ _ _ _
    have ha1 : Rep σ1.heap pa a := ha.mono (heap_nx σ _ _ _ _)
    have hb1 : Rep σ1.heap pb b := hb.mono (heap_nx σ _ _ _ _)
    obtain ⟨x1, x2, x3, hx, -, -⟩ := ha1.load hσ1
    have hrec1 : ((kb (decide (a ≠ .nil)), ![σ1.regs (laM σ1.mode), x1, x2, x3]) : Rec Kd) ∈ σ1.heap := hx
    have hpath : (Tree.cons a b).path = decide (a ≠ .nil) :: b.path := rfl
    rw [hpath]
    have key : Mach.SumTo (UM θ supp) σ1 (θ (p.1 ++ decide (a ≠ .nil) :: b.path) * S)
        (B + 2 * (Lm supp - p.1.length : ℕ)) := by
      generalize decide (a ≠ .nil) = bt at hrec1 ⊢
      have hsplit : p.1 ++ bt :: b.path = (p.1 ++ [bt]) ++ b.path := by simp
      by_cases hp : p.1 ++ [bt] ∈ pre supp
      · have hnext : nextR supp σ1.mode (kb bt) = some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩)))) := by
          change nextR supp (.TB p) (kb bt) = _
          cases bt
          · exact dif_pos hp
          · exact dif_pos hp
        have h2 := ih ⟨_, hp⟩ (nx θ σ1 (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩)))) x1 x2 x3) (hσ1.nx _ _ _ _) rfl
          (hb1.mono (heap_nx σ1 _ _ _ _)) (KS.heap (fun _ hc => heap_nx σ1 _ _ _ _ (heap_nx σ _ _ _ _ hc)) hk)
        have h3 := sumTo_rule hσ1 hrec1 _ hnext (by change Md.TB p ≠ .P; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Md.TB p ≠ .D 7; simp)) rfl rfl h2
        have hw : (rule θ supp (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩))))).wt = 1 := rfl
        rw [hw, one_mul] at h3
        rw [hsplit]
        refine h3.mono ?_
        have h5 := length_pre hp
        simp only [List.length_append, List.length_singleton] at h5 ⊢
        have h6 : ((Lm supp - p.1.length : ℕ) : ℤ) = ((Lm supp - (p.1.length + 1) : ℕ) : ℤ) + 1 := by
          have : Lm supp - p.1.length = Lm supp - (p.1.length + 1) + 1 := by omega
          rw [this]
          push_cast
          ring
        rw [h6]
        linarith
      · have hz : θ (p.1 ++ bt :: b.path) = 0 := by rw [hsplit]; exact not_pre hp hθ _
        rw [hz, zero_mul]
        refine sumTo_stuck hσ1 hrec1 ?_ (by change Md.TB p ≠ .P; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Md.TB p ≠ .D 7; simp)) (by change Md.TB p ≠ .Z; simp) _
        change nextR supp (.TB p) (kb bt) = none
        cases bt
        · exact dif_neg hp
        · exact dif_neg hp
    have h3 := sumTo_rule hσ hrec' (.inr (.inr (.inr (.inl p)))) (by rw [hm]; rfl) (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl key
    have hw : (rule θ supp (.inr (.inr (.inr (.inl p))))).wt = 1 := rfl
    rw [hw, one_mul] at h3
    exact h3.mono (by linarith)

end Nc.Uni
end

/-! Source module: Nc.Uni.EvThm -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal machine evaluates formulas
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

section Inv

theorem inv_quote {c c0 : Tree} (h : Fm.ofTree c = .quote c0) :
    (c = .nil ∧ c0 = .nil) ∨ ∃ o, c = .cons o c0 ∧ o.len = 0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; injection h with h; exact Or.inl ⟨rfl, h.symm⟩
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    subst h
    exact Or.inr ⟨o, rfl, by assumption⟩

theorem inv_id {c : Tree} (h : Fm.ofTree c = .id) : ∃ o a, c = .cons o a ∧ o.len = 1 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

theorem inv_hd {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .hd a0) :
    ∃ o a, c = .cons o a ∧ o.len = 2 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_tl {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .tl a0) :
    ∃ o a, c = .cons o a ∧ o.len = 3 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_cons {c : Tree} {a0 b0 : Fm} (h : Fm.ofTree c = .cons a0 b0) :
    ∃ o a, c = .cons o a ∧ o.len = 4 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl = b0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h'
    exact ⟨o, a, rfl, by assumption, h, h'⟩

theorem inv_ite {c : Tree} {a0 b0 c0 : Fm} (h : Fm.ofTree c = .ite a0 b0 c0) :
    ∃ o a, c = .cons o a ∧ o.len = 5 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl.hd = b0 ∧ Fm.ofTree a.tl.tl = c0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h' h''
    exact ⟨o, a, rfl, by assumption, h, h', h''⟩

theorem inv_run {c : Tree} {a0 b0 : Fm} (h : Fm.ofTree c = .run a0 b0) :
    ∃ o a, c = .cons o a ∧ o.len = 6 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl = b0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h'
    exact ⟨o, a, rfl, by assumption, h, h'⟩

theorem inv_guess {c : Tree} (h : Fm.ofTree c = .guess) : ∃ o a, c = .cons o a ∧ o.len = 7 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

theorem inv_fail {c : Tree} (h : Fm.ofTree c = .fail) : ∃ o a, c = .cons o a ∧ (o.len = 8 ∨ 11 ≤ o.len) := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    refine ⟨o, a, rfl, ?_⟩
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    · left; assumption
    · right
      by_contra hc
      push Not at hc
      generalize o.len = k at *
      interval_cases k <;> simp_all

theorem inv_theta {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .theta a0) :
    ∃ o a, c = .cons o a ∧ o.len = 9 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_mul {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .mul a0) : ∃ o a, c = .cons o a ∧ o.len = 10 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

end Inv

/-- The sum over the runs without named constants. -/
def tot (m : Run A → A) (l : List (Run A)) : A := (l.map fun r => if r.bill = [] then r.th * m r else 0).sum

theorem tot_nil (m : Run A → A) : tot m [] = 0 := rfl

theorem tot_append (m : Run A → A) (l l' : List (Run A)) : tot m (l ++ l') = tot m l + tot m l' := by simp [tot]

theorem tot_flatMap (m : Run A → A) {ι : Type*} (l : List ι) (f : ι → List (Run A)) :
    tot m (l.flatMap f) = (l.map fun i => tot m (f i)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.flatMap_cons, tot_append, ih, List.map_cons, List.sum_cons]

/-- One run after the other. -/
theorem tot_seq (m : Run A → A) (la : List (Run A)) (L : Run A → List (Run A)) (o : Run A → Run A → Tree) :
    tot m (la.flatMap fun r => (L r).map fun s => (r.seq s).tick (o r s)) =
      tot (fun r => tot (fun s => m ((r.seq s).tick (o r s))) (L r)) la := by
  rw [tot_flatMap]
  unfold tot
  congr 1
  refine List.map_congr_left fun r _ => ?_
  rw [List.map_map]
  by_cases hr : r.bill = []
  · rw [if_pos hr, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, Run.tick, Run.seq, hr, List.nil_append]
    split_ifs
    · ring
    · ring
  · rw [if_neg hr]
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.mem_map] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact if_neg fun h => hr (List.append_eq_nil_iff.1 h).1

variable (supp) in
/-- Steps of the machine for one step of the evaluation. -/
def Cc : ℤ := 40 + 2 * (Lm supp : ℤ)

theorem Cc_ge : 40 ≤ Cc supp := by
  unfold Cc
  have : (0 : ℤ) ≤ (Lm supp : ℤ) := Int.natCast_nonneg _
  linarith

/-- The machine is about to evaluate the formula F at the tree x. -/
structure ES (σ : St supp) (F : Fm) (x : Tree) : Prop where
  ok : OKs σ
  mode : σ.mode = .E
  fm : ∃ c, Rep σ.heap (σ.regs 1) c ∧ Fm.ofTree c = F
  arg : Rep σ.heap (σ.regs 2) x

variable (θ supp) in
/-- The machine evaluates the formula correctly. -/
def EvOK (F : Fm) (x : Tree) (l : List (Run A)) : Prop :=
  ∀ σ : St supp, ES σ F x → ∀ (m : Run A → A) (Bd : Run A → ℤ) (B : ℤ),
    (∀ r ∈ l, r.bill = [] → KS θ supp σ.heap (σ.regs 3) σ.inp r.out (m r) (Bd r) ∧ Cc supp * r.cost + Bd r ≤ B) →
    Mach.SumTo (UM θ supp) σ (tot m l) B

/-- A step from an opcode. -/
theorem dstep {σ : St supp} (hσ : OKs σ) {c : Fin 11} (hm : σ.mode = .D c) (h1 : σ.regs 1 = 0) (r : Ra)
    (hr : nextR supp (.D c) .N = some (.inl r)) (hc : c ≠ 7) (hs : (ruleA r : RD A (Nm supp)).src = .D c)
    (hk : (ruleA r : RD A (Nm supp)).lk = .N) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) 0 0 0) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
    rw [h1]
    exact hσ.nil
  have h2 := sumTo_ruleA hσ hrec r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp [hc]) (by rw [hm]; exact hs)
    hk h
  exact h2.mono (by omega)

theorem EvOK.quote (c0 x : Tree) : EvOK θ supp (.quote c0) x [.det 1 c0] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 c0) (by simp) rfl
  have ht : tot m [.det 1 c0] = m (.det 1 c0) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 c0) ≤ B := by
    have : ((Run.det 1 c0 : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  rcases inv_quote hF with ⟨rfl, rfl⟩ | ⟨o, rfl, hl⟩
  · have h0 : σ.regs 1 = 0 := hc
    have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
      rw [h0]
      exact ok.nil
    have h2 := hk (nx θ σ (.inl .en) 0 0 0) 0 (ok.nx _ _ _ _) rfl h0 rfl (heap_nx σ _ _ _ _)
      (inpA σ _ (by simp) (by simp) _ _ _) rfl
    exact (sumTo_ruleA ok hrec .en (by rw [hm]; rfl) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; rfl) rfl h2).mono
      (by linarith)
  · refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
    have hm1' : σ1.mode = .D 0 := by rw [hm1]; congr 1; exact Fin.ext hl
    refine dstep ok1 hm1' h11 .d0 rfl (by decide) rfl rfl ?_
    refine (hk (nx θ σ1 (.inl .d0) 0 0 0) (σ1.regs 2) (ok1.nx _ _ _ _) rfl rfl h14
      (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1)
      (h12.mono (heap_nx σ1 _ _ _ _))).mono (by linarith)

theorem EvOK.id (x : Tree) : EvOK θ supp .id x [.det 1 x] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 x) (by simp) rfl
  have ht : tot m [.det 1 x] = m (.det 1 x) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 x) ≤ B := by
    have : ((Run.det 1 x : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  obtain ⟨o, a, rfl, hl⟩ := inv_id hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 1 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d1 rfl (by decide) rfl rfl ?_
  refine (hk (nx θ σ1 (.inl .d1) 0 0 0) (σ1.regs 3) (ok1.nx _ _ _ _) rfl rfl h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1) ?_).mono (by linarith)
  rw [h13]
  exact hx.mono fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)

theorem EvOK.fail (x : Tree) : EvOK θ supp .fail x [] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  rw [tot_nil]
  obtain ⟨o, a, rfl, hl | hl⟩ := inv_fail hF
  · refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
    have hm1' : σ1.mode = .D 8 := by rw [hm1]; congr 1; exact Fin.ext hl
    have hrec : ((.N, ![σ1.regs (laM σ1.mode), 0, 0, 0]) : Rec Kd) ∈ σ1.heap := by
      rw [hm1']
      change ((.N, ![σ1.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ1.heap
      rw [h11]
      exact ok1.nil
    exact sumTo_stuck ok1 hrec (by rw [hm1']; rfl) (by rw [hm1']; simp) (by
      rw [hm1']
      rintro ⟨h, -⟩
      injection h with h
      exact absurd h (by decide)) (by rw [hm1']; simp) _
  · exact noOp ok hm hc hl

end Nc.Uni
end

/-! Source module: Nc.Uni.EvThm2 -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal machine evaluates formulas: the cases with subformulas
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

theorem tot_map (m : Run A → A) (l : List (Run A)) (f : Run A → Tree) :
    tot m (l.map fun r => r.tick (f r)) = tot (fun r => m (r.tick (f r))) l := by
  unfold tot
  rw [List.map_map]
  rfl

/-- A step from a returned value; the frame is in the heap. -/
theorem rstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .R) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 2, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp .R κ = some (.inl r))
    (hs : (ruleA r : RD A (Nm supp)).src = .R) (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; exact hs) hk
    h).mono (by omega)

/-- A step that loads the record of register 1. -/
theorem lstep {σ : St supp} (hσ : OKs σ) {md : Md (Nm supp)} (hm : σ.mode = md) (hla : laM md = 1) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp md κ = some (.inl r))
    (hP : md ≠ .P) (hD : md ≠ .D 7) (hs : (ruleA r : RD A (Nm supp)).src = md)
    (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm, hla]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; exact hP) (by rw [hm]; exact fun e => hD e.1)
    (by rw [hm]; exact hs) hk h).mono (by omega)

theorem cost_tick (r : Run A) (o : Tree) : ((r.tick o).cost : ℤ) = r.cost + 1 := by
  simp [Run.tick]

theorem cost_seq (r s : Run A) : ((r.seq s).cost : ℤ) = r.cost + s.cost := by
  simp [Run.seq]

theorem EvOK.hd {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.hd a) x (l.map fun r => r.tick r.out.hd) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_hd hF
  have hC := Cc_ge (supp := supp)
  rw [tot_map]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 2 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d2 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d2) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d2) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (r.tick r.out.hd) + 2) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (r.tick r.out.hd) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    rw [cost_tick] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.HD, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d2) 0 0 0)
    refine rstep ok3 hm3 hfr .rhd rfl rfl rfl ?_
    have ok4 := ok3.nx (θ := θ) (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
    subst h31
    obtain ⟨p, q, s, hrec, hp, hq⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0))).load ok4
    generalize decide (r.out ≠ .nil) = b at hrec
    refine lstep ok4 (md := .H) rfl rfl hrec (.h b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
    refine (k1 (nx θ (nx θ σ3 (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) (.inl (.h b)) p q s) p
      (ok4.nx _ _ _ _) rfl rfl h14 (fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh3 (hh2 hc)))) ?_
      (hp.mono (heap_nx _ _ _ _ _))).mono (by linarith)
    rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), hi1]

theorem EvOK.tl {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.tl a) x (l.map fun r => r.tick r.out.tl) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_tl hF
  have hC := Cc_ge (supp := supp)
  rw [tot_map]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 3 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d3 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d3) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d3) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (r.tick r.out.tl) + 2) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (r.tick r.out.tl) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    rw [cost_tick] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.TL, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d3) 0 0 0)
    refine rstep ok3 hm3 hfr .rtl rfl rfl rfl ?_
    have ok4 := ok3.nx (θ := θ) (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
    subst h31
    obtain ⟨p, q, s, hrec, hp, hq⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0))).load ok4
    generalize decide (r.out ≠ .nil) = b at hrec
    refine lstep ok4 (md := .T) rfl rfl hrec (.t b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
    refine (k1 (nx θ (nx θ σ3 (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) (.inl (.t b)) p q s) q
      (ok4.nx _ _ _ _) rfl rfl h14 (fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh3 (hh2 hc)))) ?_
      (hq.mono (heap_nx _ _ _ _ _))).mono (by linarith)
    rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), hi1]

theorem EvOK.cons {a b : Fm} {x : Tree} {la lb : List (Run A)} (iha : EvOK θ supp a x la) (ihb : EvOK θ supp b x lb) :
    EvOK θ supp (.cons a b) x (la.flatMap fun r => lb.map fun s => (r.seq s).tick (.cons r.out s.out)) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl⟩ := inv_cons hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq m la (fun _ => lb) fun r s => .cons r.out s.out]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 4 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d4 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d4) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d4) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K4) rfl rfl hrec (.k4 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d4) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k4 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k4 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 2) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.CO1, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k4 bt)) p q s)
    refine rstep ok3 hm3 hfr .rco1 rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rco1) q (σ2.regs 2) (σ2.regs 3)
    set σ4 := nx θ σ3 (.inl .rco1) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    refine (ihb σ4 ⟨ok4, rfl, ⟨a'.tl, ?_, rfl⟩, ?_⟩ (fun s => m ((r.seq s).tick (.cons r.out s.out)))
      (fun s => Bd ((r.seq s).tick (.cons r.out s.out)) + 1) (B - Cc supp * r.cost - Cc supp + 1) ?_).mono (by linarith)
    · change Rep σ4.heap q a'.tl
      exact ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    · change Rep σ4.heap (σ2.regs 2) x
      rw [hr2]
      exact hx.mono hh4
    · intro s' hs' hb'
      obtain ⟨k1, k2⟩ := h ((r.seq s').tick (.cons r.out s'.out))
        (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨s', hs', rfl⟩⟩) (by simp [Run.tick, Run.seq, hb, hb'])
      rw [cost_tick, cost_seq] at k2
      refine ⟨fun σ5 v' ok5 hm5 h51 h52 hh5 hi5 hv' => ?_, by linarith⟩
      have hfr' : ((.CO2, ![σ5.regs 2, σ3.regs 1, σ2.regs 3, σ3.regs 0]) : Rec Kd) ∈ σ5.heap := by
        rw [h52]
        exact hh5 (new_nx (θ := θ) σ3 (.inl .rco1) q (σ2.regs 2) (σ2.regs 3))
      refine rstep ok5 hm5 hfr' .rco2 rfl rfl rfl ?_
      subst h51
      refine (k1 _ (σ5.n + 1) (ok5.nx _ _ _ _) rfl rfl hr3 (fun _ hc => heap_nx _ _ _ _ _ (hh5 (hh4 hc))) ?_ ?_).mono
        (by linarith)
      · rw [inpA _ _ (by simp) (by simp), hi5, inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp),
          inpA _ _ (by simp) (by simp), hi1]
      · refine ⟨σ3.regs 1, σ5.regs 1, σ5.regs 0, new_nx (θ := θ) σ5 (.inl .rco2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0), ?_, ?_⟩
        · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh5).mono (heap_nx _ _ _ _ _)
        · exact hv'.mono (heap_nx _ _ _ _ _)

theorem EvOK.ite {a b c : Fm} {x : Tree} {la : List (Run A)} {L : Run A → List (Run A)} (iha : EvOK θ supp a x la)
    (ihb : ∀ r ∈ la, r.out ≠ .nil → EvOK θ supp b x (L r)) (ihc : ∀ r ∈ la, r.out = .nil → EvOK θ supp c x (L r)) :
    EvOK θ supp (.ite a b c) x (la.flatMap fun r => (L r).map fun s => (r.seq s).tick s.out) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c', hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl, rfl⟩ := inv_ite hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq m la L fun r s => s.out]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 5 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d5 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d5) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d5) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K5) rfl rfl hrec (.k5 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d5) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k5 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k5 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 3) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.IT, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k5 bt)) p q s)
    refine rstep ok3 hm3 hfr .rit rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rit) q (σ2.regs 2) (σ2.regs 3)
    have hv4 := hv.mono (heap_nx (θ := θ) σ3 (.inl .rit) q (σ2.regs 2) (σ2.regs 3))
    set σ4 := nx θ σ3 (.inl .rit) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    have hq4 : Rep σ4.heap q a'.tl := ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    have hi4 : σ4.inp = σ.inp := by
      rw [inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi1]
    obtain ⟨y1, y2, y3, hrec4, -, -⟩ := hv4.load ok4
    have hrec4' : ((kb (decide (r.out ≠ .nil)), ![σ4.regs 1, y1, y2, y3]) : Rec Kd) ∈ σ4.heap := hrec4
    have hks : ∀ s' ∈ L r, s'.bill = [] → KS θ supp σ.heap (σ.regs 3) σ.inp s'.out (m ((r.seq s').tick s'.out))
        (Bd ((r.seq s').tick s'.out)) ∧ Cc supp * s'.cost + Bd ((r.seq s').tick s'.out) ≤
          B - Cc supp * r.cost - Cc supp := by
      intro s' hs' hb'
      obtain ⟨k1, k2⟩ := h ((r.seq s').tick s'.out)
        (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨s', hs', rfl⟩⟩) (by simp [Run.tick, Run.seq, hb, hb'])
      rw [cost_tick, cost_seq] at k2
      exact ⟨k1, by linarith⟩
    by_cases ho : r.out = .nil
    · have hkb : kb (decide (r.out ≠ .nil)) = .N := by simp [kb, ho]
      rw [hkb] at hrec4'
      refine lstep ok4 (md := .I) rfl rfl hrec4' .inn rfl (by simp) (by simp) rfl rfl ?_
      have ok5 := ok4.nx (θ := θ) (.inl .inn) y1 y2 y3
      have hq5 := hq4.mono (heap_nx (θ := θ) σ4 (.inl .inn) y1 y2 y3)
      set σ5 := nx θ σ4 (.inl .inn) y1 y2 y3 with hσ5
      obtain ⟨z1, z2, z3, hrec5, hz1, hz2⟩ := hq5.load ok5
      generalize decide (a'.tl ≠ .nil) = bu at hrec5
      have hrec5' : ((kb bu, ![σ5.regs 1, z1, z2, z3]) : Rec Kd) ∈ σ5.heap := hrec5
      refine lstep ok5 (md := .I2) rfl rfl hrec5' (.i2 bu) (by cases bu <;> rfl) (by simp) (by simp) rfl rfl ?_
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh4 hc))
      refine (ihc r hr ho (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3) ⟨ok5.nx _ _ _ _, rfl,
        ⟨a'.tl.tl, hz2.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ (fun s' => m ((r.seq s').tick s'.out))
        (fun s' => Bd ((r.seq s').tick s'.out)) (B - Cc supp * r.cost - Cc supp) ?_).mono (by linarith)
      · change Rep _ (σ2.regs 2) x
        rw [hr2]
        exact hx.mono hh6
      · intro s' hs' hb'
        obtain ⟨k1, k2⟩ := hks s' hs' hb'
        refine ⟨?_, k2⟩
        have e1 : (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi4]
        rw [e1, e2]
        exact k1.heap hh6
    · have hkb : kb (decide (r.out ≠ .nil)) = .C := by simp [kb, ho]
      rw [hkb] at hrec4'
      refine lstep ok4 (md := .I) rfl rfl hrec4' .ic rfl (by simp) (by simp) rfl rfl ?_
      have ok5 := ok4.nx (θ := θ) (.inl .ic) y1 y2 y3
      have hq5 := hq4.mono (heap_nx (θ := θ) σ4 (.inl .ic) y1 y2 y3)
      set σ5 := nx θ σ4 (.inl .ic) y1 y2 y3 with hσ5
      obtain ⟨z1, z2, z3, hrec5, hz1, hz2⟩ := hq5.load ok5
      generalize decide (a'.tl ≠ .nil) = bu at hrec5
      have hrec5' : ((kb bu, ![σ5.regs 1, z1, z2, z3]) : Rec Kd) ∈ σ5.heap := hrec5
      refine lstep ok5 (md := .I1) rfl rfl hrec5' (.i1 bu) (by cases bu <;> rfl) (by simp) (by simp) rfl rfl ?_
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh4 hc))
      refine (ihb r hr ho (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3) ⟨ok5.nx _ _ _ _, rfl,
        ⟨a'.tl.hd, hz1.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ (fun s' => m ((r.seq s').tick s'.out))
        (fun s' => Bd ((r.seq s').tick s'.out)) (B - Cc supp * r.cost - Cc supp) ?_).mono (by linarith)
      · change Rep _ (σ2.regs 2) x
        rw [hr2]
        exact hx.mono hh6
      · intro s' hs' hb'
        obtain ⟨k1, k2⟩ := hks s' hs' hb'
        refine ⟨?_, k2⟩
        have e1 : (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi4]
        rw [e1, e2]
        exact k1.heap hh6

end Nc.Uni
end

/-! Source module: Nc.Uni.EvThm3 -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal machine evaluates formulas: the other cases, and the input
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

theorem tot_seq3 (m : Run A → A) (la lb : List (Run A)) (L : Run A → Run A → List (Run A)) :
    tot m (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out) =
      tot (fun r => tot (fun s => tot (fun t => m (((r.seq s).seq t).tick t.out)) (L r s)) lb) la := by
  rw [tot_flatMap]
  unfold tot
  congr 1
  refine List.map_congr_left fun r _ => ?_
  have h1 := tot_flatMap m lb fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out
  unfold tot at h1
  rw [h1]
  by_cases hr : r.bill = []
  · rw [if_pos hr, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    rw [List.map_map]
    by_cases hs : s.bill = []
    · rw [if_pos hs, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp, Run.tick, Run.seq, hr, hs, List.nil_append]
      split_ifs
      · ring
      · ring
    · rw [if_neg hs, mul_zero]
      refine List.sum_eq_zero fun y hy => ?_
      rw [List.mem_map] at hy
      obtain ⟨t, -, rfl⟩ := hy
      exact if_neg fun h => hs (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).2
  · rw [if_neg hr]
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.mem_map] at hy
    obtain ⟨s, -, rfl⟩ := hy
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact if_neg fun h => hr (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).1

theorem EvOK.run {a b : Fm} {x : Tree} {la lb : List (Run A)} {L : Run A → Run A → List (Run A)}
    (iha : EvOK θ supp a x la) (ihb : EvOK θ supp b x lb)
    (ihc : ∀ r ∈ la, ∀ s ∈ lb, EvOK θ supp (Fm.ofTree r.out) s.out (L r s)) :
    EvOK θ supp (.run a b) x (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t =>
      ((r.seq s).seq t).tick t.out) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl⟩ := inv_run hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq3]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 6 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d6 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d6) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d6) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K6) rfl rfl hrec (.k6 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d6) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k6 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k6 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 2) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.RU1, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k6 bt)) p q s)
    refine rstep ok3 hm3 hfr .rru1 rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rru1) q (σ2.regs 2) (σ2.regs 3)
    set σ4 := nx θ σ3 (.inl .rru1) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    refine (ihb σ4 ⟨ok4, rfl, ⟨a'.tl, ?_, rfl⟩, ?_⟩ (fun s => tot (fun t => m (((r.seq s).seq t).tick t.out)) (L r s))
      (fun s => B - Cc supp * r.cost - Cc supp * s.cost - Cc supp + 1) (B - Cc supp * r.cost - Cc supp + 1) ?_).mono
      (by linarith)
    · change Rep σ4.heap q a'.tl
      exact ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    · change Rep σ4.heap (σ2.regs 2) x
      rw [hr2]
      exact hx.mono hh4
    · intro s' hs' hb'
      refine ⟨fun σ5 v' ok5 hm5 h51 h52 hh5 hi5 hv' => ?_, by linarith⟩
      have hfr' : ((.RU2, ![σ5.regs 2, σ3.regs 1, σ2.regs 3, σ3.regs 0]) : Rec Kd) ∈ σ5.heap := by
        rw [h52]
        exact hh5 (new_nx (θ := θ) σ3 (.inl .rru1) q (σ2.regs 2) (σ2.regs 3))
      refine rstep ok5 hm5 hfr' .rru2 rfl rfl rfl ?_
      subst h51
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (hh5 (hh4 hc))
      refine (ihc r hr s' hs' (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)) ⟨ok5.nx _ _ _ _, rfl,
        ⟨r.out, ?_, rfl⟩, hv'.mono (heap_nx _ _ _ _ _)⟩ (fun t => m (((r.seq s').seq t).tick t.out))
        (fun t => Bd (((r.seq s').seq t).tick t.out)) (B - Cc supp * r.cost - Cc supp * s'.cost - Cc supp) ?_).mono
        (by linarith)
      · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh5).mono (heap_nx _ _ _ _ _)
      · intro t ht hbt
        obtain ⟨k1, k2⟩ := h (((r.seq s').seq t).tick t.out)
          (List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨s', hs', List.mem_map.2 ⟨t, ht, rfl⟩⟩⟩)
          (by simp [Run.tick, Run.seq, hb, hb', hbt])
        rw [cost_tick, cost_seq, cost_seq] at k2
        refine ⟨?_, by linarith⟩
        have e1 : (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), hi5, inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp),
            inpA _ _ (by simp) (by simp), hi1]
        rw [e1, e2]
        exact k1.heap hh6

theorem EvOK.guess (x : Tree) : EvOK θ supp .guess x [.det 1 .nil, .det 1 Tree.one] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk0, hB0⟩ := h (.det 1 .nil) (by simp) rfl
  obtain ⟨hk1, hB1⟩ := h (.det 1 Tree.one) (by simp) rfl
  have ht : tot m [.det 1 .nil, .det 1 Tree.one] = 1 * m (.det 1 .nil) + 1 * m (.det 1 Tree.one) := by
    simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB0' : Cc supp + Bd (.det 1 .nil) ≤ B := by
    have : ((Run.det 1 .nil : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB0
    linarith
  have hB1' : Cc supp + Bd (.det 1 Tree.one) ≤ B := by
    have : ((Run.det 1 Tree.one : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB1
    linarith
  obtain ⟨o, a, rfl, hl⟩ := inv_guess hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 7 := by rw [hm1]; congr 1; exact Fin.ext hl
  have hrec : ((.N, ![σ1.regs (laM σ1.mode), 0, 0, 0]) : Rec Kd) ∈ σ1.heap := by
    rw [hm1']
    change ((.N, ![σ1.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ1.heap
    rw [h11]
    exact ok1.nil
  have hz : σ1.mode ≠ (UM θ supp).mh := by
    rw [hm1']
    change Md.D 7 ≠ .Z
    simp
  have g0 := hk0 (nx θ σ1 (.inl (.d7 false)) 0 0 0) 0 (ok1.nx _ _ _ _) rfl ok1.r0 h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1) rfl
  have g1 := hk1 (nx θ σ1 (.inl (.d7 true)) 0 0 0) (σ1.n + 1) (ok1.nx _ _ _ _) rfl rfl h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1)
    ⟨σ1.regs 0, σ1.regs 0, σ1.regs 0, new_nx (θ := θ) σ1 (.inl (.d7 true)) 0 0 0, ok1.r0, ok1.r0⟩
  have hfire : ∀ st' : (UM θ supp).Step, Mach.Fire σ1 st' ↔ st' = (.inl (.d7 false), envOf σ1 0 0 0) ∨
      st' = (.inl (.d7 true), envOf σ1 0 0 0) := by
    intro st'
    rw [fire_iff ok1 hrec, hm1']
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      have h5 : ∃ b, st'.1 = .inl (.d7 b) := by
        by_contra hne
        have hsp : ¬ Sp st'.1 := by
          rintro (e | e | e)
          · rw [e] at h1; exact absurd h1 (by simp [rule, ruleA, rl])
          · rw [e] at h1; exact absurd h1 (by simp [rule, ruleA, rl])
          · exact hne e
        have h6 := nextR_of (θ := θ) st'.1 hsp
        rw [h1, h2] at h6
        exact absurd h6 (by simp [nextR])
      obtain ⟨b, hb⟩ := h5
      cases b
      · exact Or.inl (Prod.ext hb h4)
      · exact Or.inr (Prod.ext hb h4)
    · rintro (rfl | rfl)
      · exact ⟨rfl, rfl, List.nil_prefix, rfl⟩
      · exact ⟨rfl, rfl, List.nil_prefix, rfl⟩
  have h9 := Mach.SumTo.two hz _ _ (fun e => by
    have h8 : (Sum.inl (Ra.d7 false) : Ru supp) = Sum.inl (Ra.d7 true) := congrArg Prod.fst e
    exact absurd h8 (by simp)) hfire (g0.mono (B' := B - 12) (by linarith)) (g1.mono (B' := B - 12) (by linarith))
  exact h9.mono (by omega)

theorem EvOK.mul {a : Fm} {x : Tree} {l : List (Run A)} :
    EvOK θ supp (.mul a) x (l.map fun r => ⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  have ht : tot m (l.map fun r => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)) = 0 := by
    unfold tot
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨r, -, rfl⟩ := hy
    simp
  rw [ht]
  obtain ⟨o, a', rfl, hl⟩ := inv_mul hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 10 := by rw [hm1]; congr 1; exact Fin.ext hl
  have hrec : ((.N, ![σ1.regs (laM σ1.mode), 0, 0, 0]) : Rec Kd) ∈ σ1.heap := by
    rw [hm1']
    change ((.N, ![σ1.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ1.heap
    rw [h11]
    exact ok1.nil
  exact sumTo_stuck ok1 hrec (by rw [hm1']; rfl) (by rw [hm1']; simp) (by
      rw [hm1']
      rintro ⟨h, -⟩
      injection h with h
      exact absurd h (by decide)) (by rw [hm1']; simp) _

theorem EvOK.theta (hθ : ∀ q, q ∉ supp → θ q = 0) {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.theta a) x (l.map fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_theta hF
  have hC := Cc_ge (supp := supp)
  let f : Run A → Run A := fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩
  have ht : tot m (l.map f) = tot (fun r => θ r.out.path * m (f r)) l := by
    unfold tot
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp, f]
    split_ifs
    · ring
    · rfl
  change Mach.SumTo (UM θ supp) σ (tot m (l.map f)) B
  rw [ht]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 9 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d9 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d9) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d9) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (f r) + 2 + 2 * (Lm supp : ℤ)) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (f r) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    have hcost : ((f r).cost : ℤ) = r.cost + 1 := by simp [f]
    rw [hcost] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by unfold Cc at *; linarith⟩
    have hfr : ((.TH, ![σ3.regs (laM σ3.mode), σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [hm3]
      change ((.TH, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d9) 0 0 0)
    by_cases hp : ([] : List Bool) ∈ pre supp
    · have ok4 := ok3.nx (θ := θ) (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
      have h4 := readName (θ := θ) hθ (S := m (f r)) (B := Bd (f r)) r.out ⟨[], hp⟩
        (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) ok4 rfl ?_ ?_
      · have h5 := sumTo_rule ok3 hfr (.inr (.inl ⟨(), hp⟩)) (by rw [hm3]; exact dif_pos hp) (by rw [hm3]; simp)
          (by rw [hm3]; simp) (by rw [hm3]; rfl) rfl h4
        have hw : (rule θ supp (.inr (.inl ⟨(), hp⟩))).wt = 1 := rfl
        rw [hw, one_mul] at h5
        refine h5.mono ?_
        simp only [List.length_nil, Nat.sub_zero]
        linarith
      · change Rep _ (σ3.regs 1) r.out
        rw [h31]
        exact hv.mono (heap_nx _ _ _ _ _)
      · have e1 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).regs 2 = σ.regs 3 := h14
        have e2 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).inp = σ.inp := by
          have e3 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).inp = σ3.inp := rfl
          rw [e3, hi3, inpA _ _ (by simp) (by simp), hi1]
        rw [e1, e2]
        exact k1.heap fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    · have hz : θ r.out.path = 0 := by
        have := not_pre hp hθ r.out.path
        simpa using this
      rw [hz, zero_mul]
      exact sumTo_stuck ok3 hfr (by rw [hm3]; exact dif_neg hp) (by rw [hm3]; simp) (by rw [hm3]; simp)
        (by rw [hm3]; simp) _

/-- **The machine evaluates all formulas.** -/
theorem evOK (hθ : ∀ q, q ∉ supp → θ q = 0) {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : EvOK θ supp F x l := by
  induction h with
  | quote c x => exact EvOK.quote c x
  | id x => exact EvOK.id x
  | hd _ ih => exact EvOK.hd ih
  | tl _ ih => exact EvOK.tl ih
  | cons _ _ iha ihb => exact EvOK.cons iha ihb
  | ite _ _ _ iha ihb ihc => exact EvOK.ite iha ihb ihc
  | run _ _ _ iha ihb ih => exact EvOK.run iha ihb ih
  | guess x => exact EvOK.guess x
  | fail x => exact EvOK.fail x
  | theta _ ih => exact EvOK.theta hθ ih
  | mul _ _ => exact EvOK.mul

end Nc.Uni
end

/-! Source module: Nc.Uni.TopU -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal machine: input and result
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The word of a tree: brackets in preorder. -/
def word : Tree → List Bool
  | .nil => [false]
  | .cons a b => true :: (word a ++ word b)

/-- What happens when a tree that has been read is returned to the frame k. -/
def PKS (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec Kd)) (k : ℕ) (inp : List Bool) (o : Tree) (S : A)
    (B : ℤ) : Prop :=
  ∀ (σ : St supp) (v : ℕ), OKs σ → σ.mode = .PR → σ.regs 1 = v → σ.regs 2 = k → H ⊆ σ.heap → σ.inp = inp →
    Rep σ.heap v o → Mach.SumTo (UM θ supp) σ S B

/-- A step after a tree has been read. -/
theorem pstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .PR) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 2, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp .PR κ = some (.inl r))
    (hs : (ruleA r : RD A (Nm supp)).src = .PR) (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; exact hs) hk
    h).mono (by omega)

/-- A step that reads a bracket. -/
theorem bstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .P) (b : Bool) {rest : List Bool} (hi : σ.inp = b :: rest) {S : A}
    {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl (if b then .pr1 else .pr0)) 0 0 0) S (B - 1)) :
    Mach.SumTo (UM θ supp) σ S B := by
  have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    change ((.N, ![σ.regs 0, 0, 0, 0]) : Rec Kd) ∈ σ.heap
    rw [hσ.r0]
    exact hσ.nil
  have hz : σ.mode ≠ (UM θ supp).mh := by
    rw [hm]
    change Md.P ≠ .Z
    simp
  have hfire : ∀ st' : (UM θ supp).Step, Mach.Fire σ st' ↔ st' = (.inl (if b then .pr1 else .pr0), envOf σ 0 0 0) := by
    intro st'
    rw [fire_iff hσ hrec, hm, hi]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine Prod.ext ?_ h4
      have hsp : Sp st'.1 := by
        by_contra hsp
        have h6 := nextR_of (θ := θ) st'.1 hsp
        rw [h1, h2] at h6
        exact absurd h6 (by simp [nextR])
      rcases hsp with e | e | ⟨c, e⟩
      · rw [e] at h3
        cases b
        · exact e
        · exfalso
          simp [rule, ruleA, rl] at h3
      · rw [e] at h3
        cases b
        · exfalso
          simp [rule, ruleA, rl] at h3
        · exact e
      · exfalso
        rw [e] at h1
        cases c
        · exact absurd h1 (by simp [rule, ruleA, rl])
        · exact absurd h1 (by simp [rule, ruleA, rl])
    · rintro rfl
      cases b
      · refine ⟨rfl, rfl, ?_, rfl⟩
        simp [rule, ruleA, rl]
      · refine ⟨rfl, rfl, ?_, rfl⟩
        simp [rule, ruleA, rl]
  have h9 := Mach.SumTo.one hz _ hfire h
  have hw : (UM θ supp).wt (.inl (if b then .pr1 else .pr0)) = 1 := wtA _
  rw [hw, one_mul] at h9
  exact h9.mono (by omega)

/-- **Reading a tree.** -/
theorem parse {S : A} (a : Tree) : ∀ (B : ℤ) (σ : St supp) (k : ℕ) (rest : List Bool), OKs σ → σ.mode = .P → σ.regs 1 = k →
    σ.inp = word a ++ rest → PKS θ supp σ.heap k rest a S B → Mach.SumTo (UM θ supp) σ S (B + 3 * a.size) := by
  induction a with
  | nil =>
    intro B σ k rest hσ hm h1 hi hk
    refine bstep hσ hm false (rest := rest) hi ?_
    refine (hk (nx θ σ (.inl .pr0) 0 0 0) 0 (hσ.nx _ _ _ _) rfl hσ.r0 h1 (heap_nx _ _ _ _ _) ?_ rfl).mono ?_
    · rw [inp_nx, hi]
      rfl
    · simp only [Tree.size]
      push_cast
      linarith
  | cons a b iha ihb =>
    intro B σ k rest hσ hm h1 hi hk
    have hi' : σ.inp = true :: (word a ++ (word b ++ rest)) := by
      rw [hi]
      simp [word]
    refine bstep hσ hm true hi' ?_
    have ok1 := hσ.nx (θ := θ) (.inl .pr1) 0 0 0
    refine (iha (B + 3 * b.size + 2) (nx θ σ (.inl .pr1) 0 0 0) (σ.n + 1) (word b ++ rest) ok1 rfl rfl ?_ ?_).mono ?_
    · rw [inp_nx, hi']
      rfl
    · intro σ2 v ok2 hm2 h21 h22 hh2 hi2 hv
      have hfr : ((.PA, ![σ2.regs 2, σ.regs 1, σ.regs 0, σ.regs 0]) : Rec Kd) ∈ σ2.heap := by
        rw [h22]
        exact hh2 (new_nx (θ := θ) σ (.inl .pr1) 0 0 0)
      refine pstep ok2 hm2 hfr .pa rfl rfl rfl ?_
      subst h21
      have ok3 := ok2.nx (θ := θ) (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0)
      refine (ihb (B + 1) (nx θ σ2 (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0)) (σ2.n + 1) rest ok3 rfl rfl ?_ ?_).mono
        (by linarith)
      · rw [inpA _ _ (by simp) (by simp), hi2]
      · intro σ4 v' ok4 hm4 h41 h42 hh4 hi4 hv'
        have hfr' : ((.PB, ![σ4.regs 2, σ2.regs 1, σ.regs 1, σ2.regs 0]) : Rec Kd) ∈ σ4.heap := by
          rw [h42]
          exact hh4 (new_nx (θ := θ) σ2 (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0))
        refine pstep ok4 hm4 hfr' .pb rfl rfl rfl ?_
        subst h41
        refine (hk (nx θ σ4 (.inl .pb) (σ2.regs 1) (σ.regs 1) (σ2.regs 0)) (σ4.n + 1) (ok4.nx _ _ _ _) rfl rfl h1
          (fun _ hc => heap_nx _ _ _ _ _ (hh4 (heap_nx _ _ _ _ _ (hh2 (heap_nx _ _ _ _ _ hc))))) ?_ ?_).mono (by linarith)
        · rw [inpA _ _ (by simp) (by simp), hi4]
        · refine ⟨σ2.regs 1, σ4.regs 1, σ4.regs 0, new_nx (θ := θ) σ4 (.inl .pb) (σ2.regs 1) (σ.regs 1) (σ2.regs 0), ?_, ?_⟩
          · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh4).mono (heap_nx _ _ _ _ _)
          · exact hv'.mono (heap_nx _ _ _ _ _)
    · simp only [Tree.size]
      push_cast
      linarith

variable (supp) in
/-- The first state. -/
def σ0 (z : Tree) : St supp := ⟨.S0, fun _ => 0, [(.N, ![0, 0, 0, 0])], 0, word z⟩

theorem ok_σ0 (z : Tree) : OKs (σ0 supp z) := by
  refine ⟨by simp [σ0], ?_, ?_, rfl⟩
  · intro c hc
    simp only [σ0, List.mem_singleton] at hc
    subst hc
    exact le_rfl
  · intro c hc c' hc' _
    simp only [σ0, List.mem_singleton] at hc hc'
    rw [hc, hc']

theorem closed_σ0 (z : Tree) : Mach.Closed (σ0 supp z) := by
  refine ⟨?_, ?_, fun _ => le_rfl⟩
  · intro c hc i
    simp only [σ0, List.mem_singleton] at hc
    subst hc
    fin_cases i <;> exact le_rfl
  · intro j hj
    have : j = 0 := Nat.le_zero.1 hj
    subst this
    exact ⟨(.N, ![0, 0, 0, 0]), by simp [σ0], rfl⟩

/-- A step that loads the record of register 0. -/
theorem zstep {σ : St supp} (hσ : OKs σ) {md : Md (Nm supp)} (hm : σ.mode = md) (hla : laM md = 0) (r : Ra)
    (hr : nextR supp md .N = some (.inl r)) (hP : md ≠ .P) (hD : md ≠ .D 7) (hs : (ruleA r : RD A (Nm supp)).src = md)
    (hk : (ruleA r : RD A (Nm supp)).lk = .N) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) 0 0 0) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm, hla, hσ.r0]
    exact hσ.nil
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; exact hP) (by rw [hm]; exact fun e => hD e.1)
    (by rw [hm]; exact hs) hk h).mono (by omega)

/-- The end of a run. -/
theorem KS_halt {H : List (Rec Kd)} {k : ℕ} (hk : ((.HT, ![k, 0, 0, 0]) : Rec Kd) ∈ H) (o : Tree) :
    KS θ supp H k [] o 1 1 := by
  intro σ v ok hm h1 h2 hh hi hv
  have hht : ((.HT, ![σ.regs 2, 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [h2]
    exact hh hk
  refine rstep ok hm hht .rht rfl rfl rfl ?_
  refine (Mach.SumTo.halt (P := UM θ supp) rfl ?_ (fun r => src_ne r)).mono (by norm_num)
  rw [inpA _ _ (by simp) (by simp), hi]

theorem pv_eq {τ : ℕ} {z : Tree} (h : Plain θ τ z) : pv θ z = tot (fun _ => 1) (evl θ (Fm.ofTree z.hd) z.tl) := by
  unfold pv tot pval
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [if_pos (h.2 r hr).1, mul_one]

/-- After the tree has been read. -/
theorem PKS_eval (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) {H : List (Rec Kd)} {k j s0 s1 : ℕ}
    (hj : ((.PE, ![j, k, s0, s1]) : Rec Kd) ∈ H) (hk : ((.HT, ![k, 0, 0, 0]) : Rec Kd) ∈ H) :
    PKS θ supp H j [] z (pv θ z) (Cc supp * τ + 3) := by
  intro σ3 v ok3 hm3 h31 h32 hh3 hi3 hv
  have hev := evOK (supp := supp) hθ h.1.ev
  have hfr : ((.PE, ![σ3.regs 2, k, s0, s1]) : Rec Kd) ∈ σ3.heap := by
    rw [h32]
    exact hh3 hj
  refine pstep ok3 hm3 hfr .pe rfl rfl rfl ?_
  subst h31
  have ok4 := ok3.nx (θ := θ) (.inl .pe) k s0 s1
  obtain ⟨p, q, s, hrec, hp', hq'⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .pe) k s0 s1)).load ok4
  have hi4 : (nx θ σ3 (.inl .pe) k s0 s1).inp = [] := (inpA _ _ (by simp) (by simp) _ _ _).trans hi3
  have hh4 : H ⊆ (nx θ σ3 (.inl .pe) k s0 s1).heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 hc)
  have hr4 : (nx θ σ3 (.inl .pe) k s0 s1).regs 2 = k := rfl
  have hrec4 : ((kb (decide (z ≠ .nil)), ![(nx θ σ3 (.inl .pe) k s0 s1).regs 1, p, q, s]) : Rec Kd) ∈
    (nx θ σ3 (.inl .pe) k s0 s1).heap := hrec
  have hm4 : (nx θ σ3 (.inl .pe) k s0 s1).mode = .S2 := rfl
  generalize nx θ σ3 (.inl .pe) k s0 s1 = σ4 at *
  generalize decide (z ≠ .nil) = b at hrec4
  refine lstep ok4 hm4 rfl hrec4 (.s2 b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
  rw [pv_eq h]
  refine (hev (nx θ σ4 (.inl (.s2 b)) p q s) ⟨ok4.nx _ _ _ _, rfl, ⟨z.hd, hp'.mono (heap_nx _ _ _ _ _), rfl⟩,
    hq'.mono (heap_nx _ _ _ _ _)⟩ (fun _ => 1) (fun _ => 1) (Cc supp * τ + 1) ?_).mono (by linarith)
  intro r hr hb
  refine ⟨?_, ?_⟩
  · have e1 : (nx θ σ4 (.inl (.s2 b)) p q s).regs 3 = k := hr4
    have e2 : (nx θ σ4 (.inl (.s2 b)) p q s).inp = [] := (inpA _ _ (by simp) (by simp) _ _ _).trans hi4
    rw [e1, e2]
    exact KS_halt (heap_nx _ _ _ _ _ (hh4 hk)) _
  · have hC := Cc_ge (supp := supp)
    have h9 : (r.cost : ℤ) ≤ τ := by exact_mod_cast (h.2 r hr).2
    have h10 : Cc supp * r.cost ≤ Cc supp * τ := mul_le_mul_of_nonneg_left h9 (by linarith)
    linarith

/-- The first step. -/
theorem start0 {σ : St supp} (ok : OKs σ) (hm : σ.mode = .S0) {S : A} {B : ℤ}
    (h : ∀ (σ' : St supp) (j : ℕ), OKs σ' → σ'.mode = .S1 → σ'.regs 1 = j → ((.HT, ![j, 0, 0, 0]) : Rec Kd) ∈ σ'.heap →
      σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  refine zstep ok hm rfl .s0 rfl (by simp) (by simp) rfl rfl ?_
  refine h (nx θ σ (.inl .s0) 0 0 0) (σ.n + 1) (ok.nx _ _ _ _) rfl rfl ?_ (inpA _ _ (by simp) (by simp) _ _ _)
  have h1 : ((.HT, ![σ.n + 1, σ.regs 0, σ.regs 0, σ.regs 0]) : Rec Kd) ∈ (nx θ σ (.inl .s0) 0 0 0).heap :=
    new_nx (θ := θ) σ (.inl .s0) 0 0 0
  rw [ok.r0] at h1
  exact h1

/-- The second step. -/
theorem start1 {σ : St supp} (ok : OKs σ) (hm : σ.mode = .S1) {S : A} {B : ℤ}
    (h : ∀ (σ' : St supp) (j s0 s1 : ℕ), OKs σ' → σ'.mode = .P → σ'.regs 1 = j →
      ((.PE, ![j, σ.regs 1, s0, s1]) : Rec Kd) ∈ σ'.heap → σ.heap ⊆ σ'.heap →
      σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  refine zstep ok hm rfl .s1 rfl (by simp) (by simp) rfl rfl ?_
  exact h (nx θ σ (.inl .s1) 0 0 0) (σ.n + 1) (σ.regs 0) (σ.regs 0) (ok.nx _ _ _ _) rfl rfl
    (new_nx (θ := θ) σ (.inl .s1) 0 0 0) (heap_nx _ _ _ _ _) (inpA _ _ (by simp) (by simp) _ _ _)

/-- From the first state. -/
theorem start (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) {σ : St supp} (ok : OKs σ)
    (hm : σ.mode = .S0) (hi : σ.inp = word z) :
    Mach.SumTo (UM θ supp) σ (pv θ z) (3 * z.size + Cc supp * τ + 10) := by
  refine start0 ok hm fun σ1 j ok1 hm1 hr1 hht hi1 => ?_
  refine start1 ok1 hm1 fun σ2 k s0 s1 ok2 hm2 hr2 hpe hh2 hi2 => ?_
  rw [hr1] at hpe
  refine (parse z (Cc supp * τ + 3) σ2 k [] ok2 hm2 hr2 (by rw [hi2, hi1, hi, List.append_nil])
    (PKS_eval hθ h hpe (hh2 hht))).mono (by linarith)

/-- **The universal machine.** -/
theorem sum_machine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) :
    Mach.SumTo (UM θ supp) (σ0 supp z) (pv θ z) (3 * z.size + Cc supp * τ + 10) :=
  start hθ h (ok_σ0 z) rfl rfl

end Nc.Uni
end

/-! Source module: Nc.Tape.ProgRun -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# From programs to runs

A program (a rational series on the channels) is an automaton that emits the letters of the program and then
idles.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F]

section Idle

variable {Ω : Type*}

/-- The words of the program, followed by idle letters. -/
def Series.idle (P : Series F Ω) : Series F (Option Ω) := Series.mul
  (fun o => if o.all Option.isSome then P o.reduceOption else 0) (fun o => if o.all Option.isNone then 1 else 0)

theorem RatLe.idle {n : ℕ} {P : Series F Ω} (hP : RatLe n P) : RatLe (n + 1) (Series.idle P) := by
  refine RatLe.mul ?_ ?_
  · obtain ⟨Q, _, r, hn, rfl⟩ := hP
    refine ⟨Q, inferInstance, ⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩, hn, ?_⟩
    have key : ∀ o : List (Option Ω), (⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩ : Rep F (Option Ω) Q).tail o =
        if o.all Option.isSome then r.tail o.reduceOption else 0 := by
      intro o
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a with
        | none => simp
        | some a =>
          by_cases h : o.all Option.isSome
          · simp only [h, if_true, List.all_cons, Option.isSome_some, Bool.true_and,
              List.reduceOption_cons_of_some, Option.elim]
            rfl
          · simp [h]
    funext o
    rw [Rep.series, key]
    by_cases h : o.all Option.isSome
    · simp only [h, if_true]; rfl
    · simp [h]
  · refine ⟨Unit, inferInstance, ⟨1, fun a => a.elim 1 fun _ => 0, 1⟩, by simp, ?_⟩
    have key : ∀ o : List (Option Ω), (⟨1, fun a => a.elim 1 fun _ => 0, 1⟩ : Rep F (Option Ω) Unit).tail o =
        if o.all Option.isNone then 1 else 0 := by
      intro o
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a with
        | none => simp
        | some a => simp
    funext o
    rw [Rep.series, key]
    by_cases h : o.all Option.isNone <;> simp [h]

theorem idle_apply (P : Series F Ω) (w : List Ω) (j : ℕ) :
    Series.idle P (w.map some ++ List.replicate j none) = P w := by
  rw [Series.idle, Series.mul, Finset.sum_eq_single w.length]
  · rw [List.take_left' (by simp), List.drop_left' (by simp)]
    simp [List.reduceOption]
  · intro k hk hne
    rw [mem_range, List.length_append, List.length_map, List.length_replicate] at hk
    rcases lt_or_gt_of_ne hne with h | h
    · have hmem : some w[k] ∈ (w.map some ++ List.replicate j none).drop k := by
        rw [List.drop_append_of_le_length (by simp; omega), List.mem_append, ← List.map_drop]
        left
        rw [List.mem_map]
        refine ⟨w[k], ?_, rfl⟩
        rw [List.drop_eq_getElem_cons h]
        exact List.mem_cons_self
      have : ¬ ((w.map some ++ List.replicate j none).drop k).all Option.isNone = true := by
        intro hall
        have := List.all_eq_true.1 hall _ hmem
        simp at this
      rw [if_neg this, mul_zero]
    · have hmem : none ∈ (w.map some ++ List.replicate j none).take k := by
        rw [List.take_append, List.mem_append]
        right
        rw [List.length_map, List.take_replicate, List.mem_replicate]
        exact ⟨by omega, rfl⟩
      have : ¬ ((w.map some ++ List.replicate j none).take k).all Option.isSome = true := by
        intro hall
        have := List.all_eq_true.1 hall _ hmem
        simp at this
      rw [if_neg this, zero_mul]
  · intro h
    exfalso
    apply h
    rw [mem_range, List.length_append, List.length_map]
    omega

theorem idle_ne_zero (P : Series F Ω) (o : List (Option Ω)) (h : Series.idle P o ≠ 0) :
    ∃ (w : List Ω) (j : ℕ), o = w.map some ++ List.replicate j none := by
  unfold Series.idle Series.mul at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  beta_reduce at hk
  have h1 : (o.take k).all Option.isSome = true := by
    by_contra hn
    rw [if_neg hn, zero_mul] at hk
    exact hk rfl
  have h2 : (o.drop k).all Option.isNone = true := by
    by_contra hn
    rw [if_neg hn, mul_zero] at hk
    exact hk rfl
  refine ⟨(o.take k).reduceOption, (o.drop k).length, ?_⟩
  have e1 : ∀ l : List (Option Ω), l.all Option.isSome = true → l.reduceOption.map some = l := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      cases a with
      | none => simp at hl
      | some a =>
        simp only [List.all_cons, Option.isSome_some, Bool.true_and] at hl
        rw [List.reduceOption_cons_of_some, List.map_cons, ih hl]
  have e2 : ∀ l : List (Option Ω), l.all Option.isNone = true → List.replicate l.length none = l := by
    intro l hl
    symm
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun a ha => ?_⟩
    have := List.all_eq_true.1 hl a ha
    simpa using this
  rw [e1 _ h1, e2 _ h2, List.take_append_drop]

end Idle

variable {Γ S J : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J]

/-- Channels as a sum. -/
def chSumEquiv (S J : Type*) : Ch S J ≃ (S × Bool) ⊕ J where
  toFun z := match z with
    | .tp s b => Sum.inl (s, b)
    | .inp j => Sum.inr j
  invFun x := match x with
    | Sum.inl (s, b) => .tp s b
    | Sum.inr j => .inp j
  left_inv z := by cases z <;> rfl
  right_inv x := by rcases x with ⟨s, b⟩ | j <;> rfl

theorem sum_length_tup (W : S → List Γ) (u : J → List Γ) :
    ∑ z, (tup W u z).length = 2 * ∑ s, (W s).length + ∑ j, (u j).length := by
  rw [Fintype.sum_equiv (chSumEquiv S J) _ (Sum.elim (fun x : S × Bool => (W x.1).length)
    fun j => (u j).length)]
  · rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.mul_sum]
    simp [two_mul]
  · intro z
    cases z <;> rfl

theorem ofFn_getElem? {Ω : Type*} (w : List Ω) (t : ℕ) (h : w.length ≤ t) :
    List.ofFn (fun k : Fin t => w[(k : ℕ)]?) = w.map some ++ List.replicate (t - w.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    rw [List.getElem_ofFn]
    by_cases hk : k < w.length
    · rw [List.getElem_append_left (by simpa using hk)]
      simp [hk]
    · rw [List.getElem_append_right (by simpa using hk)]
      simp; omega

theorem emit_idle (w : List (Ch S J × Γ)) (j : ℕ) :
    emit (w.map some ++ List.replicate j none) = proj w := by
  have : (w.map some ++ List.replicate j none).reduceOption = w := by
    rw [List.reduceOption_append]
    simp [List.reduceOption]
  rw [emit, this]

/-- **From programs to runs.** -/
theorem exists_run {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F) (i e : Q),
      Fintype.card Q ≤ n + 3 ∧ ∀ t, 1 ≤ t → ∀ u : J → List Γ, runVal mu i e t u =
        ∑ W ∈ (contents S Γ t).filter (fun W => 2 * ∑ s, (W s).length + ∑ j, (u j).length ≤ t),
          hat P (tup W u) := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, hmu⟩ := hP.idle.normal
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t ht u => ?_⟩
  have hne : ∀ o : Fin t → Letter S J Γ, List.ofFn o ≠ [] := by
    intro o h
    have := congrArg List.length h
    simp at this
    omega
  rw [runVal, Finset.sum_congr rfl fun o _ => by rw [hmu _ (hne o)]]
  simp only [hat]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_of_injOn (fun x k => x.2[(k : ℕ)]?) ?_ (by simp) ?_ ?_
  · rintro ⟨W, w⟩ hx ⟨W', w'⟩ hx' h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib] at hx hx'
    have l1 : w.length ≤ t := by
      rw [← sum_length_proj w, hx.2, sum_length_tup]; exact hx.1.2
    have l2 : w'.length ≤ t := by
      rw [← sum_length_proj w', hx'.2, sum_length_tup]; exact hx'.1.2
    have hw : w = w' := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < t
      · exact congrFun h ⟨k, hk⟩
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    subst hw
    have hW : W = W' := by
      funext s
      have := congrFun (hx.2.symm.trans hx'.2) (.tp s false)
      exact this
    rw [hW]
  · intro o _ ho
    by_contra hcon
    have hm : Matched (List.ofFn o) u := by
      by_contra hm
      exact hcon (if_neg hm)
    rw [if_pos hm] at hcon
    obtain ⟨w, j, hw⟩ := idle_ne_zero P _ hcon
    have hlen : w.length + j = t := by
      have := congrArg List.length hw
      simpa using this.symm
    apply ho
    have hproj : proj w = tup (fun s => proj w (.tp s false)) u := by
      rw [Matched, hw, emit_idle] at hm
      funext z
      cases z with
      | tp s b =>
        cases b with
        | false => rfl
        | true => exact (hm.1 s).symm
      | inp j => exact hm.2 j
    have hlen2 := sum_length_proj w
    rw [hproj, sum_length_tup] at hlen2
    refine ⟨⟨fun s => proj w (.tp s false), w⟩, ?_, ?_⟩
    · simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib, mem_contents]
      exact ⟨⟨by omega, by omega⟩, hproj⟩
    · apply List.ofFn_injective
      rw [hw, ofFn_getElem? w t (by omega)]
      congr 2
      omega
  · rintro ⟨W, w⟩ hx
    simp only [mem_sigma, mem_filter, mem_fib] at hx
    have l1 : w.length ≤ t := by
      rw [← sum_length_proj w, hx.2, sum_length_tup]; exact hx.1.2
    rw [ofFn_getElem? w t l1, if_pos, idle_apply]
    rw [Matched, emit_idle, hx.2]
    exact ⟨fun s => rfl, fun j => rfl⟩

/-- A bounded program is an automaton. -/
theorem exists_run_val {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F) (i e : Q),
      Fintype.card Q ≤ n + 3 ∧ ∀ (t₀ t : ℕ) (u : J → List Γ), Bdd t₀ P u →
        2 * t₀ + ∑ j, (u j).length + 1 ≤ t → runVal mu i e t u = val t₀ P u := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, H⟩ := exists_run hP
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t₀ t u hb ht => ?_⟩
  rw [H t (by omega) u, val]
  symm
  apply Finset.sum_subset
  · intro W hW
    rw [mem_contents] at hW
    rw [mem_filter, mem_contents]
    omega
  · intro W _ hW
    by_contra hne
    exact hW (mem_contents.2 (hb W hne))

end Nc
end

/-! Source module: Nc.Uni.Bounds -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The universal automaton: bounds for the time
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset NS1

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

theorem tU_mono {b T T' L L' : ℕ} (hT : T ≤ T') (hL : L ≤ L') : tU b T L ≤ tU b T' L' := by
  unfold tU
  gcongr

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The number of steps. -/
def stepsU (supp : Finset (List Bool)) (τ s : ℕ) : ℕ := 3 * s + (40 + 2 * Lm supp) * τ + 10

theorem tU_le (b T L : ℕ) : tU b T L ≤ (50 + b) * ((T + 1) * (L + 1) ^ 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t := ⟨T, rfl⟩
  have h1 : T ≤ T + 1 := Nat.le_succ _
  have h2 : L + 4 ≤ 4 * (L + 1) := by omega
  have h3 : L + 2 ≤ 2 * (L + 1) := by omega
  have h4 : L + 3 ≤ 3 * (L + 1) := by omega
  have h5 : 2 * T + 1 ≤ 2 * (T + 1) := by omega
  have hl : 1 ≤ L + 1 := by omega
  have ht : 1 ≤ T + 1 := by omega
  unfold tU
  generalize T + 1 = t at *
  generalize L + 1 = l at *
  calc 5 * (t * l) + t + t * l + T * l + T * (L + 4) +
        ((L + 2) * ((2 * T + 1) * (L + 4) + 1) + (l * ((2 * T + 1) * (L + 4)) + b * l) + 2 * ((2 * T + 1) * (L + 3)))
      ≤ 5 * (t * l) + t + t * l + t * l + t * (4 * l) +
        (2 * l * (2 * t * (4 * l) + 1) + (l * (2 * t * (4 * l)) + b * l) + 2 * (2 * t * (3 * l))) := by gcongr
    _ = 24 * (t * l ^ 2) + 23 * (t * l) + t + 2 * l + b * l := by ring
    _ ≤ 24 * (t * l ^ 2) + 23 * (t * l ^ 2) + t * l ^ 2 + 2 * (t * l ^ 2) + b * (t * l ^ 2) := by
        have a1 : l ≤ l ^ 2 := by nlinarith
        have a2 : t * l ≤ t * l ^ 2 := Nat.mul_le_mul_left _ a1
        have a3 : t ≤ t * l ^ 2 := by nlinarith
        have a4 : l ≤ t * l ^ 2 := by nlinarith
        gcongr
    _ = (50 + b) * (t * l ^ 2) := by ring

theorem size_le_lg (n : ℕ) : Nat.size n ≤ lg n := by
  rw [Nat.size_le, lg]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

end Nc.Uni
end

/-! Source module: Paper.UniversalSteps -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Cutting computations": the universal automaton is exact
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset NS1 Nc Nc.Uni

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

/-- **Paper: proof of Proposition prop:universal, the automaton is exact.** "So accepting runs correspond to matched
sequences of length t, provided that these are long enough": the value of the automaton's program is the sum of the
weights of the accepting runs of the machine. -/
theorem prop_universal_automaton {S₀ : Series A (Zc K × Sy M K)} (h : IsRuns S₀ (emX P) fun x => (x.2.2.1.map fun s => P.wt s.1).prod)
    {bits : List Bool} (hc : Mach.Closed (σi P bits)) (R : Finset (List P.Step))
    (hR : ∀ tr, tr ∈ R ↔ Mach.GV (σi P bits) tr) {Tm : ℕ} (hTm : ∀ tr ∈ R, tr.length ≤ Tm) :
    Bdd (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) ∧
      val (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) = ∑ tr ∈ R, Mach.wts tr := by
  classical
  have hle : ∀ x : XP P, Mt (emX P) (fun _ => bits.map .bit) x →
      ∑ s, (emX P x (.tp s true)).length ≤ tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1)) := by
    intro x hx
    rw [mt_X] at hx
    have h1 : x.2.2.1.length ≤ Tm := by
      have := hTm _ ((hR _).2 hx.gv)
      simpa using this
    rw [hx.total]
    refine tU_mono h1 ?_
    rw [← hx.size_eq]
    exact Nat.size_le_size (by omega)
  refine ⟨h.bdd hle, ?_⟩
  have hex : ∀ tr, ∃ x : XP P, tr ∈ R → MX x bits ∧ x.2.2.1.map nst = tr := by
    intro tr
    by_cases htr : tr ∈ R
    · have hgv := (hR tr).1 htr
      have hseq := (Mach.gv_iff hc tr).1 hgv
      have hb := hseq.le hc
      obtain ⟨x, hx⟩ := exists_MX hgv (by
        intro st hst i
        have := hb st hst i
        simpa [σi] using this)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨([], [], [], ([], []), [], ([], [], ([], [], (false, [])))), fun h => absurd h htr⟩
  choose f hf using hex
  have hinj : ∀ tr ∈ R, ∀ tr' ∈ R, f tr = f tr' → tr = tr' := by
    intro tr htr tr' htr' e
    rw [← (hf tr htr).2, ← (hf tr' htr').2, e]
  rw [h.val_eq _ _ (R.image f), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun tr htr => ?_
    have e := (hf tr htr).2
    rw [Mach.wts]
    conv_rhs => rw [← e]
    rw [List.map_map]
    rfl
  · intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨tr, htr, rfl⟩
      have hx := (mt_X (f tr) bits).2 (hf tr htr).1
      exact ⟨hx, hle _ hx⟩
    · rintro ⟨hx, -⟩
      have hx' := (mt_X x bits).1 hx
      have htr : x.2.2.1.map nst ∈ R := (hR _).2 hx'.gv
      exact ⟨_, htr, MX.unique (hf _ htr).1 hx' (hf _ htr).2⟩

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- **Paper: proof of Proposition prop:universal, the pointer machine is exact.** "So an accepting run of cost c gives
exactly one accepting run of the machine with the same weight, of at most O(|z|+c) steps, and there are no others", as
used: the accepting runs of the machine form a finite set, their weights sum to pv(z), and they have O(|z|+τ) steps. -/
theorem prop_universal_machine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) :
    ∃ R : Finset (List (UM θ supp).Step), (∀ tr, tr ∈ R ↔ Mach.GV (σ0 supp z) tr) ∧
      ∑ tr ∈ R, Mach.wts tr = pv θ z ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ 3 * z.size + Cc supp * τ + 10 := by
  obtain ⟨R, h1, h2, h3⟩ := sum_machine (supp := supp) hθ h
  refine ⟨R, fun tr => ?_, h2, h3⟩
  rw [h1, Mach.gv_iff (closed_σ0 z)]

variable (θ supp) in
/-- **Paper: proof of Proposition prop:universal, exactness and time.** The series of the automaton has the value pv(z) in
O((|z|+τ) lg(|z|+τ)²) letters. -/
theorem prop_universal_series (hθ : ∀ q, q ∉ supp → θ q = 0) :
    ∃ S₀ : Series A (Ch (Tp Kd) Unit × Sy (Md (Nm supp)) Kd), RatLe (dimX (UM θ supp)) S₀ ∧
      ∃ C : ℕ, ∀ (τ : ℕ) (z : Tree), Plain θ τ z →
        Bdd (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀ (fun _ => (word z).map .bit) ∧
        Nc.val (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀ (fun _ => (word z).map .bit) = pv θ z := by
  obtain ⟨S₀, h1, h2⟩ := runs_X (UM θ supp)
  let c := 41 + 2 * Lm supp
  let d := Nat.size c + 2
  refine ⟨S₀, h1, (50 + Fintype.card (Bl Kd)) * (c * d ^ 2), fun τ z hz => ?_⟩
  obtain ⟨R, r1, r2, r3⟩ := prop_universal_machine (supp := supp) hθ hz
  have hT : ∀ tr ∈ R, tr.length ≤ stepsU supp τ z.size := by
    intro tr htr
    have h3 := r3 tr htr
    have : (3 * z.size + Cc supp * τ + 10 : ℤ) = ((stepsU supp τ z.size : ℕ) : ℤ) := by
      unfold stepsU Cc
      push_cast
      ring
    rw [this] at h3
    exact_mod_cast h3
  obtain ⟨a1, a2⟩ := prop_universal_automaton h2 (closed_σ0 z) R r1 hT
  replace a2 := a2.trans r2
  set N := z.size + τ + 2 with hN
  have hT : stepsU supp τ z.size + 1 ≤ c * N := by
    have hs := Tree.size_pos z
    simp only [stepsU, c, hN]
    nlinarith [Nat.zero_le (Lm supp * z.size), Nat.zero_le (Lm supp)]
  have hlg : 1 ≤ lg N := Nat.le_add_left 1 _
  have hL : Nat.size (stepsU supp τ z.size + 1) + 1 ≤ d * lg N := by
    have h3 : Nat.size (stepsU supp τ z.size + 1) ≤ Nat.size c + lg N :=
      (Nat.size_le_size hT).trans ((size_mul_le c N).trans (Nat.add_le_add_left (size_le_lg N) _))
    have h4 : Nat.size c ≤ Nat.size c * lg N := Nat.le_mul_of_pos_right _ hlg
    simp only [d]
    nlinarith
  have ht : tU (Fintype.card (Bl Kd)) (stepsU supp τ z.size) (Nat.size (stepsU supp τ z.size + 1)) ≤
      (50 + Fintype.card (Bl Kd)) * (c * d ^ 2) * (N * lg N ^ 2) := by
    refine (tU_le _ _ _).trans ?_
    calc (50 + Fintype.card (Bl Kd)) * ((stepsU supp τ z.size + 1) * (Nat.size (stepsU supp τ z.size + 1) + 1) ^ 2)
        ≤ (50 + Fintype.card (Bl Kd)) * (c * N * (d * lg N) ^ 2) := by gcongr
      _ = _ := by ring
  exact ⟨fun W hW => (a1 W hW).trans ht, by rw [val_eq_of_bdd a1 ht, a2]⟩

end Paper
end

/-! Source module: Nc.Dl.Cut -/
section
namespace Nc.Dl
open NS1 NS1.Tree
theorem length_wordG {Γ : Type} (b0 b1 : Γ) (z : Tree) : (wordG b0 b1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [wordG, List.length_cons, List.length_append, iha, ihb, Tree.size]


end Nc.Dl
end

/-! Source module: NS1.Main -/
section
namespace NS1
theorem lt_two_pow_lg (n : ℕ) : n < 2 ^ lg n := Nat.lt_pow_succ_log_self (by norm_num) n


end NS1
end

/-! Source module: Paper.Universal -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Cutting computations": the universal automaton
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A]

theorem map_word {Γ : Type} (f : Bool → Γ) (z : Tree) :
    (Nc.Uni.word z).map f = Nc.Dl.wordG (f false) (f true) z := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [Nc.Uni.word, Nc.Dl.wordG, List.map_cons, List.map_append, iha, ihb]

/-- **Paper: Proposition prop:universal.** "There are a tape automaton and a constant C such that its value, on the standard
code of an instance z as a word, in t steps, is pv(z) whenever z is τ-plain and t ≥ C(|z|+τ) lg(|z|+τ)²." -/
theorem prop_universal (θ : List Bool → A) (hθ : (Function.support θ).Finite) :
    ∃ (S Γ Q : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype Γ) (_ : DecidableEq Γ) (_ : Fintype Q)
      (_ : DecidableEq Q) (mu : Nc.Letter S Unit Γ → Matrix Q Q A) (i e : Q) (b0 b1 : Γ) (C : ℕ),
      ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
        Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z := by
  classical
  have hs : ∀ q, q ∉ hθ.toFinset → θ q = 0 := by
    intro q hq
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hq
    exact hq
  obtain ⟨S₀, h1, C, h2⟩ := prop_universal_series θ hθ.toFinset hs
  obtain ⟨Q, iQ, dQ, mu, i, e, -, h3⟩ := Nc.exists_run_val h1
  refine ⟨_, _, Q, inferInstance, inferInstance, inferInstance, inferInstance, iQ, dQ, mu, i, e, .bit false, .bit true,
    27 * (2 * C + 2), fun τ z t hp ht => ?_⟩
  obtain ⟨a1, a2⟩ := h2 τ z hp
  rw [← map_word Nc.Uni.Sy.bit z, ← a2]
  refine h3 _ _ _ a1 (le_trans ?_ ht)
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, map_word, Nc.Dl.length_wordG]
  have hn : 1 ≤ z.size + τ := by
    have := Tree.size_pos z
    omega
  have hlg : lg (z.size + τ + 2) ≤ 3 * lg (z.size + τ) := by
    have h3 : z.size + τ + 2 < 2 ^ (lg (z.size + τ) + 2) := by
      have := lt_two_pow_lg (z.size + τ)
      rw [pow_add]
      omega
    have h4 : lg (z.size + τ + 2) ≤ lg (z.size + τ) + 2 := Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow' (by omega) h3)
    have h5 : 1 ≤ lg (z.size + τ) := Nat.succ_le_succ (Nat.zero_le _)
    omega
  have h6 : 1 ≤ lg (z.size + τ + 2) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h7 : z.size + 1 ≤ 2 * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2) := by
    have := Nat.le_mul_of_pos_right (z.size + τ + 2) (show 0 < lg (z.size + τ + 2) ^ 2 by omega)
    omega
  calc 2 * (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) + z.size + 1
      ≤ (2 * C + 2) * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2) := by
        rw [add_mul (2 * C) 2, mul_assoc 2 C]; omega
    _ ≤ (2 * C + 2) * ((3 * (z.size + τ)) * (3 * lg (z.size + τ)) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hlg 2))
    _ = _ := by ring

end Paper
end

open NS1
theorem solution {A : Type} [CommRing A] (θ : List Bool → A) (hθ : (Function.support θ).Finite) :
    ∃ (S Γ Q : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype Γ) (_ : DecidableEq Γ) (_ : Fintype Q)
      (_ : DecidableEq Q) (mu : Nc.Letter S Unit Γ → Matrix Q Q A) (i e : Q) (b0 b1 : Γ) (C : ℕ),
      ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
        Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z := Paper.prop_universal θ hθ
