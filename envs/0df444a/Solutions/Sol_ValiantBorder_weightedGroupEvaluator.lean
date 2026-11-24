-- Prove2me | solution 1 for ValiantBorder.weightedGroupEvaluator
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:09:36.195828+00:00
-- url     : https://prove2.me/submissions/9762de31-1b98-4978-af9c-03f319b50834

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_groupEvaluator
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
source `anthropics/formal-math` at `11b6c7e3c927df2658f513b6b68ea7f8929c62c5`.
The weighted evaluator, group instructions and resource estimates are from
`Nc/G/Defs.lean`, `Nc/Grp/{Script,GroupThm,GrpTime}.lean`, `Nc/Dl/{Inst,GrpCost}.lean`,
and `Paper/Cuts.lean`. Apache-2.0. -/
set_option linter.unusedSectionVars false

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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Weighted functions computed by formulas

`Does θ F x Q c`: all runs of the formula `F` at the tree `x` stop, they use no named constants, the accepting ones
have cost at most `c`, and for every function of the value their weighted sum is that of the list `Q` of pairs
(weight, value).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Weighted sums over a list of pairs (weight, value). -/
def wsum (Q : List (A × Tree)) (φ : Tree → A) : A := (Q.map fun q => q.1 * φ q.2).sum

@[simp] theorem wsum_nil (φ : Tree → A) : wsum ([] : List (A × Tree)) φ = 0 := rfl

@[simp] theorem wsum_cons (q : A × Tree) (Q : List (A × Tree)) (φ : Tree → A) :
    wsum (q :: Q) φ = q.1 * φ q.2 + wsum Q φ := by simp [wsum]

theorem wsum_append (Q Q' : List (A × Tree)) (φ : Tree → A) : wsum (Q ++ Q') φ = wsum Q φ + wsum Q' φ := by
  simp [wsum]

theorem wsum_congr {Q : List (A × Tree)} {φ φ' : Tree → A} (h : ∀ q ∈ Q, φ q.2 = φ' q.2) : wsum Q φ = wsum Q φ' := by
  unfold wsum
  congr 1
  exact List.map_congr_left fun q hq => by rw [h q hq]

/-- First `Q`, then `R` at the value. -/
def bindW (Q : List (A × Tree)) (R : Tree → List (A × Tree)) : List (A × Tree) :=
  Q.flatMap fun q => (R q.2).map fun p => (q.1 * p.1, p.2)

theorem wsum_bindW (Q : List (A × Tree)) (R : Tree → List (A × Tree)) (φ : Tree → A) :
    wsum (bindW Q R) φ = wsum Q fun o => wsum (R o) φ := by
  unfold wsum bindW
  rw [sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, mul_assoc]

theorem mem_bindW {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {p : A × Tree} (h : p ∈ bindW Q R) :
    ∃ q ∈ Q, ∃ r ∈ R q.2, p.2 = r.2 ∧ p.1 = q.1 * r.1 := by
  unfold bindW at h
  rw [List.mem_flatMap] at h
  obtain ⟨q, hq, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨q, hq, r, hr, rfl, rfl⟩

theorem mem_bindW_of {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {q r : A × Tree} (hq : q ∈ Q)
    (hr : r ∈ R q.2) : (q.1 * r.1, r.2) ∈ bindW Q R :=
  List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨r, hr, rfl⟩⟩

/-- The formula computes the weighted list `Q` at `x`. -/
def Does (θ : List Bool → A) (F : Fm) (x : Tree) (Q : List (A × Tree)) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.bill = [] ∧ r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, (l.map fun r => r.th * φ r.out).sum = wsum Q φ

/-- The formula has the value `o` at `x`, with weight 1. -/
def Gives (θ : List Bool → A) (F : Fm) (x o : Tree) (c : ℕ) : Prop := Does θ F x [(1, o)] c

namespace Does

variable {F G H : Fm} {x : Tree} {Q : List (A × Tree)} {c d : ℕ}

theorem mono (h : Does θ F x Q c) (hc : c ≤ d) : Does θ F x Q d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1, (h2 r hr).2.1.trans hc, (h2 r hr).2.2⟩, h3⟩

/-- Replace the list by an equivalent one. -/
theorem congr {Q' : List (A × Tree)} (h : Does θ F x Q c) (h1 : ∀ q ∈ Q, ∃ q' ∈ Q', q'.2 = q.2)
    (h2 : ∀ φ : Tree → A, wsum Q φ = wsum Q' φ) : Does θ F x Q' c := by
  obtain ⟨l, e1, e2, e3⟩ := h
  refine ⟨l, e1, fun r hr => ⟨(e2 r hr).1, (e2 r hr).2.1, ?_⟩, fun φ => (e3 φ).trans (h2 φ)⟩
  obtain ⟨q, hq, hqr⟩ := (e2 r hr).2.2
  obtain ⟨q', hq', e⟩ := h1 q hq
  exact ⟨q', hq', e.trans hqr⟩

theorem hl (h : Does θ F x Q c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : Does θ F x Q c) : (∀ r ∈ NS1.evl θ F x, r.bill = [] ∧ r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, ((NS1.evl θ F x).map fun r => r.th * φ r.out).sum = wsum Q φ := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

/-- A computation is a plain sum. -/
theorem plain (h : Does θ F x Q c) : Plain θ c (.cons F.code x) ∧ pv θ (.cons F.code x) = (Q.map Prod.fst).sum := by
  obtain ⟨h1, h2⟩ := h.evl
  refine ⟨⟨?_, fun r hr => ?_⟩, ?_⟩
  · simp only [hd_cons, tl_cons, Fm.ofTree_code]
    exact h.hl
  · simp only [hd_cons, tl_cons, Fm.ofTree_code] at hr
    exact ⟨(h1 r hr).1, (h1 r hr).2.1⟩
  · simp only [pv, hd_cons, tl_cons, Fm.ofTree_code, pval]
    have := h2 fun _ => 1
    simpa [wsum] using this

theorem of_dt {o : Tree} (h : Dt θ F x o c) : Does θ F x [(1, o)] c := by
  refine ⟨_, h, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, le_rfl, (1, o), List.mem_singleton_self _, rfl⟩
  · simp [Run.det]

/-- Pairs. -/
theorem cons {R : List (A × Tree)} (hF : Does θ F x Q c) (hG : Does θ G x R d) : Does θ (.cons F G) x
    (Q.flatMap fun q => R.map fun r => (q.1 * r.1, .cons q.2 r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    obtain ⟨a1, a2, q, hq, a3⟩ := e2 r1 h1
    obtain ⟨b1, b2, p, hp, b3⟩ := f2 r2 h2
    refine ⟨?_, ?_, (q.1 * p.1, .cons q.2 p.2), List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨p, hp, rfl⟩⟩, ?_⟩
    · simp [Run.seq, Run.tick, a1, b1]
    · simp only [Run.seq, Run.tick]
      omega
    · simp [Run.tick, a3, b3]
  · rw [sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map fun u => u.th * φ u.out).sum =
        r.th * wsum R fun o => φ (.cons r.out o) := by
      intro r
      rw [← f3, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    simp only [h1]
    rw [e3 fun o => wsum R fun o' => φ (.cons o o'), wsum, wsum, sum_flatMap_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [wsum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, mul_assoc]

/-- Apply a fixed program to the value. -/
theorem app {p : Tree} {R : Tree → List (A × Tree)} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) d) : Does θ (app p F) x (bindW Q R) (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, Does θ (Fm.ofTree p) s.out (R s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, q, hq, a3⟩ := e2 s hs
    obtain ⟨b1, b2, r, hr, b3⟩ := (hG' s hs).evl.1 t ht
    rw [← a3] at hr
    refine ⟨by rw [h2, a1, b1]; rfl, by omega, (q.1 * r.1, r.2), mem_bindW_of hq hr, ?_⟩
    rw [h3, ← b3]
  · rw [wsum_bindW, sum_flatMap_map, ← wsum_congr (φ := fun o => ((NS1.evl θ (Fm.ofTree p) o).map fun t =>
      t.th * φ t.out).sum) (fun q hq => (hG q hq).evl.2 φ), ← e3]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Run.seq, Run.tick, Run.det, one_mul, mul_assoc]

/-- `let`. -/
theorem lett {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G q.2 (R q.2) d) :
    Does θ (lett F G) x (bindW Q R) (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

/-- `let`, with the argument kept. -/
theorem letk {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G (.cons x q.2) (R q.2) d) :
    Does θ (NS1.lett (.cons .id F) G) x (bindW Q R) (c + d + 4) := by
  have h1 := (of_dt (Dt.id x)).cons hF
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul] at h1
  have h2 := h1.lett (G := G) (R := fun o => R o.tl) (d := d) (by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact hG q' hq')
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    rw [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨_, mem_bindW_of hq' hr, h3.symm⟩
  · rw [wsum_bindW, wsum_bindW]
    simp [wsum, Function.comp_def]

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {R : List (A × Tree)} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : Does θ (Fm.ofTree p) y R e) : Does θ (.run F G) x R (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have ho' : ∀ r ∈ l', r.out = y := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := f2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2, c3⟩ := h.evl.1 t ht
    refine ⟨by simp [Run.seq, Run.tick, a1, b1, c1], ?_, c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum R φ := by
      intro r hr
      rw [sum_flatMap_map]
      have h2 : ∀ s ∈ l', (((NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
          ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = s.th * (r.th * wsum R φ) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2 φ, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, Run.seq, Run.tick]
        ring
      rw [List.map_congr_left h2]
      have := f3 fun _ => r.th * wsum R φ
      rw [this]
      simp [wsum]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum R φ
    rw [this]
    simp [wsum]

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Does θ G x Q d) :
    Does θ (.ite F G H) x Q (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r _ _ => f1) (fun r hr h => absurd ((hout r hr).symm.trans h) ho), ?_,
    fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp [wsum]

theorem ite_false (hF : Gives θ F x .nil c) (hH : Does θ H x Q d) : Does θ (.ite F G H) x Q (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp [wsum]

/-- Guess between two formulas. -/
theorem either {R : List (A × Tree)} (hG : Does θ G x Q c) (hH : Does θ H x R d) :
    Does θ (.ite .guess G H) x (Q ++ R) (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2, q, hq, a3⟩ := f2 s hs
      refine ⟨by simp [Run.seq, Run.tick, a1], ?_, q, List.mem_append_right _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
    · obtain ⟨a1, a2, q, hq, a3⟩ := e2 s hs
      refine ⟨by simp [Run.seq, Run.tick, a1], ?_, q, List.mem_append_left _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
  · rw [wsum_append, ← e3 φ, ← f3 φ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    rw [add_comm]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, one_mul]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, one_mul]

theorem fail (x : Tree) : Does θ .fail x [] 0 := ⟨[], .fail x, by simp, by simp⟩

/-- Multiply by a constant of `A`. -/
theorem theta {o : Tree} (h : Gives θ F x o c) : Does θ (.theta F) x [(θ o.path, .nil)] (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.theta e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    exact ⟨a1, by simpa using a2, _, List.mem_singleton_self _, rfl⟩
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A =>
        (⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩ : Run A)) r = r.th * (θ o.path * φ .nil) := by
      intro r hr
      simp only [Function.comp_apply, hout r hr, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => θ o.path * φ .nil
    rw [this]
    simp [wsum]

theorem hd {o : Tree} (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.hd e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨a1, by simpa [Run.tick] using a2, _, List.mem_singleton_self _, ?_⟩
    simp [Run.tick, hout r hr]
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A => r.tick r.out.hd) r = r.th * φ o.hd := by
      intro r hr
      simp only [Function.comp_apply, Run.tick, hout r hr]
    rw [List.map_congr_left h1]
    have := e3 fun _ => φ o.hd
    rw [this]
    simp [wsum]

theorem tl {o : Tree} (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.tl e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨a1, by simpa [Run.tick] using a2, _, List.mem_singleton_self _, ?_⟩
    simp [Run.tick, hout r hr]
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A => r.tick r.out.tl) r = r.th * φ o.tl := by
      intro r hr
      simp only [Function.comp_apply, Run.tick, hout r hr]
    rw [List.map_congr_left h1]
    have := e3 fun _ => φ o.tl
    rw [this]
    simp [wsum]

end Does

namespace Gives

variable {F G H : Fm} {x o o' : Tree} {c d : ℕ}

theorem mono (h : Gives θ F x o c) (hc : c ≤ d) : Gives θ F x o d := Does.mono h hc

theorem id (x : Tree) : Gives θ .id x x 1 := Does.of_dt (Dt.id x)

theorem quote (a x : Tree) : Gives θ (.quote a) x a 1 := Does.of_dt (Dt.quote a x)

theorem hd (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) := Does.hd h

theorem tl (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) := Does.tl h

theorem cons (h : Gives θ F x o c) (h' : Gives θ G x o' d) : Gives θ (.cons F G) x (.cons o o') (c + d + 1) := by
  have := Does.cons h h'
  simpa [Gives] using this

theorem app {p : Tree} (h : Gives θ F x o c) (h' : Gives θ (Fm.ofTree p) o o' d) :
    Gives θ (NS1.app p F) x o' (c + d + 2) := by
  have := Does.app (p := p) (R := fun _ => [(1, o')]) h (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [Gives, bindW] using this

theorem lett (h : Gives θ F x o c) (h' : Gives θ G o o' d) : Gives θ (NS1.lett F G) x o' (c + d + 2) :=
  app (p := G.code) h (by rw [Fm.ofTree_code]; exact h')

theorem letk (h : Gives θ F x o c) (h' : Gives θ G (.cons x o) o' d) :
    Gives θ (NS1.lett (.cons .id F) G) x o' (c + d + 4) :=
  (((id x).cons h).lett h').mono (by omega)

theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d) (h : Gives θ (Fm.ofTree p) y o e) :
    Gives θ (.run F G) x o (c + d + e + 1) := Does.run hF hG h

theorem ite_true (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Gives θ G x o' d) :
    Gives θ (.ite F G H) x o' (c + d + 1) := Does.ite_true hF ho hG

theorem ite_false (hF : Gives θ F x .nil c) (hH : Gives θ H x o' d) : Gives θ (.ite F G H) x o' (c + d + 1) :=
  Does.ite_false hF hH

/-- A computation, then a deterministic one. -/
theorem after {Q : List (A × Tree)} (h : Does θ F x Q c) {f : Tree → Tree} (h' : ∀ q ∈ Q, Gives θ G q.2 (f q.2) d) :
    Does θ (NS1.lett F G) x (Q.map fun q => (q.1, f q.2)) (c + d + 2) := by
  have := h.lett (R := fun o => [(1, f o)]) h'
  simpa [bindW, flatMap_single] using this

end Gives

/-- The weighted list of a deterministic computation followed by another one. -/
theorem Does.of_gives {F G : Fm} {x o : Tree} {Q : List (A × Tree)} {c d : ℕ} (h : Gives θ F x o c)
    (h' : Does θ G o Q d) : Does θ (NS1.lett F G) x Q (c + d + 2) := by
  have := Does.lett (R := fun _ => Q) h (G := G) (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [bindW] using this

end NS1

end

section










set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}




@[simp] theorem toList_listT (xs : List Tree) : (listT xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listT, toList, ih]

theorem listT_toList (x : Tree) : listT x.toList = x := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp [listT, toList, ih]

theorem listT_ofBits (w : List Bool) : listT (w.map bit) = ofBits w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [listT, ofBits, ih]


theorem Does.runW {F G : Fm} {x p : Tree} {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {c d e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x Q d) (h : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) e) :
    Does θ (.run F G) x (bindW Q R) (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have hG' : ∀ s ∈ l', Does θ (Fm.ofTree p) s.out (R s.out) e := by
    intro s hs
    obtain ⟨-, -, q, hq, h'⟩ := f2 s hs
    rw [← h']
    exact h q hq
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr]; exact (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    obtain ⟨c1, c2, q', hq', c3⟩ := (hG' s hs).evl.1 t ht
    rw [← b3] at hq'
    refine ⟨by simp [Run.seq, Run.tick, a1, b1, c1], ?_, (q.1 * q'.1, q'.2), mem_bindW_of hq hq', c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map, wsum_bindW]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q fun o => wsum (R o) φ := by
      intro r hr
      rw [sum_flatMap_map, ← f3 fun o => wsum (R o) φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      rw [ho r hr, List.map_map, ← (hG' s hs).evl.2 φ, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick]
      ring
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q fun o => wsum (R o) φ
    rw [this]
    simp [wsum]

section Fold



def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))


def foldF (step s l : Fm) : Fm := app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))


def foldW (f : Tree → Tree → List (A × Tree)) : List Tree → Tree → List (A × Tree)
  | [], σ => [(1, σ)]
  | x :: xs, σ => bindW (f x σ) (foldW f xs)

theorem foldB_does {step : Fm} {f : Tree → Tree → List (A × Tree)} {Inv : List Tree → Tree → Prop} {d : Tree → ℕ}
    {xs : List Tree} (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → Does θ step (.cons x σ) (f x σ) (d x) ∧
      ∀ q ∈ f x σ, Inv ys q.2) {σ : Tree} (hσ : Inv xs σ) :
    Does θ (foldB step) (.cons (foldB step).code (.cons σ (listT xs))) (foldW f xs σ)
      ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing σ with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs σ List.mem_cons_self hσ
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons σ (listT (x :: xs)))) (f x σ) (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd
      (Does.cons e1 (Gives.id (.cons (foldB step).code (.cons σ (listT (x :: xs))))).tl.tl.tl)
    have e3 := Does.runW (R := fun o => foldW f xs o.tl.hd) (e := (xs.map fun x => d x + 30).sum + 10)
      (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd e2 (by
      intro q hq
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      show Does θ (Fm.ofTree (foldB step).code) (.cons (foldB step).code (.cons q2.2 (listT xs))) _ _
      rw [Fm.ofTree_code]
      exact ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h2 q2 hq2))
    refine ((Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e3).congr ?_ fun φ => ?_).mono ?_
    · intro p hp
      obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      exact ⟨_, mem_bindW_of hq2 hr, h3.symm⟩
    · rw [foldW, wsum_bindW, wsum_bindW]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      simp only [wsum, List.map_map, one_mul, mul_one, flatMap_single, Function.comp_def, hd_cons, tl_cons]
    · simp only [List.map_cons, List.sum_cons]
      omega

theorem foldF_does {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {f : Tree → Tree → List (A × Tree)}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Does θ step (.cons x σ) (f x σ) (d x) ∧ ∀ q ∈ f x σ, Inv ys q.2) (hσ : Inv xs σ) :
    Does θ (foldF step s l) x (foldW f xs σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) (foldB step).code x) (Gives.cons hs hl)
  have h2 := Does.app (p := (foldB step).code) (R := fun _ => foldW f xs σ) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact foldB_does h hσ)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

theorem foldW_det (g : Tree → Tree → Tree) (xs : List Tree) (σ : Tree) :
    foldW (A := A) (fun x σ => [(1, g x σ)]) xs σ = [(1, xs.foldl (fun σ x => g x σ) σ)] := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih => simp [foldW, bindW, ih]


theorem foldF_gives {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {g : Tree → Tree → Tree}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Gives θ step (.cons x σ) (g x σ) (d x) ∧ Inv ys (g x σ)) (hσ : Inv xs σ) :
    Gives θ (foldF step s l) x (xs.foldl (fun σ x => g x σ) σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldF_does (f := fun x σ => [(1, g x σ)]) hs hl (fun x ys σ hx hσ => by
    obtain ⟨h1, h2⟩ := h x ys σ hx hσ
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) hσ
  rwa [foldW_det] at this


theorem foldl_rev (xs : List Tree) (ys : List Tree) :
    xs.foldl (fun σ x => Tree.cons x σ) (listT ys) = listT (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, show Tree.cons x (listT ys) = listT (x :: ys) from rfl, ih]
    simp

theorem rev_gives {s l : Fm} {x : Tree} {cs cl : ℕ} {xs ys : List Tree} (hs : Gives θ s x (listT ys) cs)
    (hl : Gives θ l x (listT xs) cl) :
    Gives θ (foldF .id s l) x (listT (xs.reverse ++ ys)) (cs + cl + xs.length * 31 + 20) := by
  have := foldF_gives (step := .id) (g := fun x σ => .cons x σ) (Inv := fun _ _ => True) (d := fun _ => 1) hs hl
    (fun x _ σ _ _ => ⟨Gives.id _, trivial⟩) trivial
  rw [foldl_rev] at this
  simpa using this


def appF (a b : Fm) : Fm := foldF .id b (foldF .id (.quote .nil) a)

theorem appF_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {xs ys : List Tree} (ha : Gives θ a x (listT xs) ca)
    (hb : Gives θ b x (listT ys) cb) :
    Gives θ (appF a b) x (listT (xs ++ ys)) (ca + cb + xs.length * 62 + 41) := by
  have h1 := rev_gives (Gives.quote (θ := θ) (listT []) x) ha
  rw [List.append_nil] at h1
  have h2 := rev_gives hb h1
  rw [List.reverse_reverse, List.length_reverse] at h2
  exact h2.mono (by omega)

end Fold

section Map



def mapB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
    (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.tl .id)) (.tl (.tl (.tl .id))))))) (.quote .nil)


def mapF (step e l : Fm) : Fm := app (mapB step).code (.cons (.quote (mapB step).code) (.cons e l))

theorem mapB_gives {step : Fm} {e : Tree} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapB step) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
      ((xs.map fun x => d x + 40).sum + 10) := by
  induction xs with
  | nil => exact ((Gives.id _).tl.tl.ite_false (Gives.quote _ _)).mono (by simp)
  | cons x xs ih =>
    have e1 : Gives θ (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
        (.cons (mapB step).code (.cons e (listT (x :: xs)))) (g x) (8 + d x + 2) :=
      Gives.lett (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd) (h x List.mem_cons_self)
    have ih' : Gives θ (Fm.ofTree (mapB step).code) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
        ((xs.map fun x => d x + 40).sum + 10) := by
      rw [Fm.ofTree_code]
      exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e2 := Gives.run (Gives.id (θ := θ) (.cons (mapB step).code (.cons e (listT (x :: xs))))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.tl)) ih'
    refine (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) (Gives.cons e1 e2)).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem mapF_gives {step ef l : Fm} {x e : Tree} {ce cl : ℕ} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (he : Gives θ ef x e ce) (hl : Gives θ l x (listT xs) cl) (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapF step ef l) x (listT (xs.map g)) (ce + cl + (xs.map fun x => d x + 40).sum + 20) := by
  refine (Gives.app (p := (mapB step).code) (Gives.cons (Gives.quote _ _) (Gives.cons he hl)) (by
    rw [Fm.ofTree_code]
    exact mapB_gives h)).mono (by omega)

end Map

section Eq


def eqB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.tl .id))
    (.ite (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id))) (.hd (.tl (.tl .id))))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl .id))))))
      (.quote .nil))
    (.quote .nil))
  (.ite (.tl (.tl .id)) (.quote .nil) (.quote one))


def eqF (a b : Fm) : Fm := app eqB.code (.cons (.quote eqB.code) (.cons a b))

theorem eqB_gives (a b : Tree) : Gives θ eqB (.cons eqB.code (.cons a b)) (bit (decide (a = b))) (60 * a.size) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_false (Gives.quote one _))).mono ?_
      simp [size]
    | cons b1 b2 =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_true (by simp) (Gives.quote .nil _))).mono ?_
      simp [size]
  | cons a1 a2 ih1 ih2 =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_false (Gives.quote .nil _))).mono ?_
      simp only [size]
      omega
    | cons b1 b2 =>
      have h1 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a1 b1)) (bit (decide (a1 = b1))) (60 * a1.size) := by
        rw [Fm.ofTree_code]; exact ih1 b1
      have h2 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a2 b2)) (bit (decide (a2 = b2))) (60 * a2.size) := by
        rw [Fm.ofTree_code]; exact ih2 b2
      have r1 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.hd (Gives.id _).tl.tl.hd)) h1
      have r2 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl)) h2
      by_cases hab : a1 = b1
      · have hb : bit (decide (a1 = b1)) ≠ .nil := by simp [hab, bit, one]
        have e : decide (Tree.cons a1 a2 = Tree.cons b1 b2) = decide (a2 = b2) := by simp [hab]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_true r1 hb r2))).mono ?_
        simp only [size]
        omega
      · have hb : bit (decide (a1 = b1)) = .nil := by simp [hab, bit]
        rw [hb] at r1
        have e : bit (decide (Tree.cons a1 a2 = Tree.cons b1 b2)) = .nil := by simp [hab, bit]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_false r1 (Gives.quote .nil _)))).mono ?_
        simp only [size]
        omega

theorem eqF_gives {a b : Fm} {x u v : Tree} {ca cb : ℕ} (ha : Gives θ a x u ca) (hb : Gives θ b x v cb) :
    Gives θ (eqF a b) x (bit (decide (u = v))) (ca + cb + 60 * u.size + 10) := by
  refine (Gives.app (p := eqB.code) (Gives.cons (Gives.quote _ _) (Gives.cons ha hb)) (by
    rw [Fm.ofTree_code]
    exact eqB_gives u v)).mono (by omega)

end Eq

section Choice


def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail


def pickF (l : Fm) : Fm := app pickB.code (.cons (.quote pickB.code) l)

theorem pickB_does (xs : List Tree) :
    Does θ pickB (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
  induction xs with
  | nil => exact (Does.ite_false (Gives.id _).tl (Does.fail _)).mono (by simp)
  | cons x xs ih =>
    have ih' : Does θ (Fm.ofTree pickB.code) (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
      rw [Fm.ofTree_code]; exact ih
    have r := Does.run (Gives.id (θ := θ) (.cons pickB.code (listT (x :: xs)))).hd
      (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) ih'
    refine (Does.ite_true (Gives.id _).tl (by simp [listT]) (Does.either (Gives.id _).tl.hd r)).mono ?_
    simp only [List.length_cons]
    omega

theorem pickF_does {l : Fm} {x : Tree} {cl : ℕ} {xs : List Tree} (hl : Gives θ l x (listT xs) cl) :
    Does θ (pickF l) x (xs.map fun x => (1, x)) (cl + 20 * xs.length + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) pickB.code x) hl
  have h2 := Does.app (p := pickB.code) (R := fun _ => xs.map fun x => ((1 : A), x)) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact pickB_does xs)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

end Choice

section Tries


def tget : List Bool → Tree → Tree
  | [], t => t.hd
  | true :: p, t => tget p t.tl.tl
  | false :: p, t => tget p t.tl.hd


def tset : List Bool → Tree → Tree → Tree
  | [], v, t => .cons v t.tl
  | true :: p, v, t => .cons t.hd (.cons t.tl.hd (tset p v t.tl.tl))
  | false :: p, v, t => .cons t.hd (.cons (tset p v t.tl.hd) t.tl.tl)

theorem tget_nil (p : List Bool) : tget p .nil = .nil := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

theorem tget_tset (p p' : List Bool) (v t : Tree) : tget p (tset p' v t) = if p = p' then v else tget p t := by
  induction p' generalizing p t with
  | nil =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [tset, tget]
  | cons b' p' ih =>
    cases p with
    | nil => cases b' <;> simp [tset, tget]
    | cons b p =>
      cases b <;> cases b' <;> simp [tset, tget, ih]


def getB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl (.tl .id)))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.hd (.tl (.tl (.tl .id))))))))
  (.hd (.tl (.tl .id)))


def getF (p t : Fm) : Fm := app getB.code (.cons (.quote getB.code) (.cons p t))

theorem getB_gives (p : Tree) (t : Tree) :
    Gives θ getB (.cons getB.code (.cons p t)) (tget p.path t) (30 * p.len + 10) := by
  induction p generalizing t with
  | nil => exact ((Gives.id _).tl.hd.ite_false (Gives.id _).tl.tl.hd).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.hd)) (tget p.path t.tl.hd)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons .nil p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.hd)) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd r)).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.tl)) (tget p.path t.tl.tl)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons a p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.tl)) h1
      have e : tget (Tree.cons a p).path t = tget p.path t.tl.tl := by simp [path, ha, tget]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha) r)).mono ?_
      simp only [len]
      omega

theorem getF_gives {pf tf : Fm} {x p t : Tree} {cp ct : ℕ} (hp : Gives θ pf x p cp) (ht : Gives θ tf x t ct) :
    Gives θ (getF pf tf) x (tget p.path t) (cp + ct + 30 * p.len + 20) := by
  refine (Gives.app (p := getB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp ht)) (by
    rw [Fm.ofTree_code]
    exact getB_gives p t)).mono (by omega)


def setB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.tl (.tl (.tl (.tl (.tl .id)))))))))))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.hd (.tl (.tl (.tl (.tl .id)))))))))
      (.tl (.tl (.tl (.tl (.tl .id))))))))
  (.cons (.hd (.tl (.tl .id))) (.tl (.tl (.tl (.tl .id)))))


def setF (p v t : Fm) : Fm := app setB.code (.cons (.quote setB.code) (.cons p (.cons v t)))

theorem setB_gives (p v t : Tree) :
    Gives θ setB (.cons setB.code (.cons p (.cons v t))) (tset p.path v t) (60 * p.len + 20) := by
  induction p generalizing t with
  | nil =>
    exact ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.tl.tl.tl)).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.hd))) (tset p.path v t.tl.hd)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons .nil p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.hd))) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons r (Gives.id _).tl.tl.tl.tl.tl)))).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.tl))) (tset p.path v t.tl.tl)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons a p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.tl))) h1
      have e : tset (Tree.cons a p).path v t = .cons t.hd (.cons t.tl.hd (tset p.path v t.tl.tl)) := by
        simp [path, ha, tset]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha)
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons (Gives.id _).tl.tl.tl.tl.hd r)))).mono ?_
      simp only [len]
      omega

theorem setF_gives {pf vf tf : Fm} {x p v t : Tree} {cp cv ct : ℕ} (hp : Gives θ pf x p cp) (hv : Gives θ vf x v cv)
    (ht : Gives θ tf x t ct) : Gives θ (setF pf vf tf) x (tset p.path v t) (cp + cv + ct + 60 * p.len + 30) := by
  refine (Gives.app (p := setB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp (Gives.cons hv ht))) (by
    rw [Fm.ofTree_code]
    exact setB_gives p v t)).mono (by omega)

end Tries

section Weights








def WE.fm : WE → Fm
  | zero => .fail
  | one => .quote .nil
  | nm p => .theta (.quote (ofBits p))
  | add a b => .ite .guess a.fm b.fm
  | mul a b => lett a.fm (lett b.fm (.quote .nil))


def WE.cost : WE → ℕ
  | zero => 1
  | one => 1
  | nm _ => 2
  | add a b => max a.cost b.cost + 2
  | mul a b => a.cost + b.cost + 10


theorem WE.does (e : WE) (x : Tree) : Does θ e.fm x [(e.val θ, .nil)] e.cost := by
  induction e generalizing x with
  | zero =>
    refine ((Does.fail x).congr (by simp) fun φ => ?_).mono (Nat.zero_le _)
    simp [WE.val]
  | one => exact Gives.quote .nil x
  | nm p =>
    have := Does.theta (Gives.quote (θ := θ) (ofBits p) x)
    rwa [path_ofBits] at this
  | add a b iha ihb =>
    refine (Does.either (iha x) (ihb x)).congr ?_ fun φ => ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · simp [WE.val, add_mul]
  | mul a b iha ihb =>
    have h1 := Does.lett (R := fun _ => [(b.val θ, .nil)]) (G := lett b.fm (.quote .nil)) (iha x)
      (d := b.cost + 1 + 2) (by
        intro q hq
        have := Does.lett (R := fun _ => [((1 : A), Tree.nil)]) (G := .quote .nil) (ihb q.2) (d := 1)
          fun p _ => Gives.quote .nil p.2
        simpa [bindW] using this)
    refine (h1.congr ?_ fun φ => ?_).mono ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [bindW, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at hq
      subst hq
      rfl
    · simp [bindW, WE.val]
    · simp only [WE.cost]
      omega


theorem WE.exists_of_adjoin {p₀ : List Bool} (h : θ p₀ = -1) {a : A} (ha : a ∈ Subring.closure (Set.range θ)) :
    ∃ e : WE, e.val θ = a := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨.nm p, rfl⟩
  | zero => exact ⟨.zero, rfl⟩
  | one => exact ⟨.one, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.add e f, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.mul e f, rfl⟩
  | neg x _ hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨.mul (.nm p₀) e, by simp [WE.val, h]⟩

end Weights

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Weighted lists of typed values

Programs of the tree machine whose values are encodings of typed values. `bindL`, `sumL`: weighted lists.
`Does.appT`, `Does.lettT`, `foldT`: composition and folds with typed values.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {α β γ : Type}

/-- First `l`, then `f`. -/
def bindL (l : List (A × α)) (f : α → List (A × β)) : List (A × β) :=
  l.flatMap fun p => (f p.2).map fun r => (p.1 * r.1, r.2)

/-- The weighted sum of a function. -/
def sumL (l : List (A × α)) (G : α → A) : A := (l.map fun p => p.1 * G p.2).sum

@[simp] theorem sumL_nil (G : α → A) : sumL ([] : List (A × α)) G = 0 := rfl

@[simp] theorem sumL_cons (p : A × α) (l : List (A × α)) (G : α → A) :
    sumL (p :: l) G = p.1 * G p.2 + sumL l G := by simp [sumL]

theorem sumL_append (l l' : List (A × α)) (G : α → A) : sumL (l ++ l') G = sumL l G + sumL l' G := by
  simp [sumL]

@[simp] theorem sumL_single (a : α) (G : α → A) : sumL [((1 : A), a)] G = G a := by simp [sumL]

theorem sumL_map_mul (c : A) (l : List (A × α)) (G : α → A) :
    sumL (l.map fun r => (c * r.1, r.2)) G = c * sumL l G := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, sumL_cons, ih]; ring

theorem sumL_bindL (l : List (A × α)) (f : α → List (A × β)) (G : β → A) :
    sumL (bindL l f) G = sumL l fun a => sumL (f a) G := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [sumL_cons, ← ih, bindL, List.flatMap_cons, sumL_append, sumL_map_mul]
    rfl

theorem sumL_congr {l : List (A × α)} {G G' : α → A} (h : ∀ p ∈ l, G p.2 = G' p.2) : sumL l G = sumL l G' := by
  unfold sumL
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem sumL_map (l : List (A × α)) (e : α → β) (G : β → A) :
    sumL (l.map (Prod.map id e)) G = sumL l fun a => G (e a) := by
  unfold sumL
  rw [List.map_map]
  rfl

theorem wsum_eq_sumL (Q : List (A × Tree)) (φ : Tree → A) : wsum Q φ = sumL Q φ := rfl

theorem mem_bindL {l : List (A × α)} {f : α → List (A × β)} {p : A × β} (h : p ∈ bindL l f) :
    ∃ a ∈ l, ∃ r ∈ f a.2, p.2 = r.2 := by
  unfold bindL at h
  rw [List.mem_flatMap] at h
  obtain ⟨a, ha, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨a, ha, r, hr, rfl⟩

theorem mem_bindL_of {l : List (A × α)} {f : α → List (A × β)} {a : A × α} {r : A × β} (ha : a ∈ l)
    (hr : r ∈ f a.2) : (a.1 * r.1, r.2) ∈ bindL l f :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨r, hr, rfl⟩⟩

theorem bindL_single (a : α) (f : α → List (A × β)) : bindL [((1 : A), a)] f = f a := by
  simp [bindL]

theorem bindL_assoc (l : List (A × α)) (f : α → List (A × β)) (g : β → List (A × γ)) :
    bindL (bindL l f) g = bindL l fun a => bindL (f a) g := by
  simp only [bindL, List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, mul_assoc]

theorem bindL_pure (l : List α) (g : α → β) (f : β → List (A × γ)) :
    bindL (l.map fun t => ((1 : A), g t)) f = l.flatMap fun t => f (g t) := by
  simp only [bindL, List.flatMap_map, one_mul, List.map_id']

/-- The weighted sums are determined by the program. -/
theorem _root_.NS1.Does.wsum_unique {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c d : ℕ} (h : Does θ F x Q c)
    (h' : Does θ F x Q' d) (φ : Tree → A) : wsum Q φ = wsum Q' φ := by
  rw [← h.evl.2 φ, ← h'.evl.2 φ]

/-- Replace the list. -/
theorem _root_.NS1.Does.replace {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c : ℕ} (h : Does θ F x Q c) (hQ : Q = Q') :
    Does θ F x Q' c := hQ ▸ h

/-- Apply a fixed program to typed values. -/
theorem _root_.NS1.Does.appT {F : Fm} {x p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d : ℕ}
    (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
    Does θ (app p F) x (bindL l f) (c + d + 2) := by
  classical
  let R : Tree → List (A × Tree) := fun t => if h : ∃ b ∈ l, enc b.2 = t then f h.choose.2 else []
  have hR : ∀ b ∈ l, ∃ b' ∈ l, R (enc b.2) = f b'.2 ∧ enc b'.2 = enc b.2 := by
    intro b hb
    have h : ∃ b' ∈ l, enc b'.2 = enc b.2 := ⟨b, hb, rfl⟩
    exact ⟨h.choose, h.choose_spec.1, dif_pos h, h.choose_spec.2⟩
  have h1 := Does.app (p := p) (R := R) (d := d) hF (by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    show Does θ (Fm.ofTree p) (enc b.2) (R (enc b.2)) d
    rw [e1, ← e2]
    exact hG b' hb')
  refine h1.congr ?_ fun φ => ?_
  · intro z hz
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    have hr' : r ∈ f b'.2 := by rw [← e1]; exact hr
    exact ⟨_, mem_bindL_of hb' hr', h3.symm⟩
  · rw [wsum_bindW, wsum_eq_sumL, wsum_eq_sumL, sumL_bindL, sumL_map]
    refine sumL_congr fun b hb => ?_
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    rw [e1]
    have h5 := hG b' hb'
    rw [e2] at h5
    exact Does.wsum_unique h5 (hG b hb) φ

/-- `let` with typed values. -/
theorem _root_.NS1.Does.lettT {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d : ℕ}
    (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ G (enc b.2) (f b.2) d) :
    Does θ (lett F G) x (bindL l f) (c + d + 2) :=
  Does.appT (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem bindL_map (l : List (A × α)) (f : α → List (A × β)) (e : β → γ) :
    bindL l (fun a => (f a).map (Prod.map id e)) = (bindL l f).map (Prod.map id e) := by
  simp only [bindL, List.map_flatMap, List.map_map]
  rfl

/-- `let` with typed values and typed results. -/
theorem _root_.NS1.Does.lettE {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {enc' : γ → Tree}
    {f : β → List (A × γ)} {c d : ℕ} (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) ((f b.2).map (Prod.map id enc')) d) :
    Does θ (lett F G) x ((bindL l f).map (Prod.map id enc')) (c + d + 2) := by
  rw [← bindL_map]
  exact Does.lettT hF hG

/-- The first of two formulas has the empty value: go on with the second one. -/
theorem _root_.NS1.Does.ite_nil {F G H : Fm} {x : Tree} {a : A} {Q : List (A × Tree)} {c d : ℕ} (hF : Does θ F x [(a, .nil)] c)
    (hH : Does θ H x Q d) : Does θ (.ite F G H) x (Q.map fun r => (a * r.1, r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, (a * q.1, q.2), List.mem_map.2 ⟨q, hq, rfl⟩, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp only [wsum_cons, wsum_nil, add_zero]
    exact (sumL_map_mul a Q φ).symm

/-- Apply a program that is a value to typed values. -/
theorem _root_.NS1.Does.runT {F G : Fm} {x p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x (l.map (Prod.map id enc)) d)
    (h : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) e) : Does θ (.run F G) x (bindL l f) (c + d + e + 1) := by
  classical
  let R : Tree → List (A × Tree) := fun t => if h : ∃ b ∈ l, enc b.2 = t then f h.choose.2 else []
  have hR : ∀ b ∈ l, ∃ b' ∈ l, R (enc b.2) = f b'.2 ∧ enc b'.2 = enc b.2 := by
    intro b hb
    have h : ∃ b' ∈ l, enc b'.2 = enc b.2 := ⟨b, hb, rfl⟩
    exact ⟨h.choose, h.choose_spec.1, dif_pos h, h.choose_spec.2⟩
  have h1 := Does.runW (p := p) (R := R) (e := e) hF hG (by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    show Does θ (Fm.ofTree p) (enc b.2) (R (enc b.2)) e
    rw [e1, ← e2]
    exact h b' hb')
  refine h1.congr ?_ fun φ => ?_
  · intro z hz
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    have hr' : r ∈ f b'.2 := by rw [← e1]; exact hr
    exact ⟨_, mem_bindL_of hb' hr', h3.symm⟩
  · rw [wsum_bindW, wsum_eq_sumL, wsum_eq_sumL, sumL_bindL, sumL_map]
    refine sumL_congr fun b hb => ?_
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    rw [e1]
    have h5 := h b' hb'
    rw [e2] at h5
    exact Does.wsum_unique h5 (h b hb) φ

/-- `let`, with the argument kept, typed values. -/
theorem _root_.NS1.Does.letkT {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)}
    {c d : ℕ} (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ G (.cons x (enc b.2)) (f b.2) d) :
    Does θ (lett (.cons .id F) G) x (bindL l f) (c + d + 4) := by
  have h1 : Does θ (.cons .id F) x (l.map (Prod.map id fun b => .cons x (enc b))) (1 + c + 1) := by
    refine (Does.cons (Gives.id (θ := θ) x) hF).replace ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
    rfl
  exact (Does.lettT h1 hG).mono (by omega)

section Fold

variable {ε : Type}

/-- The weighted list of a fold. -/
def foldL (f : ε → β → List (A × β)) : List ε → β → List (A × β)
  | [], s => [(1, s)]
  | x :: xs, s => bindL (f x s) (foldL f xs)

theorem foldB_doesT {step : Fm} {encE : ε → Tree} {enc : β → Tree} {f : ε → β → List (A × β)}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧ ∀ q ∈ f x s, Inv ys q.2)
    {s : β} (hs : Inv xs s) :
    Does θ (foldB step) (.cons (foldB step).code (.cons (enc s) (listT (xs.map encE))))
      ((foldL f xs s).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing s with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs s List.mem_cons_self hs
    rw [List.map_cons]
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE)))) ((f x s).map (Prod.map id enc))
        (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd
      (Does.cons e1 (Gives.id (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).tl.tl.tl)
    have e3 : Does θ (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.tl (.tl (.tl .id))))) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))
        ((f x s).map (Prod.map id fun s' => .cons (foldB step).code (.cons (enc s') (listT (xs.map encE)))))
        (8 + d x + 2 + 8) := by
      refine (e2.replace ?_).mono (by omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, one_mul, mul_one,
        List.map_map, flatMap_single]
      rfl
    -- apply the program to the new state
    have hR : ∀ b ∈ f x s, Does θ (Fm.ofTree (foldB step).code)
        (.cons (foldB step).code (.cons (enc b.2) (listT (xs.map encE))))
        ((foldL f xs b.2).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
      intro b hb
      rw [Fm.ofTree_code]
      exact ih (fun y ys s hy => h y ys s (List.mem_cons_of_mem _ hy)) (h2 b hb)
    have e4 := Does.runT (f := fun s' => (foldL f xs s').map (Prod.map id enc))
      (Gives.id (θ := θ) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd e3 hR
    rw [bindL_map] at e4
    refine (Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e4).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A fold with a typed state. -/
theorem foldT {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree} {f : ε → β → List (A × β)}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ} {s₀ : β} (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧ ∀ q ∈ f x s, Inv ys q.2)
    (h0 : Inv xs s₀) : Does θ (foldF step s l) x ((foldL f xs s₀).map (Prod.map id enc))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) (foldB step).code x) (Gives.cons hs hl)
  have h2 := Does.appT (p := (foldB step).code) (l := [((1 : A), ())])
    (enc := fun _ => .cons (foldB step).code (.cons (enc s₀) (listT (xs.map encE))))
    (f := fun _ => (foldL f xs s₀).map (Prod.map id enc)) h1 (fun b _ => by
      rw [Fm.ofTree_code]
      exact foldB_doesT h h0)
  rw [bindL_single] at h2
  exact h2.mono (by omega)

theorem foldL_det (g : ε → β → β) (xs : List ε) (s : β) :
    foldL (A := A) (fun x s => [(1, g x s)]) xs s = [(1, xs.foldl (fun s x => g x s) s)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [foldL, bindL_single, ih]; rfl

/-- A deterministic fold with a typed state. -/
theorem foldTG {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree} {g : ε → β → β}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ} {s₀ : β} (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Gives θ step (.cons (encE x) (enc s)) (enc (g x s)) (d x) ∧ Inv ys (g x s)) (h0 : Inv xs s₀) :
    Gives θ (foldF step s l) x (enc (xs.foldl (fun s x => g x s) s₀))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldT (θ := θ) (f := fun x s => [((1 : A), g x s)]) (enc := enc) hs hl (fun x ys s hx hs => by
    obtain ⟨h1, h2⟩ := h x ys s hx hs
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) h0
  rw [foldL_det] at this
  exact this

end Fold

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Finite transducers

A finite control reads one bit of each of finitely many input lists in every step, chooses an option (with a weight
in the ring generated by the constants) and pushes constant words on finitely many output lists. One formula runs a
transducer for any number of steps, at constant cost a step.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Bounds for finitely many formulas. -/
theorem exists_uniform {ι : Type*} [Finite ι] {P : ι → ℕ → Prop} (hm : ∀ i k k', k ≤ k' → P i k → P i k')
    (h : ∀ i, ∃ k, P i k) : ∃ k, ∀ i, P i k := by
  classical
  cases nonempty_fintype ι
  choose k hk using h
  exact ⟨Finset.univ.sup k, fun i => hm i _ _ (Finset.le_sup (Finset.mem_univ i)) (hk i)⟩

theorem listT_hd (l : List Tree) : (listT l).hd = l.getD 0 .nil := by cases l <;> rfl

theorem listT_tl (l : List Tree) : (listT l).tl = listT l.tail := by cases l <;> rfl

theorem ofBits_hd (w : List Bool) : (ofBits w).hd = bit (w.headD false) := by cases w <;> rfl

theorem ofBits_tl (w : List Bool) : (ofBits w).tl = ofBits w.tail := by cases w <;> rfl

theorem num_eq_listT (k : ℕ) : num k = listT (List.replicate k .nil) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [num, ih, List.replicate_succ, listT]

theorem num_eq_ofBits (k : ℕ) : num k = ofBits (List.replicate k false) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [num, ih, List.replicate_succ, ofBits]; rfl

/-- Element number `k` of a list. -/
def nthF : ℕ → Fm → Fm
  | 0, b => .hd b
  | k + 1, b => nthF k (.tl b)

theorem nthF_gives {b : Fm} {x : Tree} {l : List Tree} {c : ℕ} (k : ℕ) (h : Gives θ b x (listT l) c) :
    Gives θ (nthF k b) x (l.getD k .nil) (c + k + 1) := by
  induction k generalizing b l c with
  | zero => rw [← listT_hd]; exact h.hd
  | succ k ih =>
    have h1 := h.tl
    rw [listT_tl] at h1
    have h2 := ih h1
    have e : l.tail.getD k (.nil : Tree) = l.getD (k + 1) .nil := by cases l <;> simp
    rw [e] at h2
    exact h2.mono (by omega)

/-- A list of given values. -/
def mkList : List Fm → Fm
  | [] => .quote .nil
  | f :: fs => .cons f (mkList fs)

theorem mkList_gives {m : ℕ} {f : Fin m → Fm} {x : Tree} {o : Fin m → Tree} {c : ℕ}
    (h : ∀ i, Gives θ (f i) x (o i) c) : Gives θ (mkList (List.ofFn f)) x (listT (List.ofFn o)) (m * (c + 1) + 1) := by
  induction m with
  | zero => simpa [mkList, listT] using Gives.quote (θ := θ) (.nil : Tree) x
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, mkList, listT]
    refine (Gives.cons (h 0) (ih fun i => h i.succ)).mono ?_
    rw [Nat.add_mul]
    omega

/-- Push a constant word. -/
def pushF : List Tree → Fm → Fm
  | [], b => b
  | t :: ts, b => .cons (.quote t) (pushF ts b)

theorem pushF_gives {b : Fm} {x : Tree} {l : List Tree} {c : ℕ} (ts : List Tree) (h : Gives θ b x (listT l) c) :
    Gives θ (pushF ts b) x (listT (ts ++ l)) (c + 2 * ts.length) := by
  induction ts with
  | nil => exact h
  | cons t ts ih =>
    refine (Gives.cons (Gives.quote t x) ih).mono ?_
    rw [List.length_cons]
    omega

/-- Distinguish bits. -/
def dispF : (m : ℕ) → (Fin m → Fm) → ((Fin m → Bool) → Fm) → Fm
  | 0, _, k => k Fin.elim0
  | m + 1, g, k => .ite (g 0) (dispF m (fun i => g i.succ) fun v => k (Fin.cons true v))
      (dispF m (fun i => g i.succ) fun v => k (Fin.cons false v))

theorem dispF_does {m : ℕ} {g : Fin m → Fm} {k : (Fin m → Bool) → Fm} {x : Tree} {v : Fin m → Bool}
    {Q : List (A × Tree)} {c d : ℕ} (hg : ∀ i, Gives θ (g i) x (bit (v i)) c) (hk : Does θ (k v) x Q d) :
    Does θ (dispF m g k) x Q (m * (c + 1) + d) := by
  induction m with
  | zero =>
    have : v = Fin.elim0 := funext fun i => i.elim0
    rw [this] at hk
    exact hk.mono (by omega)
  | succ m ih =>
    have hv : Fin.cons (v 0) (fun i => v i.succ) = v := Fin.cons_self_tail v
    have h1 := ih (k := fun w => k (Fin.cons (v 0) w)) (v := fun i => v i.succ) (fun i => hg i.succ) (by rw [hv]; exact hk)
    have h0 := hg 0
    rw [dispF]
    cases hb : v 0 with
    | true =>
      rw [hb] at h0 h1
      refine (Does.ite_true h0 (by simp [bit, one]) h1).mono ?_
      rw [Nat.add_mul]
      omega
    | false =>
      rw [hb] at h0 h1
      refine (Does.ite_false h0 h1).mono ?_
      rw [Nat.add_mul]
      omega

/-- Distinguish numbers. -/
def switchF (t : Fm) : List Fm → Fm
  | [] => .fail
  | f :: fs => .ite t (switchF (.tl t) fs) f

theorem switchF_does {t : Fm} {fs : List Fm} {x : Tree} {j c d : ℕ} {Q : List (A × Tree)}
    (ht : Gives θ t x (num j) c) {f : Fm} (hf : fs[j]? = some f) (h : Does θ f x Q d) :
    Does θ (switchF t fs) x Q ((j + 1) * (c + j + 1) + d) := by
  induction fs generalizing t j c with
  | nil => simp at hf
  | cons f' fs ih =>
    rw [switchF]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      exact (Does.ite_false ht h).mono (by omega)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hf
      have h1 := ih (t := .tl t) (j := j) (c := c + 1) ht.tl hf
      refine (Does.ite_true ht (by simp [num]) h1).mono ?_
      have : (j + 1 + 1) * (c + (j + 1) + 1) = (j + 1) * (c + 1 + j + 1) + (c + (j + 1) + 1) := by ring
      omega

section transducer

variable {Λ : Type}

/-- An option of a transducer. -/
structure Opt (nC nO : ℕ) (Λ : Type) where
  /-- weight -/
  wt : WE
  /-- next control -/
  nxt : Fin nC
  /-- words that are pushed -/
  push : Fin nO → List Λ

variable {nC nI nO : ℕ}

/-- States of a transducer. -/
abbrev TSt (nC nI nO : ℕ) (Λ : Type) := Fin nC × (Fin nI → List Bool) × (Fin nO → List Λ)

variable (eL : Λ → Tree)

/-- A state as a tree. -/
def encS (s : TSt nC nI nO Λ) : Tree :=
  .cons (num s.1) (.cons (listT (List.ofFn fun i => ofBits (s.2.1 i)))
    (listT (List.ofFn fun j => listT ((s.2.2 j).map eL))))

/-- An option is carried out. -/
def Opt.app (o : Opt nC nO Λ) (s : TSt nC nI nO Λ) : TSt nC nI nO Λ :=
  (o.nxt, fun i => (s.2.1 i).tail, fun j => o.push j ++ s.2.2 j)

variable (θ) in
/-- One step. -/
def stepL (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (s : TSt nC nI nO Λ) : List (A × TSt nC nI nO Λ) :=
  (tab s.1 fun i => (s.2.1 i).headD false).map fun o => (o.wt.val θ, o.app s)

variable {eL}

theorem ins_gives {s : TSt nC nI nO Λ} (i : Fin nI) :
    Gives θ (nthF i (.hd (.tl .id))) (encS eL s) (ofBits (s.2.1 i)) (nI + 4) := by
  have h1 : Gives θ (.hd (.tl .id)) (encS eL s) (listT (List.ofFn fun i => ofBits (s.2.1 i))) 3 := (Gives.id _).tl.hd
  have h2 := nthF_gives i h1
  rw [List.getD_eq_getElem _ _ (by simp)] at h2
  simp only [List.getElem_ofFn, Fin.eta] at h2
  exact h2.mono (by have := i.2; omega)

theorem outs_gives {s : TSt nC nI nO Λ} (j : Fin nO) :
    Gives θ (nthF j (.tl (.tl .id))) (encS eL s) (listT ((s.2.2 j).map eL)) (nO + 4) := by
  have h1 : Gives θ (.tl (.tl .id)) (encS eL s) (listT (List.ofFn fun j => listT ((s.2.2 j).map eL))) 3 :=
    (Gives.id _).tl.tl
  have h2 := nthF_gives j h1
  rw [List.getD_eq_getElem _ _ (by simp)] at h2
  simp only [List.getElem_ofFn, Fin.eta] at h2
  exact h2.mono (by have := j.2; omega)

variable (eL)

theorem ex_opt (o : Opt nC nO Λ) : ∃ F κ, ∀ s : TSt nC nI nO Λ,
    Does θ F (encS eL s) [(o.wt.val θ, encS eL (o.app s))] κ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, ∀ j : Fin nO, 2 * (o.push j).length ≤ κ := exists_uniform
    (fun i k k' h h' => h'.trans h) fun j => ⟨_, le_rfl⟩
  refine ⟨.ite o.wt.fm .fail (.cons (.quote (num o.nxt)) (.cons
    (mkList (List.ofFn fun i : Fin nI => .tl (nthF i (.hd (.tl .id)))))
    (mkList (List.ofFn fun j : Fin nO => pushF ((o.push j).map eL) (nthF j (.tl (.tl .id))))))),
    o.wt.cost + (1 + (nI * (nI + 5 + 1) + 1 + (nO * (nO + 4 + κ + 1) + 1) + 1) + 1) + 1, fun s => ?_⟩
  have h1 : Gives θ (mkList (List.ofFn fun i : Fin nI => .tl (nthF i (.hd (.tl .id))))) (encS eL s)
      (listT (List.ofFn fun i => ofBits (s.2.1 i).tail)) _ := mkList_gives (c := nI + 5) fun i => by
    rw [← ofBits_tl]
    exact (ins_gives i).tl
  have h2 : Gives θ (mkList (List.ofFn fun j : Fin nO => pushF ((o.push j).map eL) (nthF j (.tl (.tl .id)))))
      (encS eL s) (listT (List.ofFn fun j => listT ((o.push j ++ s.2.2 j).map eL))) _ :=
    mkList_gives (c := nO + 4 + κ) fun j => by
      rw [List.map_append]
      exact (pushF_gives ((o.push j).map eL) (outs_gives j)).mono (by
        have := hκ j
        rw [List.length_map]
        omega)
  have h3 := Does.ite_nil (G := .fail) (o.wt.does (θ := θ) (encS eL s))
    (Gives.cons (Gives.quote (num o.nxt) (encS eL s)) (Gives.cons h1 h2))
  refine h3.replace ?_
  simp only [List.map_cons, List.map_nil, mul_one]
  rfl

theorem ex_opts (os : List (Opt nC nO Λ)) : ∃ F κ, ∀ s : TSt nC nI nO Λ,
    Does θ F (encS eL s) (os.map fun o => (o.wt.val θ, encS eL (o.app s))) κ := by
  induction os with
  | nil => exact ⟨.fail, 0, fun s => Does.fail _⟩
  | cons o os ih =>
    obtain ⟨F, κ, h⟩ := ih
    obtain ⟨G, κ', h'⟩ := ex_opt (θ := θ) (nI := nI) eL o
    exact ⟨.ite .guess G F, max κ' κ + 2, fun s => Does.either (h' s) (h s)⟩

/-- One formula for the steps of a transducer. -/
theorem ex_step (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) : ∃ F κ, ∀ s : TSt nC nI nO Λ,
    Does θ F (encS eL s) ((stepL θ tab s).map (Prod.map id (encS eL))) κ := by
  choose F κ h using fun z : Fin nC × (Fin nI → Bool) => ex_opts (θ := θ) (nI := nI) eL (tab z.1 z.2)
  obtain ⟨κ', hκ'⟩ : ∃ κ', ∀ z, κ z ≤ κ' := exists_uniform (fun i k k' h h' => h'.trans h) fun z => ⟨_, le_rfl⟩
  refine ⟨switchF (.hd .id) (List.ofFn fun c : Fin nC => dispF nI (fun i => .hd (nthF i (.hd (.tl .id)))) fun v => F (c, v)),
    (nC + 1) * (nC + 4) + (nI * (nI + 5 + 1) + κ'), fun s => ?_⟩
  have h1 := (h (s.1, fun i => (s.2.1 i).headD false) s).mono (hκ' _)
  have h2 := dispF_does (θ := θ) (x := encS eL s) (g := fun i => .hd (nthF i (.hd (.tl .id)))) (k := fun v => F (s.1, v))
    (v := fun i => (s.2.1 i).headD false) (c := nI + 5) (fun i => by
      rw [← ofBits_hd]
      exact (ins_gives i).hd) h1
  have h3 : Gives θ (.hd .id) (encS eL s) (num s.1) 2 := (Gives.id _).hd
  have h4 := switchF_does h3 (fs := List.ofFn fun c : Fin nC => dispF nI (fun i => .hd (nthF i (.hd (.tl .id))))
    fun v => F (c, v)) (f := dispF nI (fun i => .hd (nthF i (.hd (.tl .id)))) fun v => F (s.1, v)) (by
      rw [List.getElem?_eq_getElem (by simp)]
      simp) h2
  refine (h4.replace ?_).mono ?_
  · rw [stepL, List.map_map]
    rfl
  · have hs := s.1.2
    have : ((s.1 : ℕ) + 1) * (2 + s.1 + 1) ≤ (nC + 1) * (nC + 4) := Nat.mul_le_mul (by omega) (by omega)
    omega

variable (θ) in
/-- A run of `k` steps. -/
def runL (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (k : ℕ) (s : TSt nC nI nO Λ) :
    List (A × TSt nC nI nO Λ) :=
  foldL (fun (_ : Unit) s => stepL θ tab s) (List.replicate k ()) s

/-- **One formula runs a transducer.** -/
theorem ex_run (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) : ∃ F κ, ∀ (k : ℕ) (s : TSt nC nI nO Λ),
    Does θ F (.cons (num k) (encS eL s)) ((runL θ tab k s).map (Prod.map id (encS eL))) (κ * (k + 1)) := by
  obtain ⟨F, κ, h⟩ := ex_step (θ := θ) eL tab
  refine ⟨foldF (lett (.tl .id) F) (.tl .id) (.hd .id), κ + 60, fun k s => ?_⟩
  have h1 : Gives θ (.hd .id) (.cons (num k) (encS eL s)) (listT ((List.replicate k ()).map fun _ => .nil)) 2 := by
    rw [List.map_replicate, ← num_eq_listT]
    exact (Gives.id _).hd
  have h2 := foldT (θ := θ) (f := fun (_ : Unit) s => stepL θ tab s) (Inv := fun _ _ => True) (d := fun _ => κ + 4)
    (encE := fun _ => .nil) (step := lett (.tl .id) F) (s := .tl .id) (l := .hd .id) (x := .cons (num k) (encS eL s))
    (enc := encS eL) (s₀ := s)
    (Gives.id _).tl h1 (fun x ys s _ _ => ⟨(Does.of_gives (Gives.id _).tl (h s)).mono (by omega), fun _ _ => trivial⟩)
    trivial
  refine h2.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

theorem mem_foldL_induct {β ε : Type} {f : ε → β → List (A × β)} {Inv : ℕ → β → Prop} {xs : List ε} {s : β} {m : ℕ}
    (h : ∀ x ∈ xs, ∀ s m, Inv m s → ∀ q ∈ f x s, Inv (m + 1) q.2) (hs : Inv m s) :
    ∀ q ∈ foldL f xs s, Inv (m + xs.length) q.2 := by
  induction xs generalizing s m with
  | nil =>
    intro q hq
    rw [foldL, List.mem_singleton] at hq
    subst hq
    exact hs
  | cons x xs ih =>
    intro q hq
    obtain ⟨a, ha, r, hr, hqr⟩ := mem_bindL hq
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (h x List.mem_cons_self s m hs a ha) r hr
    rw [hqr, List.length_cons]
    convert this using 1
    omega

/-- Lengths of the output lists. -/
theorem exists_runL_length (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) : ∃ κ, ∀ (k : ℕ)
    (s : TSt nC nI nO Λ), (∀ j, s.2.2 j = []) → ∀ q ∈ runL θ tab k s, ∀ j, (q.2.2.2 j).length ≤ κ * k := by
  obtain ⟨κ, hκ⟩ : ∃ κ, ∀ z : Fin nC × (Fin nI → Bool), ∀ o ∈ tab z.1 z.2, ∀ j, (o.push j).length ≤ κ := by
    refine exists_uniform (fun z k k' h h' o ho j => (h' o ho j).trans h) fun z => ?_
    induction tab z.1 z.2 with
    | nil => exact ⟨0, by simp⟩
    | cons o os ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨k', hk'⟩ : ∃ k', ∀ j, (o.push j).length ≤ k' :=
        exists_uniform (fun j k k' h h' => h'.trans h) fun j => ⟨_, le_rfl⟩
      refine ⟨max k k', fun o' ho' j => ?_⟩
      rcases List.mem_cons.1 ho' with rfl | ho'
      · exact (hk' j).trans (le_max_right _ _)
      · exact (hk o' ho' j).trans (le_max_left _ _)
  refine ⟨κ, fun k s hs q hq j => ?_⟩
  have := mem_foldL_induct (f := fun (_ : Unit) s => stepL θ tab s) (xs := List.replicate k ())
    (Inv := fun m s => ∀ j, (s.2.2 j).length ≤ κ * m) (m := 0) (s := s) (fun x _ s m hm q hq j => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      have h1 := hκ (s.1, fun i => (s.2.1 i).headD false) o ho j
      have h2 := hm j
      show (o.push j ++ s.2.2 j).length ≤ _
      rw [List.length_append, Nat.mul_succ]
      omega) (fun j => by rw [hs j]; simp) q hq j
  simpa using this

end transducer

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Cutting the letters of a tape into segments

The letters come in reverse order; the segments are made from the last partner to the first one. Every segment is
closed by a separator and stands in front of the string that the partner has from the later tapes.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Flags: 0 = nothing is taken, 1 = something, 2 = anything. -/
def okFlag (f : ℕ) (tk : Bool) : Bool :=
  match f with
  | 0 => !tk
  | 1 => tk
  | _ => true

/-- All ways to cut the letters `rest`: `f`, `tk`, `cur` flag, `something has been taken`, string of the partner at hand;
`fs`, `as` flags and strings of the partners before; `out` strings of the partners behind. -/
def segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as : List (List Bool))
    (rest : List (List Bool)) (out : List (List Bool)) : List (List (List Bool)) :=
  (if okFlag f tk then
    match fs with
    | [] => if rest = [] then [cur :: out] else []
    | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)
  else []) ++
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out
termination_by fs.length + rest.length

/-- The state of the program. -/
def segS (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : Tree :=
  .cons (num f) (.cons (bit tk) (.cons (ofBits cur) (.cons (listT (fs.map num)) (.cons (listT (as.map ofBits))
    (.cons (listT (rest.map ofBits)) (listT (out.map ofBits)))))))

/-- Parts of the state, in the argument (this program, state). -/
def sgF : Fm := .hd (.tl .id)
/-- tk -/
def sgTk : Fm := .hd (.tl (.tl .id))
/-- cur -/
def sgCur : Fm := .hd (.tl (.tl (.tl .id)))
/-- fs -/
def sgFs : Fm := .hd (.tl (.tl (.tl (.tl .id))))
/-- as -/
def sgAs : Fm := .hd (.tl (.tl (.tl (.tl (.tl .id)))))
/-- rest -/
def sgRest : Fm := .hd (.tl (.tl (.tl (.tl (.tl (.tl .id))))))
/-- out -/
def sgOut : Fm := .tl (.tl (.tl (.tl (.tl (.tl (.tl .id))))))

/-- Concatenation of lists of bits. -/
theorem appB_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {v w : List Bool} (ha : Gives θ a x (ofBits v) ca)
    (hb : Gives θ b x (ofBits w) cb) : Gives θ (appF a b) x (ofBits (v ++ w)) (ca + cb + v.length * 62 + 41) := by
  rw [← listT_ofBits] at ha hb ⊢
  have := appF_gives ha hb
  rw [← List.map_append, List.length_map] at this
  exact this

/-- The next partner. -/
def segNext (sep : List Bool) : Fm := .cons (.hd .id) (.cons (.hd sgFs) (.cons (.quote .nil)
  (.cons (appF (.quote (ofBits sep)) (.hd sgAs)) (.cons (.tl sgFs) (.cons (.tl sgAs) (.cons sgRest
  (.cons sgCur sgOut)))))))

/-- Take a letter. -/
def segTake : Fm := .cons (.hd .id) (.cons sgF (.cons (.quote one) (.cons (appF (.hd sgRest) sgCur)
  (.cons sgFs (.cons sgAs (.cons (.tl sgRest) sgOut))))))

/-- Close a segment. -/
def segClose (sep : List Bool) : Fm := .ite sgFs (.run (.hd .id) (segNext sep)) (.ite sgRest .fail (.cons sgCur sgOut))

/-- The program. -/
def segB (sep : List Bool) : Fm := .ite .guess
  (.ite sgF (.ite (.tl sgF) (segClose sep) (.ite sgTk (segClose sep) .fail)) (.ite sgTk .fail (segClose sep)))
  (.ite sgRest (.run (.hd .id) segTake) .fail)

section parts

variable {p : Tree} {f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}

theorem sgF_gives : Gives θ sgF (.cons p (segS f tk cur fs as rest out)) (num f) 3 := (Gives.id _).tl.hd

theorem sgTk_gives : Gives θ sgTk (.cons p (segS f tk cur fs as rest out)) (bit tk) 4 := (Gives.id _).tl.tl.hd

theorem sgCur_gives : Gives θ sgCur (.cons p (segS f tk cur fs as rest out)) (ofBits cur) 5 :=
  (Gives.id _).tl.tl.tl.hd

theorem sgFs_gives : Gives θ sgFs (.cons p (segS f tk cur fs as rest out)) (listT (fs.map num)) 6 :=
  (Gives.id _).tl.tl.tl.tl.hd

theorem sgAs_gives : Gives θ sgAs (.cons p (segS f tk cur fs as rest out)) (listT (as.map ofBits)) 7 :=
  (Gives.id _).tl.tl.tl.tl.tl.hd

theorem sgRest_gives : Gives θ sgRest (.cons p (segS f tk cur fs as rest out)) (listT (rest.map ofBits)) 8 :=
  (Gives.id _).tl.tl.tl.tl.tl.tl.hd

theorem sgOut_gives : Gives θ sgOut (.cons p (segS f tk cur fs as rest out)) (listT (out.map ofBits)) 8 :=
  (Gives.id _).tl.tl.tl.tl.tl.tl.tl

end parts

theorem listB_hd (l : List (List Bool)) : (listT (l.map ofBits)).hd = ofBits (l.headD []) := by cases l <;> rfl

theorem listB_tl (l : List (List Bool)) : (listT (l.map ofBits)).tl = listT (l.tail.map ofBits) := by cases l <;> rfl

/-- The results of a program without weights. -/
abbrev encL (l : List (List (List Bool))) : List (A × Tree) := l.map fun l => ((1 : A), listT (l.map ofBits))

/-- What remains to do when a segment is closed. -/
def closeL (sep cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : List (List (List Bool)) :=
  match fs with
  | [] => if rest = [] then [cur :: out] else []
  | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)

/-- What remains to do when a letter is taken. -/
def takeL (sep : List Bool) (f : ℕ) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    List (List (List Bool)) :=
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out

theorem segL_eq (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    segL sep f tk cur fs as rest out =
      (if okFlag f tk then closeL sep cur fs as rest out else []) ++ takeL sep f cur fs as rest out := by
  rw [segL.eq_def]
  cases fs <;> cases rest <;> rfl

section step

variable {sep : List Bool} {c d f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}

theorem segClose_does (hsep : sep.length ≤ c) (h1 : ∀ f' fs', fs = f' :: fs' → Does θ (segB sep)
      (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
      (encL (segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out))) d) :
    Does θ (segClose sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (closeL sep cur fs as rest out)) (d + 62 * c + 200) := by
  cases fs with
  | nil =>
    cases rest with
    | nil =>
      have e : Gives θ (.cons sgCur sgOut) (.cons (segB sep).code (segS f tk cur [] as [] out))
          (listT ((cur :: out).map ofBits)) 20 := (Gives.cons sgCur_gives sgOut_gives).mono (by omega)
      exact (Does.ite_false sgFs_gives (Does.ite_false sgRest_gives e)).mono (by omega)
    | cons a r =>
      have hne : listT ((a :: r).map ofBits) ≠ .nil := by simp [listT]
      exact (Does.ite_false sgFs_gives (Does.ite_true sgRest_gives hne
        (Does.fail (.cons (segB sep).code (segS f tk cur [] as (a :: r) out))))).mono (by omega)
  | cons f' fs' =>
    have e1 : Gives θ (appF (.quote (ofBits sep)) (.hd sgAs)) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
        (ofBits (sep ++ as.headD [])) (1 + 8 + sep.length * 62 + 41) := by
      refine appB_gives (Gives.quote _ _) ?_
      rw [← listB_hd]
      exact sgAs_gives.hd
    have e2 : Gives θ (segNext sep) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
        (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
        (62 * c + 150) := by
      have eA : Gives θ (.tl sgAs) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
          (listT (as.tail.map ofBits)) 8 := by
        rw [← listB_tl]
        exact sgAs_gives.tl
      exact (Gives.cons (Gives.id _).hd (Gives.cons sgFs_gives.hd (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons sgFs_gives.tl (Gives.cons eA (Gives.cons sgRest_gives
          (Gives.cons sgCur_gives sgOut_gives)))))))).mono (by omega)
    have e3 := Does.run (Gives.id (θ := θ) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))).hd e2
      (show Does θ (Fm.ofTree (segB sep).code) _ _ _ by rw [Fm.ofTree_code]; exact h1 f' fs' rfl)
    have hne : listT ((f' :: fs').map num) ≠ .nil := by simp [listT]
    exact (Does.ite_true sgFs_gives hne e3).mono (by omega)

theorem segTake_does (hc : ∀ a ∈ rest, a.length ≤ c) (h2 : ∀ a r, rest = a :: r → Does θ (segB sep)
      (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (encL (segL sep f true (a ++ cur) fs as r out)) d) :
    Does θ (.ite sgRest (.run (.hd .id) segTake) .fail) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (takeL sep f cur fs as rest out)) (d + 62 * c + 200) := by
  cases rest with
  | nil =>
    exact (Does.ite_false sgRest_gives (Does.fail (.cons (segB sep).code (segS f tk cur fs as [] out)))).mono (by omega)
  | cons a r =>
    have ha := hc a List.mem_cons_self
    have e1 : Gives θ (appF (.hd sgRest) sgCur) (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))
        (ofBits (a ++ cur)) (9 + 5 + a.length * 62 + 41) := appB_gives sgRest_gives.hd sgCur_gives
    have e2 : Gives θ segTake (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))
        (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (62 * c + 150) := by
      refine (Gives.cons (Gives.id _).hd (Gives.cons sgF_gives (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons sgFs_gives (Gives.cons sgAs_gives (Gives.cons sgRest_gives.tl sgOut_gives))))))).mono ?_
      omega
    have e3 := Does.run (Gives.id (θ := θ) (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))).hd e2
      (show Does θ (Fm.ofTree (segB sep).code) _ _ _ by rw [Fm.ofTree_code]; exact h2 a r rfl)
    have hne : listT ((a :: r).map ofBits) ≠ .nil := by simp [listT]
    exact (Does.ite_true sgRest_gives hne e3).mono (by omega)

theorem seg_step (hsep : sep.length ≤ c) (hc : ∀ a ∈ rest, a.length ≤ c)
    (h1 : ∀ f' fs', fs = f' :: fs' → Does θ (segB sep)
      (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
      (encL (segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out))) d)
    (h2 : ∀ a r, rest = a :: r → Does θ (segB sep)
      (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (encL (segL sep f true (a ++ cur) fs as r out)) d) :
    Does θ (segB sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (segL sep f tk cur fs as rest out)) (d + (62 * c + 300)) := by
  have hcl := segClose_does (f := f) (tk := tk) hsep h1
  have htk := segTake_does (tk := tk) hc h2
  have hok : Does θ (.ite sgF (.ite (.tl sgF) (segClose sep) (.ite sgTk (segClose sep) .fail))
      (.ite sgTk .fail (segClose sep))) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (if okFlag f tk then closeL sep cur fs as rest out else [])) (d + 62 * c + 200 + 30) := by
    have hfail : Does θ .fail (.cons (segB sep).code (segS f tk cur fs as rest out)) (encL (A := A) []) 0 := Does.fail _
    match f, tk with
    | 0, false => exact (Does.ite_false sgF_gives (Does.ite_false sgTk_gives hcl)).mono (by omega)
    | 0, true => exact (Does.ite_false sgF_gives (Does.ite_true sgTk_gives (by simp [bit, one]) hfail)).mono (by omega)
    | 1, false => exact (Does.ite_true sgF_gives (by simp [num]) (Does.ite_false sgF_gives.tl
        (Does.ite_false sgTk_gives hfail))).mono (by omega)
    | 1, true => exact (Does.ite_true sgF_gives (by simp [num]) (Does.ite_false sgF_gives.tl
        (Does.ite_true sgTk_gives (by simp [bit, one]) hcl))).mono (by omega)
    | f + 2, tk =>
      have h2 : num (f + 2) ≠ .nil := by simp [num]
      have h3 : (num (f + 2)).tl ≠ .nil := by simp [num]
      rw [if_pos (show okFlag (f + 2) tk = true from rfl)]
      exact (Does.ite_true (H := .ite sgTk .fail (segClose sep)) sgF_gives h2 (Does.ite_true
        (H := .ite sgTk (segClose sep) .fail) sgF_gives.tl h3 hcl)).mono (by omega)
  refine ((Does.either hok htk).replace ?_).mono (by omega)
  rw [segL_eq]
  simp

end step

/-- **The program cuts.** -/
theorem segB_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (m : ℕ) (f : ℕ) (tk : Bool) (cur : List Bool)
    (fs : List ℕ) (as rest out : List (List Bool)) (hm : fs.length + rest.length ≤ m) (hc : ∀ a ∈ rest, a.length ≤ c) :
    Does θ (segB sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (segL sep f tk cur fs as rest out)) ((62 * c + 300) * (m + 1)) := by
  induction m generalizing f tk cur fs as rest out with
  | zero =>
    refine (seg_step (d := 0) hsep hc (fun f' fs' h => ?_) fun a r h => ?_).mono (by omega)
    · subst h
      simp at hm
    · subst h
      simp at hm
  | succ m ih =>
    refine (seg_step (d := (62 * c + 300) * (m + 1)) hsep hc (fun f' fs' h => ?_) fun a r h => ?_).mono
      (le_of_eq (by ring))
    · subst h
      exact ih f' false _ fs' as.tail rest (cur :: out) (by simp only [List.length_cons] at hm; omega) hc
    · subst h
      exact ih f true _ fs as r out (by simp only [List.length_cons] at hm; omega) fun b hb =>
        hc b (List.mem_cons_of_mem _ hb)

/-- All ways to cut the letters of a tape. -/
def segRow (sep : List Bool) (fl : List ℕ) (accs l : List (List Bool)) : List (List (List Bool)) :=
  match fl with
  | [] => []
  | f :: fs => segL sep f false (sep ++ accs.headD []) fs accs.tail l []

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sum over the ways to cut a word
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

theorem segL_eq' (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    segL sep f tk cur fs as rest out =
      (if okFlag f tk then closeL sep cur fs as rest out else []) ++
      match rest with
      | [] => []
      | a :: r => segL sep f true (a ++ cur) fs as r out := by
  rw [segL.eq_def]
  cases fs <;> cases rest <;> rfl

variable {A : Type} [CommRing A]

/-- The sum over the number of letters that are taken. -/
theorem sum_segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool))
    (G : List (List Bool) → A) : ((segL sep f tk cur fs as rest out).map G).sum =
      ∑ j ∈ range (rest.length + 1), if okFlag f (tk || decide (0 < j)) then
        ((closeL sep ((rest.take j).reverse.flatten ++ cur) fs as (rest.drop j) out).map G).sum else 0 := by
  induction rest generalizing tk cur with
  | nil =>
    rw [segL_eq']
    simp only [List.append_nil, List.length_nil, zero_add, range_one, sum_singleton, lt_self_iff_false,
      decide_false, Bool.or_false, List.take_nil, List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_nil]
    split_ifs <;> simp
  | cons a r ih =>
    rw [segL_eq', List.map_append, List.sum_append, sum_range_succ']
    simp only [ih, List.length_cons, lt_self_iff_false, decide_false, Bool.or_false, List.take_zero,
      List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
      List.reverse_cons, List.flatten_append, List.flatten_cons, List.append_nil, List.append_assoc, Bool.true_or,
      Nat.zero_lt_succ, decide_true, Bool.or_true]
    rw [add_comm]
    congr 1
    split_ifs <;> simp

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

theorem cat_snoc {m : ℕ} (X : Fin m → List Γ) (y : List Γ) :
    cat (Fin.snoc X y : Fin (m + 1) → List Γ) = cat X ++ y := by
  simp only [cat, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Cutting off the last segment. -/
theorem sum_cut {m : ℕ} (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (p : Fin (m + 1) → List Γ → Prop)
    [∀ b, DecidablePred (p b)] (H : (Fin (m + 1) → List Γ) → A) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter (fun X => cat X = l ∧ ∀ b, p b (X b)), H X =
      ∑ j ∈ range (l.length + 1), if p (Fin.last m) (l.drop (l.length - j)) then
        ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
          (fun X => cat X = l.take (l.length - j) ∧ ∀ b, p b.castSucc (X b)),
          H (Fin.snoc X (l.drop (l.length - j))) else 0 := by
  have hinit : ∀ X : Fin (m + 1) → List Γ, cat X = cat (Fin.init X) ++ X (Fin.last m) := by
    intro X
    conv_lhs => rw [← Fin.snoc_init_self X]
    rw [cat_snoc]
  have hdrop : ∀ X : Fin (m + 1) → List Γ, cat X = l →
      cat (Fin.init X) = l.take (l.length - (X (Fin.last m)).length) ∧
      X (Fin.last m) = l.drop (l.length - (X (Fin.last m)).length) := by
    intro X hX
    rw [hinit] at hX
    have h1 : l.length = (cat (Fin.init X)).length + (X (Fin.last m)).length := by rw [← hX, List.length_append]
    have h2 : l.length - (X (Fin.last m)).length = (cat (Fin.init X)).length := by omega
    rw [h2, ← hX]
    simp
  rw [← sum_fiberwise_of_maps_to (s := (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
    (fun X => cat X = l ∧ ∀ b, p b (X b))) (t := range (l.length + 1)) (g := fun X => (X (Fin.last m)).length)]
  · refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    split_ifs with hp
    · refine sum_nbij' (i := fun X => Fin.init X) (j := fun X => Fin.snoc X (l.drop (l.length - j))) ?_ ?_ ?_ ?_ ?_
      · intro X hX
        simp only [mem_filter, Fintype.mem_piFinset] at hX ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hX
        refine ⟨fun b => h1 _, ?_, fun b => h3 _⟩
        rw [← h4]
        exact (hdrop X h2).1
      · intro X hX
        simp only [mem_filter, Fintype.mem_piFinset] at hX ⊢
        obtain ⟨h1, h2, h3⟩ := hX
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · rw [Fin.snoc_last, mem_wordsLe, List.length_drop]
            omega
          · rw [Fin.snoc_castSucc]
            exact h1 b
        · rw [cat_snoc, h2, List.take_append_drop]
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · rw [Fin.snoc_last]
            exact hp
          · rw [Fin.snoc_castSucc]
            exact h3 b
        · rw [Fin.snoc_last, List.length_drop]
          omega
      · intro X hX
        simp only [mem_filter] at hX
        obtain ⟨⟨-, h2, -⟩, h4⟩ := hX
        have := (hdrop X h2).2
        rw [h4] at this
        rw [← this, Fin.snoc_init_self]
      · intro X _
        exact Fin.init_snoc _ _
      · intro X hX
        simp only [mem_filter] at hX
        obtain ⟨⟨-, h2, -⟩, h4⟩ := hX
        have := (hdrop X h2).2
        rw [h4] at this
        rw [← this, Fin.snoc_init_self]
    · refine sum_eq_zero fun X hX => ?_
      simp only [mem_filter] at hX
      obtain ⟨⟨-, h2, h3⟩, h4⟩ := hX
      exfalso
      apply hp
      have := (hdrop X h2).2
      rw [h4] at this
      rw [← this]
      exact h3 _
  · intro X hX
    simp only [mem_filter] at hX
    rw [mem_range, ← hX.2.1, hinit, List.length_append]
    omega

theorem drop_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    (l.map bits).reverse.drop j = ((l.take (l.length - j)).map bits).reverse := by
  rw [List.drop_reverse, List.length_map, List.map_take]

theorem take_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    ((l.map bits).reverse.take j).reverse.flatten = (l.drop (l.length - j)).flatMap bits := by
  rw [List.take_reverse, List.length_map, List.reverse_reverse, ← List.map_drop, List.flatMap_def]

theorem ofFn_rev {α : Type} {m : ℕ} (f : Fin (m + 1) → α) :
    (List.ofFn f).reverse = f (Fin.last m) :: (List.ofFn fun b => f b.castSucc).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem sum_segL_start (sep : List Bool) (bits : Γ → List Bool) (T : ℕ) {m : ℕ} (fl : Fin (m + 1) → ℕ)
    (acc : Fin (m + 1) → List Bool) (l : List Γ) (hT : l.length ≤ T) (out : List (List Bool))
    (G : List (List Bool) → A) :
    ((segL sep (fl (Fin.last m)) false (sep ++ acc (Fin.last m)) (List.ofFn fun b => fl b.castSucc).reverse
      (List.ofFn fun b => acc b.castSucc).reverse (l.map bits).reverse out).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G ((List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) ++ out) := by
  induction m generalizing l out with
  | zero =>
    rw [sum_segL, sum_cut T l hT (fun b x => okFlag (fl b) (decide (x ≠ [])) = true), List.length_reverse,
      List.length_map]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
      apply decide_eq_decide.2
      rw [← List.length_pos_iff, List.length_drop]
      omega
    simp only [Bool.false_or, e1]
    refine if_congr Iff.rfl ?_ rfl
    rw [take_rev, drop_rev]
    simp only [List.ofFn_zero, List.reverse_nil, closeL]
    have e2 : ∀ X : Fin 0 → List Γ, cat X = [] := fun X => by simp [cat]
    by_cases h : l.take (l.length - j) = []
    · rw [if_pos (by rw [h]; rfl), Finset.sum_eq_single (fun b : Fin 0 => b.elim0)]
      · have e3 : ∀ (X : Fin 0 → List Γ) (y : List Γ), (Fin.snoc X y : Fin 1 → List Γ) 0 = y :=
          fun X y => Fin.snoc_last (α := fun _ => List Γ) y X
        simp [List.ofFn_succ, e3]
      · intro X _ hX
        exact absurd (Subsingleton.elim _ _) hX
      · intro hX
        exfalso
        apply hX
        rw [mem_filter, Fintype.mem_piFinset]
        exact ⟨fun b => b.elim0, by rw [e2, h], fun b => b.elim0⟩
    · rw [if_neg (by simpa using h), Finset.sum_eq_zero]
      · rfl
      · intro X hX
        simp only [mem_filter, e2] at hX
        exact absurd hX.2.1.symm h
  | succ m ih =>
    rw [sum_segL, sum_cut T l hT (fun b x => okFlag (fl b) (decide (x ≠ [])) = true), List.length_reverse,
      List.length_map]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
      apply decide_eq_decide.2
      rw [← List.length_pos_iff, List.length_drop]
      omega
    simp only [Bool.false_or, e1]
    refine if_congr Iff.rfl ?_ rfl
    rw [take_rev, drop_rev, ofFn_rev, ofFn_rev, closeL]
    have h := ih (fun b => fl b.castSucc) (fun b => acc b.castSucc) (l.take (l.length - j))
      ((List.length_take_le _ _).trans ((Nat.sub_le _ _).trans hT))
      (((l.drop (l.length - j)).flatMap bits ++ (sep ++ acc (Fin.last (m + 1)))) :: out)
    simp only [List.headD_cons, List.tail_cons]
    rw [h]
    refine sum_congr rfl fun X _ => ?_
    rw [List.ofFn_succ' (n := m + 1)]
    simp

/-- **The sum over the ways to cut a word.** -/
theorem sum_segRow' (sep : List Bool) {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (bits : Γ → List Bool) (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (G : List (List Bool) → A) :
    ((segRow sep (List.ofFn fl).reverse (List.ofFn acc).reverse (l.map bits).reverse).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G (List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := sum_segL_start sep bits T fl acc l hT [] G
  rw [ofFn_rev, ofFn_rev, segRow]
  simpa only [List.headD_cons, List.tail_cons, List.append_nil] using h

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Writing units: definitions
-/

namespace Nc.Grp

open NS1 NS1.Tree

/-- The first `ub` bits, filled with zeros. -/
def padTake (ub : ℕ) (r : List Bool) : List Bool := r.take ub ++ List.replicate (ub - r.length) false

/-- Write the units of a string (with its final 1) at the keys; fail if the number of keys is wrong. -/
def putL (ub : ℕ) : List (List Bool) → List Bool → Tree → List Tree
  | [], r, t => if r = [] then [t] else []
  | k :: ks, r, t => if r = [] then [] else putL ub ks (r.drop ub) (tset k (ofBits (padTake ub r)) t)

/-- Write contents at keys. -/
def putAll : List (List Bool) → (ℕ → List Bool) → Tree → Tree
  | [], _, t => t
  | k :: ks, u, t => putAll ks (fun i => u (i + 1)) (tset k (ofBits (u 0)) t)

/-- Write several strings. -/
def putsL (ub : ℕ) : List (List (List Bool)) → List (List Bool) → Tree → List Tree
  | [], _, t => [t]
  | ks :: kss, strs, t => (putL ub ks (strs.headD []) t).flatMap (putsL ub kss strs.tail)

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Writing units: programs
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Results without weights. -/
abbrev encT (l : List Tree) : List (A × Tree) := l.map fun t => ((1 : A), t)

theorem reverse_gives {l : Fm} {x : Tree} {c : ℕ} {w : List Bool} (h : Gives θ l x (ofBits w) c) (v : List Bool) :
    Gives θ (foldF .id (.quote (ofBits v)) l) x (ofBits (w.reverse ++ v)) (c + w.length * 31 + 21) := by
  rw [← listT_ofBits w] at h
  have := rev_gives (Gives.quote (θ := θ) (listT (v.map bit)) x) h
  rw [← List.map_reverse, ← List.map_append, List.length_map, listT_ofBits, listT_ofBits] at this
  exact this.mono (by omega)

/-- Take the bits of a unit: argument (rest, accumulator), yardstick `num ub`. -/
def unitStep : Fm := .cons (.tl (.hd (.tl .id))) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))

theorem replicate_append_cons (n : ℕ) (acc : List Bool) :
    List.replicate n false ++ false :: acc = false :: (List.replicate n false ++ acc) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem foldl_unit (ub : ℕ) (r acc : List Bool) :
    (List.replicate ub ()).foldl (fun (s : List Bool × List Bool) _ => (s.1.tail, s.1.headD false :: s.2)) (r, acc) =
      (r.drop ub, (padTake ub r).reverse ++ acc) := by
  induction ub generalizing r acc with
  | zero => simp [padTake]
  | succ ub ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    cases r with
    | nil => simp [padTake, List.replicate_succ, replicate_append_cons]
    | cons b r => simp [padTake]

theorem unit_gives {s y : Fm} {x : Tree} {cs cy ub : ℕ} {r : List Bool} (hs : Gives θ s x (ofBits r) cs)
    (hy : Gives θ y x (num ub) cy) :
    Gives θ (foldF unitStep (.cons s (.quote .nil)) y) x (.cons (ofBits (r.drop ub)) (ofBits (padTake ub r).reverse))
      (cs + cy + ub * 50 + 40) := by
  have h0 : Gives θ (.cons s (.quote .nil)) x (.cons (ofBits r) (ofBits [])) (cs + 1 + 1) :=
    Gives.cons hs (Gives.quote _ _)
  have hy' : Gives θ y x (listT ((List.replicate ub ()).map fun _ => .nil)) cy := by
    rw [List.map_replicate, ← num_eq_listT]
    exact hy
  have := foldTG (θ := θ) (encE := fun _ : Unit => (.nil : Tree))
    (enc := fun s : List Bool × List Bool => .cons (ofBits s.1) (ofBits s.2)) (s₀ := (r, []))
    (g := fun _ s => (s.1.tail, s.1.headD false :: s.2)) (Inv := fun _ _ => True) (d := fun _ => 20)
    (step := unitStep) h0 hy' (fun _ _ s _ _ => ⟨by
      have h1 : Gives θ (.tl (.hd (.tl .id))) (.cons .nil (.cons (ofBits s.1) (ofBits s.2))) (ofBits s.1.tail) 4 := by
        rw [← ofBits_tl]
        exact (Gives.id _).tl.hd.tl
      have h2 : Gives θ (.hd (.hd (.tl .id))) (.cons .nil (.cons (ofBits s.1) (ofBits s.2))) (bit (s.1.headD false)) 4 := by
        rw [← ofBits_hd]
        exact (Gives.id _).tl.hd.hd
      exact (Gives.cons h1 (Gives.cons h2 (Gives.id _).tl.tl)).mono (by omega), trivial⟩) trivial
  rw [foldl_unit, List.append_nil] at this
  refine this.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  omega

/-- Step of the writing program: argument (key, (yardstick, (rest, trie))). -/
def putStep : Fm := .ite (.hd (.tl (.tl .id)))
  (lett (.cons .id (foldF unitStep (.cons (.hd (.tl (.tl .id))) (.quote .nil)) (.hd (.tl .id))))
    (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id))
      (setF (.hd (.hd .id)) (foldF .id (.quote (ofBits [])) (.tl (.tl .id))) (.tl (.tl (.tl (.hd .id))))))))
  .fail

variable (A) in
/-- One key. -/
def putOne (ub : ℕ) (k : List Bool) (s : List Bool × Tree) : List (A × (List Bool × Tree)) :=
  if s.1 = [] then [] else [(1, (s.1.drop ub, tset k (ofBits (padTake ub s.1)) s.2))]

theorem length_padTake (ub : ℕ) (r : List Bool) : (padTake ub r).length = ub := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

theorem len_ofBits (w : List Bool) : (ofBits w).len = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ofBits, len, ih]

theorem putStep_does (ub : ℕ) (k : List Bool) (s : List Bool × Tree) :
    Does θ putStep (.cons (ofBits k) (.cons (num ub) (.cons (ofBits s.1) s.2)))
      ((putOne A ub k s).map (Prod.map id fun s => .cons (num ub) (.cons (ofBits s.1) s.2)))
      (ub * 90 + k.length * 60 + 300) := by
  obtain ⟨r, t⟩ := s
  cases r with
  | nil =>
    refine (Does.ite_false (Gives.id _).tl.tl.hd ?_).mono (c := 4 + 0 + 1) (by omega)
    simpa [putOne] using Does.fail (θ := θ) (.cons (ofBits k) (.cons (num ub) (.cons (ofBits []) t)))
  | cons b r =>
    have h1 := unit_gives (θ := θ) (x := .cons (ofBits k) (.cons (num ub) (.cons (ofBits (b :: r)) t))) (r := b :: r)
      (s := .hd (.tl (.tl .id))) (y := .hd (.tl .id)) (Gives.id _).tl.tl.hd (Gives.id _).tl.hd
    have h2 := reverse_gives (θ := θ) (x := .cons (.cons (ofBits k) (.cons (num ub) (.cons (ofBits (b :: r)) t)))
      (.cons (ofBits ((b :: r).drop ub)) (ofBits (padTake ub (b :: r)).reverse))) (l := .tl (.tl .id))
      (w := (padTake ub (b :: r)).reverse) (Gives.id _).tl.tl []
    rw [List.reverse_reverse, List.append_nil] at h2
    have h3 := setF_gives (θ := θ) (x := .cons (.cons (ofBits k) (.cons (num ub) (.cons (ofBits (b :: r)) t)))
      (.cons (ofBits ((b :: r).drop ub)) (ofBits (padTake ub (b :: r)).reverse))) (pf := .hd (.hd .id))
      (tf := .tl (.tl (.tl (.hd .id)))) (p := ofBits k) (t := t) (Gives.id _).hd.hd h2 (Gives.id _).hd.tl.tl.tl
    rw [path_ofBits] at h3
    have h4 := Gives.letk h1 (Gives.cons (Gives.id _).hd.tl.hd (Gives.cons (Gives.id _).tl.hd h3))
    refine (Does.ite_true (Gives.id _).tl.tl.hd (by simp [ofBits]) h4).mono ?_
    rw [List.length_reverse, length_padTake, len_ofBits]
    omega

/-- Write the units of a string: argument (yardstick, (keys, (rest, trie))). -/
def putF : Fm := lett (foldF putStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id)))
  (.ite (.hd (.tl .id)) .fail (.tl (.tl .id)))

theorem bind_putOne (ub : ℕ) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    bindL (foldL (putOne A ub) keys (r, t)) (fun s => if s.1 = [] then [((1 : A), s.2)] else []) =
      encT (putL ub keys r t) := by
  induction keys generalizing r t with
  | nil =>
    rw [foldL, bindL_single, putL]
    by_cases h : r = [] <;> simp [h]
  | cons k ks ih =>
    rw [foldL, putOne, putL]
    by_cases h : r = []
    · simp [h, bindL]
    · simp only [h, if_false]
      rw [bindL_single]
      exact ih _ _

theorem putF_does (ub : ℕ) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    Does θ putF (.cons (num ub) (.cons (listT (keys.map ofBits)) (.cons (ofBits r) t)))
      (encT (putL ub keys r t)) ((keys.map fun k => ub * 90 + k.length * 60 + 330).sum + 100) := by
  have h1 := foldT (θ := θ) (A := A) (encE := ofBits) (xs := keys)
    (enc := fun s : List Bool × Tree => .cons (num ub) (.cons (ofBits s.1) s.2)) (s₀ := (r, t)) (f := putOne A ub)
    (Inv := fun _ _ => True) (d := fun k => ub * 90 + k.length * 60 + 300) (step := putStep)
    (s := .cons (.hd .id) (.tl (.tl .id))) (l := .hd (.tl .id))
    (x := .cons (num ub) (.cons (listT (keys.map ofBits)) (.cons (ofBits r) t)))
    (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) (Gives.id _).tl.hd
    (fun k _ s _ _ => ⟨putStep_does ub k s, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettT (G := .ite (.hd (.tl .id)) .fail (.tl (.tl .id)))
    (f := fun s => if s.1 = [] then [((1 : A), s.2)] else []) (d := 20) h1 (by
      rintro ⟨a, r, t⟩ -
      cases r with
      | nil => exact (Does.ite_false (Gives.id _).tl.hd (Gives.id _).tl.tl).mono (by omega)
      | cons b r => exact (Does.ite_true (Gives.id _).tl.hd (by simp [ofBits]) (Does.fail _)).mono (by omega))
  rw [bind_putOne] at h2
  refine h2.mono ?_
  have e : (keys.map fun k => ub * 90 + k.length * 60 + 300 + 30) = keys.map fun k => ub * 90 + k.length * 60 + 330 :=
    List.map_congr_left fun k _ => by omega
  rw [e]
  omega

/-- Step for several strings: argument (keys, (yardstick, (strings, trie))). -/
def putsStep : Fm := .cons (.hd (.tl .id)) (.cons (.tl (.hd (.tl (.tl .id))))
  (lett (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id)))) (.tl (.tl (.tl .id)))))) putF))

/-- Write several strings: argument (yardstick, (lists of keys, (strings, trie))). -/
def putsF : Fm := lett (foldF putsStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id))) (.tl (.tl .id))

theorem bind_puts (ub : ℕ) (kss : List (List (List Bool))) (strs : List (List Bool)) (t : Tree) :
    bindL (foldL (fun ks (s : List (List Bool) × Tree) => (putL ub ks (s.1.headD []) s.2).map fun t =>
      ((1 : A), (s.1.tail, t))) kss (strs, t)) (fun s => [((1 : A), s.2)]) = encT (putsL ub kss strs t) := by
  induction kss generalizing strs t with
  | nil => rw [foldL, bindL_single, putsL]; rfl
  | cons ks kss ih =>
    rw [foldL, putsL, bindL_assoc, bindL_pure]
    show _ = List.map _ (List.flatMap _ _)
    rw [List.map_flatMap]
    exact List.flatMap_congr fun t _ => ih _ _

theorem putsF_does (ub : ℕ) (kss : List (List (List Bool))) (strs : List (List Bool)) (t : Tree) :
    Does θ putsF (.cons (num ub) (.cons (listT (kss.map fun ks => listT (ks.map ofBits)))
        (.cons (listT (strs.map ofBits)) t))) (encT (putsL ub kss strs t))
      ((kss.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum + 100) := by
  have h1 := foldT (θ := θ) (A := A) (encE := fun ks : List (List Bool) => listT (ks.map ofBits)) (xs := kss)
    (enc := fun s : List (List Bool) × Tree => .cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)) (s₀ := (strs, t))
    (f := fun ks (s : List (List Bool) × Tree) => (putL ub ks (s.1.headD []) s.2).map fun t =>
      ((1 : A), (s.1.tail, t))) (Inv := fun _ _ => True)
    (d := fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 160) (step := putsStep)
    (s := .cons (.hd .id) (.tl (.tl .id))) (l := .hd (.tl .id))
    (x := .cons (num ub) (.cons (listT (kss.map fun ks => listT (ks.map ofBits))) (.cons (listT (strs.map ofBits)) t)))
    (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) (Gives.id _).tl.hd
    (fun ks _ s _ _ => ⟨by
      have e1 : Gives θ (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id)))) (.tl (.tl (.tl .id))))))
          (.cons (listT (ks.map ofBits)) (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))
          (.cons (num ub) (.cons (listT (ks.map ofBits)) (.cons (ofBits (s.1.headD [])) s.2))) 30 := by
        refine (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.id _).hd (Gives.cons (o := ofBits (s.1.headD []))
          (c := 6) ?_ (Gives.id _).tl.tl.tl))).mono (by omega)
        rw [← listB_hd]
        exact ((Gives.id _).tl.tl.hd.hd).mono (by omega)
      have e2 : Gives θ (.tl (.hd (.tl (.tl .id))))
          (.cons (listT (ks.map ofBits)) (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))
          (listT (s.1.tail.map ofBits)) 6 := by
        rw [← listB_tl]
        exact ((Gives.id _).tl.tl.hd.tl).mono (by omega)
      have e3 := Does.of_gives e1 (putF_does (θ := θ) ub ks (s.1.headD []) s.2)
      have e4 := Does.cons (Gives.id (θ := θ) (.cons (listT (ks.map ofBits))
        (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))).tl.hd (Does.cons e2 e3)
      refine (e4.replace ?_).mono (by omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
      rfl, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettT (G := .tl (.tl .id)) (f := fun s : List (List Bool) × Tree => [((1 : A), s.2)]) (d := 3) h1
    (fun b _ => by exact (Gives.id _).tl.tl)
  rw [bind_puts] at h2
  refine h2.mono ?_
  have : ∀ l : List (List (List Bool)), (l.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 160 + 30).sum ≤
      (l.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum := by
    intro l
    exact List.sum_le_sum fun ks _ => by omega
  have := this kss
  omega

end Nc.Grp

end

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


def Common (e : W) (New : Finset U) : Finset (U → W) := univ.filter fun z => ∀ id, id ∉ New → z id = e

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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over contents, one step after the other

A step writes the cells of a set `wr`: it chooses `ω`, with a weight, and the contents of the cells, both as functions
of the cells written before. The sum, over all contents of the cells, of the product of the factors of the steps is
the sum over all executions.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {F : Type*} [CommRing F] {Ce W : Type*} [Fintype Ce] [DecidableEq Ce] [Fintype W] [DecidableEq W]

/-- Write the cells of `wr`. -/
def ovr (wr : Finset Ce) (v σ : Ce → W) : Ce → W := fun c => if c ∈ wr then v c else σ c

/-- A step: a sum over choices of a weight and contents of the cells of `wr`. The sum is given by its values
`sum σ f` at functions `f` of the new contents. -/
structure WStep (F Ce W : Type*) where
  /-- choices -/
  ι : Type
  /-- finitely many choices -/
  Om : Finset ι
  /-- cells that are written -/
  wr : Finset Ce
  /-- weight -/
  w : ι → (Ce → W) → F
  /-- contents -/
  v : ι → (Ce → W) → Ce → W
  /-- cells that are read -/
  rd : Finset Ce

namespace WStep

/-- The factor of a step. -/
def phi (s : WStep F Ce W) (y : Ce → W) : F :=
  ∑ ω ∈ s.Om, if ∀ c ∈ s.wr, y c = s.v ω y c then s.w ω y else 0

/-- The cells written by a list of steps. -/
def wrs : List (WStep F Ce W) → Finset Ce
  | [] => ∅
  | s :: l => s.wr ∪ wrs l

/-- The sum over all executions. -/
def exec : List (WStep F Ce W) → ((Ce → W) → F) → (Ce → W) → F
  | [], G, σ => G σ
  | s :: l, G, σ => ∑ ω ∈ s.Om, s.w ω σ * exec l G (ovr s.wr (s.v ω σ) σ)

/-- Steps read only what has been written before, and write every cell once. -/
def Seq : List (WStep F Ce W) → Prop
  | [] => True
  | s :: l => Disjoint s.wr (wrs l) ∧ (∀ ω ∈ s.Om, ∀ y y' : Ce → W, (∀ c, c ∉ s.wr ∪ wrs l → y c = y' c) →
      s.w ω y = s.w ω y' ∧ ∀ c ∈ s.wr, s.v ω y c = s.v ω y' c) ∧ Seq l

/-- **Sums over contents are sums over executions.** -/
theorem sum_eq_exec (l : List (WStep F Ce W)) (hl : Seq l) (G : (Ce → W) → F) (σ : Ce → W) :
    (∑ y ∈ univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs l → y c = σ c), (l.map fun s => s.phi y).prod * G y) =
      exec l G σ := by
  induction l generalizing σ with
  | nil =>
    have : univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs ([] : List (WStep F Ce W)) → y c = σ c) = {σ} := by
      ext y
      simp only [wrs, Finset.notMem_empty, not_false_eq_true, true_imp_iff, mem_filter, mem_univ, true_and,
        mem_singleton]
      exact funext_iff.symm
    rw [this, sum_singleton]
    simp [exec]
  | cons s l ih =>
    obtain ⟨hd, hr, hl⟩ := hl
    have h1 : ∀ y ∈ univ.filter (fun y : Ce → W => ∀ c, c ∉ wrs (s :: l) → y c = σ c),
        ((s :: l).map fun s => s.phi y).prod * G y = ∑ ω ∈ s.Om,
          if ∀ c ∈ s.wr, y c = s.v ω σ c then s.w ω σ * ((l.map fun s => s.phi y).prod * G y) else 0 := by
      intro y hy
      have hy' := (mem_filter.1 hy).2
      rw [List.map_cons, List.prod_cons, phi, mul_assoc, sum_mul]
      refine sum_congr rfl fun ω hω => ?_
      obtain ⟨e1, e2⟩ := hr ω hω y σ hy'
      have e3 : (∀ c ∈ s.wr, y c = s.v ω y c) ↔ ∀ c ∈ s.wr, y c = s.v ω σ c := by
        constructor
        · intro h c hc
          rw [← e2 c hc, h c hc]
        · intro h c hc
          rw [e2 c hc, h c hc]
      simp only [e3, e1, ite_mul, zero_mul]
    rw [sum_congr rfl h1, sum_comm, exec]
    refine sum_congr rfl fun ω _ => ?_
    rw [← ih hl, mul_sum, ← sum_filter, filter_filter]
    refine sum_congr ?_ fun y _ => rfl
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      by_cases hcs : c ∈ s.wr
      · rw [ovr, if_pos hcs, h2 c hcs]
      · rw [ovr, if_neg hcs]
        exact h1 c fun h => (mem_union.1 h).elim hcs hc
    · intro h
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [wrs, mem_union, not_or] at hc
        rw [h c hc.2, ovr, if_neg hc.1]
      · rw [h c fun h' => (disjoint_left.1 hd hc h'), ovr, if_pos hc]

theorem mem_wrs {l : List (WStep F Ce W)} {c : Ce} : c ∈ wrs l ↔ ∃ s ∈ l, c ∈ s.wr := by
  induction l with
  | nil => simp [wrs]
  | cons s l ih => simp [wrs, ih]

/-- A criterion for `Seq`. -/
theorem seq_of {l : List (WStep F Ce W)}
    (h1 : l.Pairwise fun s s' => Disjoint s.wr s'.wr ∧ Disjoint s.rd s'.wr)
    (h2 : ∀ s ∈ l, Disjoint s.rd s.wr ∧ ∀ ω ∈ s.Om, ∀ y y' : Ce → W, (∀ c ∈ s.rd, y c = y' c) →
      s.w ω y = s.w ω y' ∧ ∀ c ∈ s.wr, s.v ω y c = s.v ω y' c) : Seq l := by
  induction l with
  | nil => trivial
  | cons s l ih =>
    rw [List.pairwise_cons] at h1
    obtain ⟨h3, h4⟩ := h2 s List.mem_cons_self
    refine ⟨?_, fun ω hω y y' hy => h4 ω hω y y' fun c hc => hy c ?_, ih h1.2 fun s' hs' =>
      h2 s' (List.mem_cons_of_mem _ hs')⟩
    · rw [disjoint_left]
      intro c hc hc'
      obtain ⟨s', hs', hc''⟩ := mem_wrs.1 hc'
      exact disjoint_left.1 (h1.1 s' hs').1 hc hc''
    · rw [mem_union, not_or]
      refine ⟨disjoint_left.1 h3 hc, fun hc' => ?_⟩
      obtain ⟨s', hs', hc''⟩ := mem_wrs.1 hc'
      exact disjoint_left.1 (h1.1 s' hs').2 hc hc''

end WStep

end Nc.Grp

end

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
# Row data of a staircase, and strings of segments

A matrix of words with staircase support has exactly one valid sequence of row data; valid row data imply
staircase support. The string of the segments between two parties determines the segments.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Rows

variable {Γ : Type} {A : ℕ}

/-- The row data on one tape are those of a staircase, row `p`. -/
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

/-- Valid row data imply staircase support. -/
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

/-- The largest column that is used in a row before row `q`. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Start, I: segments

For given states between the blocks, the sum over what the blocks emit is a sum over the common segments of the
parties on all tapes, with staircase support.
-/

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

/-- A block emits at most `T` letters in all. -/
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

/-- A party writes at most `T` letters in all. -/
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

/-- The product of the weights of the parties. -/
noncomputable def segW (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p)

/-- Segments of at most `T` letters. -/
noncomputable def segs (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T

theorem mem_segs {K T : ℕ} {X : Option S → Fin (K + K) → Fin (K + K) → List Γ} :
    X ∈ segs Γ S K T ↔ ∀ s a b, (X s a b).length ≤ T := by
  simp [segs, mem_wordsLe]

variable {mu T}

/-- What the non-vanishing of the product of the weights means. -/
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
/-- **Segments.** -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Tables with code words, and the strings on the sides

The string on a side determines the indices and the strings of all blocks.
-/

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

/-- The code word of a string: its first `U` units. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Start, II: units

The sum over the segments with staircase support is the sum, over the row data and the numbers of units, of the
values of the starting positions.
-/

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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Contraction, and the power of a law
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

section Contract

variable {F : Type} [CommRing F] {Ro Cn ι : Type} [Fintype Ro] [DecidableEq Ro] [Fintype Cn] [DecidableEq Cn]
  [Fintype ι] {S : ι → Cn → Type} [∀ i ν, Fintype (S i ν)] {Z : Type} [Fintype Z] (c d : Cn → Ro)
  (code : (ν : Cn) → (i : ι) → S i ν → Z)

open Classical in
/-- The table of a role with code words on its channels. -/
noncomputable def codeTab (p : Ro) (G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) (z : Cn → Z) : F :=
  ∑ i, ∑ g : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν then G i g else 0

/-- Only the code words on the channels of the role matter. -/
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
/-- **Contraction.** Tables with code words, summed over the code words on all channels, give the sum of the products
of the tables. -/
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

/-- **The power of a law**: `B` blocks. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The identity of one move, for general laws
-/

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

/-- Two copies of a slot agree if the units do. -/
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

/-- The role depends on the units given and on the new units at its channels only. -/
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

/-- The roles at the ends of a channel force its new units to be present. -/
theorem role_new_ne_none {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) {k : Fin U1} (hk : k ≤ o ⟨x, ν⟩) : y (.new ⟨x, ν⟩ k) ≠ none := by
  obtain ⟨-, i, g, hg, -⟩ := role_ne_zero h
  exact (hg ⟨ν, hν⟩).ne_none hk

end Role

section Law

variable (L : Law F)

/-- The code word of the string on a channel: its first `U1` units. -/
def chCode (ub U1 B : ℕ) (ν : L.Cn) (i : Fin B → L.I) (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool) : Fin U1 → UW ub :=
  fun k => unitsOf ub (chString L.lab (fun j => L.len j ν) i g) k

theorem length_chString {I : Type} {lam B : ℕ} (lb : I → Fin lam → Bool) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : (chString lb len i g).length = ∑ k, (lam + len (i k)) :=
  length_sideString lb len i g

/-- A bound for the lengths of the strings of a law. -/
structure Law.Le (L : Law F) (m : ℕ) : Prop where
  len_le : ∀ i ν, L.len i ν ≤ m

variable {L}

theorem chCode_injective (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1) (ν : L.Cn) :
    Function.Injective fun q : Σ i : Fin B → L.I, (k : Fin B) → Fin (L.len (i k) ν) → Bool =>
      chCode L ub U1 B ν q.1 q.2 :=
  codeWord_injective (len := fun i => L.len i ν) L.lab_inj hub (fun i => hm.len_le i ν) hB

open Classical in
variable (L) in
/-- The table of the law for an outcome; `X p k e` are the bits. -/
noncomputable def outTab (ub : ℕ) {U1 B : ℕ} (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1) (p : L.Ro)
    (i : Fin B → L.I) (g : (ν : L.CnAt p) → (k : Fin B) → Fin (L.len (i k) ν) → Bool) : F :=
  if ∀ ν : L.CnAt p, ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1 then
    ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k else 0

/-- Tables with code words, summed over all outcomes. -/
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

/-- Impossible outcomes contribute nothing. -/
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

/-- The role as a table with code words. -/
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

/-- Set the outcome of move `x`. -/
def upd (M : Sys F (A + A') E) (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) : M.N → Fin U1 := fun ν =>
  if h : x = ν.1 then (h ▸ oo : (M.kind ν.1).Cn → Fin U1) ν.2 else o ν

theorem upd_self (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) (ν : (M.kind x).Cn) :
    upd M o x oo ⟨x, ν⟩ = oo ν := by simp [upd]

theorem upd_ne (o : M.N → Fin U1) {x : Fin E} (oo : (M.kind x).Cn → Fin U1) {ν : M.N} (h : ν.1 ≠ x) :
    upd M o x oo ν = o ν := by
  rw [upd, dif_neg (Ne.symm h)]

/-- One outcome of a move, as a sum over code words. -/
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

/-- **The identity of one move.** -/
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

/-- Impossible outcomes of a move contribute nothing. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The play, for general laws
-/

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

/-- The units seen in the end. -/
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

/-- The joint weight before move `x`. -/
noncomputable def tabUpTo (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F) (x : ℕ) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : F :=
  (∏ a, init a (y a)) * ∏ x' ∈ univ.filter (fun x' : Fin E => x'.1 < x), ∏ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p))

variable {init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F}

/-- Units that are present if the joint weight is not zero. -/
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

/-- The joint weight before move `x` does not depend on the copies of later units. -/
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

/-- The units given in a move. -/
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
/-- **Paper: Units.** "Each choice of indices and bits occurs for exactly one outcome, so the value does not change":
one move, as a sum over outcomes that are good. -/
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
/-- **Paper: Units.** "Every possible outcome is good ...; so the sum may be restricted to good outcomes": a whole plan
of moves keeps the value. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Start: units (general laws)

The sum over the segments with staircase support is the sum, over the row data and the numbers of units, of the
values of the starting positions.
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

/-- The condition in the table of a party at the beginning. -/
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

/-- All initial units held by a party are present if its table is not zero. -/
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

/-- The table of a party at the beginning depends on its copies of initial units only. -/
theorem tabInit_congr {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)} {y y' : Uid (K + K) U0 N U1 → UW ub}
    (h : ∀ a b k, y (.init a b k) = y' (.init a b k)) :
    tabInit mu T cb q x ρ n p y = tabInit mu T cb q x ρ n p y' := by
  classical
  rw [tabInit_eq, tabInit_eq]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr ?_ rfl rfl
  simp only [InitOk, h]

/-- What the parties write or read. -/
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
/-- **Units.** -/
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
/-- **Start.** The value of an automaton in `K * T` steps is the sum, over the states between the blocks, the row data
and the numbers of units, of the values of the starting positions. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Exactness of a whole cut

The value of an automaton is the sum, over the states between the blocks, the row data, the numbers of units, the
outcomes of the moves, and the contents of the units shared by different groups, of the products of the values of
the groups.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Groups

variable {AA UU W G : Type*} [Fintype AA] [DecidableEq AA] [Fintype UU] [DecidableEq UU]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

/-- If the tables vanish unless all units held are present, the contents of shared units are present. -/
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

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The tables of the parties at the beginning and after the moves, and the values of groups
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A A' K E U0 U1 ub c : ℕ}

section Play

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}

/-- All units ever held by a party are present if its table is not zero. -/
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

/-- The tables of all parties at the beginning. -/
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

/-- The contents of shared units are present if the value of the group is not zero. -/
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

section













set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]


def isInit {A U0 : ℕ} {N : Type} {U1 : ℕ} : G.Uid A U0 N U1 → Bool
  | .init _ _ _ => true
  | .new _ _ => false


def isNewOf {M : Sys F (K + K + A') E} (x : Fin E) : G.Uid (K + K) U0 M.N U1 → Bool
  | .init _ _ _ => false
  | .new ν _ => decide (ν.1 = x)

section

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)
  {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)





def dom : Finset (Cell M U0 U1) := univ.filter fun c =>
  grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2


noncomputable def initV (ub : ℕ) (N : Type) (U0 U1 : ℕ) (R C : Option S → Fin (K + K) → List Γ) (p : Fin (K + K)) :
    G.Uid (K + K) U0 N U1 → UW ub
  | .init a b k => if a = p then unitsOf ub (strOf cb fun s => R s b) k else unitsOf ub (strOf cb fun s => C s a) k
  | .new _ _ => none


def InitC (ub U0 : ℕ) (n : Fin (K + K) → Fin (K + K) → ℕ) (ρ : Option S → RowData (K + K)) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p) ∧
    ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R s p) k = unitsOf ub (strOf cb fun s => C s p) k

open Classical in

noncomputable def baseStep (ub : ℕ) (p : Fin (K + K)) : WStep F (Cell M U0 U1) (UW ub) where
  ι := (Option S → Fin (K + K) → List Γ) × (Option S → Fin (K + K) → List Γ)
  Om := (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T) ×ˢ
    (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T)
  wr := (dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true
  w RC _ := if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p RC.1 RC.2 then
    partyW mu T q x p RC.1 RC.2 else 0
  v RC _ c := initV cb ub M.N U0 U1 RC.1 RC.2 p c.2
  rd := ∅


abbrev Bk (L : Law F) (p : L.Ro) := Σ i : L.I, ∀ ν : L.CnAt p, Fin (L.len i ν) → Bool


def chS (L : Law F) (p : L.Ro) {B : ℕ} (f : Fin B → Bk L p) (ν : L.CnAt p) : List Bool :=
  chString L.lab (fun j => L.len j ν) (fun k => (f k).1) (fun k => (f k).2 ν)

open Classical in

noncomputable def roleV (ub : ℕ) {M : Sys F (K + K + A') E} (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) :
    G.Uid (K + K) U0 M.N U1 → UW ub
  | .init _ _ _ => none
  | .new ν k => if h : ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ν then
      unitsOf ub (chS (M.kind r.1) r.2 f h.choose) k else none

open Classical in

noncomputable def roleStep (ub : ℕ) (r : M.R) : WStep F (Cell M U0 U1) (UW ub) where
  ι := Fin (P.num n o r.1 * ub) → Bk (M.kind r.1) r.2
  Om := univ
  wr := (dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true
  w f σ := if (∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none) ∧
      ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 then
    ∏ k, (M.kind r.1).tab r.2 (f k).1 (fun e => (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
      fun id => σ (M.rp r, id)).getD k false) (f k).2 else 0
  v f _ c := roleV ub r f c.2
  rd := univ.filter fun c => c.1 = M.rp r ∧ ∃ e : (M.kind r.1).SlAt r.2, c.2 ∈ P.ids n o ⟨r.1, e.1⟩











noncomputable def steps (ub : ℕ) : List (WStep F (Cell M U0 U1) (UW ub)) :=
  (baseList grp g).map (baseStep mu T cb q x ρ n o grp g ub) ++ (roleList grp g M).map (roleStep P n o grp g ub)

end

section facts

variable {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

theorem mem_dom {c : Cell M U0 U1} : c ∈ dom n o grp g ↔
    grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2 := by
  simp [dom]

theorem mem_baseList {p : Fin (K + K)} : p ∈ baseList (A' := A') grp g ↔ grp (Fin.castAdd A' p) = g := by
  simp [baseList]

theorem mem_allRoles (r : M.R) : r ∈ allRoles M := by
  obtain ⟨x, p⟩ := r
  exact List.mem_flatMap.2 ⟨x, List.mem_finRange x, List.mem_map.2 ⟨p, Finset.mem_toList.2 (mem_univ p), rfl⟩⟩

theorem mem_roleList {r : M.R} : r ∈ roleList grp g M ↔ grp (M.rp r) = g := by
  simp [roleList, mem_allRoles]

theorem nodup_baseList : (baseList (A' := A') (K := K) grp g).Nodup := (List.nodup_finRange _).filter _

theorem pairwise_allRoles : (allRoles M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 := by
  unfold allRoles
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp fun {p p'} h => ⟨fun h' => h ?_, le_rfl⟩
    exact eq_of_heq (Sigma.mk.inj h').2
  · refine (List.pairwise_lt_finRange E).imp fun {x x'} hx r hr r' hr' => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hr'
    exact ⟨fun h => hx.ne (Sigma.mk.inj h).1, hx.le⟩

theorem pairwise_roleList : (roleList grp g M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 :=
  pairwise_allRoles.filter _


theorem exists_role {a : Fin (K + K + A')} {ν : M.N} {k : Fin U1}
    (h : Holds (G.hold0 M.np) (G.hold1 M.np) a (G.Uid.new ν k : G.Uid (K + K) U0 M.N U1)) :
    ∃ d, a = M.rp (M.nr ν d) := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem role_eq_of_rp {x : Fin E} {p p' : (M.kind x).Ro} (h : M.rp ⟨x, p⟩ = M.rp ⟨x, p'⟩) : p = p' :=
  M.inj x h


theorem exists_cnAt {r : M.R} {ν : M.N} {k : Fin U1} (hx : ν.1 = r.1)
    (h : Holds (G.hold0 M.np) (G.hold1 M.np) (M.rp r) (G.Uid.new ν k : G.Uid (K + K) U0 M.N U1)) :
    ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ν := by
  obtain ⟨x, p⟩ := r
  obtain ⟨x', ν⟩ := ν
  simp only at hx
  subst hx
  rcases h with h | h
  · have : p = (M.kind x').c ν := role_eq_of_rp h
    exact ⟨⟨ν, Or.inl this.symm⟩, rfl⟩
  · have : p = (M.kind x').d ν := role_eq_of_rp h
    exact ⟨⟨ν, Or.inr this.symm⟩, rfl⟩

theorem holds_cnAt {r : M.R} (ν : (M.kind r.1).CnAt r.2) (k : Fin U1) :
    Holds (G.hold0 M.np) (G.hold1 M.np) (M.rp r) (G.Uid.new ⟨r.1, ν.1⟩ k : G.Uid (K + K) U0 M.N U1) := by
  obtain ⟨x, p⟩ := r
  obtain ⟨ν, h | h⟩ := ν
  · exact Or.inl (congrArg (M.part x) h.symm)
  · exact Or.inr (congrArg (M.part x) h.symm)

theorem roleV_new (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) (ν : (M.kind r.1).CnAt r.2) (k : Fin U1) :
    roleV ub r f (G.Uid.new ⟨r.1, ν.1⟩ k : G.Uid (K + K) U0 M.N U1) = unitsOf ub (chS (M.kind r.1) r.2 f ν) k := by
  have h : ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ⟨r.1, ν.1⟩ := ⟨ν, rfl⟩
  rw [roleV, dif_pos h]
  have : h.choose = ν := Subtype.ext (eq_of_heq (Sigma.mk.inj h.choose_spec).2)
  rw [this]


theorem wrs_steps : WStep.wrs (steps mu T cb P q x ρ n o grp g ub) = dom n o grp g := by
  ext ⟨a, id⟩
  rw [WStep.mem_wrs]
  constructor
  · rintro ⟨s, hs, hc⟩
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      exact (mem_filter.1 hc).1
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
      exact (mem_filter.1 hc).1
  · intro hc
    obtain ⟨h1, h2, h3⟩ := mem_dom.1 hc
    cases id with
    | init a' b' k =>
      obtain ⟨p, rfl⟩ : ∃ p : Fin (K + K), a = Fin.castAdd A' p := by
        rcases h3 with h3 | h3
        · exact ⟨a', h3⟩
        · exact ⟨b', h3⟩
      exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨p, mem_baseList.2 h1, rfl⟩),
        mem_filter.2 ⟨hc, rfl, rfl⟩⟩
    | new ν k =>
      obtain ⟨d, rfl⟩ := exists_role h3
      refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨M.nr ν d, mem_roleList.2 h1, rfl⟩), ?_⟩
      exact mem_filter.2 ⟨hc, rfl, by simp [isNewOf, Sys.nr]⟩


theorem seq_steps (hP : P.Ok cap) : WStep.Seq (steps mu T cb P q x ρ n o grp g ub) := by
  have hnew : ∀ (r : M.R) (e : (M.kind r.1).SlAt r.2) (id) , id ∈ P.ids n o ⟨r.1, e.1⟩ →
      ∀ x', r.1 ≤ x' → isNewOf x' id = false := by
    intro r e id hid x' hx'
    have h1 := hP.sub n o _ (G.Plan.mem_ids.1 hid)
    have h2 := (G.Plan.mem_cur.1 h1).1
    cases id with
    | init _ _ _ => rfl
    | new ν k =>
      have h3 := (G.Plan.new_mem_seenAt.1 h2).1
      simp only [isNewOf, decide_eq_false_iff_not]
      rintro rfl
      exact absurd h3 (not_lt.2 hx')
  refine WStep.seq_of ?_ ?_
  · unfold steps
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine nodup_baseList.imp fun {p p'} hpp' => ⟨?_, disjoint_empty_left _⟩
      rw [disjoint_left]
      intro c hc hc'
      have h1 := (mem_filter.1 hc).2.1
      have h2 := (mem_filter.1 hc').2.1
      exact hpp' (Fin.castAdd_injective _ _ (h1.symm.trans h2))
    · rw [List.pairwise_map]
      refine pairwise_roleList.imp fun {r r'} hrr' => ⟨?_, ?_⟩
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
        obtain ⟨-, h4, h5⟩ := mem_filter.1 hc'
        cases id with
        | init _ _ _ => simp [isNewOf] at h3
        | new ν k =>
          simp only [isNewOf, decide_eq_true_eq] at h3 h5
          obtain ⟨x, p⟩ := r
          obtain ⟨x', p'⟩ := r'
          simp only at h2 h3 h4 h5
          obtain rfl := h3.symm.trans h5
          exact hrr'.1 (by rw [role_eq_of_rp (h2.symm.trans h4)])
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨-, -, e, he⟩ := mem_filter.1 hc
        have h5 := (mem_filter.1 hc').2.2
        rw [hnew r e id he _ hrr'.2] at h5
        exact absurd h5 (by simp)
    · intro s hs s' hs'
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs'
      refine ⟨?_, disjoint_empty_left _⟩
      rw [disjoint_left]
      rintro ⟨a, id⟩ hc hc'
      have h1 := (mem_filter.1 hc).2.2
      have h2 := (mem_filter.1 hc').2.2
      cases id with
      | init _ _ _ => simp [isNewOf] at h2
      | new _ _ => simp [isInit] at h1
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨disjoint_empty_left _, fun ω _ y y' _ => ⟨rfl, fun c _ => rfl⟩⟩
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
      refine ⟨?_, fun f _ y y' hy => ⟨?_, fun c _ => rfl⟩⟩
      · rw [disjoint_left]
        rintro ⟨a, id⟩ hc hc'
        obtain ⟨-, -, e, he⟩ := mem_filter.1 hc
        have h5 := (mem_filter.1 hc').2.2
        rw [hnew r e id he _ le_rfl] at h5
        exact absurd h5 (by simp)
      · have hy' : ∀ (e : (M.kind r.1).SlAt r.2), ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) = y' (M.rp r, id) :=
          fun e id hid => hy _ (mem_filter.2 ⟨mem_univ _, rfl, e, hid⟩)
        have e1 : (∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) ≠ none) ↔
            ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y' (M.rp r, id) ≠ none := by
          refine forall_congr' fun e => forall₂_congr fun id hid => ?_
          rw [hy' e id hid]
        have e2 : ∀ e : (M.kind r.1).SlAt r.2, slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
            (fun id => y (M.rp r, id)) = slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
            (fun id => y' (M.rp r, id)) := by
          intro e
          unfold slotBits
          congr 1
          refine List.flatMap_congr fun id hid => ?_
          simp only [hy' e id hid]
        simp only [roleStep, e1, e2]

end facts

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program of a role: streams

The contents of the units given at the slots are put together to streams of bits.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Step: argument (key, (trie, bits)). -/
def streamStep : Fm := .ite (getF (.hd .id) (.hd (.tl .id)))
  (.cons (.hd (.tl .id)) (appF (getF (.hd .id) (.hd (.tl .id))) (.tl (.tl .id)))) .fail

/-- A stream: argument (trie, keys). -/
def streamF : Fm := lett (foldF streamStep (.cons (.hd .id) (.quote .nil)) (.tl .id)) (.tl .id)

/-- Step for several streams: argument (keys, (trie, streams)). -/
def streamsStep : Fm := .cons (.hd (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd .id)) streamF) (.tl (.tl .id)))

/-- Several streams: argument (trie, lists of keys). -/
def streamsF : Fm := lett (foldF streamsStep (.cons (.hd .id) (.quote .nil)) (.tl .id))
  (foldF .id (.quote .nil) (.tl .id))

section stream

variable {ub : ℕ} {ct : List Bool → List Bool} {t : Tree}

theorem streamStep_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (k : List Bool) (acc : List Bool) :
    Does θ streamStep (.cons (ofBits k) (.cons t (ofBits acc)))
      ((if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []).map (Prod.map id fun acc => .cons t (ofBits acc)))
      (ub * 62 + k.length * 60 + 300) := by
  have h1 : Gives θ (getF (.hd .id) (.hd (.tl .id))) (.cons (ofBits k) (.cons t (ofBits acc))) (ofBits (ct k))
      (k.length * 30 + 40) := by
    have := getF_gives (θ := θ) (x := .cons (ofBits k) (.cons t (ofBits acc)))
      (pf := .hd .id) (tf := .hd (.tl .id)) (p := ofBits k) (t := t) (Gives.id _).hd (Gives.id _).tl.hd
    rw [path_ofBits, hct, len_ofBits] at this
    exact this.mono (by omega)
  by_cases hk : ct k = []
  · have h0 : Gives θ (getF (.hd .id) (.hd (.tl .id))) (.cons (ofBits k) (.cons t (ofBits acc))) .nil
        (k.length * 30 + 40) := by
      rw [hk] at h1
      exact h1
    refine ((Does.ite_false h0 (Does.fail _)).replace ?_).mono (by omega)
    simp [hk]
  · have h2 := appB_gives h1 (Gives.id (θ := θ) (.cons (ofBits k) (.cons t (ofBits acc)))).tl.tl
    have h3 : ofBits (ct k) ≠ .nil := by
      cases h : ct k with
      | nil => exact absurd h hk
      | cons b w => simp [ofBits]
    have h5 := hlen k
    refine ((Does.ite_true h1 h3 (Gives.cons (Gives.id _).tl.hd h2)).replace ?_).mono (by omega)
    simp [hk]

theorem foldL_stream (es : List (List Bool)) (acc : List Bool) :
    foldL (A := A) (fun k acc => if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []) es acc =
      if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct ++ acc)] else [] := by
  induction es generalizing acc with
  | nil => simp [foldL]
  | cons e es ih =>
    rw [foldL]
    by_cases he : ct e ≠ []
    · rw [if_pos he, bindL_single, ih]
      by_cases hes : ∀ k ∈ es, ct k ≠ []
      · rw [if_pos hes, if_pos (by
          intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact he
          · exact hes k hk)]
        simp
      · rw [if_neg hes, if_neg fun h => hes fun k hk => h k (List.mem_cons_of_mem _ hk)]
    · rw [if_neg he, if_neg fun h => he (h e List.mem_cons_self)]
      rfl

theorem streamF_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (es : List (List Bool)) :
    Does θ streamF (.cons t (listT (es.map ofBits)))
      ((if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct)] else []).map (Prod.map id ofBits))
      ((es.map fun k => ub * 62 + k.length * 60 + 330).sum + 60) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons t (listT (es.map ofBits))) (.cons t (ofBits [])) 8 :=
    (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have h1 := foldT (θ := θ) (A := A) (encE := ofBits) (xs := es)
    (enc := fun acc : List Bool => .cons t (ofBits acc)) (s₀ := [])
    (f := fun k acc => if ct k ≠ [] then [((1 : A), ct k ++ acc)] else []) (Inv := fun _ _ => True)
    (d := fun k => ub * 62 + k.length * 60 + 300) (step := streamStep) (l := .tl .id) h0 (Gives.id _).tl
    (fun k _ acc _ _ => ⟨streamStep_does hct hlen k acc, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettE (G := .tl .id) (f := fun acc => [((1 : A), acc)]) (enc' := ofBits) (d := 2) h1
    (fun b _ => by exact (Gives.id _).tl)
  rw [foldL_stream] at h2
  have e : (es.map fun k => ub * 62 + k.length * 60 + 300 + 30) = es.map fun k => ub * 62 + k.length * 60 + 330 :=
    List.map_congr_left fun k _ => by omega
  rw [e] at h2
  refine (h2.replace ?_).mono (by omega)
  split_ifs <;> simp [bindL]

theorem streamsStep_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (es : List (List Bool)) (acc : List (List Bool)) :
    Does θ streamsStep (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))
      ((if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)] else []).map
        (Prod.map id fun acc => .cons t (listT (acc.map ofBits))))
      ((es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150) := by
  have e1 : Gives θ (.cons (.hd (.tl .id)) (.hd .id)) (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))
      (.cons t (listT (es.map ofBits))) 20 := (Gives.cons (Gives.id _).tl.hd (Gives.id _).hd).mono (by omega)
  have e2 := Does.of_gives e1 (streamF_does (θ := θ) hct hlen es)
  have e3 := Does.cons (Gives.id (θ := θ) (.cons (listT (es.map ofBits)) (.cons t (listT (acc.map ofBits))))).tl.hd
    (Does.cons e2 (Gives.id _).tl.tl)
  refine (e3.replace ?_).mono (by omega)
  split_ifs <;> simp [listT]

theorem foldL_streams (slots : List (List (List Bool))) (acc : List (List Bool)) :
    foldL (A := A) (fun es acc => if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)]
      else []) slots acc = if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
        [((1 : A), (slots.map fun es => es.reverse.flatMap ct).reverse ++ acc)] else [] := by
  induction slots generalizing acc with
  | nil => simp [foldL]
  | cons es slots ih =>
    rw [foldL]
    by_cases he : ∀ k ∈ es, ct k ≠ []
    · rw [if_pos he, bindL_single, ih]
      by_cases hes : ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ []
      · rw [if_pos hes, if_pos (by
          intro es' h'
          rcases List.mem_cons.1 h' with rfl | h'
          · exact he
          · exact hes es' h')]
        simp
      · rw [if_neg hes, if_neg fun h => hes fun es' h' => h es' (List.mem_cons_of_mem _ h')]
    · rw [if_neg he, if_neg fun h => he (h es List.mem_cons_self)]
      rfl

theorem streamsF_does (hct : ∀ k, tget k t = ofBits (ct k)) (hlen : ∀ k, (ct k).length ≤ ub)
    (slots : List (List (List Bool))) :
    Does θ streamsF (.cons t (keysT slots))
      ((if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then [((1 : A), slots.map fun es => es.reverse.flatMap ct)]
        else []).map (Prod.map id fun l : List (List Bool) => listT (l.map ofBits)))
      ((slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum + 100) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons t (keysT slots))
      (.cons t (listT (([] : List (List Bool)).map ofBits))) 8 :=
    (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have h1 := foldT (θ := θ) (A := A) (encE := fun es : List (List Bool) => listT (es.map ofBits)) (xs := slots)
    (enc := fun acc : List (List Bool) => .cons t (listT (acc.map ofBits))) (s₀ := [])
    (f := fun es acc => if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)] else [])
    (Inv := fun ys acc => ys.length + acc.length = slots.length)
    (d := fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150) (step := streamsStep)
    (l := .tl .id) h0 (Gives.id _).tl
    (fun es ys acc _ hinv => ⟨streamsStep_does hct hlen es acc, fun q hq => by
      split_ifs at hq
      · rw [List.mem_singleton] at hq
        subst hq
        simp only [List.length_cons] at hinv ⊢
        omega
      · simp at hq⟩) (by simp)
  rw [foldL_streams, List.append_nil] at h1
  have h2 := Does.lettE (G := foldF .id (.quote .nil) (.tl .id)) (f := fun acc => [((1 : A), acc.reverse)])
    (enc' := fun l : List (List Bool) => listT (l.map ofBits)) (d := slots.length * 31 + 30) h1 (fun b hb => by
      have hl : b.2.length = slots.length := by
        split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          simp
        · simp at hb
      have := rev_gives (θ := θ) (x := .cons t (listT (b.2.map ofBits))) (ys := [])
        (xs := b.2.map ofBits) (s := .quote .nil) (l := .tl .id) (Gives.quote _ _) (Gives.id _).tl
      rw [List.append_nil, ← List.map_reverse, List.length_map, hl] at this
      exact this.mono (by omega))
  refine (h2.replace ?_).mono ?_
  · split_ifs <;> simp [bindL]
  · have : (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 150 + 30).sum + slots.length * 60 =
        (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum := by
      clear h1 h2 h0
      induction slots with
      | nil => rfl
      | cons es slots ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    omega

end stream

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program of a role: the loop
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

variable (θ) in
open Classical in
/-- A formula for an element of the ring. -/
noncomputable def we (a : A) : WE := if h : ∃ e : WE, e.val θ = a then h.choose else .zero

theorem we_val {a : A} (h : ∃ e : WE, e.val θ = a) : (we θ a).val θ = a := by
  rw [we, dif_pos h]
  exact h.choose_spec

/-- Slots of a role, as a list. -/
noncomputable def slList (L : G.Law A) (p : L.Ro) : List (L.SlAt p) := (univ : Finset (L.SlAt p)).toList

/-- Channels of a role, as a list. -/
noncomputable def cnList (L : G.Law A) (p : L.Ro) : List (L.CnAt p) := (univ : Finset (L.CnAt p)).toList

/-- The number of a slot. -/
noncomputable def slIdx (L : G.Law A) (p : L.Ro) (e : L.SlAt p) : Fin (slList L p).length :=
  ⟨(slList L p).idxOf e, List.idxOf_lt_length_of_mem (Finset.mem_toList.2 (mem_univ e))⟩

variable (θ) in
/-- The transducer of a role. -/
noncomputable def roleTab (L : G.Law A) (p : L.Ro) (_ : Fin 1) (v : Fin (slList L p).length → Bool) :
    List (Opt 1 (cnList L p).length Bool) :=
  (univ : Finset (Bk L p)).toList.map fun z => ⟨we θ (L.tab p z.1 (fun e => v (slIdx L p e)) z.2), 0,
    fun j => (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ((cnList L p).get j))).reverse⟩

/-- The yardstick: argument (yardstick `num ub`, (trie, (num t, …))). -/
def yardF : Fm := .tl (foldF (.cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id)))) (.cons (.hd .id) (.quote .nil))
  (.hd (.tl (.tl .id))))

theorem foldl_yard (tt ub m : ℕ) : (List.replicate tt ()).foldl (fun (k : ℕ) _ => ub + k) m = tt * ub + m := by
  induction tt generalizing m with
  | zero => simp
  | succ tt ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    ring

theorem yardF_gives (ub tt : ℕ) (t y : Tree) :
    Gives θ yardF (.cons (num ub) (.cons t (.cons (num tt) y))) (num (tt * ub)) (tt * (ub * 62 + 100) + 60) := by
  have h0 : Gives θ (.cons (.hd .id) (.quote .nil)) (.cons (num ub) (.cons t (.cons (num tt) y)))
      (.cons (num ub) (num 0)) 4 := (Gives.cons (Gives.id _).hd (Gives.quote _ _)).mono (by omega)
  have hl : Gives θ (.hd (.tl (.tl .id))) (.cons (num ub) (.cons t (.cons (num tt) y)))
      (listT ((List.replicate tt ()).map fun _ => .nil)) 4 := by
    rw [List.map_replicate, ← num_eq_listT]
    exact (Gives.id _).tl.tl.hd
  have h1 := foldTG (θ := θ) (encE := fun _ : Unit => (.nil : Tree)) (enc := fun k : ℕ => .cons (num ub) (num k)) (s₀ := 0)
    (g := fun _ k => ub + k) (Inv := fun _ _ => True) (d := fun _ => ub * 62 + 60)
    (step := .cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id)))) h0 hl (fun _ _ k _ _ => ⟨by
      have e1 : Gives θ (.hd (.tl .id)) (.cons .nil (.cons (num ub) (num k))) (ofBits (List.replicate ub false)) 3 := by
        rw [← num_eq_ofBits]
        exact (Gives.id _).tl.hd
      have e2 : Gives θ (.tl (.tl .id)) (.cons .nil (.cons (num ub) (num k))) (ofBits (List.replicate k false)) 3 := by
        rw [← num_eq_ofBits]
        exact (Gives.id _).tl.tl
      have e3 := appB_gives e1 e2
      rw [← List.replicate_add, ← num_eq_ofBits, List.length_replicate] at e3
      exact (Gives.cons (Gives.id _).tl.hd e3).mono (by omega), trivial⟩) trivial
  have h2 : (List.replicate tt ()).foldl (fun (k : ℕ) _ => ub + k) 0 = tt * ub := by
    rw [foldl_yard, add_zero]
  rw [h2] at h1
  refine h1.tl.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

variable (θ) in
/-- What a role does with a trie with the contents `ct`. -/
noncomputable def roleSem (L : G.Law A) (p : L.Ro) (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
    bindL (runL θ (roleTab θ L p) (tt * ub)
      (0, fun i => ((slots.map fun es => es.reverse.flatMap ct).getD i []), fun _ => [])) fun s =>
      encT (putsL ub keys (List.ofFn fun j => (s.2.2 j).reverse ++ [true]) t)
  else []

/-- The last part: argument ((yardstick, (trie, (num t, (slots, keys)))), state of the transducer). -/
def roleEnd : Fm := lett (.cons (.hd (.hd .id)) (.cons (.tl (.tl (.tl (.tl (.hd .id)))))
  (.cons (mapF (foldF .id (.quote (ofBits [true])) (.tl .id)) (.quote .nil) (.tl (.tl (.tl .id))))
    (.hd (.tl (.hd .id)))))) putsF

theorem roleEnd_does (ub : ℕ) (t y sl ins : Tree) (c0 : Tree) (keys : List (List (List Bool))) (m : ℕ) (outs : List (List Bool))
    (hm : ∀ w ∈ outs, w.length ≤ m) :
    Does θ roleEnd (.cons (.cons (num ub) (.cons t (.cons y (.cons sl (keysT keys)))))
        (.cons c0 (.cons ins (listT (outs.map ofBits)))))
      (encT (putsL ub keys (outs.map fun w => w.reverse ++ [true]) t))
      (outs.length * (m * 31 + 100) + ((keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum + 200)) := by
  set x : Tree := .cons (.cons (num ub) (.cons t (.cons y (.cons sl (keysT keys)))))
    (.cons c0 (.cons ins (listT (outs.map ofBits)))) with hx
  have h1 := mapF_gives (θ := θ) (x := x) (step := foldF .id (.quote (ofBits [true])) (.tl .id)) (ef := .quote .nil)
    (l := .tl (.tl (.tl .id))) (e := .nil) (xs := outs.map ofBits) (g := fun y => ofBits (y.path.reverse ++ [true]))
    (d := fun _ => m * 31 + 30) (Gives.quote _ _) (Gives.id _).tl.tl.tl (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
      rw [path_ofBits]
      have := reverse_gives (θ := θ) (x := .cons (.nil : Tree) (ofBits w)) (l := .tl .id) (w := w) (Gives.id _).tl [true]
      have h2 := hm w hw
      exact this.mono (by omega))
  have h2 : ((outs.map ofBits).map fun y => ofBits (y.path.reverse ++ [true])) =
      (outs.map fun w => w.reverse ++ [true]).map ofBits := by
    simp [Function.comp_def]
  rw [h2] at h1
  have h3 := Gives.cons (Gives.id (θ := θ) x).hd.hd (Gives.cons (Gives.id _).hd.tl.tl.tl.tl (Gives.cons h1
    (Gives.id _).hd.tl.hd))
  have h4 := putsF_does (θ := θ) ub keys (outs.map fun w => w.reverse ++ [true]) t
  refine (Does.of_gives h3 h4).mono ?_
  simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul]
  ring_nf
  omega

/-- **The program of a role.** -/
theorem ex_role (L : G.Law A) (p : L.Ro) : ∃ F κ, ∀ (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree),
    (∀ k, tget k t = ofBits (ct k)) → (∀ k, (ct k).length ≤ ub) → slots.length = (slList L p).length →
    Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots)
        (keysT keys))))) (roleSem θ L p ub ct tt slots keys t)
      (κ * (tt * (ub + 1) + (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum +
        (keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum + 1)) := by
  obtain ⟨F, κ, hF⟩ := ex_run (θ := θ) bit (roleTab θ L p)
  obtain ⟨κ', hκ'⟩ := exists_runL_length (θ := θ) (roleTab θ L p)
  set nO := (cnList L p).length with hnO
  refine ⟨lett (.cons .id (lett (.cons yardF (.cons (.quote (num 0)) (.cons
    (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) streamsF)
    (.quote (listT (List.replicate nO .nil)))))) F)) roleEnd, κ + nO * (κ' * 31 + 100) + 1000,
    fun ub ct tt slots keys t hct hlen hslots => ?_⟩
  set x : Tree := .cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots)
        (keysT keys)))) with hx
  have h1 := yardF_gives (θ := θ) ub tt t (.cons (keysT slots) (keysT keys))
  have h2 : Gives θ (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) x (.cons t (keysT slots)) 15 :=
    (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.tl.hd).mono (by omega)
  have h3 := Does.of_gives h2 (streamsF_does (θ := θ) hct hlen slots)
  set bs := slots.map fun es => es.reverse.flatMap ct with hbs
  -- the state at the beginning
  let s₀ : TSt 1 (slList L p).length nO Bool := (0, fun i => bs.getD i [], fun _ => [])
  have hs₀ : encS bit s₀ = .cons (num 0) (.cons (listT (bs.map ofBits)) (listT (List.replicate nO .nil))) := by
    have e1 : (List.ofFn fun i : Fin (slList L p).length => ofBits (bs.getD i [])) = bs.map ofBits := by
      apply List.ext_getElem
      · simp [hbs, hslots]
      · intro k h1 h2
        simp only [List.length_map] at h2
        rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem _ _ h2]
    have e2 : (List.ofFn fun _ : Fin nO => listT (([] : List Bool).map bit)) = List.replicate nO .nil := by
      rw [List.ofFn_const]
      rfl
    simp only [encS, s₀, e1, e2]
    rfl
  have h4 := Does.cons h1 (Does.cons (Gives.quote (θ := θ) (num 0) x) (Does.cons h3
    (Gives.quote (listT (List.replicate nO .nil)) x)))
  have h5 : Does θ (.cons yardF (.cons (.quote (num 0)) (.cons
      (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl (.tl .id))))) streamsF)
      (.quote (listT (List.replicate nO .nil)))))) x
      ((if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then [((1 : A), ())] else []).map
        (Prod.map id fun _ => .cons (num (tt * ub)) (encS bit s₀)))
      (tt * (ub * 62 + 100) + ((slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum) + 200) := by
    refine (h4.replace ?_).mono (by omega)
    rw [hs₀]
    split_ifs <;> simp
  have h6 := Does.lettE (G := F) (f := fun _ => runL θ (roleTab θ L p) (tt * ub) s₀) (enc' := encS bit)
    (d := κ * (tt * ub + 1)) h5 (fun _ _ => hF (tt * ub) s₀)
  have h7 := Does.letkT (G := roleEnd) (f := fun s => encT (putsL ub keys (List.ofFn fun j => (s.2.2 j).reverse ++ [true]) t))
    (d := nO * (κ' * (tt * ub) * 31 + 100) + ((keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum
      + 200)) h6 (by
      intro b hb
      obtain ⟨a, ha, r, hr, hbr⟩ := mem_bindL hb
      have h8 := hκ' (tt * ub) s₀ (fun j => rfl) r hr
      rw [hbr]
      have e1 : (List.ofFn fun j => listT ((r.2.2.2 j).map bit)) = (List.ofFn r.2.2.2).map ofBits := by
        rw [List.map_ofFn]
        congr 1
        funext j
        exact listT_ofBits _
      have e2 : (List.ofFn fun j => (r.2.2.2 j).reverse ++ [true]) =
          (List.ofFn r.2.2.2).map fun w => w.reverse ++ [true] := by
        rw [List.map_ofFn]
        rfl
      rw [e2]
      unfold encS
      rw [e1]
      have h9 := roleEnd_does (θ := θ) ub t (num tt) (keysT slots)
        (listT (List.ofFn fun i => ofBits (r.2.2.1 i))) (num r.2.1) keys (κ' * (tt * ub)) (List.ofFn r.2.2.2) (by
          intro w hw
          obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hw
          exact h8 j)
      rw [List.length_ofFn] at h9
      exact h9)
  refine (h7.replace ?_).mono ?_
  · unfold roleSem
    split_ifs
    · rw [bindL_single]
    · rfl
  · set Z := (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum
    set Y := (keys.map fun ks => (ks.map fun k => ub * 90 + k.length * 60 + 330).sum + 200).sum
    have a1 : nO * (κ' * (tt * ub) * 31 + 100) ≤ nO * (κ' * 31 + 100) * (tt * (ub + 1) + 1) := by
      have : tt * ub ≤ tt * (ub + 1) + 1 := by nlinarith
      calc nO * (κ' * (tt * ub) * 31 + 100) ≤ nO * (κ' * (tt * (ub + 1) + 1) * 31 + 100 * (tt * (ub + 1) + 1)) := by
            gcongr
            omega
        _ = _ := by ring
    have a2 : κ * (tt * ub + 1) ≤ κ * (tt * (ub + 1) + 1) := by gcongr; omega
    have a3 : tt * (ub * 62 + 100) ≤ 100 * (tt * (ub + 1)) := by nlinarith
    nlinarith [Nat.zero_le (κ * Z), Nat.zero_le (κ * Y), Nat.zero_le (nO * (κ' * 31 + 100) * Z),
      Nat.zero_le (nO * (κ' * 31 + 100) * Y)]

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program of a base party

The automaton is simulated (or the part of the input is taken); the letters of every tape are cut into segments for the
partners; the strings of the partners are cut into units.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section seg

/-- Items: flags and letters of a tape. -/
abbrev Item := List ℕ × List (List Bool)

/-- As a tree. -/
def encI (it : Item) : Tree := .cons (listT (it.1.map num)) (listT (it.2.map ofBits))

/-- Strings as a tree. -/
def encA (l : List (List Bool)) : Tree := listT (l.map ofBits)

variable (A) in
/-- One tape. -/
def segOne (sep : List Bool) (it : Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  (segRow sep it.1 accs it.2).map fun out => ((1 : A), out.reverse)

theorem length_segL (sep : List Bool) (m f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool))
    (hm : fs.length + rest.length ≤ m) :
    ∀ l ∈ segL sep f tk cur fs as rest out, l.length = fs.length + 1 + out.length := by
  induction m generalizing f tk cur fs as rest out with
  | zero =>
    intro l hl
    have h1 : fs = [] := List.length_eq_zero_iff.1 (by omega)
    have h2 : rest = [] := List.length_eq_zero_iff.1 (by omega)
    subst h1 h2
    rw [segL_eq] at hl
    simp only [closeL, takeL, List.append_nil, if_true] at hl
    split_ifs at hl
    · rw [List.mem_singleton] at hl
      subst hl
      simp
      omega
    · simp at hl
  | succ m ih =>
    intro l hl
    rw [segL_eq, List.mem_append] at hl
    rcases hl with hl | hl
    · split_ifs at hl
      · unfold closeL at hl
        cases fs with
        | nil =>
          simp only at hl
          split_ifs at hl
          · rw [List.mem_singleton] at hl
            subst hl
            simp
            omega
          · simp at hl
        | cons f' fs' =>
          have := ih f' false _ fs' as.tail rest (cur :: out) (by simp only [List.length_cons] at hm; omega) l hl
          simp only [List.length_cons] at this ⊢
          omega
      · simp at hl
    · unfold takeL at hl
      cases rest with
      | nil => simp at hl
      | cons a r => exact ih f true _ fs as r out (by simp only [List.length_cons] at hm; omega) l hl

theorem length_segRow {sep : List Bool} {fl : List ℕ} {accs l : List (List Bool)} :
    ∀ out ∈ segRow sep fl accs l, out.length = fl.length := by
  intro out hout
  cases fl with
  | nil => simp [segRow] at hout
  | cons f fs =>
    have := length_segL sep _ f false _ fs accs.tail l [] le_rfl out hout
    simpa using this

/-- Step: argument ((flags, letters), strings). -/
def segStepF (sep : List Bool) : Fm := .ite (.hd (.hd .id))
  (lett (app (segB sep).code (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
    (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
      (.cons (.tl (.hd .id)) (.quote .nil))))))))) (foldF .id (.quote .nil) .id)) .fail

theorem segStepF_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (it : Item) (accs : List (List Bool))
    (hc : ∀ a ∈ it.2, a.length ≤ c) : Does θ (segStepF sep) (.cons (encI it) (encA accs))
      ((segOne A sep it accs).map (Prod.map id encA)) ((62 * c + 700) * (it.1.length + it.2.length + 1)) := by
  obtain ⟨fl, l⟩ := it
  set x : Tree := .cons (encI (fl, l)) (encA accs) with hx
  cases fl with
  | nil =>
    refine ((Does.ite_false (Gives.id _).hd.hd (Does.fail _)).replace ?_).mono ?_
    · simp [segOne, segRow]
    · simp only [List.length_nil]
      nlinarith
  | cons f fs =>
    have e1 : Gives θ (appF (.quote (ofBits sep)) (.hd (.tl .id))) x (ofBits (sep ++ accs.headD []))
        (1 + 3 + sep.length * 62 + 41) := by
      refine appB_gives (Gives.quote _ _) ?_
      rw [← listB_hd]
      exact (Gives.id _).tl.hd
    have e2 : Gives θ (.tl (.tl .id)) x (listT (accs.tail.map ofBits)) 3 := by
      rw [← listB_tl]
      exact (Gives.id _).tl.tl
    have e3 : Gives θ (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
        (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
        (.cons (.tl (.hd .id)) (.quote .nil)))))))) x
        (.cons (segB sep).code (segS f false (sep ++ accs.headD []) fs accs.tail l [])) (62 * c + 100) :=
      (Gives.cons (Gives.quote _ _) (Gives.cons (Gives.id _).hd.hd.hd (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons (Gives.id _).hd.hd.tl (Gives.cons e2 (Gives.cons (Gives.id _).hd.tl (Gives.quote _ _)))))))).mono
        (by omega)
    have e4 := segB_does (θ := θ) sep c hsep (fs.length + l.length) f false (sep ++ accs.headD []) fs accs.tail l [] le_rfl hc
    have e5 := Does.appT (p := (segB sep).code) (l := [((1 : A), ())])
      (enc := fun _ => .cons (segB sep).code (segS f false (sep ++ accs.headD []) fs accs.tail l []))
      (f := fun _ => encL (segL sep f false (sep ++ accs.headD []) fs accs.tail l [])) e3 (fun b _ => by
        rw [Fm.ofTree_code]
        exact e4)
    rw [bindL_single] at e5
    have e6 : Does θ (app (segB sep).code (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
        (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
        (.cons (.tl (.hd .id)) (.quote .nil))))))))) x
        (((segRow sep (f :: fs) accs l).map fun out => ((1 : A), out)).map (Prod.map id encA)) _ := e5.replace (by
      rw [List.map_map]
      rfl)
    have e7 := Does.lettE (G := foldF .id (.quote .nil) .id) (f := fun out => [((1 : A), out.reverse)]) (enc' := encA)
      (d := (fs.length + 1) * 31 + 30) e6 (fun b hb => by
        obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hb
        have h1 := length_segRow out hout
        have := rev_gives (θ := θ) (x := encA out) (ys := []) (xs := out.map ofBits) (s := .quote .nil) (l := .id)
          (Gives.quote _ _) (Gives.id _)
        rw [List.append_nil, ← List.map_reverse, List.length_map, h1, List.length_cons] at this
        exact this.mono (by omega))
    have hne : x.hd.hd ≠ .nil := by simp [hx, encI, listT]
    refine ((Does.ite_true (Gives.id x).hd.hd hne e7).replace ?_).mono ?_
    · congr 1
      rw [bindL_pure _ (fun out => out)]
      simp [segOne, flatMap_single]
    · simp only [List.length_cons]
      nlinarith

variable (A) in
/-- Several tapes (the last one first). -/
def segsL (sep : List Bool) (items : List Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  foldL (segOne A sep) items accs

/-- Several tapes: argument (items, strings). -/
def segsF (sep : List Bool) : Fm := foldF (segStepF sep) (.tl .id) (.hd .id)

theorem segsF_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (items : List Item) (accs : List (List Bool))
    (hc : ∀ it ∈ items, ∀ a ∈ it.2, a.length ≤ c) : Does θ (segsF sep) (.cons (listT (items.map encI)) (encA accs))
      ((segsL A sep items accs).map (Prod.map id encA))
      ((items.map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum + 30) := by
  have := foldT (θ := θ) (A := A) (encE := encI) (xs := items) (enc := encA) (s₀ := accs) (f := segOne A sep)
    (Inv := fun _ _ => True) (d := fun it => (62 * c + 700) * (it.1.length + it.2.length + 1)) (step := segStepF sep)
    (s := .tl .id) (l := .hd .id) (x := .cons (listT (items.map encI)) (encA accs)) (Gives.id _).tl (Gives.id _).hd
    (fun it _ accs hit _ => ⟨segStepF_does sep c hsep it accs (hc it hit), fun _ _ => trivial⟩) trivial
  exact this.mono (by omega)

end seg

end Nc.Grp

end

section










set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section sim

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)


noncomputable def tapes (S : Type) [Fintype S] [DecidableEq S] : List (Option S) := (univ : Finset (Option S)).toList


noncomputable abbrev nT (S : Type) [Fintype S] [DecidableEq S] : ℕ := (tapes S).length


def chOf : Ch S Unit → Option S × Bool
  | .tp s b => (some s, b)
  | .inp _ => (none, true)


noncomputable def outOf (j : Fin (nT S + nT S)) : Option S × Bool :=
  Fin.addCases (motive := fun _ => Option S × Bool) (fun i => ((tapes S).get i, false)) (fun i => ((tapes S).get i, true)) j


def code (a : Γ) : List Bool := List.ofFn (cb (some a))


noncomputable def pushOf (z : Letter S Unit Γ) (j : Fin (nT S + nT S)) : List (List Bool) :=
  match z with
  | none => []
  | some (ch, a) => if chOf ch = outOf j then [code cb a] else []




variable (θ) in

noncomputable def simTab (q : Fin (Fintype.card Q)) (_ : Fin 0 → Bool) :
    List (Opt (Fintype.card Q) (nT S + nT S) (List Bool)) :=
  (univ : Finset (Letter S Unit Γ × Q)).toList.map fun z => ⟨we θ (mu z.1 ((qn Q).symm q) z.2), qn Q z.2, pushOf cb z.1⟩


abbrev Outs (S : Type) [Fintype S] [DecidableEq S] := Fin (nT S + nT S) → List (List Bool)


noncomputable def encO (o : Outs S) : Tree := listT (List.ofFn fun j => listT ((o j).map ofBits))

variable (θ) in

noncomputable def simSem (T : ℕ) (q q' : Fin (Fintype.card Q)) : List (A × Outs S) :=
  bindL (runL θ (simTab θ mu cb) T (q, Fin.elim0, fun _ => [])) fun s => if s.1 = q' then [((1 : A), s.2.2)] else []

theorem num_injective : Function.Injective num := by
  intro a b h
  rw [← len_num a, h, len_num]

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [num, size, ih]
    omega


theorem ex_sim : ∃ F κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)),
    Does θ F (.cons (num T) (.cons (num q) (num q'))) ((simSem θ mu cb T q q').map (Prod.map id encO)) (κ * (T + 1)) := by
  obtain ⟨F, κ, hF⟩ := ex_run (θ := θ) ofBits (simTab θ mu cb)
  refine ⟨lett (.cons .id (lett (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
    (.quote (listT (List.replicate (nT S + nT S) .nil)))))) F))
    (.ite (eqF (.hd (.tl .id)) (.tl (.tl (.hd .id)))) (.tl (.tl (.tl .id))) .fail),
    κ + 120 * Fintype.card Q + 300, fun T q q' => ?_⟩
  set x : Tree := .cons (num T) (.cons (num q) (num q')) with hx
  let s₀ : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool) := (q, Fin.elim0, fun _ => [])
  have hs₀ : encS ofBits s₀ = .cons (num q) (.cons .nil (listT (List.replicate (nT S + nT S) .nil))) := by
    have e2 : (List.ofFn fun _ : Fin (nT S + nT S) => listT (([] : List (List Bool)).map ofBits)) =
        List.replicate (nT S + nT S) .nil := by
      rw [List.ofFn_const]
      rfl
    simp only [encS, s₀, e2]
    rfl
  have h1 : Gives θ (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
      (.quote (listT (List.replicate (nT S + nT S) .nil)))))) x (.cons (num T) (encS ofBits s₀)) 20 := by
    rw [hs₀]
    exact (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.quote _ _)
      (Gives.quote _ _)))).mono (by omega)
  have h2 := Does.of_gives h1 (hF T s₀)
  have h3 := Does.letkT (G := .ite (eqF (.hd (.tl .id)) (.tl (.tl (.hd .id)))) (.tl (.tl (.tl .id))) .fail)
    (f := fun s => (if s.1 = q' then [((1 : A), s.2.2)] else []).map (Prod.map id encO))
    (d := 120 * Fintype.card Q + 200) h2 (by
      rintro ⟨a, s⟩ -
      simp only
      have e1 := eqF_gives (θ := θ) (x := .cons x (encS ofBits s)) (a := .hd (.tl .id)) (b := .tl (.tl (.hd .id)))
        (u := num s.1) (v := num q') (Gives.id _).tl.hd (Gives.id _).hd.tl.tl
      have hs := s.1.2
      rw [size_num] at e1
      by_cases h : s.1 = q'
      · have e2 : bit (decide (num s.1 = num q')) ≠ .nil := by simp [h, bit, one]
        refine ((Does.ite_true (H := .fail) e1 e2 (Gives.id _).tl.tl.tl).replace ?_).mono (by omega)
        rw [if_pos h]
        rfl
      · have e2 : bit (decide (num s.1 = num q')) = .nil := by
          have : num s.1 ≠ num q' := fun h' => h (Fin.ext (num_injective h'))
          simp [this, bit]
        rw [e2] at e1
        refine ((Does.ite_false e1 (Does.fail _)).replace ?_).mono (by omega)
        rw [if_neg h]
        rfl)
  rw [bindL_map] at h3
  refine h3.mono ?_
  nlinarith

theorem length_of_mem_pushOf {z : Letter S Unit Γ} {j : Fin (nT S + nT S)} {a : List Bool} (ha : a ∈ pushOf cb z j) :
    a.length ≤ c := by
  cases z with
  | none => simp [pushOf] at ha
  | some z =>
    obtain ⟨ch, x⟩ := z
    simp only [pushOf] at ha
    split_ifs at ha
    · rw [List.mem_singleton] at ha
      subst ha
      simp [code]
    · simp at ha


theorem exists_simSem_length : ∃ κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)), ∀ r ∈ simSem θ mu cb T q q',
    (∀ j, (r.2 j).length ≤ κ * T) ∧ ∀ j, ∀ a ∈ r.2 j, a.length ≤ c := by
  obtain ⟨κ, hκ⟩ := exists_runL_length (θ := θ) (simTab θ mu cb)
  refine ⟨κ, fun T q q' r hr => ?_⟩
  obtain ⟨s, hs, z, hz, hrz⟩ := mem_bindL hr
  have h1 := hκ T (q, Fin.elim0, fun _ => []) (fun _ => rfl) s hs
  have h2 := mem_foldL_induct (f := fun (_ : Unit) s => stepL θ (simTab θ mu cb) s) (xs := List.replicate T ())
    (Inv := fun _ s => ∀ j, ∀ a ∈ s.2.2 j, a.length ≤ c) (m := 0) (s := (q, Fin.elim0, fun _ => []))
    (fun x _ s m hm q hq j a ha => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 ho
      rcases List.mem_append.1 ha with ha | ha
      · exact length_of_mem_pushOf cb ha
      · exact hm j a ha) (fun j a ha => by simp at ha) s hs
  split_ifs at hz
  · rw [List.mem_singleton] at hz
    subst hz
    rw [hrz]
    exact ⟨h1, h2⟩
  · simp at hz


noncomputable def inOuts (part : List (List Bool)) : Outs S := fun j => if outOf j = (none, false) then part else []


theorem ex_inOuts : ∃ F : Fm → Fm, ∃ κ, ∀ (p : Fm) (x : Tree) (part : List (List Bool)) (cp : ℕ),
    Gives θ p x (listT (part.map ofBits)) cp → Gives θ (F p) x (encO (inOuts (S := S) part)) (κ * (cp + 1)) := by
  refine ⟨fun p => mkList (List.ofFn fun j : Fin (nT S + nT S) => if outOf j = (none, false) then p else .quote .nil),
    2 * (nT S + nT S) + 2, fun p x part cp hp => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S + nT S) (c := cp + 1)
    (f := fun j => if outOf j = (none, false) then p else .quote .nil)
    (o := fun j => listT ((inOuts (S := S) part j).map ofBits)) (fun j => by
      by_cases h : outOf j = ((none : Option S), false)
      · simp only [inOuts, h, if_true]
        exact hp.mono (by omega)
      · simp only [inOuts, h, if_false]
        exact (Gives.quote _ _).mono (by omega))
  refine h1.mono ?_
  nlinarith

section pack


noncomputable def itemsR (flags : List (List ℕ)) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (flags.getD i.rev [], o (Fin.castAdd (nT S) i.rev))


noncomputable def itemsC (m : ℕ) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (List.replicate m 2, o (Fin.natAdd (nT S) i.rev))

theorem itemsR_gives : ∃ G : Fm → Fm → Fm, ∃ κ, ∀ (a b : Fm) (x : Tree) (flags : List (List ℕ)) (o : Outs S) (ca cb : ℕ),
    Gives θ a x (listT (flags.map fun l => listT (l.map num))) ca → Gives θ b x (encO o) cb →
    Gives θ (G a b) x (listT ((itemsR flags o).map encI)) (κ * (ca + cb + 1)) := by
  refine ⟨fun a b => mkList (List.ofFn fun i : Fin (nT S) => .cons (nthF i.rev a) (nthF i.rev b)),
    nT S * (2 * nT S + 10) + 1, fun a b x flags o ca cb ha hb => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S) (c := ca + cb + 2 * nT S + 5)
    (f := fun i : Fin (nT S) => .cons (nthF i.rev a) (nthF i.rev b))
    (o := fun i => encI (flags.getD i.rev [], o (Fin.castAdd (nT S) i.rev))) (fun i => by
      have h2 := nthF_gives (i.rev : ℕ) ha
      have e2 : (flags.map fun l => listT (l.map num)).getD (i.rev : ℕ) .nil = listT ((flags.getD i.rev []).map num) := by
        rw [show (.nil : Tree) = (fun l : List ℕ => listT (l.map num)) [] from rfl, List.getD_map]
      rw [e2] at h2
      have h3 := nthF_gives (i.rev : ℕ) hb
      have e3 : (List.ofFn fun j => listT ((o j).map ofBits)).getD (i.rev : ℕ) .nil =
          listT ((o (Fin.castAdd (nT S) i.rev)).map ofBits) := by
        have hlt : (i.rev : ℕ) < (List.ofFn fun j => listT ((o j).map ofBits)).length := by
          rw [List.length_ofFn]
          have := i.rev.2
          omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      rw [e3] at h3
      have := i.rev.2
      exact (Gives.cons h2 h3).mono (by omega))
  rw [itemsR, List.map_ofFn]
  refine h1.mono ?_
  nlinarith [Nat.zero_le (nT S * nT S * (ca + cb)), Nat.zero_le (nT S * (ca + cb))]

theorem itemsC_gives : ∃ G : Fm → Fm → Fm, ∃ κ, ∀ (a b : Fm) (x : Tree) (m : ℕ) (o : Outs S) (ca cb : ℕ),
    Gives θ a x (listT ((List.replicate m 2).map num)) ca → Gives θ b x (encO o) cb →
    Gives θ (G a b) x (listT ((itemsC m o).map encI)) (κ * (ca + cb + 1)) := by
  refine ⟨fun a b => mkList (List.ofFn fun i : Fin (nT S) => .cons a (nthF (nT S + i.rev) b)),
    nT S * (2 * nT S + 10) + 1, fun a b x m o ca cb ha hb => ?_⟩
  have h1 := mkList_gives (θ := θ) (x := x) (m := nT S) (c := ca + cb + 2 * nT S + 5)
    (f := fun i : Fin (nT S) => .cons a (nthF (nT S + i.rev) b))
    (o := fun i => encI (List.replicate m 2, o (Fin.natAdd (nT S) i.rev))) (fun i => by
      have h3 := nthF_gives (nT S + i.rev : ℕ) hb
      have e3 : (List.ofFn fun j => listT ((o j).map ofBits)).getD (nT S + i.rev : ℕ) .nil =
          listT ((o (Fin.natAdd (nT S) i.rev)).map ofBits) := by
        have hlt : (nT S + i.rev : ℕ) < (List.ofFn fun j => listT ((o j).map ofBits)).length := by
          rw [List.length_ofFn]
          have := i.rev.2
          omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rfl
      rw [e3] at h3
      have := i.rev.2
      exact (Gives.cons ha h3).mono (by omega))
  rw [itemsC, List.map_ofFn]
  refine h1.mono ?_
  nlinarith [Nat.zero_le (nT S * nT S * (ca + cb)), Nat.zero_le (nT S * (ca + cb))]

end pack

end sim

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over simulations
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem sumL_toList {X β : Type} [Fintype X] (f : X → A × β) (G : β → A) :
    sumL ((univ : Finset X).toList.map f) G = ∑ x, (f x).1 * G (f x).2 := by
  rw [sumL, List.map_map, Finset.sum_map_toList]
  rfl

theorem sumL_runL_succ {Λ : Type} {nC nI nO : ℕ} (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (k : ℕ)
    (s : TSt nC nI nO Λ) (G : TSt nC nI nO Λ → A) :
    sumL (runL θ tab (k + 1) s) G = sumL (stepL θ tab s) fun s' => sumL (runL θ tab k s') G := by
  rw [runL, List.replicate_succ, foldL, sumL_bindL]
  rfl

theorem foldL_append {β ε : Type} (f : ε → β → List (A × β)) (xs ys : List ε) (s : β) (G : β → A) :
    sumL (foldL f (xs ++ ys) s) G = sumL (foldL f xs s) fun s' => sumL (foldL f ys s') G := by
  induction xs generalizing s with
  | nil => rw [List.nil_append, foldL, sumL_single]
  | cons x xs ih =>
    rw [List.cons_append, foldL, foldL, sumL_bindL, sumL_bindL]
    exact sumL_congr fun p _ => ih _

section sim

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)

theorem sumL_sim (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (k : ℕ) (q : Q) (f : Outs S)
    (G : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool) → A) :
    sumL (runL θ (simTab θ mu cb) k (qn Q q, Fin.elim0, f)) G = ∑ o : Fin k → Letter S Unit Γ, ∑ q' : Q,
      ((List.ofFn o).map mu).prod q q' * G (qn Q q', Fin.elim0, fun j =>
        (List.ofFn o).reverse.flatMap (fun z => pushOf cb z j) ++ f j) := by
  induction k generalizing q f with
  | zero =>
    rw [runL, List.replicate_zero, foldL, sumL_single, Fintype.sum_unique]
    simp only [List.ofFn_zero, List.map_nil, List.prod_nil, List.reverse_nil, List.flatMap_nil, List.nil_append]
    rw [Finset.sum_eq_single q]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro q' _ hq'
      rw [Matrix.one_apply_ne hq'.symm, zero_mul]
    · simp
  | succ k ih =>
    rw [sumL_runL_succ]
    have h1 : sumL (stepL θ (simTab θ mu cb) (qn Q q, Fin.elim0, f)) (fun s' => sumL (runL θ (simTab θ mu cb) k s') G) =
        ∑ z : Letter S Unit Γ × Q, mu z.1 q z.2 * sumL (runL θ (simTab θ mu cb) k (qn Q z.2, Fin.elim0, fun j =>
          pushOf cb z.1 j ++ f j)) G := by
      rw [stepL, simTab, List.map_map, sumL_toList]
      refine Finset.sum_congr rfl fun z _ => ?_
      have e0 : (fun i : Fin 0 => ((Fin.elim0 : Fin 0 → List Bool) i).tail) = Fin.elim0 := funext fun i => i.elim0
      simp only [Function.comp_apply, Opt.app, e0, Equiv.symm_apply_apply, we_val (hmu _ _ _)]
    rw [h1, Fintype.sum_prod_type, ← (Fin.consEquiv fun _ : Fin (k + 1) => Letter S Unit Γ).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [ih]
    have h2 : ∀ o : Fin k → Letter S Unit Γ, (List.ofFn ((Fin.consEquiv fun _ : Fin (k + 1) => Letter S Unit Γ) (z, o))) =
        z :: List.ofFn o := by
      intro o
      rw [List.ofFn_succ]
      rfl
    simp only [h2, List.map_cons, List.prod_cons, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, List.reverse_cons,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm]

/-- The output lists of a run. -/
noncomputable def outsOf (w : List (Letter S Unit Γ)) : Outs S := fun j => w.reverse.flatMap fun z => pushOf cb z j

theorem sumL_simSem (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (T : ℕ) (q q' : Q) (G : Outs S → A) :
    sumL (simSem θ mu cb T (qn Q q) (qn Q q')) G = ∑ o : Fin T → Letter S Unit Γ,
      ((List.ofFn o).map mu).prod q q' * G (outsOf cb (List.ofFn o)) := by
  rw [simSem, sumL_bindL, sumL_sim mu cb hmu]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single q']
  · simp only [if_true, sumL_single, List.append_nil]
    rfl
  · intro q'' _ h
    have : qn Q q'' ≠ qn Q q' := fun h' => h ((qn Q).injective h')
    simp [this]
  · simp

theorem length_pushOf (z : Letter S Unit Γ) (j : Fin (nT S + nT S)) : (pushOf cb z j).reverse = pushOf cb z j := by
  unfold pushOf
  split
  · rfl
  · split_ifs <;> rfl

theorem outsOf_eq (w : List (Letter S Unit Γ)) (j : Fin (nT S + nT S)) :
    outsOf cb w j = (w.flatMap fun z => pushOf cb z j).reverse := by
  unfold outsOf
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [List.reverse_cons, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.reverse_append, length_pushOf]

theorem chOf_injective : Function.Injective (chOf (S := S)) := by
  rintro (⟨s, b⟩ | ⟨u⟩) (⟨s', b'⟩ | ⟨u'⟩) h
  · simp only [chOf, Prod.mk.injEq, Option.some.injEq] at h
    rw [h.1, h.2]
  · simp [chOf] at h
  · simp [chOf] at h
  · rfl

theorem flatMap_pushOf (w : List (Letter S Unit Γ)) {j : Fin (nT S + nT S)} {ch : Ch S Unit} (h : chOf ch = outOf j) :
    (w.flatMap fun z => pushOf cb z j) = (emit w ch).map (code cb) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [List.flatMap_cons, ih]
    cases z with
    | none => rfl
    | some a =>
      obtain ⟨ch', a⟩ := a
      have e1 : emit (some (ch', a) :: w) ch = if ch' = ch then a :: emit w ch else emit w ch := by
        simp only [emit, List.reduceOption_cons_of_some, proj_cons]
      rw [e1]
      by_cases hch : ch' = ch
      · subst hch
        simp [pushOf, h]
      · have : chOf ch' ≠ outOf j := fun h' => hch (chOf_injective (h'.trans h.symm))
        simp [pushOf, this, hch]

theorem flatMap_pushOf_none (w : List (Letter S Unit Γ)) {j : Fin (nT S + nT S)} (h : outOf j = ((none : Option S), false)) :
    (w.flatMap fun z => pushOf cb z j) = [] := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [List.flatMap_cons, ih, List.append_nil]
    cases z with
    | none => rfl
    | some a =>
      obtain ⟨ch', a⟩ := a
      have : chOf ch' ≠ outOf j := by
        rw [h]
        cases ch' <;> simp [chOf]
      simp [pushOf, this]

/-- What a run writes and reads on a tape. -/
def wr (w : List (Letter S Unit Γ)) : Option S → List Γ
  | none => []
  | some s => emit w (.tp s false)

/-- What a run reads. -/
def rdr (w : List (Letter S Unit Γ)) : Option S → List Γ
  | none => emit w (.inp ())
  | some s => emit w (.tp s true)

theorem outsOf_left (w : List (Letter S Unit Γ)) (i : Fin (nT S)) :
    outsOf cb w (Fin.castAdd (nT S) i) = ((wr w ((tapes S).get i)).map (code cb)).reverse := by
  rw [outsOf_eq]
  congr 1
  have h : outOf (Fin.castAdd (nT S) i) = ((tapes S).get i, false) := by
    rw [outOf, Fin.addCases_left]
  generalize hs : (tapes S).get i = s at h
  cases s with
  | none => exact flatMap_pushOf_none cb w h
  | some s => exact flatMap_pushOf cb w (ch := .tp s false) h.symm

theorem outsOf_right (w : List (Letter S Unit Γ)) (i : Fin (nT S)) :
    outsOf cb w (Fin.natAdd (nT S) i) = ((rdr w ((tapes S).get i)).map (code cb)).reverse := by
  rw [outsOf_eq]
  congr 1
  have h : outOf (Fin.natAdd (nT S) i) = ((tapes S).get i, true) := by
    rw [outOf, Fin.addCases_right]
  generalize hs : (tapes S).get i = s at h
  cases s with
  | none => exact flatMap_pushOf cb w (ch := .inp ()) h.symm
  | some s => exact flatMap_pushOf cb w (ch := .tp s true) h.symm

theorem inOuts_left (u : List Γ) (i : Fin (nT S)) :
    inOuts (S := S) (u.map (code cb)).reverse (Fin.castAdd (nT S) i) =
      (((if (tapes S).get i = none then u else []) : List Γ).map (code cb)).reverse := by
  have h : outOf (Fin.castAdd (nT S) i) = ((tapes S).get i, false) := by
    rw [outOf, Fin.addCases_left]
  rw [inOuts, h]
  by_cases hs : (tapes S).get i = none
  · rw [if_pos (by rw [hs]), if_pos hs]
  · rw [if_neg (fun h' => hs (Prod.ext_iff.1 h').1), if_neg hs]
    rfl

theorem inOuts_right (u : List Γ) (i : Fin (nT S)) :
    inOuts (S := S) (u.map (code cb)).reverse (Fin.natAdd (nT S) i) = (([] : List Γ).map (code cb)).reverse := by
  have h : outOf (Fin.natAdd (nT S) i) = ((tapes S).get i, true) := by
    rw [outOf, Fin.addCases_right]
  rw [inOuts, h]
  simp

end sim

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over the ways to cut the letters of all tapes
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {A : Type} [CommRing A]

/-- Functions with values in a finite set. -/
theorem sum_pi_coe {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (s : Finset β) (f : (ι → β) → A) :
    ∑ x ∈ Fintype.piFinset fun _ : ι => s, f x = ∑ x : ι → s, f fun i => (x i : β) := by
  symm
  refine Finset.sum_bij (fun (x : ι → s) _ => fun i => (x i : β)) ?_ ?_ ?_ ?_
  · intro x _
    exact Fintype.mem_piFinset.2 fun i => (x i).2
  · intro x _ y _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro y hy
    exact ⟨fun i => ⟨y i, Fintype.mem_piFinset.1 hy i⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- Words of length at most `T`, as a type. -/
abbrev Wt (Γ : Type) [Fintype Γ] [DecidableEq Γ] (T : ℕ) := ↥(wordsLe Γ T)

/-- The string of a partner. -/
def joined (bits : Γ → List Bool) (sep : List Bool) {N : ℕ} (X : Fin N → List Γ) : List Bool :=
  (List.ofFn fun i => (X i).flatMap bits ++ sep).flatten

theorem joined_snoc (bits : Γ → List Bool) (sep : List Bool) {N : ℕ} (X : Fin N → List Γ) (y : List Γ) :
    joined bits sep (Fin.snoc X y : Fin (N + 1) → List Γ) = joined bits sep X ++ (y.flatMap bits ++ sep) := by
  simp only [joined, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The condition on the segments of a tape. -/
def CutOk {m : ℕ} (fl : Fin m → ℕ) (l : List Γ) (X : Fin m → List Γ) : Prop :=
  cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true

instance {m : ℕ} (fl : Fin m → ℕ) (l : List Γ) (X : Fin m → List Γ) : Decidable (CutOk fl l X) := by
  unfold CutOk
  infer_instance

/-- One tape. -/
theorem sumL_segOne (sep : List Bool) {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (bits : Γ → List Bool) (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (G : List (List Bool) → A) :
    sumL (segOne A sep ((List.ofFn fl).reverse, (l.map bits).reverse) (List.ofFn acc).reverse) G =
      ∑ X : Fin m → Wt Γ T, if CutOk fl l (fun b => (X b : List Γ)) then
        G (List.ofFn fun b => (X b : List Γ).flatMap bits ++ (sep ++ acc b)).reverse else 0 := by
  have h := sum_segRow' sep hm fl acc bits T l hT fun out => G out.reverse
  rw [Finset.sum_filter, sum_pi_coe] at h
  rw [sumL, segOne, List.map_map]
  simp only [Function.comp_def, one_mul]
  rw [h]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : CutOk fl l (fun b => (X b : List Γ))
  · exact (if_pos hX).trans (if_pos hX).symm
  · exact (if_neg hX).trans (if_neg hX).symm

/-- **All tapes.** -/
theorem sumL_segs (sep : List Bool) {m : ℕ} (hm : 0 < m) (bits : Γ → List Bool) (T : ℕ) {N : ℕ} (fl : Fin N → Fin m → ℕ)
    (l : Fin N → List Γ) (hT : ∀ i, (l i).length ≤ T) (acc : Fin m → List Bool) (G : List (List Bool) → A) :
    sumL (segsL A sep (List.ofFn fun i : Fin N => ((List.ofFn (fl i.rev)).reverse, ((l i.rev).map bits).reverse))
        (List.ofFn acc).reverse) G =
      ∑ X : Fin N → Fin m → Wt Γ T, if ∀ i, CutOk (fl i) (l i) (fun b => (X i b : List Γ)) then
        G (List.ofFn fun b => joined bits sep (fun i => (X i b : List Γ)) ++ acc b).reverse else 0 := by
  induction N generalizing acc with
  | zero =>
    rw [List.ofFn_zero, segsL, foldL, sumL_single, Fintype.sum_unique, if_pos fun i => i.elim0]
    rfl
  | succ N ih =>
    rw [List.ofFn_succ, segsL, foldL, sumL_bindL]
    have e0 : (0 : Fin (N + 1)).rev = Fin.last N := Fin.rev_zero N
    have e1 : (List.ofFn fun i : Fin N => ((List.ofFn (fl i.succ.rev)).reverse, ((l i.succ.rev).map bits).reverse)) =
        List.ofFn fun i : Fin N => ((List.ofFn (fl i.rev.castSucc)).reverse, ((l i.rev.castSucc).map bits).reverse) := by
      congr 1
      funext i
      rw [Fin.rev_succ]
    rw [e0, e1, sumL_segOne sep hm (fl (Fin.last N)) acc bits T (l (Fin.last N)) (hT _)]
    rw [← (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : CutOk (fl (Fin.last N)) (l (Fin.last N)) (fun b => (Y b : List Γ))
    · rw [if_pos hY]
      have h2 := ih (fun i => fl i.castSucc) (fun i => l i.castSucc) (fun i => hT _)
        (fun b => (Y b : List Γ).flatMap bits ++ (sep ++ acc b))
      rw [segsL] at h2
      rw [h2]
      refine Finset.sum_congr rfl fun X _ => ?_
      have e2 : (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X) = Fin.snoc X Y := rfl
      have e3 : (∀ i, CutOk (fl i) (l i) fun b =>
          (((Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X)) i b : List Γ)) ↔
          ∀ i : Fin N, CutOk (fl i.castSucc) (l i.castSucc) fun b => (X i b : List Γ) := by
        rw [e2]
        constructor
        · intro h i
          have := h i.castSucc
          simpa only [Fin.snoc_castSucc] using this
        · intro h i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simpa only [Fin.snoc_last] using hY
          · simpa only [Fin.snoc_castSucc] using h i
      have e4 : ∀ b, (fun i => (((Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X)) i b : List Γ)) =
          (Fin.snoc (fun i => (X i b : List Γ)) (Y b : List Γ) : Fin (N + 1) → List Γ) := by
        intro b
        rw [e2]
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last, Fin.snoc_last]
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      refine if_congr e3.symm ?_ rfl
      congr 2
      congr 1
      funext b
      rw [e4, joined_snoc]
      simp only [List.append_assoc]
    · rw [if_neg hY]
      symm
      refine Finset.sum_eq_zero fun X _ => if_neg fun h => hY ?_
      have := h (Fin.last N)
      have e2 : (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X) = Fin.snoc X Y := rfl
      rw [e2] at this
      simpa only [Fin.snoc_last] using this

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Writing the units of a string into a store
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

theorem putAll_congr (keys : List (List Bool)) {u u' : ℕ → List Bool} (t : Tree)
    (h : ∀ i < keys.length, u i = u' i) : putAll keys u t = putAll keys u' t := by
  induction keys generalizing u u' t with
  | nil => rfl
  | cons k ks ih =>
    simp only [putAll]
    rw [h 0 (by simp)]
    exact ih _ fun i hi => h (i + 1) (by simpa using hi)

theorem padTake_eq (ub : ℕ) (r : List Bool) :
    padTake ub r = List.ofFn fun b : Fin ub => r.getD b false := by
  apply List.ext_getElem
  · simp only [padTake, List.length_append, List.length_take, List.length_replicate, List.length_ofFn]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD]
    simp only [padTake]
    by_cases hi : i < r.length
    · have h3 : i < ub := by simpa using h2
      rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem?_eq_getElem hi, Option.getD_some]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate, List.getElem?_eq_none (by omega),
        Option.getD_none]

theorem putL_gen {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    putL ub keys r t = if (r.length + ub - 1) / ub = keys.length then
      [putAll keys (fun k => List.ofFn fun b : Fin ub => r.getD (k * ub + b) false) t] else [] := by
  induction keys generalizing r t with
  | nil =>
    simp only [putL, putAll, List.length_nil]
    refine if_congr ?_ rfl rfl
    rw [Nat.div_eq_zero_iff, ← List.length_eq_zero_iff]
    omega
  | cons k ks ih =>
    rw [putL]
    by_cases hr : r = []
    · subst hr
      rw [if_pos rfl, if_neg]
      rw [List.length_nil, zero_add, Nat.div_eq_of_lt (by omega)]
      simp
    · rw [if_neg hr, ih]
      have hl : 0 < r.length := List.length_pos_iff.2 hr
      have hc : (r.length + ub - 1) / ub = ((r.drop ub).length + ub - 1) / ub + 1 := by
        rw [List.length_drop]
        rcases le_or_gt ub r.length with h | h
        · have e1 : r.length + ub - 1 = (r.length - ub + ub - 1) + ub := by omega
          rw [e1, Nat.add_div_right _ hub]
        · have e1 : r.length - ub + ub - 1 = ub - 1 := by omega
          have e2 : r.length + ub - 1 = r.length - 1 + ub := by omega
          rw [e1, e2, Nat.add_div_right _ hub, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
      refine if_congr ?_ ?_ rfl
      · rw [hc, List.length_cons]
        omega
      · simp only [putAll, zero_mul, zero_add, padTake_eq]
        congr 1
        refine putAll_congr _ _ fun i _ => ?_
        congr 1
        funext b
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2
        ring

theorem putL_eq {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (L : List Bool) (t : Tree) :
    putL ub keys (L ++ [true]) t = if ucount ub L = keys.length then
      [putAll keys (fun k => uwBits (unitsOf ub L k)) t] else [] := by
  rw [putL_gen hub]
  have hc : ((L ++ [true]).length + ub - 1) / ub = ucount ub L := by
    have e : (L ++ [true]).length + ub - 1 = L.length + ub := by simp
    rw [e, Nat.add_div_right _ hub, ucount]
  rw [hc]
  split_ifs with h
  · congr 1
    refine putAll_congr _ _ fun i hi => ?_
    rw [unitsOf, if_pos (by omega)]
    rfl
  · rfl

theorem tget_putAll (keys : List (List Bool)) (hk : keys.Nodup) (u : ℕ → List Bool) (t : Tree) (p : List Bool) :
    tget p (putAll keys u t) = if p ∈ keys then ofBits (u (keys.idxOf p)) else tget p t := by
  induction keys generalizing u t with
  | nil => simp [putAll]
  | cons k ks ih =>
    rw [List.nodup_cons] at hk
    rw [putAll, ih hk.2, tget_tset]
    by_cases h1 : p ∈ ks
    · have hne : k ≠ p := fun h => hk.1 (h ▸ h1)
      rw [if_pos h1, if_pos (List.mem_cons_of_mem _ h1), List.idxOf_cons_ne _ hne]
    · rw [if_neg h1]
      by_cases h2 : p = k
      · subst h2
        rw [if_pos rfl, if_pos List.mem_cons_self, List.idxOf_cons_self]
      · rw [if_neg h2, if_neg (by simp [h1, h2])]

end Nc.Grp

end

section










set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {S : Type} [Fintype S] [DecidableEq S]

variable (A) in

noncomputable def packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) : List (A × Tree) :=
  bindL (segsL A sep (itemsR B.flags o) (List.replicate B.kR.length [true])) fun sR =>
    bindL (encT (A := A) (putsL ub B.kR sR.reverse t)) fun t1 =>
      bindL (segsL A sep (itemsC B.kR.length o) (List.replicate B.kR.length [true])) fun sC =>
        encT (putsL ub B.kC sC.reverse t1)







theorem length_getD_le (l : List (List ℕ)) (i : ℕ) : (l.getD i []).length ≤ flen l := by
  rcases lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, List.getElem_mem h, rfl⟩)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.zero_le _

theorem length_segsL {sep : List Bool} {items : List Item} {accs : List (List Bool)} {N : ℕ}
    (h : ∀ it ∈ items, it.1.length ≤ N) (ha : accs.length ≤ N) : ∀ r ∈ segsL A sep items accs, r.2.length ≤ N := by
  refine mem_foldL_induct (f := segOne A sep) (xs := items) (Inv := fun _ s => s.length ≤ N) (m := 0)
    (fun it hit s m _ q hq => ?_) ha
  obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hq
  have := length_segRow out hout
  have := h it hit
  simp only [List.length_reverse]
  omega

theorem row_gives (v : Tree) {k : Fm} {x : Tree} {ck : ℕ} {kss : List (List (List Bool))}
    (hk : Gives θ k x (keysT kss) ck) :
    Gives θ (mapF (.quote v) (.quote .nil) k) x (listT (List.replicate kss.length v)) (ck + kss.length * 41 + 21) := by
  have hk' : Gives θ k x (listT (kss.map fun ks => listT (ks.map ofBits))) ck := hk
  have := mapF_gives (θ := θ) (x := x) (step := .quote v) (ef := .quote .nil) (e := .nil) (l := k)
    (xs := kss.map fun ks => listT (ks.map ofBits)) (g := fun _ => v) (d := fun _ => 1) (Gives.quote _ _) hk'
    (fun _ _ => Gives.quote _ _)
  rw [List.map_map] at this
  simp only [Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at this
  exact this.mono (by omega)

theorem rev_encA {k : Fm} {x : Tree} {ck : ℕ} {l : List (List Bool)} (hk : Gives θ k x (encA l) ck) :
    Gives θ (foldF .id (.quote .nil) k) x (listT (l.reverse.map ofBits)) (ck + l.length * 31 + 21) := by
  have := rev_gives (θ := θ) (x := x) (ys := []) (xs := l.map ofBits) (s := .quote .nil) (l := k) (Gives.quote _ _) hk
  rw [List.append_nil, ← List.map_reverse, List.length_map] at this
  exact this.mono (by omega)

theorem sum_items_le {items : List Item} {n c N : ℕ} (hn : items.length = n)
    (h : ∀ it ∈ items, it.1.length + it.2.length + 1 ≤ N) :
    (items.map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum ≤ n * ((62 * c + 730) * N) := by
  rw [← hn]
  have h1 : ∀ y ∈ items.map (fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30), y ≤ (62 * c + 730) * N := by
    intro y hy
    obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hy
    have := h it hit
    have h2 : (62 * c + 700) * (it.1.length + it.2.length + 1) ≤ (62 * c + 700) * N := Nat.mul_le_mul_left _ this
    have h3 : 1 ≤ N := by omega
    nlinarith
  have := List.sum_le_card_nsmul _ _ h1
  simpa using this


theorem ex_pack (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) : ∃ F κ, ∀ (ub : ℕ) (B : Body) (o : Outs S) (t : Tree)
    (O : ℕ), (∀ j, (o j).length ≤ O) → (∀ j, ∀ a ∈ o j, a.length ≤ c) →
    Does θ F (.cons (encO o) (.cons (num ub) (.cons t B.tree))) (packSem A sep ub B o t)
      (κ * (O + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1)) := by
  obtain ⟨GR, κR, hGR⟩ := itemsR_gives (θ := θ) (S := S)
  obtain ⟨GC, κC, hGC⟩ := itemsC_gives (θ := θ) (S := S)
  refine ⟨lett (.cons .id (lett (.cons .id (lett (.cons (GR (.hd (.tl (.tl (.tl .id)))) (.hd .id))
      (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))) (segsF sep)))
      (lett (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl (.tl (.tl (.tl (.hd .id))))))
        (.cons (foldF .id (.quote .nil) (.tl .id)) (.hd (.tl (.tl (.hd .id))))))) putsF)))
    (lett (.cons .id (lett (.hd .id) (lett (.cons (GC (mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))
        (.hd .id)) (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))) (segsF sep))))
      (lett (.cons (.hd (.tl (.hd (.hd .id)))) (.cons (.tl (.tl (.tl (.tl (.tl (.hd (.hd .id)))))))
        (.cons (foldF .id (.quote .nil) (.tl .id)) (.tl (.hd .id))))) putsF)),
    10 * κR + κC * 100 + 2 * (nT S * (62 * c + 730)) + 2000, fun ub B o t O hO hc => ?_⟩
  set x : Tree := .cons (encO o) (.cons (num ub) (.cons t B.tree)) with hx
  set m := B.kR.length with hm
  set N := O + flen B.flags + m + putCost ub B.kR + putCost ub B.kC + 1 with hN
  have gO : Gives θ (.hd .id) x (encO o) 2 := (Gives.id _).hd
  have gF : Gives θ (.hd (.tl (.tl (.tl .id)))) x (listT (B.flags.map fun l => listT (l.map num))) 5 :=
    (Gives.id _).tl.tl.tl.hd
  have gK : Gives θ (.hd (.tl (.tl (.tl (.tl .id))))) x (keysT B.kR) 6 := (Gives.id _).tl.tl.tl.tl.hd
  -- what is written
  have a1 : Gives θ (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id)))))) x
      (encA (List.replicate m [true])) (6 + m * 41 + 21) := by
    have := row_gives (ofBits [true]) gK
    rw [encA, List.map_replicate]
    exact this
  have a2 := Gives.cons (hGR _ _ x B.flags o 5 2 gF gO) a1
  have hcR : ∀ it ∈ itemsR B.flags o, ∀ a ∈ it.2, a.length ≤ c := by
    intro it hit a ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    exact hc _ a ha
  have hlR : ∀ it ∈ itemsR B.flags o, it.1.length + it.2.length + 1 ≤ N ∧ it.1.length ≤ flen B.flags := by
    intro it hit
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    have h1 := length_getD_le B.flags i.rev
    have h2 := hO (Fin.castAdd (nT S) i.rev)
    exact ⟨by simp only; omega, h1⟩
  have a3 := Does.of_gives a2 (segsF_does (θ := θ) sep c hsep _ _ hcR)
  have a4 := Does.letkT (G := lett (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl (.tl (.tl (.tl (.hd .id))))))
      (.cons (foldF .id (.quote .nil) (.tl .id)) (.hd (.tl (.tl (.hd .id))))))) putsF)
    (f := fun sR => (encT (A := A) (putsL ub B.kR sR.reverse t)).map (Prod.map id id))
    (d := (flen B.flags + m) * 31 + putCost ub B.kR + 300) a3 (by
      intro b hb
      have h1 := length_segsL (N := flen B.flags + m) (fun it hit => (hlR it hit).2.trans (Nat.le_add_right _ _))
        (by rw [List.length_replicate]; exact Nat.le_add_left _ _) b hb
      have e1 := rev_encA (θ := θ) (x := .cons x (encA b.2)) (k := .tl .id) (l := b.2) (Gives.id _).tl
      have e2 := Gives.cons (Gives.id (θ := θ) (.cons x (encA b.2))).hd.tl.hd (Gives.cons
        (Gives.id _).hd.tl.tl.tl.tl.hd (Gives.cons e1 (Gives.id _).hd.tl.tl.hd))
      have e3 := Does.of_gives e2 (putsF_does (θ := θ) ub B.kR b.2.reverse t)
      refine (e3.replace ?_).mono ?_
      · simp
      · simp only [putCost]
        omega)
  rw [bindL_map] at a4
  -- what is read
  have gO' : ∀ t1, Gives θ (.hd .id) (.cons x t1) x 2 := fun t1 => (Gives.id _).hd
  have b1 : Gives θ (mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id)))))) x
      (listT ((List.replicate m 2).map num)) (6 + m * 41 + 21) := by
    have := row_gives (num 2) gK
    rw [List.map_replicate]
    exact this
  have b2 := Gives.cons (hGC _ _ x m o _ 2 b1 gO) a1
  have hcC : ∀ it ∈ itemsC m o, ∀ a ∈ it.2, a.length ≤ c := by
    intro it hit a ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    exact hc _ a ha
  have hlC : ∀ it ∈ itemsC m o, it.1.length + it.2.length + 1 ≤ N ∧ it.1.length ≤ m := by
    intro it hit
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hit
    have h2 := hO (Fin.natAdd (nT S) i.rev)
    refine ⟨?_, ?_⟩
    · simp only [List.length_replicate]
      omega
    · simp
  have b3 := Does.of_gives b2 (segsF_does (θ := θ) sep c hsep _ _ hcC)
  have b4 := Does.letkT (G := _) (f := fun t1 => bindL (segsL A sep (itemsC m o) (List.replicate m [true])) fun sC =>
      encT (A := A) (putsL ub B.kC sC.reverse t1))
    (d := 2 + (κC * (6 + m * 41 + 21 + 2 + 1) + (6 + m * 41 + 21) + 1 +
        (((itemsC m o).map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum + 30) + 2) + 2 +
        (m * 31 + putCost ub B.kC + 300) + 4) a4 (by
      intro b hb
      have c1 := Does.of_gives (gO' b.2) b3
      have c2 := Does.letkT (G := lett (.cons (.hd (.tl (.hd (.hd .id)))) (.cons (.tl (.tl (.tl (.tl (.tl (.hd (.hd .id)))))))
          (.cons (foldF .id (.quote .nil) (.tl .id)) (.tl (.hd .id))))) putsF)
        (f := fun sC => encT (A := A) (putsL ub B.kC sC.reverse b.2)) (d := m * 31 + putCost ub B.kC + 300) c1 (by
          intro r hr
          have h1 := length_segsL (N := m) (fun it hit => (hlC it hit).2) (by rw [List.length_replicate]) r hr
          have e1 := rev_encA (θ := θ) (x := .cons (.cons x b.2) (encA r.2)) (k := .tl .id) (l := r.2) (Gives.id _).tl
          have e2 := Gives.cons (Gives.id (θ := θ) (.cons (.cons x b.2) (encA r.2))).hd.hd.tl.hd (Gives.cons
            (Gives.id _).hd.hd.tl.tl.tl.tl.tl (Gives.cons e1 (Gives.id _).hd.tl))
          have e3 := Does.of_gives e2 (putsF_does (θ := θ) ub B.kC r.2.reverse b.2)
          refine e3.mono ?_
          simp only [putCost]
          omega)
      exact c2)
  refine (b4.replace ?_).mono ?_
  · unfold packSem
    rw [bindL_assoc]
  · have h1 := sum_items_le (c := c) (N := N) (n := nT S) (by simp [itemsR]) (fun it hit => (hlR it hit).1)
    have h2 := sum_items_le (c := c) (N := N) (n := nT S) (by simp [itemsC]) (fun it hit => (hlC it hit).1)
    have h3 : m ≤ N := by omega
    have h4 : 1 ≤ N := by omega
    have h5 : κC * (6 + m * 41 + 21 + 2 + 1) ≤ κC * 71 * N := by
      calc κC * (6 + m * 41 + 21 + 2 + 1) ≤ κC * (71 * N) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    have h6 : κR * (5 + 2 + 1) ≤ κR * 8 * N := by nlinarith
    have h7 : nT S * ((62 * c + 730) * N) = nT S * (62 * c + 730) * N := by ring
    have h8 : (10 * κR + κC * 100 + 2 * (nT S * (62 * c + 730)) + 2000) * N =
      10 * (κR * N) + 100 * (κC * N) + 2 * (nT S * (62 * c + 730) * N) + 2000 * N := by ring
    have h9 : κC * 71 * N = 71 * (κC * N) := by ring
    have h10 : κR * 8 * N = 8 * (κR * N) := by ring
    rw [h8]
    rw [h7] at h1 h2
    rw [h9] at h5
    rw [h10] at h6
    omega

end Nc.Grp

end

section










set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section unary


def unF (b : Fm) : Fm := foldF (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
  (.quote .nil) b

theorem le_foldl_bval (w : List Bool) (a : ℕ) : a ≤ w.foldl (fun a b => 2 * a + b.toNat) a := by
  induction w generalizing a with
  | nil => exact le_rfl
  | cons b w ih => exact le_trans (by omega) (ih (2 * a + b.toNat))

theorem unStep_gives (b : Bool) (a v : ℕ) (ha : a ≤ v) :
    Gives θ (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
      (.cons (bit b) (num a)) (num (2 * a + b.toNat)) (v * 62 + 90) := by
  have e1 : Gives θ (.tl .id) (.cons (bit b) (num a)) (ofBits (List.replicate a false)) 2 := by
    rw [← num_eq_ofBits]
    exact (Gives.id _).tl
  have e2 := appB_gives e1 e1
  rw [← List.replicate_add, ← num_eq_ofBits, List.length_replicate, ← two_mul] at e2
  cases b with
  | false => exact (Gives.ite_false (Gives.id _).hd e2).mono (by omega)
  | true =>
    have e3 : Gives θ (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (.cons (bit true) (num a)) (num (2 * a + 1))
        (v * 62 + 80) := (Gives.cons (Gives.quote .nil _) e2).mono (by omega)
    exact (Gives.ite_true (Gives.id _).hd (by simp [bit, one]) e3).mono (by omega)

theorem unF_gives {b : Fm} {x : Tree} {w : List Bool} {c : ℕ} (h : Gives θ b x (ofBits w) c) :
    Gives θ (unF b) x (num (bval w)) (c + w.length * (bval w * 62 + 130) + 30) := by
  have hl : Gives θ b x (listT (w.map bit)) c := by
    rw [listT_ofBits]
    exact h
  have h1 := foldTG (θ := θ) (encE := bit) (xs := w) (enc := num) (s₀ := 0) (g := fun b a => 2 * a + b.toNat)
    (Inv := fun ys a => ys.foldl (fun a b => 2 * a + b.toNat) a = bval w) (d := fun _ => bval w * 62 + 90)
    (step := .ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
    (s := .quote .nil) (Gives.quote _ _) hl (fun b ys a _ hinv => ⟨unStep_gives b a _ (by
      rw [← hinv]
      exact le_trans (by omega) (le_foldl_bval ys (2 * a + b.toNat))), hinv⟩) rfl
  refine h1.mono ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

end unary

section group

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro))


def sepOf : List Bool := List.ofFn (cb none)

variable (θ) in

noncomputable def insSem (T ub : ℕ) : Ins → Tree → List (A × Tree)
  | .block q q' B, t => if h : q < Fintype.card Q ∧ q' < Fintype.card Q then
      bindL (simSem θ mu cb T ⟨q, h.1⟩ ⟨q', h.2⟩) fun o => packSem A (sepOf cb) ub B o t else []
  | .input part B, t => packSem A (sepOf cb) ub B (inOuts (S := S) part) t
  | .both k k', t => if tget k t = tget k' t then [(1, t)] else []
  | .one k w, t => if tget k t = ofBits w then [(1, t)] else []
  | .role j tt slots keys, t => match kinds[j]? with
    | some z => roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t
    | none => []


def InsOk (S Q : Type) [Fintype S] [DecidableEq S] [Fintype Q] (c : ℕ) (kinds : List (Σ L : G.Law A, L.Ro)) : Ins → Prop
  | .block q q' _ => q < Fintype.card Q ∧ q' < Fintype.card Q
  | .input part _ => ∀ a ∈ part, a.length ≤ c
  | .both _ _ => True
  | .one _ _ => True
  | .role j _ slots _ => ∃ z, kinds[j]? = some z ∧ slots.length = (slList z.1 z.2).length








def TOk (ub : ℕ) (t : Tree) : Prop := ∀ k, ∃ w : List Bool, tget k t = ofBits w ∧ w.length ≤ ub

theorem TOk.path {ub : ℕ} {t : Tree} (h : TOk ub t) (k : List Bool) : tget k t = ofBits (tget k t).path ∧
    (tget k t).path.length ≤ ub := by
  obtain ⟨w, h1, h2⟩ := h k
  rw [h1, path_ofBits]
  exact ⟨rfl, h2⟩

theorem tOk_nil (ub : ℕ) : TOk ub .nil := fun k => ⟨[], by rw [tget_nil]; rfl, Nat.zero_le _⟩

theorem TOk.tset {ub : ℕ} {t : Tree} (h : TOk ub t) (k w : List Bool) (hw : w.length ≤ ub) :
    TOk ub (tset k (ofBits w) t) := by
  intro k'
  rw [tget_tset]
  split_ifs
  · exact ⟨w, rfl, hw⟩
  · exact h k'

theorem TOk.putL {ub : ℕ} {keys : List (List Bool)} {r : List Bool} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putL ub keys r t, TOk ub t' := by
  induction keys generalizing r t with
  | nil =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · rw [List.mem_singleton] at ht'
      exact ht' ▸ h
    · simp at ht'
  | cons k ks ih =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · simp at ht'
    · exact ih (h.tset k _ (length_padTake _ _).le) t' ht'

theorem TOk.putsL {ub : ℕ} {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putsL ub kss strs t, TOk ub t' := by
  induction kss generalizing strs t with
  | nil =>
    intro t' ht'
    rw [Grp.putsL, List.mem_singleton] at ht'
    exact ht' ▸ h
  | cons ks kss ih =>
    intro t' ht'
    rw [Grp.putsL, List.mem_flatMap] at ht'
    obtain ⟨t1, h1, h2⟩ := ht'
    exact ih (h.putL t1 h1) t' h2

theorem mem_encT {l : List Tree} {q : A × Tree} (h : q ∈ encT (A := A) l) : q.2 ∈ l := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ht

theorem TOk.pack {sep : List Bool} {ub : ℕ} {B : Body} {o : Outs S} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ packSem A sep ub B o t, TOk ub q.2 := by
  intro q hq
  obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
  obtain ⟨b, hb, r', hr', e2⟩ := mem_bindL hr
  obtain ⟨d, -, r'', hr'', e3⟩ := mem_bindL hr'
  rw [e1, e2, e3]
  exact (h.putsL _ (mem_encT hb)).putsL _ (mem_encT hr'')

theorem TOk.insSem {T ub : ℕ} {i : Ins} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ insSem θ mu cb kinds T ub i t, TOk ub q.2 := by
  intro q hq
  cases i with
  | block q₁ q₂ B =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
      rw [e1]
      exact h.pack r hr
    · simp at hq
  | input part B => exact h.pack q hq
  | both k k' =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | one k w =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | role j tt slots keys =>
    rw [Grp.insSem] at hq
    split at hq
    · unfold roleSem at hq
      split_ifs at hq
      · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
        rw [e1]
        exact h.putsL _ (mem_encT hr)
      · simp at hq
    · simp at hq


def encG (T ub : ℕ) (t : Tree) : Tree := .cons (num T) (.cons (num ub) t)


theorem ex_kinds : ∃ (Fs : List Fm) (κ : ℕ), ∀ (j : ℕ) (z : Σ L : G.Law A, L.Ro), kinds[j]? = some z →
    ∃ F, Fs[j]? = some F ∧ ∀ (ub tt : ℕ) (slots keys : List (List (List Bool))) (t : Tree), TOk ub t →
      slots.length = (slList z.1 z.2).length →
      Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots) (keysT keys)))))
        (roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t)
        (κ * (tt * (ub + 1) + putCost ub slots + putCost ub keys + 1)) := by
  induction kinds with
  | nil => exact ⟨[], 0, fun j z h => by simp at h⟩
  | cons z₀ kinds ih =>
    obtain ⟨Fs, κ, h⟩ := ih
    obtain ⟨F, κ', h'⟩ := ex_role (θ := θ) z₀.1 z₀.2
    refine ⟨F :: Fs, max κ (2 * κ'), fun j z hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      refine ⟨F, rfl, fun ub tt slots keys t ht hs => ?_⟩
      refine (h' ub (fun k => (tget k t).path) tt slots keys t (fun k => (ht.path k).1) (fun k => (ht.path k).2) hs).mono ?_
      have h1 : (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum ≤ 2 * putCost ub slots := by
        unfold putCost
        rw [← List.sum_map_mul_left]
        refine List.sum_le_sum fun es _ => ?_
        have : (es.map fun k => ub * 62 + k.length * 60 + 330).sum ≤ (es.map fun k => ub * 90 + k.length * 60 + 330).sum :=
          List.sum_le_sum fun k _ => by omega
        omega
      change κ' * (_ + _ + putCost ub keys + 1) ≤ _
      refine le_trans ?_ (Nat.mul_le_mul_right _ (le_max_right κ (2 * κ')))
      rw [mul_comm 2 κ', mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨F', h1, h2⟩ := h j z hj
      exact ⟨F', by simpa using h1, fun ub tt slots keys t ht hs => (h2 ub tt slots keys t ht hs).mono
        (Nat.mul_le_mul_right _ (le_max_left _ _))⟩


theorem ex_ins (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (T ub : ℕ) (i : Ins) (t : Tree), InsOk S Q c kinds i → TOk ub t →
    Does θ F (.cons i.tree (encG T ub t)) ((insSem (S := S) θ mu cb kinds T ub i t).map (Prod.map id (encG T ub)))
      (κ * insCost T ub i) := by
  obtain ⟨Fs, κs, hFs⟩ := ex_sim (θ := θ) mu cb
  obtain ⟨κl, hκl⟩ := exists_simSem_length (θ := θ) mu cb
  obtain ⟨Fp, κp, hFp⟩ := ex_pack (A := A) (θ := θ) (S := S) (sepOf cb) c hc
  obtain ⟨Fi, κi, hFi⟩ := ex_inOuts (θ := θ) (S := S)
  obtain ⟨Fk, κk, hFk⟩ := ex_kinds (θ := θ) kinds
  -- the formulas
  set fBlock : Fm := lett (.cons .id (lett (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) Fs))
    (lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
      (.tl (.tl (.hd (.hd .id))))))) Fp) with hBlock
  set fInput : Fm := lett (.cons (Fi (.hd (.tl (.hd .id)))) (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id)))
      (.tl (.tl (.hd .id)))))) Fp with hInput
  set fBoth : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (getF (.tl (.tl (.hd .id)))
      (.tl (.tl (.tl .id))))) (.tl (.tl (.tl .id))) .fail with hBoth
  set fOne : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (.tl (.tl (.hd .id))))
      (.tl (.tl (.tl .id))) .fail with hOne
  set fs : List Fm := fBlock :: fInput :: fBoth :: fOne :: Fk.map fun G =>
    lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G with hfs
  set sw : ℕ := (kinds.length + 5) * (kinds.length + 10) with hsw
  refine ⟨.cons (.hd (.tl .id)) (.cons (.hd (.tl (.tl .id))) (switchF (.hd (.hd .id)) fs)),
    κs + κp * (κl + 2) + κi * 10 + κk + sw + 2000, fun T ub i t hi ht => ?_⟩
  set x : Tree := .cons i.tree (encG T ub t) with hx
  have gT : Gives θ (.hd (.tl .id)) x (num T) 3 := (Gives.id _).tl.hd
  have gU : Gives θ (.hd (.tl (.tl .id))) x (num ub) 4 := (Gives.id _).tl.tl.hd
  have gt : Gives θ (.tl (.tl (.tl .id))) x t 4 := (Gives.id _).tl.tl.tl
  have gpos : 1 ≤ insCost T ub i := by
    cases i <;> simp only [insCost, bodyCost] <;> omega
  -- it is enough to make the trie
  suffices h : Does θ (switchF (.hd (.hd .id)) fs) x (insSem (S := S) θ mu cb kinds T ub i t)
      ((κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub i) by
    refine ((Does.cons gT (Does.cons gU h)).replace ?_).mono ?_
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
      rfl
    · have : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 2000) * insCost T ub i =
        (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub i + 100 * insCost T ub i := by ring
      omega
  cases i with
  | block q q' B =>
    obtain ⟨hq, hq'⟩ := hi
    have g0 : Gives θ (.hd (.hd .id)) x (num 0) 3 := (Gives.id _).hd.hd
    have e1 : Gives θ (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) x (.cons (num T) (.cons (num q) (num q'))) 8 :=
      (Gives.cons gT (Gives.id _).hd.tl.hd).mono (by omega)
    have e2 := Does.of_gives e1 (hFs T ⟨q, hq⟩ ⟨q', hq'⟩)
    have e3 := Does.letkT (G := lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
        (.tl (.tl (.hd (.hd .id))))))) Fp) (f := fun o => packSem A (sepOf cb) ub B o t)
      (d := 30 + κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) + 2) e2 (by
        intro b hb
        obtain ⟨h1, h2⟩ := hκl T ⟨q, hq⟩ ⟨q', hq'⟩ b hb
        have e4 : Gives θ (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
            (.tl (.tl (.hd (.hd .id))))))) (.cons x (encO b.2)) (.cons (encO b.2) (.cons (num ub) (.cons t B.tree))) 30 :=
          (Gives.cons (Gives.id _).tl (Gives.cons (Gives.id _).hd.tl.tl.hd (Gives.cons (Gives.id _).hd.tl.tl.tl
            (Gives.id _).hd.hd.tl.tl))).mono (by omega)
        exact Does.of_gives e4 (hFp ub B b.2 t (κl * T) h1 h2))
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBlock) rfl e3
    refine (e5.replace ?_).mono ?_
    · rw [insSem, dif_pos ⟨hq, hq'⟩]
    · simp only [insCost, bodyCost]
      set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1 with hN
      have h1 : κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
          κp * ((κl + 2) * (T + N)) := by
        refine Nat.mul_le_mul_left _ ?_
        have : (κl + 2) * (T + N) = κl * T + κl * N + 2 * T + 2 * N := by ring
        rw [this]
        omega
      have h2 : κs * (T + 1) ≤ κs * (T + N) := Nat.mul_le_mul_left _ (by omega)
      have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * (T + N) = κs * (T + N) + κp * ((κl + 2) * (T + N)) +
        κi * 10 * (T + N) + κk * (T + N) + sw * (T + N) + 1900 * (T + N) := by ring
      have h4 : 1 ≤ T + N := by omega
      omega
  | input part B =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 1) 3 := (Gives.id _).hd.hd
    have e1 := hFi (.hd (.tl (.hd .id))) x part 4 (Gives.id _).hd.tl.hd
    have e2 := Gives.cons e1 (Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl.tl))
    have e3 := hFp ub B (inOuts (S := S) part) t part.length (fun j => by
        unfold inOuts
        split_ifs
        · exact le_rfl
        · simp) (fun j a ha => by
        unfold inOuts at ha
        split_ifs at ha
        · exact hi a ha
        · simp at ha)
    have e4 := Does.of_gives e2 e3
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fInput) rfl e4
    refine e5.mono ?_
    simp only [insCost, bodyCost]
    set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1 with hN
    have h1 : κp * (part.length + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
        κp * ((κl + 2) * (part.length + N)) := by
      refine Nat.mul_le_mul_left _ ?_
      have : (κl + 2) * (part.length + N) = κl * (part.length + N) + 2 * part.length + 2 * N := by ring
      rw [this]
      omega
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * (part.length + N) = κs * (part.length + N) +
      κp * ((κl + 2) * (part.length + N)) + κi * 10 * (part.length + N) + κk * (part.length + N) +
      sw * (part.length + N) + 1900 * (part.length + N) := by ring
    have h4 : 1 ≤ part.length + N := by omega
    have h5 : κi * (4 + 1) ≤ κi * 10 * (part.length + N) := by nlinarith
    omega
  | both k k' =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 2) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (x := x) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e2 := getF_gives (θ := θ) (x := x) (pf := .tl (.tl (.hd .id))) (p := ofBits k') (Gives.id _).hd.tl.tl gt
    have e3 := eqF_gives e1 e2
    rw [path_ofBits, path_ofBits, len_ofBits, len_ofBits] at e3
    have h1 : (tget k t).size ≤ 4 * ub + 1 := by
      obtain ⟨a1, a2⟩ := ht.path k
      rw [a1]
      exact (size_ofBits _).trans (by omega)
    have h2 : Does θ fBoth x (insSem (S := S) θ mu cb kinds T ub (.both k k') t) (300 * insCost T ub (.both k k')) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = tget k' t
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = tget k' t)) ≠ .nil := by simp [h, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = tget k' t)) = .nil := by simp [h, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBoth) rfl h2
    refine e5.mono ?_
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub (.both k k') =
      κs * insCost T ub (.both k k') + κp * (κl + 2) * insCost T ub (.both k k') + κi * 10 * insCost T ub (.both k k') +
      κk * insCost T ub (.both k k') + sw * insCost T ub (.both k k') + 1900 * insCost T ub (.both k k') := by ring
    omega
  | one k w =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 3) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (x := x) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e3 := eqF_gives e1 (Gives.id (θ := θ) x).hd.tl.tl
    rw [path_ofBits, len_ofBits] at e3
    have h1 : (tget k t).size ≤ 4 * ub + 1 := by
      obtain ⟨a1, a2⟩ := ht.path k
      rw [a1]
      exact (size_ofBits _).trans (by omega)
    have h2 : Does θ fOne x (insSem (S := S) θ mu cb kinds T ub (.one k w) t) (300 * insCost T ub (.one k w)) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = ofBits w
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) ≠ .nil := by
          have : tget k t = x.hd.tl.tl := h
          simp [this, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) = .nil := by
          have : ¬ tget k t = x.hd.tl.tl := h
          simp [this, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fOne) rfl h2
    refine e5.mono ?_
    have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub (.one k w) =
      κs * insCost T ub (.one k w) + κp * (κl + 2) * insCost T ub (.one k w) + κi * 10 * insCost T ub (.one k w) +
      κk * insCost T ub (.one k w) + sw * insCost T ub (.one k w) + 1900 * insCost T ub (.one k w) := by ring
    omega
  | role j tt slots keys =>
    obtain ⟨z, hz, hsl⟩ := hi
    obtain ⟨G, hG, hG'⟩ := hFk j z hz
    have hj : j < kinds.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.1 h)] at hz
      simp at hz
    have g0 : Gives θ (.hd (.hd .id)) x (num (4 + j)) 3 := (Gives.id _).hd.hd
    have e1 := Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl)
    have e2 := Does.of_gives e1 (hG' ub tt slots keys t ht hsl)
    have hf : fs[4 + j]? = some (lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G) := by
      rw [hfs, add_comm]
      simp [hG]
    have e5 := switchF_does (θ := θ) g0 (fs := fs) hf e2
    refine (e5.replace ?_).mono ?_
    · rw [insSem, hz]
    · simp only [insCost]
      set N := tt * (ub + 1) + putCost ub slots + putCost ub keys + 1 with hN
      have h1 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw * N := by
        have h2 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw := Nat.mul_le_mul (by omega) (by omega)
        have h3 : 1 ≤ N := by omega
        nlinarith
      have h3 : (κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * N = κs * N + κp * (κl + 2) * N + κi * 10 * N + κk * N +
        sw * N + 1900 * N := by ring
      have h4 : 1 ≤ N := by omega
      omega

variable (θ) in

noncomputable def scriptSem (T ub : ℕ) (l : List Ins) (t : Tree) : List (A × Tree) :=
  foldL (insSem (S := S) θ mu cb kinds T ub) l t


theorem ex_group (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (bT bub : List Bool) (l : List Ins),
    (∀ i ∈ l, InsOk S Q c kinds i) →
    Does θ F (scriptT bT bub l) ((scriptSem (S := S) θ mu cb kinds (bval bT) (bval bub) l .nil).map
      (Prod.map id (encG (bval bT) (bval bub))))
      (κ * ((bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) +
        (l.map (insCost (bval bT) (bval bub))).sum + l.length)) := by
  obtain ⟨F, κ, hF⟩ := ex_ins (θ := θ) mu cb kinds hc
  refine ⟨foldF F (.cons (unF (.hd (.hd .id))) (.cons (unF (.tl (.hd .id))) (.quote .nil))) (.tl .id), κ + 300,
    fun bT bub l hl => ?_⟩
  have g1 : Gives θ (.hd (.hd .id)) (scriptT bT bub l) (ofBits bT) 3 := (Gives.id _).hd.hd
  have g2 : Gives θ (.tl (.hd .id)) (scriptT bT bub l) (ofBits bub) 3 := (Gives.id _).hd.tl
  have h0 := Gives.cons (unF_gives g1) (Gives.cons (unF_gives g2) (Gives.quote .nil (scriptT bT bub l)))
  have h1 := foldT (θ := θ) (A := A) (encE := Ins.tree) (xs := l) (enc := encG (bval bT) (bval bub)) (s₀ := .nil)
    (f := insSem (S := S) θ mu cb kinds (bval bT) (bval bub)) (Inv := fun _ t => TOk (bval bub) t)
    (d := fun i => κ * insCost (bval bT) (bval bub) i) (step := F) (l := .tl .id) (x := scriptT bT bub l) h0
    (Gives.id _).tl (fun i _ t hi ht => ⟨hF _ _ i t (hl i hi) ht, fun q hq => ht.insSem mu cb kinds q hq⟩) (tOk_nil _)
  refine h1.mono ?_
  have h2 : ∀ l : List Ins, (l.map fun i => κ * insCost (bval bT) (bval bub) i + 30).sum =
      κ * (l.map (insCost (bval bT) (bval bub))).sum + 30 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring
  rw [h2]
  set P := (bT.length + 1) * (bval bT + 1) with hP
  set R := (bub.length + 1) * (bval bub + 1) with hR
  set Sm := (l.map (insCost (bval bT) (bval bub))).sum
  have p1 : bT.length * (bval bT * 62 + 130) ≤ 130 * P := by rw [hP]; nlinarith
  have p2 : bub.length * (bval bub * 62 + 130) ≤ 130 * R := by rw [hR]; nlinarith
  have p3 : 1 ≤ P := Nat.succ_le_of_lt (by positivity)
  have p4 : (κ + 300) * (P + R + Sm + l.length) = κ * (P + R + l.length) + κ * Sm + 300 * (P + R + Sm + l.length) := by ring
  omega

end group

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Writing several strings
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

/-- Write the units of several strings. -/
def putsAll (ub : ℕ) : List (List (List Bool) × List Bool) → Tree → Tree
  | [], t => t
  | p :: r, t => putsAll ub r (putAll p.1 (fun i => uwBits (unitsOf ub p.2 i)) t)

theorem putsL_eq {ub : ℕ} (hub : 0 < ub) (P : List (List (List Bool) × List Bool)) (t : Tree) :
    putsL ub (P.map Prod.fst) (P.map fun p => p.2 ++ [true]) t =
      if ∀ p ∈ P, ucount ub p.2 = p.1.length then [putsAll ub P t] else [] := by
  induction P generalizing t with
  | nil => simp [putsL, putsAll]
  | cons p P ih =>
    rw [List.map_cons, List.map_cons, putsL, List.headD_cons, List.tail_cons, putL_eq hub]
    by_cases hp : ucount ub p.2 = p.1.length
    · rw [if_pos hp, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
      by_cases hP : ∀ p ∈ P, ucount ub p.2 = p.1.length
      · rw [if_pos hP, if_pos (by
          intro p' hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hp
          · exact hP p' hp')]
        rfl
      · rw [if_neg hP, if_neg fun h => hP fun p' hp' => h p' (List.mem_cons_of_mem _ hp')]
    · rw [if_neg hp, if_neg fun h => hp (h p List.mem_cons_self)]
      rfl

theorem tget_putsAll_not {ub : ℕ} {P : List (List (List Bool) × List Bool)} (hP : (P.flatMap Prod.fst).Nodup)
    {k : List Bool} (hk : k ∉ P.flatMap Prod.fst) (t : Tree) : tget k (putsAll ub P t) = tget k t := by
  induction P generalizing t with
  | nil => rfl
  | cons p P ih =>
    rw [List.flatMap_cons, List.nodup_append] at hP
    rw [List.flatMap_cons, List.mem_append, not_or] at hk
    rw [putsAll, ih hP.2.1 hk.2, tget_putAll _ hP.1, if_neg hk.1]

theorem tget_putsAll {ub : ℕ} {P : List (List (List Bool) × List Bool)} (hP : (P.flatMap Prod.fst).Nodup)
    {p : List (List Bool) × List Bool} (hp : p ∈ P) {i : ℕ} {k : List Bool} (hk : p.1[i]? = some k) (t : Tree) :
    tget k (putsAll ub P t) = ofBits (uwBits (unitsOf ub p.2 i)) := by
  induction P generalizing t with
  | nil => simp at hp
  | cons p' P ih =>
    rw [List.flatMap_cons, List.nodup_append] at hP
    rw [putsAll]
    rcases List.mem_cons.1 hp with rfl | hp
    · have hmem : k ∈ p.1 := List.mem_of_getElem? hk
      have hnot : k ∉ P.flatMap Prod.fst := fun h => hP.2.2 k hmem k h rfl
      rw [tget_putsAll_not hP.2.1 hnot, tget_putAll _ hP.1, if_pos hmem]
      congr 3
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hk
      exact hP.1.idxOf_getElem i hi
    · exact ih hP.2.1 hp _

theorem TOk.putAll {ub : ℕ} {keys : List (List Bool)} {u : ℕ → List Bool} (hu : ∀ i, (u i).length ≤ ub) {t : Tree}
    (h : TOk ub t) : TOk ub (putAll keys u t) := by
  induction keys generalizing u t with
  | nil => exact h
  | cons k ks ih => exact ih (fun i => hu (i + 1)) (h.tset k _ (hu 0))

theorem length_uwBits_le {ub : ℕ} (w : UW ub) : (uwBits w).length ≤ ub := by
  cases w with
  | none => exact Nat.zero_le _
  | some w => simp [uwBits]

theorem TOk.putsAll {ub : ℕ} {P : List (List (List Bool) × List Bool)} {t : Tree} (h : TOk ub t) :
    TOk ub (Grp.putsAll ub P t) := by
  induction P generalizing t with
  | nil => exact h
  | cons p P ih => exact ih (h.putAll fun i => length_uwBits_le _)

/-- The first numbers. -/
theorem filter_finRange {U c : ℕ} (h : c ≤ U) :
    (List.finRange U).filter (fun k => k.1 < c) = List.ofFn fun i : Fin c => Fin.castLE h i := by
  have h1 : Function.Injective (List.map (Fin.val : Fin U → ℕ)) := List.map_injective_iff.2 Fin.val_injective
  apply h1
  have h2 : ((List.finRange U).filter (fun k => k.1 < c)).map Fin.val = (List.range U).filter (fun k => k < c) := by
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    rfl
  have h3 : (List.range U).filter (fun k => k < c) = List.range c := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.range_add, List.filter_append]
    have e1 : (List.range c).filter (fun k => k < c) = List.range c :=
      List.filter_eq_self.2 fun k hk => by simpa using hk
    have e2 : ((List.range d).map (c + ·)).filter (fun k => k < c) = [] :=
      List.filter_eq_nil_iff.2 fun k hk => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hk
        simp
    rw [e1, e2, List.append_nil]
  rw [h2, h3, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro i h4 h5
    simp

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}

theorem sumL_script_cons (T ub : ℕ) (i : Ins) (l : List Ins) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (i :: l) t) Ψ = sumL (insSem (S := S) θ mu cb kinds T ub i t) fun t' =>
      sumL (scriptSem (S := S) θ mu cb kinds T ub l t') Ψ := by
  rw [scriptSem, foldL, sumL_bindL]
  rfl

theorem sumL_script_nil (T ub : ℕ) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub [] t) Ψ = Ψ t := by
  rw [scriptSem, foldL, sumL_single]

theorem sumL_script_append (T ub : ℕ) (l l' : List Ins) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l ++ l') t) Ψ =
      sumL (scriptSem (S := S) θ mu cb kinds T ub l t) fun t' =>
        sumL (scriptSem (S := S) θ mu cb kinds T ub l' t') Ψ :=
  foldL_append _ _ _ _ _

/-- Several comparisons. -/
theorem sumL_boths {ι : Type} (T ub : ℕ) (ks : List ι) (f g : ι → List Bool) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (ks.map fun k => Ins.both (f k) (g k)) t) Ψ =
      if ∀ k ∈ ks, tget (f k) t = tget (g k) t then Ψ t else 0 := by
  induction ks with
  | nil => simp [sumL_script_nil]
  | cons k ks ih =>
    rw [List.map_cons, sumL_script_cons, insSem]
    by_cases h : tget (f k) t = tget (g k) t
    · rw [if_pos h, sumL_single, ih]
      by_cases h' : ∀ k ∈ ks, tget (f k) t = tget (g k) t
      · rw [if_pos h', if_pos (by
          intro k' hk'
          rcases List.mem_cons.1 hk' with rfl | hk'
          · exact h
          · exact h' k' hk')]
      · rw [if_neg h', if_neg fun h1 => h' fun k' hk' => h1 k' (List.mem_cons_of_mem _ hk')]
    · rw [if_neg h, sumL_nil, if_neg fun h1 => h (h1 k List.mem_cons_self)]

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sum over what a base party does
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {F : Type} [CommRing F] {M : Sys F (K + K + A') E} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool}

/-- The trie has the contents `σ`. -/
def Rep (ub : ℕ) (key : Cell M U0 U1 → List Bool) (t : Tree) (σ : Cell M U0 U1 → UW ub) : Prop :=
  TOk ub t ∧ ∀ c, tget (key c) t = ofBits (uwBits (σ c))

/-- All tapes, as an equivalence. -/
noncomputable def tapeEquiv (S : Type) [Fintype S] [DecidableEq S] : Fin (nT S) ≃ Option S :=
  List.Nodup.getEquivOfForallMemList (tapes S) (Finset.nodup_toList _) fun s => Finset.mem_toList.2 (mem_univ s)

theorem tapeEquiv_apply (i : Fin (nT S)) : tapeEquiv S i = (tapes S).get i := rfl

theorem joined_tapes (X : Option S → List Γ) :
    joined (code cb) (sepOf cb) (fun i : Fin (nT S) => X ((tapes S).get i)) = strOf cb X := by
  have h1 : (List.ofFn fun i : Fin (nT S) => (X ((tapes S).get i)).flatMap (code cb) ++ sepOf cb) =
      (tapes S).map fun s => (X s).flatMap (code cb) ++ sepOf cb := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  rw [joined, h1, strOf, joinSeg, bitsOf, ← List.flatMap_def, List.flatMap_assoc]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.flatMap_append, List.flatMap_map]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem flags_rowOk {m : ℕ} {d : RowData m} (hd : d.1 = false → d.2.1 ≤ d.2.2) (X : Fin m → List Γ) :
    (∀ b, okFlag (rowFlag d b) (decide (X b ≠ [])) = true) ↔ RowOk d X := by
  unfold RowOk
  by_cases h : d.1 = true
  · rw [if_pos h]
    refine forall_congr' fun b => ?_
    simp [rowFlag, h, okFlag]
  · rw [if_neg h]
    have h' : d.1 = false := by simpa using h
    have hle := hd h'
    constructor
    · intro hb
      refine ⟨?_, ?_, fun b hXb => ?_⟩
      · have := hb d.2.1
        simpa [rowFlag, h', okFlag] using this
      · have := hb d.2.2
        simpa [rowFlag, h', okFlag] using this
      · have := hb b
        by_cases e1 : b = d.2.1 ∨ b = d.2.2
        · rcases e1 with rfl | rfl
          · exact ⟨le_rfl, hle⟩
          · exact ⟨hle, le_rfl⟩
        · by_cases e2 : d.2.1 ≤ b ∧ b ≤ d.2.2
          · exact e2
          · simp [rowFlag, h', e1, e2, okFlag, hXb] at this
    · rintro ⟨h1, h2, h3⟩ b
      by_cases e1 : b = d.2.1 ∨ b = d.2.2
      · have : X b ≠ [] := by
          rcases e1 with rfl | rfl
          · exact h1
          · exact h2
        simp [rowFlag, h', e1, okFlag, this]
      · by_cases e2 : d.2.1 ≤ b ∧ b ≤ d.2.2
        · simp [rowFlag, h', e1, e2, okFlag]
        · have : X b = [] := by
            by_contra hne
            exact e2 (h3 b hne)
          simp [rowFlag, h', e1, e2, okFlag, this]

/-- Two functions with values in a finite set. -/
theorem sum_pi_pi_coe {ι κ β : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq β]
    (s : Finset β) (f : (ι → κ → β) → A) :
    ∑ x ∈ Fintype.piFinset fun _ : ι => Fintype.piFinset fun _ : κ => s, f x =
      ∑ x : ι → κ → s, f fun i j => (x i j : β) := by
  symm
  refine Finset.sum_bij (fun (x : ι → κ → s) _ => fun i j => (x i j : β)) ?_ ?_ ?_ ?_
  · intro x _
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => (x i j).2
  · intro x _ y _ h
    funext i j
    exact Subtype.ext (congrFun (congrFun h i) j)
  · intro y hy
    exact ⟨fun i j => ⟨y i j, Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hy i) j⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

/-- The words of a base party, with their tapes. -/
abbrev Segs (S Γ : Type) [Fintype Γ] [DecidableEq Γ] (m T : ℕ) := Option S → Fin m → Wt Γ T

/-- As words. -/
def Segs.words {m : ℕ} (X : Segs S Γ m T) : Option S → Fin m → List Γ := fun s b => (X s b : List Γ)

/-- The keys of the units that are written. -/
noncomputable def kRl (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool) (p b : Fin (K + K)) :
    List (List Bool) := ((List.finRange U0).filter fun k => k.1 < (n p b).1).map fun k =>
  key (Fin.castAdd A' p, .init p b k)

/-- The keys of the units that are read. -/
noncomputable def kCl (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (p b : Fin (K + K)) :
    List (List Bool) := ((List.finRange U0).filter fun k => k.1 < (n b p).1).map fun k =>
  if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)

/-- The list of what is written. -/
noncomputable def PR (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (cb : Option Γ → Fin c → Bool) (p : Fin (K + K)) (R : Option S → Fin (K + K) → List Γ) :
    List (List (List Bool) × List Bool) := List.ofFn fun b => (kRl n key p b, strOf cb fun s => R s b)

/-- The list of what is read. -/
noncomputable def PC (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (cb : Option Γ → Fin c → Bool) (p : Fin (K + K))
    (C : Option S → Fin (K + K) → List Γ) :
    List (List (List Bool) × List Bool) := List.ofFn fun b => (kCl n key dkey p b, strOf cb fun s => C s b)

theorem sum_segs_equiv {m : ℕ} (f : (Fin (nT S) → Fin m → Wt Γ T) → A) :
    ∑ X, f X = ∑ X : Segs S Γ m T, f fun i => X ((tapes S).get i) :=
  Fintype.sum_equiv ((tapeEquiv S).arrowCongr (Equiv.refl _)) _ _ fun X => by
    congr 1
    funext i
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
    rw [← tapeEquiv_apply, Equiv.symm_apply_apply]

theorem forall_tapes {p : Option S → Prop} : (∀ i : Fin (nT S), p ((tapes S).get i)) ↔ ∀ s, p s := by
  constructor
  · intro h s
    obtain ⟨i, rfl⟩ := (tapeEquiv S).surjective s
    exact h i
  · intro h i
    exact h _

open Classical in
/-- **Cutting and writing, as a sum.** -/
theorem sumL_pack (hub : 0 < ub) (hK : 0 < K + K) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {wl rl : Option S → List Γ}
    (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) (t : Tree) (Ψ : Tree → A) :
    sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t) Ψ =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧ (∀ s, RowOk (ρ s p) (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p) then
          Ψ (putsAll ub (PC n key dkey cb p C.words) (putsAll ub (PR n key cb p R.words) t)) else 0 := by
  have hm : (bodyOf ρ n key dkey p).kR.length = K + K := by simp [bodyOf]
  have hrep : List.replicate (K + K) [true] = (List.ofFn fun _ : Fin (K + K) => [true]).reverse := by
    rw [List.ofFn_const, List.reverse_replicate]
  have hflags : ∀ i : Fin (nT S), (bodyOf ρ n key dkey p).flags.getD i.rev [] =
      (List.ofFn fun b => rowFlag (ρ ((tapes S).get i.rev) p) b).reverse := by
    intro i
    have hlt : (i.rev : ℕ) < (bodyOf ρ n key dkey p).flags.length := by
      simp only [bodyOf, List.length_map]
      exact i.rev.2
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [bodyOf, List.getElem_map]
    rfl
  have eR : itemsR (bodyOf ρ n key dkey p).flags out = List.ofFn fun i : Fin (nT S) =>
      ((List.ofFn fun b => rowFlag (ρ ((tapes S).get i.rev) p) b).reverse,
        ((wl ((tapes S).get i.rev)).map (code cb)).reverse) := by
    rw [itemsR]
    congr 1
    funext i
    rw [hflags, h1]
  have eC : itemsC (K + K) out = List.ofFn fun i : Fin (nT S) =>
      ((List.ofFn fun _ : Fin (K + K) => 2).reverse, ((rl ((tapes S).get i.rev)).map (code cb)).reverse) := by
    rw [itemsC]
    congr 1
    funext i
    rw [h2, List.ofFn_const, List.reverse_replicate]
  have hlenR : ∀ b, (kRl n key p b).length = n p b := by
    intro b
    rw [kRl, List.length_map, filter_finRange (by have := (n p b).2; omega), List.length_ofFn]
  have hlenC : ∀ b, (kCl n key dkey p b).length = n b p := by
    intro b
    rw [kCl, List.length_map, filter_finRange (by have := (n b p).2; omega), List.length_ofFn]
  rw [packSem, hm, hrep, sumL_bindL, eR,
    sumL_segs (sepOf cb) hK (code cb) T (fun i b => rowFlag (ρ ((tapes S).get i) p) b) (fun i => wl ((tapes S).get i))
      (fun i => hwl _), sum_segs_equiv]
  refine Finset.sum_congr rfl fun R _ => ?_
  have cR : (∀ i : Fin (nT S), CutOk (fun b => rowFlag (ρ ((tapes S).get i) p) b) (wl ((tapes S).get i))
      fun b => (R ((tapes S).get i) b : List Γ)) ↔ (∀ s, cat (R.words s) = wl s) ∧ ∀ s, RowOk (ρ s p) (R.words s) := by
    rw [forall_tapes (p := fun s => CutOk (fun b => rowFlag (ρ s p) b) (wl s) fun b => (R s b : List Γ)), ← forall_and]
    refine forall_congr' fun s => ?_
    unfold CutOk
    rw [flags_rowOk (hρ s)]
    rfl
  by_cases hR : (∀ s, cat (R.words s) = wl s) ∧ ∀ s, RowOk (ρ s p) (R.words s)
  swap
  · rw [if_neg fun h => hR (cR.1 h)]
    symm
    refine Finset.sum_eq_zero fun C _ => if_neg fun h => hR ⟨h.1, h.2.2.1⟩
  rw [if_pos (cR.2 hR), List.reverse_reverse, sumL_bindL]
  have sR : (List.ofFn fun b => joined (code cb) (sepOf cb) (fun i : Fin (nT S) => (R ((tapes S).get i) b : List Γ)) ++ [true]) =
      (PR n key cb p R.words).map fun z => z.2 ++ [true] := by
    rw [PR, List.map_ofFn]
    congr 1
    funext b
    show _ = strOf cb (fun s => R.words s b) ++ [true]
    rw [← joined_tapes]
    rfl
  have kR : (bodyOf ρ n key dkey p).kR = (PR n key cb p R.words).map Prod.fst := by
    rw [PR, List.map_ofFn]
    rfl
  rw [sR, kR, putsL_eq hub]
  have cR2 : (∀ z ∈ PR n key cb p R.words, ucount ub z.2 = z.1.length) ↔
      ∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b := by
    rw [PR, List.forall_mem_ofFn_iff]
    refine forall_congr' fun b => ?_
    rw [hlenR]
  by_cases hR2 : ∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b
  swap
  · rw [if_neg fun h => hR2 (cR2.1 h)]
    symm
    refine Finset.sum_eq_zero fun C _ => if_neg fun h => hR2 h.2.2.2.1
  rw [if_pos (cR2.2 hR2)]
  simp only [encT, List.map_cons, List.map_nil, sumL_single]
  rw [sumL_bindL, eC, sumL_segs (sepOf cb) hK (code cb) T (fun _ _ => 2) (fun i => rl ((tapes S).get i))
    (fun i => hrl _), sum_segs_equiv]
  refine Finset.sum_congr rfl fun C _ => ?_
  have cC : (∀ i : Fin (nT S), CutOk (fun _ => 2) (rl ((tapes S).get i)) fun b => (C ((tapes S).get i) b : List Γ)) ↔
      ∀ s, cat (C.words s) = rl s := by
    rw [forall_tapes (p := fun s => CutOk (fun _ => 2) (rl s) fun b => (C s b : List Γ))]
    refine forall_congr' fun s => ?_
    unfold CutOk
    refine and_iff_left fun b => ?_
    simp [okFlag]
  by_cases hC : ∀ s, cat (C.words s) = rl s
  swap
  · rw [if_neg fun h => hC (cC.1 h), if_neg fun h => hC h.2.1]
  rw [if_pos (cC.2 hC), List.reverse_reverse]
  have sC : (List.ofFn fun b => joined (code cb) (sepOf cb) (fun i : Fin (nT S) => (C ((tapes S).get i) b : List Γ)) ++ [true]) =
      (PC n key dkey cb p C.words).map fun z => z.2 ++ [true] := by
    rw [PC, List.map_ofFn]
    congr 1
    funext b
    show _ = strOf cb (fun s => C.words s b) ++ [true]
    rw [← joined_tapes]
    rfl
  have kC : (bodyOf ρ n key dkey p).kC = (PC n key dkey cb p C.words).map Prod.fst := by
    rw [PC, List.map_ofFn]
    rfl
  rw [sC, kC, putsL_eq hub]
  have cC2 : (∀ z ∈ PC n key dkey cb p C.words, ucount ub z.2 = z.1.length) ↔
      ∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p := by
    rw [PC, List.forall_mem_ofFn_iff]
    refine forall_congr' fun b => ?_
    rw [hlenC]
  by_cases hC2 : ∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p
  · rw [if_pos (cC2.2 hC2), if_pos ⟨hR.1, hC, hR.2, hR2, hC2⟩]
    simp only [List.map_cons, List.map_nil, sumL_single]
  · rw [if_neg fun h => hC2 (cC2.1 h), if_neg fun h => hC2 h.2.2.2.2]
    rfl

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The step of a base party
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool}

theorem ofBits_injective : Function.Injective ofBits := by
  intro v w h
  rw [← path_ofBits v, h, path_ofBits]

variable (θ mu cb kinds T key) in
/-- The instructions do what the step does. -/
def StepOK (I : List Ins) (s : WStep A (Cell M U0 U1) (UW ub)) : Prop :=
  ∀ (t : Tree) (σ : Cell M U0 U1 → UW ub) (Ψ : Tree → A) (Ψ' : (Cell M U0 U1 → UW ub) → A), Rep ub key t σ →
    (∀ t' σ', Rep ub key t' σ' → Ψ t' = Ψ' σ') →
    sumL (scriptSem (S := S) θ mu cb kinds T ub I t) Ψ = ∑ ω ∈ s.Om, s.w ω σ * Ψ' (ovr s.wr (s.v ω σ) σ)

theorem mem_kRl {p b : Fin (K + K)} {k : List Bool} :
    k ∈ kRl n key p b ↔ ∃ i : Fin U0, i.1 < (n p b).1 ∧ k = key (Fin.castAdd A' p, .init p b i) := by
  simp only [kRl, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem mem_kCl {p b : Fin (K + K)} {k : List Bool} :
    k ∈ kCl n key dkey p b ↔ ∃ i : Fin U0, i.1 < (n b p).1 ∧
      k = if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i) := by
  simp only [kCl, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem getElem_map_filter {U d : ℕ} (h : d ≤ U) (f : Fin U → List Bool) (i : Fin U) (hi : i.1 < d) :
    (((List.finRange U).filter fun k => k.1 < d).map f)[i.1]? = some (f i) := by
  rw [filter_finRange h, List.map_ofFn, List.getElem?_eq_getElem (by simpa using hi)]
  simp

section keys

variable (hkey : Function.Injective (Sum.elim key dkey))

include hkey

theorem key_injective : Function.Injective key := fun a b h => by
  have := hkey (a₁ := Sum.inl a) (a₂ := Sum.inl b) h
  simpa using this

theorem dkey_injective : Function.Injective dkey := fun a b h => by
  have := hkey (a₁ := Sum.inr a) (a₂ := Sum.inr b) h
  simpa using this

theorem key_ne_dkey (a : Cell M U0 U1) (b : Fin (K + K) × Fin U0) : key a ≠ dkey b := fun h => by
  have := hkey (a₁ := Sum.inl a) (a₂ := Sum.inr b) h
  simp at this

theorem nodup_PR (p : Fin (K + K)) (R : Option S → Fin (K + K) → List Γ) :
    ((PR n key cb p R).flatMap Prod.fst).Nodup := by
  have hk := key_injective hkey
  rw [PR, List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun b _ => ?_, (List.nodup_finRange _).imp fun {b b'} hb => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    have := hk h
    simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, rfl⟩ := mem_kRl.1 hk1
    obtain ⟨j, -, h⟩ := mem_kRl.1 hk2
    have := hk h
    simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
    exact hb this.1

theorem nodup_PC (p : Fin (K + K)) (C : Option S → Fin (K + K) → List Γ) :
    ((PC n key dkey cb p C).flatMap Prod.fst).Nodup := by
  have hk := key_injective hkey
  have hd := dkey_injective hkey
  rw [PC, List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun b _ => ?_, (List.nodup_finRange _).imp fun {b b'} hb => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    by_cases hbp : b = p
    · simp only [hbp, if_true] at h
      have := hd h
      simpa using this
    · simp only [hbp, if_false] at h
      have := hk h
      simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, h1⟩ := mem_kCl.1 hk1
    obtain ⟨j, -, h2⟩ := mem_kCl.1 hk2
    rw [h1] at h2
    by_cases hbp : b = p
    · have hbp' : b' ≠ p := fun h => hb (hbp.trans h.symm)
      rw [if_pos hbp, if_neg hbp'] at h2
      exact key_ne_dkey hkey _ _ h2.symm
    · rw [if_neg hbp] at h2
      by_cases hbp' : b' = p
      · rw [if_pos hbp'] at h2
        exact key_ne_dkey hkey _ _ h2
      · rw [if_neg hbp'] at h2
        have := hk h2
        simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
        exact hb this.1

theorem mem_PR {p : Fin (K + K)} {R : Option S → Fin (K + K) → List Γ} {k : List Bool} :
    k ∈ (PR n key cb p R).flatMap Prod.fst ↔ ∃ b, ∃ i : Fin U0, i.1 < (n p b).1 ∧
      k = key (Fin.castAdd A' p, .init p b i) := by
  rw [PR, List.ofFn_eq_map, List.flatMap_map, List.mem_flatMap]
  simp only [List.mem_finRange, true_and, mem_kRl]

theorem mem_PC {p : Fin (K + K)} {C : Option S → Fin (K + K) → List Γ} {k : List Bool} :
    k ∈ (PC n key dkey cb p C).flatMap Prod.fst ↔ ∃ b, ∃ i : Fin U0, i.1 < (n b p).1 ∧
      k = if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i) := by
  rw [PC, List.ofFn_eq_map, List.flatMap_map, List.mem_flatMap]
  simp only [List.mem_finRange, true_and, mem_kCl]

/-- The trie after a base party. -/
noncomputable def baseT (ub : ℕ) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (cb : Option Γ → Fin c → Bool) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) (t : Tree) : Tree :=
  putsAll ub (PC n key dkey cb p C) (putsAll ub (PR n key cb p R) t)

theorem baseT_R (p b : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) (i : Fin U0)
    (hi : i.1 < (n p b).1) : tget (key (Fin.castAdd A' p, .init p b i)) (baseT ub n key dkey cb p R C t) =
      ofBits (uwBits (unitsOf ub (strOf cb fun s => R s b) i)) := by
  rw [baseT, tget_putsAll_not (nodup_PC hkey p C)]
  · have hmem : (kRl n key p b, strOf cb fun s => R s b) ∈ PR n key cb p R :=
      List.mem_ofFn.2 ⟨b, rfl⟩
    exact tget_putsAll (nodup_PR hkey p R) hmem (getElem_map_filter (by have := (n p b).2; omega) _ i hi) t
  · rw [mem_PC hkey]
    rintro ⟨b', j, -, h⟩
    by_cases hb : b' = p
    · rw [if_pos hb] at h
      exact key_ne_dkey hkey _ _ h
    · rw [if_neg hb] at h
      have := key_injective hkey h
      simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
      exact hb this.1.symm

theorem baseT_C (p b : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) (i : Fin U0)
    (hi : i.1 < (n b p).1) : tget (if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i))
      (baseT ub n key dkey cb p R C t) = ofBits (uwBits (unitsOf ub (strOf cb fun s => C s b) i)) := by
  rw [baseT]
  have hmem : (kCl n key dkey p b, strOf cb fun s => C s b) ∈ PC n key dkey cb p C :=
    List.mem_ofFn.2 ⟨b, rfl⟩
  exact tget_putsAll (nodup_PC hkey p C) hmem (getElem_map_filter (by have := (n b p).2; omega)
    (fun k => if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)) i hi) _

theorem baseT_not (p : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) {k : List Bool}
    (h1 : ∀ b, ∀ i : Fin U0, i.1 < (n p b).1 → k ≠ key (Fin.castAdd A' p, .init p b i))
    (h2 : ∀ b, ∀ i : Fin U0, i.1 < (n b p).1 → k ≠ if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i)) :
    tget k (baseT ub n key dkey cb p R C t) = tget k t := by
  rw [baseT, tget_putsAll_not (nodup_PC hkey p C), tget_putsAll_not (nodup_PR hkey p R)]
  · rw [mem_PR hkey]
    rintro ⟨b, i, hi, h⟩
    exact h1 b i hi h
  · rw [mem_PC hkey]
    rintro ⟨b, i, hi, h⟩
    exact h2 b i hi h

/-- The contents after a base party. -/
theorem rep_baseT {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g) (R C : Option S → Fin (K + K) → List Γ) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) : Rep ub key (baseT ub n key dkey cb p R C t)
      (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
        (fun c => initV cb ub M.N U0 U1 R C p c.2) σ) := by
  refine ⟨h.1.putsAll.putsAll, fun c' => ?_⟩
  obtain ⟨a, id⟩ := c'
  by_cases hc : (a, id) ∈ (dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true
  · rw [ovr, if_pos hc]
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
    simp only at h2
    subst h2
    cases id with
    | new _ _ => simp [isInit] at h3
    | init a' b' k =>
      have hk : k.1 < (n a' b').1 := G.Plan.init_mem_seenAt.1 (mem_dom.1 h1).2.1
      simp only [initV]
      by_cases hap : a' = p
      · subst hap
        rw [if_pos rfl]
        exact baseT_R hkey a' b' R C t k hk
      · rw [if_neg hap]
        have hbp : b' = p := by
          rcases (mem_dom.1 h1).2.2 with h | h
          · exact absurd (Fin.castAdd_injective _ _ h).symm hap
          · exact (Fin.castAdd_injective _ _ h).symm
        subst hbp
        have := baseT_C (cb := cb) (ub := ub) hkey b' a' R C t k hk
        rw [if_neg hap] at this
        exact this
  · rw [ovr, if_neg hc, ← h.2]
    refine baseT_not hkey p R C t (fun b i hi he => hc ?_) fun b i hi he => hc ?_
    · have := key_injective hkey he
      rw [this]
      exact mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hi, Or.inl rfl⟩, rfl, rfl⟩
    · by_cases hb : b = p
      · rw [if_pos hb] at he
        exact absurd he (key_ne_dkey hkey _ _)
      · rw [if_neg hb] at he
        have := key_injective hkey he
        rw [this]
        exact mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hi, Or.inr rfl⟩, rfl, rfl⟩

/-- The comparison of the second copies. -/
theorem diag_iff (hub : 0 < ub) {p : Fin (K + K)} {R C : Option S → Fin (K + K) → List Γ}
    (hR : ucount ub (strOf cb fun s => R s p) = n p p) (hC : ucount ub (strOf cb fun s => C s p) = n p p) (t : Tree) :
    (∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
      tget (key (Fin.castAdd A' p, .init p p k)) (baseT ub n key dkey cb p R C t) =
        tget (dkey (p, k)) (baseT ub n key dkey cb p R C t)) ↔
      ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R s p) k = unitsOf ub (strOf cb fun s => C s p) k := by
  constructor
  · intro h k
    by_cases hk : k.1 < (n p p).1
    · have h1 := h k (by simp [hk])
      rw [baseT_R hkey p p R C t k hk] at h1
      have h2 := baseT_C (cb := cb) (ub := ub) hkey p p R C t k hk
      rw [if_pos rfl] at h2
      rw [h2] at h1
      refine G.uwBits_inj ?_ ?_ (ofBits_injective h1)
      · rw [Ne, unitsOf_eq_none]
        omega
      · rw [Ne, unitsOf_eq_none]
        omega
    · rw [unitsOf_eq_none.2 (by omega), unitsOf_eq_none.2 (by omega)]
  · intro h k hk
    have hk' : k.1 < (n p p).1 := by simpa using hk
    have h2 := baseT_C (cb := cb) (ub := ub) hkey p p R C t k hk'
    rw [if_pos rfl] at h2
    rw [h2, baseT_R hkey p p R C t k hk', h k]

end keys

open Classical in
/-- What a base party does with given letters. -/
theorem base_core (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2)
    {wl rl : Option S → List Γ} (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) {Ψ : Tree → A} {Ψ' : (Cell M U0 U1 → UW ub) → A}
    (hΨ : ∀ t' σ', Rep ub key t' σ' → Ψ t' = Ψ' σ') :
    sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t) (fun t' =>
        if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
          tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧
          InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ) else 0 := by
  have hK : 0 < K + K := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  rw [sumL_pack hub hK hρ hwl hrl h1 h2]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => ?_
  by_cases hc : (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧ (∀ s, RowOk (ρ s p) (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p)
  · rw [if_pos hc]
    obtain ⟨c1, c2, c3, c4, c5⟩ := hc
    have hd := diag_iff (cb := cb) hkey hub (c4 p) (c5 p) t
    by_cases hdiag : ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R.words s p) k = unitsOf ub (strOf cb fun s => C.words s p) k
    · refine (if_pos (hd.2 hdiag)).trans ?_
      rw [if_pos ⟨c1, c2, c3, c4, c5, hdiag⟩]
      exact hΨ _ _ (rep_baseT hkey hp R.words C.words h)
    · refine (if_neg fun hh => hdiag (hd.1 hh)).trans ?_
      rw [if_neg (fun hh => hdiag hh.2.2.2.2.2)]
  · rw [if_neg hc, if_neg fun hh => hc ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩]

theorem length_wr (w : List (Letter S Unit Γ)) (s : Option S) : (wr w s).length ≤ w.length := by
  cases s with
  | none => exact Nat.zero_le _
  | some s => exact length_emit_le w _

theorem length_rdr (w : List (Letter S Unit Γ)) (s : Option S) : (rdr w s).length ≤ w.length := by
  cases s with
  | none => exact length_emit_le w _
  | some s => exact length_emit_le w _

theorem emit_eq_vec {m : ℕ} (w : List (Letter S Unit Γ)) (R C : Option S → Fin m → List Γ) :
    ((∀ s, cat (R s) = wr w s) ∧ ∀ s, cat (C s) = rdr w s) ↔ (∀ b, R none b = []) ∧ emit w = vec R C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨cat_eq_nil.1 (h1 none), funext fun z => ?_⟩
    cases z with
    | tp s b =>
      cases b with
      | false => exact (h1 (some s)).symm
      | true => exact (h2 (some s)).symm
    | inp u => exact (h2 none).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun s => ?_, fun s => ?_⟩
    · cases s with
      | none => exact cat_eq_nil.2 h1
      | some s => exact (congrFun h2 (.tp s false)).symm
    · cases s with
      | none => exact (congrFun h2 (.inp ())).symm
      | some s => exact (congrFun h2 (.tp s true)).symm

open Classical in
/-- **The step of a base party.** -/
theorem stepOK_base (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) :
    StepOK θ T mu cb kinds key (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key dkey p)
      (baseStep mu T cb q x ρ n o grp g ub p) := by
  intro t σ Ψ Ψ' hrep hΨ
  -- the right side
  have hR : ∑ ω ∈ (baseStep mu T cb q x ρ n o grp g ub p).Om, (baseStep mu T cb q x ρ n o grp g ub p).w ω σ *
      Ψ' (ovr (baseStep mu T cb q x ρ n o grp g ub p).wr ((baseStep mu T cb q x ρ n o grp g ub p).v ω σ) σ) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        (if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          partyW mu T q x p R.words C.words else 0) *
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ) := by
    show ∑ ω ∈ (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T) ×ˢ
      (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T), _ = _
    rw [Finset.sum_product, sum_pi_pi_coe]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [sum_pi_pi_coe]
    rfl
  rw [hR]
  have hB : (fun t' => sumL (scriptSem (S := S) θ mu cb kinds T ub (((List.finRange U0).filter fun k => k.1 < (n p p).1).map
      fun k => Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))) t') Ψ) =
      fun t' => if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0 := by
    funext t'
    rw [sumL_boths]
    by_cases hh : ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t'
    · rw [if_pos hh, if_pos hh]
    · rw [if_neg hh, if_neg hh]
  unfold baseIns
  rw [sumL_script_cons, hB]
  refine Fin.addCases (motive := fun p => grp (Fin.castAdd A' p) = g → (∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) →
    sumL (insSem θ mu cb kinds T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) t)
      (fun t' => if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0) =
    ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        (if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          partyW mu T q x p R.words C.words else 0) *
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ)) ?_ ?_ p hp hρ
  · intro κ hp hρ
    rw [Fin.addCases_left, insSem, dif_pos ⟨(qn Q _).2, (qn Q _).2⟩, sumL_bindL, sumL_simSem mu cb hmu]
    have h1 : ∀ w : Fin T → Letter S Unit Γ, sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey (Fin.castAdd K κ))
        (outsOf cb (List.ofFn w)) t) (fun t' => if ∀ k ∈ (List.finRange U0).filter fun k =>
          k.1 < (n (Fin.castAdd K κ) (Fin.castAdd K κ)).1, tget (key (Fin.castAdd A' (Fin.castAdd K κ),
          .init (Fin.castAdd K κ) (Fin.castAdd K κ) k)) t' = tget (dkey (Fin.castAdd K κ, k)) t' then Ψ t' else 0) = _ :=
      fun w => base_core (n := n) (o := o) hkey hub hp hρ (T := T) (wl := wr (List.ofFn w)) (rl := rdr (List.ofFn w))
        (fun s => (length_wr _ s).trans (by simp)) (fun s => (length_rdr _ s).trans (by simp))
        (outsOf_left cb _) (outsOf_right cb _) hrep hΨ
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [partyW_block, blockW]
    by_cases hi : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s (Fin.castAdd K κ)) (Fin.castAdd K κ) R.words C.words
    · rw [if_pos hi]
      by_cases hn : ∀ b, R.words none b = []
      · rw [if_pos hn, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w _ => ?_
        have he := emit_eq_vec (List.ofFn w) R.words C.words
        by_cases hw : emit (List.ofFn w) = vec R.words C.words
        · obtain ⟨e1, e2⟩ := he.2 ⟨hn, hw⟩
          rw [if_pos hw, if_pos ⟨e1, e2, hi⟩]
        · rw [if_neg hw, if_neg fun hh => hw (he.1 ⟨hh.1, hh.2.1⟩).2, mul_zero, zero_mul]
      · rw [if_neg hn, zero_mul]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg fun hh => hn ((emit_eq_vec (List.ofFn w) R.words C.words).1 ⟨hh.1, hh.2.1⟩).1, mul_zero]
    · rw [if_neg hi, zero_mul]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg fun hh => hi hh.2.2, mul_zero]
  · intro κ hp hρ
    rw [Fin.addCases_right, insSem]
    have h1 := base_core (n := n) (o := o) hkey hub hp hρ (T := T) (wl := fun s => if s = none then x κ else []) (rl := fun _ => [])
      (out := inOuts (S := S) ((x κ).map (code cb)).reverse)
      (fun s => by split_ifs; exacts [hx κ, Nat.zero_le _]) (fun s => Nat.zero_le _)
      (fun i => inOuts_left cb (x κ) i) (fun i => inOuts_right cb (x κ) i) hrep hΨ
    refine h1.trans ?_
    refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => ?_
    rw [partyW_input]
    have he : ((∀ s, cat (R.words s) = if s = none then x κ else []) ∧ ∀ s, cat (C.words s) = []) ↔
        (∀ s b, R.words (some s) b = []) ∧ (∀ s b, C.words s b = []) ∧ cat (R.words none) = x κ := by
      constructor
      · rintro ⟨a, b⟩
        refine ⟨fun s => cat_eq_nil.1 ?_, fun s => cat_eq_nil.1 (b s), ?_⟩
        · have := a (some s)
          simpa using this
        · have := a none
          simpa using this
      · rintro ⟨a, b, d⟩
        refine ⟨fun s => ?_, fun s => cat_eq_nil.2 (b s)⟩
        cases s with
        | none => simpa using d
        | some s => simpa using cat_eq_nil.2 (a s)
    by_cases hi : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s (Fin.natAdd K κ)) (Fin.natAdd K κ) R.words C.words
    · rw [if_pos hi]
      by_cases hw : (∀ s b, R.words (some s) b = []) ∧ (∀ s b, C.words s b = []) ∧ cat (R.words none) = x κ
      · rw [if_pos hw, if_pos ⟨(he.2 hw).1, (he.2 hw).2, hi⟩, one_mul]
      · rw [if_neg hw, if_neg fun hh => hw (he.1 ⟨hh.1, hh.2.1⟩), zero_mul]
    · rw [if_neg hi, if_neg fun hh => hi hh.2.2, zero_mul]

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over the runs of the transducer of a role
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem chS_cons (L : G.Law A) (p : L.Ro) {B : ℕ} (z : Bk L p) (f : Fin B → Bk L p) (ν : L.CnAt p) :
    chS L p (Fin.cons z f : Fin (B + 1) → Bk L p) ν = (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ν)) ++ chS L p f ν := by
  unfold chS Nc.G.chString
  rw [List.ofFn_succ, List.flatten_cons]
  rfl

theorem headD_getD (w : List Bool) : w.headD false = w.getD 0 false := by cases w <;> rfl

theorem tail_getD (w : List Bool) (k : ℕ) : w.tail.getD k false = w.getD (k + 1) false := by cases w <;> simp

theorem sumL_role_gen (L : G.Law A) (p : L.Ro) (htab : ∀ i x g, ∃ e : WE, e.val θ = L.tab p i x g) (B : ℕ)
    (ins : Fin (slList L p).length → List Bool) (out : Fin (cnList L p).length → List Bool)
    (G : TSt 1 (slList L p).length (cnList L p).length Bool → A) :
    sumL (runL θ (roleTab θ L p) B (0, ins, out)) G = ∑ f : Fin B → Bk L p,
      (∏ k, L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD k false) (f k).2) *
        G (0, fun i => (ins i).drop B, fun j => (chS L p f ((cnList L p).get j)).reverse ++ out j) := by
  induction B generalizing ins out with
  | zero =>
    rw [runL, List.replicate_zero, foldL, sumL_single, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, List.drop_zero, chS, Nc.G.chString, List.ofFn_zero,
      List.flatten_nil, List.reverse_nil, List.nil_append]
  | succ B ih =>
    rw [sumL_runL_succ]
    have h1 : sumL (stepL θ (roleTab θ L p) (0, ins, out)) (fun s' => sumL (runL θ (roleTab θ L p) B s') G) =
        ∑ z : Bk L p, L.tab p z.1 (fun e => (ins (slIdx L p e)).headD false) z.2 *
          sumL (runL θ (roleTab θ L p) B (0, fun i => (ins i).tail, fun j =>
            (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ((cnList L p).get j))).reverse ++ out j)) G := by
      rw [stepL, roleTab, List.map_map, sumL_toList]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Function.comp_apply, Opt.app, we_val (htab _ _ _)]
    rw [h1, ← (Fin.consEquiv fun _ : Fin (B + 1) => Bk L p).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e1 : (Fin.consEquiv fun _ : Fin (B + 1) => Bk L p) (z, f) = Fin.cons z f := rfl
    rw [e1, Fin.prod_univ_succ, ← mul_assoc]
    congr 1
    · congr 1
      · show L.tab p z.1 (fun e => (ins (slIdx L p e)).headD false) z.2 =
          L.tab p z.1 (fun e => (ins (slIdx L p e)).getD 0 false) z.2
        simp only [headD_getD]
      · refine Finset.prod_congr rfl fun k _ => ?_
        show L.tab p (f k).1 (fun e => (ins (slIdx L p e)).tail.getD k false) (f k).2 =
          L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD (k + 1) false) (f k).2
        simp only [tail_getD]
    · congr 1
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · funext i
        show (ins i).tail.drop B = (ins i).drop (B + 1)
        cases ins i <;> simp
      · funext j
        show (chS L p f ((cnList L p).get j)).reverse ++ ((List.ofFn (L.lab z.1) ++
          List.ofFn (z.2 ((cnList L p).get j))).reverse ++ out j) =
          (chS L p (Fin.cons z f : Fin (B + 1) → Bk L p) ((cnList L p).get j)).reverse ++ out j
        rw [chS_cons]
        simp only [List.reverse_append, List.append_assoc]

theorem sumL_role (L : G.Law A) (p : L.Ro) (htab : ∀ i x g, ∃ e : WE, e.val θ = L.tab p i x g) (B : ℕ)
    (ins : Fin (slList L p).length → List Bool) (G : TSt 1 (slList L p).length (cnList L p).length Bool → A) :
    sumL (runL θ (roleTab θ L p) B (0, ins, fun _ => [])) G = ∑ f : Fin B → Bk L p,
      (∏ k, L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD k false) (f k).2) *
        G (0, fun i => (ins i).drop B, fun j => (chS L p f ((cnList L p).get j)).reverse) := by
  rw [sumL_role_gen L p htab]
  simp only [List.append_nil]

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The step of a role
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {tg : M.R → ℕ}

/-- The keys of the new units of a channel. -/
noncomputable def kNew (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) (ν : (M.kind r.1).CnAt r.2) :
    List (List Bool) := ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)

theorem kNew_eq (r : M.R) (ν : (M.kind r.1).CnAt r.2) : kNew o key r ν =
    ((List.finRange U1).filter fun k => k.1 < (o ⟨r.1, ν.1⟩).1 + 1).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k) := by
  unfold kNew
  congr 1
  refine List.filter_congr fun k _ => ?_
  rw [decide_eq_decide, Nat.lt_succ_iff]
  rfl

theorem length_kNew (r : M.R) (ν : (M.kind r.1).CnAt r.2) : (kNew o key r ν).length = (o ⟨r.1, ν.1⟩).1 + 1 := by
  rw [kNew_eq, List.length_map, filter_finRange (by have := (o ⟨r.1, ν.1⟩).2; omega), List.length_ofFn]

theorem mem_kNew {r : M.R} {ν : (M.kind r.1).CnAt r.2} {k : List Bool} :
    k ∈ kNew o key r ν ↔ ∃ i : Fin U1, i ≤ o ⟨r.1, ν.1⟩ ∧ k = key (M.rp r, .new ⟨r.1, ν.1⟩ i) := by
  simp only [kNew, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

/-- What a role writes. -/
noncomputable def PN (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) {B : ℕ}
    (f : Fin B → Bk (M.kind r.1) r.2) : List (List (List Bool) × List Bool) :=
  (cnList (M.kind r.1) r.2).map fun ν => (kNew o key r ν, chS (M.kind r.1) r.2 f ν)

theorem mem_cnList {L : G.Law A} {p : L.Ro} (ν : L.CnAt p) : ν ∈ cnList L p := Finset.mem_toList.2 (mem_univ ν)

theorem mem_PN {r : M.R} {B : ℕ} {f : Fin B → Bk (M.kind r.1) r.2} {k : List Bool} :
    k ∈ (PN o key r f).flatMap Prod.fst ↔ ∃ ν : (M.kind r.1).CnAt r.2, ∃ i : Fin U1, i ≤ o ⟨r.1, ν.1⟩ ∧
      k = key (M.rp r, .new ⟨r.1, ν.1⟩ i) := by
  rw [PN, List.flatMap_map, List.mem_flatMap]
  constructor
  · rintro ⟨ν, -, h⟩
    exact ⟨ν, mem_kNew.1 h⟩
  · rintro ⟨ν, h⟩
    exact ⟨ν, mem_cnList ν, mem_kNew.2 h⟩

theorem nodup_PN (hkey : Function.Injective key) (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) :
    ((PN o key r f).flatMap Prod.fst).Nodup := by
  rw [PN, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun ν _ => ?_, (Finset.nodup_toList _).imp fun {ν ν'} hν => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    have := hkey h
    simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, rfl⟩ := mem_kNew.1 hk1
    obtain ⟨j, -, h⟩ := mem_kNew.1 hk2
    have := hkey h
    simp only [Prod.mk.injEq, true_and, G.Uid.new.injEq, Sigma.mk.injEq, heq_eq_eq] at this
    exact hν (Subtype.ext this.1)

/-- The contents after a role. -/
theorem rep_role (hkey : Function.Injective key) {r : M.R} (hr : grp (M.rp r) = g) {B : ℕ}
    (f : Fin B → Bk (M.kind r.1) r.2) {t : Tree} {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) :
    Rep ub key (putsAll ub (PN o key r f) t)
      (ovr ((dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true) (fun c => roleV ub r f c.2) σ) := by
  refine ⟨h.1.putsAll, fun c' => ?_⟩
  obtain ⟨a, id⟩ := c'
  by_cases hc : (a, id) ∈ (dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true
  · rw [ovr, if_pos hc]
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
    simp only at h2
    subst h2
    cases id with
    | init _ _ _ => simp [isNewOf] at h3
    | new ν k =>
      simp only [isNewOf, decide_eq_true_eq] at h3
      have hk := (G.Plan.new_mem_seenAt.1 (mem_dom.1 h1).2.1).2
      obtain ⟨ν, rfl⟩ := exists_cnAt h3 (mem_dom.1 h1).2.2
      simp only
      rw [roleV_new]
      have hmem : (kNew o key r ν, chS (M.kind r.1) r.2 f ν) ∈ PN o key r f :=
        List.mem_map.2 ⟨ν, mem_cnList ν, rfl⟩
      refine tget_putsAll (nodup_PN hkey r f) hmem ?_ t
      simp only
      rw [kNew_eq]
      exact getElem_map_filter (by have := (o ⟨r.1, ν.1⟩).2; omega) _ k (Nat.lt_succ_of_le hk)
  · rw [ovr, if_neg hc, ← h.2, tget_putsAll_not (nodup_PN hkey r f)]
    rw [mem_PN]
    rintro ⟨ν, i, hi, he⟩
    have := hkey he
    rw [this] at hc
    exact hc (mem_filter.2 ⟨mem_dom.2 ⟨hr, G.Plan.new_mem_seenAt.2 ⟨r.1.2, hi⟩, holds_cnAt ν i⟩, rfl, by simp [isNewOf]⟩)

theorem uwBits_ne_nil (hub : 0 < ub) (w : UW ub) : uwBits w ≠ [] ↔ w ≠ none := by
  cases w with
  | none => simp [uwBits]
  | some w =>
    have : (List.ofFn w).length ≠ 0 := by
      rw [List.length_ofFn]
      omega
    simp only [uwBits, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    intro h
    rw [h] at this
    simp at this

theorem getD_append_replicate (l : List Bool) (m k : ℕ) : (l ++ List.replicate m false).getD k false = l.getD k false := by
  rcases lt_or_ge k l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default l _ h]
    rcases lt_or_ge (k - l.length) m with h' | h'
    · rw [List.getD_eq_getElem _ _ (by simpa using h'), List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (by simpa using h')]

open Classical in
/-- **The step of a role.** -/
theorem stepOK_role (hkey : Function.Injective key) (hub : 0 < ub) {r : M.R} (hr : grp (M.rp r) = g)
    (hkind : kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h) :
    StepOK (S := S) θ T mu cb kinds key [roleIns P n o key tg r] (roleStep P n o grp g ub r) := by
  intro t σ Ψ Ψ' hrep hΨ
  rw [sumL_script_cons]
  simp only [sumL_script_nil]
  rw [roleIns, insSem, hkind]
  simp only
  have hct : ∀ id, (tget (key (M.rp r, id)) t).path = uwBits (σ (M.rp r, id)) := by
    intro id
    rw [hrep.2, path_ofBits]
  have hpres : (∀ es ∈ (univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse), ∀ k ∈ es, (tget k t).path ≠ []) ↔
      ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none := by
    simp only [List.forall_mem_map, Finset.mem_toList, mem_univ, true_imp_iff, List.mem_reverse]
    refine forall_congr' fun e => forall₂_congr fun id _ => ?_
    rw [hct, uwBits_ne_nil hub]
  by_cases hp : ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none
  swap
  · rw [roleSem, if_neg fun h => hp (hpres.1 h), sumL_nil]
    symm
    refine Finset.sum_eq_zero fun f _ => ?_
    have : (roleStep P n o grp g ub r).w f σ = 0 := if_neg fun h => hp h.1
    rw [this, zero_mul]
  rw [roleSem, if_pos (hpres.2 hp), sumL_bindL, sumL_role _ _ htab]
  show _ = ∑ f : Fin (P.num n o r.1 * ub) → Bk (M.kind r.1) r.2, _
  refine Finset.sum_congr rfl fun f _ => ?_
  -- the streams
  have hins : ∀ e : (M.kind r.1).SlAt r.2, ∀ k : ℕ,
      ((((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) []).getD k false =
      (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false := by
    intro e k
    have hlt : (slIdx (M.kind r.1) r.2 e : ℕ) < ((univ : Finset ((M.kind r.1).SlAt r.2)).toList).length :=
      (slIdx (M.kind r.1) r.2 e).2
    have hget : ((univ : Finset ((M.kind r.1).SlAt r.2)).toList)[(slIdx (M.kind r.1) r.2 e : ℕ)]'hlt = e :=
      List.getElem_idxOf hlt
    have hlist : (((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) [] =
        (P.ids n o ⟨r.1, e.1⟩).flatMap fun id => uwBits (σ (M.rp r, id)) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_map]; exact hlt), List.getElem_map,
        List.getElem_map, hget, List.reverse_reverse, List.flatMap_map]
      exact List.flatMap_congr fun id _ => hct id
    rw [hlist, slotBits, getD_append_replicate]
  -- the strings
  have hkeys : ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) =
      (PN o key r f).map Prod.fst := by
    rw [PN, List.map_map]
    rfl
  have hstr : (List.ofFn fun j => ((chS (M.kind r.1) r.2 f ((cnList (M.kind r.1) r.2).get j)).reverse).reverse ++ [true]) =
      (PN o key r f).map fun z => z.2 ++ [true] := by
    rw [PN, List.map_map]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  simp only [hins]
  rw [hkeys, hstr, putsL_eq hub]
  have hcnt : (∀ z ∈ PN o key r f, ucount ub z.2 = z.1.length) ↔
      ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 := by
    rw [PN, List.forall_mem_map]
    constructor
    · intro h ν
      rw [h ν (mem_cnList ν), length_kNew]
    · intro h ν _
      rw [h ν, length_kNew]
  by_cases hc : ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1
  · rw [if_pos (hcnt.2 hc)]
    have hw : (roleStep P n o grp g ub r).w f σ = ∏ k, (M.kind r.1).tab r.2 (f k).1 (fun e =>
        (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false) (f k).2 := if_pos ⟨hp, hc⟩
    rw [hw]
    simp only [encT, List.map_cons, List.map_nil, sumL_single]
    congr 1
    exact hΨ _ _ (rep_role hkey hr f hrep)
  · rw [if_neg fun h => hc (hcnt.1 h)]
    have hw : (roleStep P n o grp g ub r).w f σ = 0 := if_neg fun h => hc h.2
    rw [hw, zero_mul]
    simp

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The value of a group as a sum over executions: the theorem
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

/-- The factor of a base party. -/
theorem phi_baseStep {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g) {y : Cell M U0 U1 → UW ub}
    (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    (baseStep mu T cb q x ρ n o grp g ub p).phi y =
      G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => y (Fin.castAdd A' p, id) := by
  classical
  rw [G.tabInit, ← Finset.sum_product']
  refine Finset.sum_congr rfl ?_
  rintro ⟨R, C⟩ -
  have key : ((∀ s, RowOk (ρ s p) (R s)) ∧
        (∀ b, ucount ub (strOf cb fun s => R s b) = n p b ∧
          ∀ k : Fin U0, y (Fin.castAdd A' p, .init p b k) = unitsOf ub (strOf cb fun s => R s b) k) ∧
        (∀ b, ucount ub (strOf cb fun s => C s b) = n b p ∧
          ∀ k : Fin U0, y (Fin.castAdd A' p, .init b p k) = unitsOf ub (strOf cb fun s => C s b) k)) ↔
      (∀ c ∈ (baseStep mu T cb q x ρ n o grp g ub p).wr, y c = initV cb ub M.N U0 U1 R C p c.2) ∧
        InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R C := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h1, fun b => (h2 b).1, fun b => (h3 b).1, fun k => ?_⟩
      · rintro ⟨a, id⟩ hc
        obtain ⟨h4, h5, h6⟩ := mem_filter.1 hc
        simp only at h5
        subst h5
        cases id with
        | new _ _ => simp [isInit] at h6
        | init a b k =>
          simp only [initV]
          by_cases hap : a = p
          · subst hap
            rw [if_pos rfl]
            exact (h2 b).2 k
          · rw [if_neg hap]
            have hbp : b = p := by
              rcases (mem_dom.1 h4).2.2 with h | h
              · exact absurd (Fin.castAdd_injective _ _ h).symm hap
              · exact (Fin.castAdd_injective _ _ h).symm
            subst hbp
            exact (h3 a).2 k
      · rw [← (h2 p).2 k, ← (h3 p).2 k]
    · rintro ⟨h1, h2, h3, h4, h5⟩
      have hin : ∀ a b (k : Fin U0), (a = p ∨ b = p) → k.1 < (n a b).1 →
          y (Fin.castAdd A' p, .init a b k) = initV cb ub M.N U0 U1 R C p (.init a b k) := by
        intro a b k hab hk
        refine h1 (Fin.castAdd A' p, .init a b k) (mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hk, ?_⟩, rfl, rfl⟩)
        rcases hab with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hout : ∀ a b (k : Fin U0), ¬ k.1 < (n a b).1 → y (Fin.castAdd A' p, .init a b k) = none := by
        intro a b k hk
        exact hy _ fun h => hk (G.Plan.init_mem_seenAt.1 (mem_dom.1 h).2.1)
      refine ⟨h2, fun b => ⟨h3 b, fun k => ?_⟩, fun b => ⟨h4 b, fun k => ?_⟩⟩
      · by_cases hk : k.1 < (n p b).1
        · rw [hin p b k (Or.inl rfl) hk, initV, if_pos rfl]
        · rw [hout p b k hk]
          exact (unitsOf_eq_none.2 (by rw [h3 b]; exact not_lt.1 hk)).symm
      · by_cases hk : k.1 < (n b p).1
        · rw [hin b p k (Or.inr rfl) hk, initV]
          by_cases hbp : b = p
          · subst hbp
            rw [if_pos rfl]
            exact h5 k
          · rw [if_neg hbp]
        · rw [hout b p k hk]
          exact (unitsOf_eq_none.2 (by rw [h4 b]; exact not_lt.1 hk)).symm
  by_cases hA : ∀ c ∈ (baseStep mu T cb q x ρ n o grp g ub p).wr, y c = initV cb ub M.N U0 U1 R C p c.2
  · by_cases h2 : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R C
    · exact (if_pos hA).trans ((if_pos h2).trans (if_pos (key.2 ⟨hA, h2⟩)).symm)
    · exact (if_pos hA).trans ((if_neg h2).trans (if_neg fun h => h2 (key.1 h).2).symm)
  · exact (if_neg hA).trans (if_neg fun h => hA (key.1 h).1).symm

/-- Choices in all blocks. -/
def bkEquiv (L : Law F) (p : L.Ro) (B : ℕ) : (Fin B → Bk L p) ≃
    Σ i : Fin B → L.I, ∀ k, ∀ ν : L.CnAt p, Fin (L.len (i k) ν) → Bool where
  toFun f := ⟨fun k => (f k).1, fun k => (f k).2⟩
  invFun z k := ⟨z.1 k, z.2 k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The factor of a role. -/
theorem phi_roleStep {r : M.R} (hr : grp (M.rp r) = g) {y : Cell M U0 U1 → UW ub}
    (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    (roleStep P n o grp g ub r).phi y = G.roleAt P n o r fun id => y (M.rp r, id) := by
  classical
  rw [G.roleAt, G.role]
  by_cases hne : ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, y (M.rp r, id) ≠ none
  swap
  · rw [if_neg hne, WStep.phi]
    refine Finset.sum_eq_zero fun f _ => ?_
    have : (roleStep P n o grp g ub r).w f y = 0 := if_neg fun h => hne h.1
    rw [this, ite_self]
  rw [if_pos hne, WStep.phi]
  have hsig := Finset.sum_sigma' (univ : Finset (Fin (P.num n o r.1 * ub) → (M.kind r.1).I)) (fun _ => univ)
    (fun i (g : ∀ k, ∀ ν : (M.kind r.1).CnAt r.2, Fin ((M.kind r.1).len (i k) ν) → Bool) =>
      if ∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1
          (chString (M.kind r.1).lab (fun j => (M.kind r.1).len j ν) i fun k => g k ν) (fun id => y (M.rp r, id))
        then ∏ k : Fin (P.num n o r.1 * ub), (M.kind r.1).tab r.2 (i k) (fun e =>
          (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => y (M.rp r, id)).getD k false) (g k) else 0)
  rw [hsig, Finset.univ_sigma_univ]
  refine Fintype.sum_equiv (bkEquiv (M.kind r.1) r.2 (P.num n o r.1 * ub)) _ _ fun f => ?_
  have key : (∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1
        (chS (M.kind r.1) r.2 f ν) (fun id => y (M.rp r, id))) ↔
      (∀ c ∈ (roleStep P n o grp g ub r).wr, y c = roleV ub r f c.2) ∧
        ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 := by
    constructor
    · intro h
      refine ⟨?_, fun ν => (h ν).1⟩
      rintro ⟨a, id⟩ hc
      obtain ⟨h4, h5, h6⟩ := mem_filter.1 hc
      simp only at h5
      subst h5
      cases id with
      | init _ _ _ => simp [isNewOf] at h6
      | new ν k =>
        simp only [isNewOf, decide_eq_true_eq] at h6
        obtain ⟨ν, rfl⟩ := exists_cnAt h6 (mem_dom.1 h4).2.2
        simp only
        rw [roleV_new]
        exact (h ν).2 k
    · rintro ⟨h1, h2⟩ ν
      refine ⟨h2 ν, fun k => ?_⟩
      by_cases hk : k ≤ o ⟨r.1, ν.1⟩
      · have hc : (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) ∈ (roleStep P n o grp g ub r).wr := by
          refine mem_filter.2 ⟨mem_dom.2 ⟨hr, G.Plan.new_mem_seenAt.2 ⟨r.1.2, hk⟩, holds_cnAt ν k⟩, rfl, ?_⟩
          simp [isNewOf]
        have := h1 _ hc
        rw [roleV_new] at this
        exact this
      · have : y (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) = none :=
          hy _ fun h => hk (G.Plan.new_mem_seenAt.1 (mem_dom.1 h).2.1).2
        show y (M.rp r, G.Uid.new ⟨r.1, ν.1⟩ k) = _
        rw [this]
        refine (unitsOf_eq_none.2 ?_).symm
        have h3 : (o ⟨r.1, ν.1⟩).1 < k.1 := not_le.1 hk
        show ucount ub (chS (M.kind r.1) r.2 f ν) ≤ k.1
        rw [h2 ν]
        exact h3
  by_cases h1 : ∀ c ∈ (roleStep P n o grp g ub r).wr, y c = roleV ub r f c.2
  · by_cases h2 : ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1
    · exact (if_pos h1).trans ((if_pos ⟨hne, h2⟩).trans (if_pos (key.2 ⟨h1, h2⟩)).symm)
    · exact (if_pos h1).trans ((if_neg fun h => h2 h.2).trans (if_neg fun h => h2 (key.1 h).2).symm)
  · exact (if_neg h1).trans (if_neg fun h => h1 (key.1 h).1).symm

/-- The product over the steps. -/
theorem prod_phi {y : Cell M U0 U1 → UW ub} (hy : ∀ c, c ∉ dom n o grp g → y c = none) :
    ((steps mu T cb P q x ρ n o grp g ub).map fun s => s.phi y).prod =
      ∏ a ∈ univ.filter (fun a => grp a = g), G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id) := by
  classical
  rw [steps, List.map_append, List.prod_append, List.map_map, List.map_map]
  have e1 : ((baseList grp g).map ((fun s => s.phi y) ∘ baseStep mu T cb q x ρ n o grp g ub)).prod =
      ∏ p ∈ univ.filter (fun p => grp (Fin.castAdd A' p) = g),
        G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => y (Fin.castAdd A' p, id) := by
    rw [← List.prod_toFinset _ nodup_baseList]
    refine Finset.prod_congr ?_ fun p hp => phi_baseStep (mem_filter.1 hp).2 hy
    ext p
    simp [mem_baseList]
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  have e2 : ((roleList grp g M).map ((fun s => s.phi y) ∘ roleStep P n o grp g ub)).prod =
      ∏ r ∈ univ.filter (fun r => grp (M.rp r) = g), G.roleAt P n o r fun id => y (M.rp r, id) := by
    rw [← List.prod_toFinset _ hnd]
    refine Finset.prod_congr ?_ fun r hr => phi_roleStep (mem_filter.1 hr).2 hy
    ext r
    simp [mem_roleList]
  rw [e1, e2]
  have e3 : ∀ a, (G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id)) =
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) *
        ∏ r : M.R, if M.rp r = a then G.roleAt P n o r (fun id => y (a, id)) else 1 := by
    intro a
    rw [G.tabFinal_eq, G.partyTab]
  rw [Finset.prod_congr rfl fun a _ => e3 a, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_filter, Finset.prod_filter]
    have h := Fin.prod_univ_add (fun a : Fin (K + K + A') => if grp a = g then
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) else 1)
    refine Eq.trans ?_ h.symm
    have h1 : (∏ p : Fin A', if grp (Fin.natAdd (K + K) p) = g then
        G.initAll mu T cb A' q x ρ n (Fin.natAdd (K + K) p) (fun id => y (Fin.natAdd (K + K) p, id)) else 1) = 1 := by
      refine Finset.prod_eq_one fun p _ => ?_
      rw [G.initAll, Fin.addCases_right, ite_self]
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [G.initAll, Fin.addCases_left]
  · rw [Finset.prod_comm, Finset.prod_filter]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.prod_ite_eq]
    simp only [mem_filter, mem_univ, true_and]

open Classical in
/-- **The value of a group is the sum over all executions of its steps.** -/
theorem grpVal_eq_exec [Fintype Gr] (hP : P.Ok cap) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    G.grpVal mu T cb P q x ρ n o grp g b = WStep.exec (steps mu T cb P q x ρ n o grp g ub)
      (fun y => if GAgree (G.hold0 M.np) (G.hold1 M.np) grp g (P.cur n o E) b (fun a id => y (a, id)) then 1 else 0)
      (fun _ => none) := by
  rw [← WStep.sum_eq_exec _ (seq_steps hP), G.grpVal, groupVal]
  refine Finset.sum_equiv (Equiv.curry (Fin (K + K + A')) (G.Uid (K + K) U0 M.N U1) (UW ub)).symm ?_ ?_
  · intro y
    rw [mem_gcontents_iff, mem_filter]
    simp only [mem_univ, true_and, wrs_steps]
    constructor
    · rintro h ⟨a, id⟩ hc
      exact h a id fun h' => hc (mem_dom.2 h')
    · intro h a id hc
      exact h (a, id) fun h' => hc (mem_dom.1 h')
  · intro y hy
    rw [mem_gcontents_iff] at hy
    have hy' : ∀ c, c ∉ dom n o grp g → (Equiv.curry (Fin (K + K + A')) (G.Uid (K + K) U0 M.N U1) (UW ub)).symm y c = none := by
      rintro ⟨a, id⟩ hc
      exact hy a id fun h' => hc (mem_dom.2 h')
    rw [prod_phi hy', mul_ite, mul_one, mul_zero]
    rfl

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# GROUP computes the value of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ}

/-- A list of steps. -/
theorem sumL_steps {ι : Type} (l : List ι) (I : ι → List Ins) (s : ι → WStep A (Cell M U0 U1) (UW ub))
    (h : ∀ i ∈ l, StepOK (S := S) θ T mu cb kinds key (I i) (s i)) (J : List Ins) (G : (Cell M U0 U1 → UW ub) → A)
    (hJ : ∀ t σ, Rep ub key t σ → sumL (scriptSem (S := S) θ mu cb kinds T ub J t) (fun _ => 1) = G σ) (t : Tree)
    (σ : Cell M U0 U1 → UW ub) (hr : Rep ub key t σ) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l.flatMap I ++ J) t) (fun _ => 1) = WStep.exec (l.map s) G σ := by
  induction l generalizing t σ with
  | nil => exact hJ t σ hr
  | cons i l ih =>
    rw [List.flatMap_cons, List.append_assoc, sumL_script_append, List.map_cons, WStep.exec]
    exact h i List.mem_cons_self t σ _ _ hr fun t' σ' hr' => ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) t' σ' hr'

/-- What is compared at a unit. -/
def EndOk (grp : Fin (K + K + A') → Gr) (g : Gr) (σ : Cell M U0 U1 → UW ub) (b : G.Uid (K + K) U0 M.N U1 → UW ub)
    (id : G.Uid (K + K) U0 M.N U1) : Prop :=
  (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) = g →
      uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))) ∧
    (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) ≠ g → uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)) ∧
    (grp (G.hold0 M.np id) ≠ g → grp (G.hold1 M.np id) = g → uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id))

open Classical in
/-- The last instructions compare. -/
theorem sumL_end (b : G.Uid (K + K) U0 M.N U1 → UW ub) (l : List (G.Uid (K + K) U0 M.N U1)) (t : Tree)
    (σ : Cell M U0 U1 → UW ub) (hr : Rep ub key t σ) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l.filterMap fun id =>
      if grp (G.hold0 M.np id) = g then
        if grp (G.hold1 M.np id) = g then some (.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
        else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
      else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
      else none) t) (fun _ => 1) =
    if ∀ id ∈ l, EndOk grp g σ b id then 1 else 0 := by
  have hof : ∀ v w : List Bool, ofBits v = ofBits w ↔ v = w := fun v w => ofBits_injective.eq_iff
  induction l with
  | nil => simp [sumL_script_nil]
  | cons id l ih =>
    have hcons : (∀ i ∈ id :: l, EndOk grp g σ b i) ↔ EndOk grp g σ b id ∧ ∀ i ∈ l, EndOk grp g σ b i :=
      List.forall_mem_cons
    by_cases h0 : grp (G.hold0 M.np id) = g
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_pos h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.1 h0 h1)]
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_neg h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.2.1 h0 h1)]
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_neg h0, if_pos h1]), sumL_script_cons, insSem]
        simp only [hr.2, hof]
        by_cases he : uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, sumL_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, sumL_nil, if_neg fun h => he ((hcons.1 h).1.2.2 h0 h1)]
      · rw [List.filterMap_cons_none (by rw [if_neg h0, if_neg h1]), ih]
        refine if_congr ?_ rfl rfl
        rw [hcons]
        simp [EndOk, h0, h1]

theorem uwBits_injective (hub : 0 < ub) : Function.Injective (uwBits (ub := ub)) := by
  intro v w h
  by_cases hv : v = none
  · by_cases hw : w = none
    · rw [hv, hw]
    · have := (uwBits_ne_nil hub w).2 hw
      rw [← h, hv] at this
      exact absurd rfl this
  · by_cases hw : w = none
    · have := (uwBits_ne_nil hub v).2 hv
      rw [h, hw] at this
      exact absurd rfl this
    · exact G.uwBits_inj hv hw h

theorem rep_nil : Rep ub key .nil (fun _ : Cell M U0 U1 => none) :=
  ⟨tOk_nil ub, fun c => by rw [tget_nil]; rfl⟩

/-- **GROUP computes the value of a group.** -/
theorem sumL_script [Fintype Gr] (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub) (hP : P.Ok cap)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) .nil) (fun _ => 1) =
      G.grpVal mu T cb P q x ρ n o grp g b := by
  classical
  rw [grpVal_eq_exec hP]
  have hk : Function.Injective key := key_injective hkey
  -- one list of steps
  let I : Fin (K + K) ⊕ M.R → List Ins := Sum.elim (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key dkey)
    fun r => [roleIns P n o key tg r]
  let s : Fin (K + K) ⊕ M.R → WStep A (Cell M U0 U1) (UW ub) := Sum.elim (baseStep mu T cb q x ρ n o grp g ub)
    (roleStep P n o grp g ub)
  let l : List (Fin (K + K) ⊕ M.R) := (baseList (A' := A') grp g).map Sum.inl ++ (roleList grp g M).map Sum.inr
  have hl : l.map s = steps mu T cb P q x ρ n o grp g ub := by
    simp only [l, s, List.map_append, List.map_map, steps]
    rfl
  have hI : script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b = l.flatMap I ++ endIns P n o grp g key b := by
    simp only [l, I, List.flatMap_append, List.flatMap_map, script, Sum.elim_inl, Sum.elim_inr]
    rw [flatMap_single]
  rw [hI, ← hl]
  refine sumL_steps (key := key) l I s ?_ _ _ ?_ _ _ rep_nil
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
      exact stepOK_base hkey hub hmu hx (mem_baseList.1 hp) fun s => hρ s p
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
      exact stepOK_role hk hub (mem_roleList.1 hr) (hkind r) (htab r)
  · intro t σ hr
    rw [endIns, sumL_end b _ t σ hr]
    refine if_congr ?_ rfl rfl
    have huw : ∀ v w : UW ub, uwBits v = uwBits w ↔ v = w := fun v w => (uwBits_injective hub).eq_iff
    simp only [List.mem_filter, G.allIds, Finset.mem_toList, mem_univ, true_and, decide_eq_true_eq, EndOk, huw]
    constructor
    · intro h
      exact ⟨fun id hid => (h id hid).1, fun id hid => (h id hid).2.1, fun id hid => (h id hid).2.2⟩
    · intro h id hid
      exact ⟨h.both id hid, h.fst id hid, h.snd id hid⟩

/-- The conditions on the instructions hold. -/
theorem insOk_script (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    ∀ i ∈ script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b, InsOk S Q c kinds i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, -, hi⟩ := List.mem_flatMap.1 hi
      rcases List.mem_cons.1 hi with rfl | hi
      · refine Fin.addCases (motive := fun p => InsOk S Q c kinds (Fin.addCases (motive := fun _ => Ins)
          (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
          (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p))
          ?_ ?_ p
        · intro κ
          rw [Fin.addCases_left]
          exact ⟨(qn Q _).2, (qn Q _).2⟩
        · intro κ
          rw [Fin.addCases_right]
          intro a ha
          rw [List.mem_reverse] at ha
          obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
          simp
      · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
        trivial
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hi
      exact ⟨_, hkind r, by simp [slList]⟩
  · obtain ⟨id, -, h⟩ := List.mem_filterMap.1 hi
    split_ifs at h
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Bounds that follow from one contributing choice

The numbers of units that a party holds at the beginning, and the outcomes of the moves.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
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

/-- The number of units of the strings to (or from) all parties. -/
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

end Nc.Cut

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# What an accepting run of GROUP tells

The numbers of units of the base parties and the outcomes of the moves are bounded if GROUP has an accepting run.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A B' : Type} [CommRing A] [CommRing B'] {θ : List Bool → A} {α β ε : Type}

theorem snd_bindL (l : List (A × α)) (f : α → List (A × β)) :
    (bindL l f).map Prod.snd = (l.map Prod.snd).flatMap fun a => (f a).map Prod.snd := by
  simp only [bindL, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem snd_foldL {f : ε → β → List (A × β)} {f' : ε → β → List (B' × β)}
    (h : ∀ x s, (f x s).map Prod.snd = (f' x s).map Prod.snd) (xs : List ε) (s : β) :
    (foldL f xs s).map Prod.snd = (foldL f' xs s).map Prod.snd := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [foldL, foldL, snd_bindL, snd_bindL, h]
    exact List.flatMap_congr fun a _ => ih a

theorem snd_segsL (sep : List Bool) (items : List Item) (accs : List (List Bool)) :
    (segsL A sep items accs).map Prod.snd = (segsL B' sep items accs).map Prod.snd := by
  refine snd_foldL (fun it s => ?_) items accs
  simp [segOne]

variable {S : Type} [Fintype S] [DecidableEq S]

theorem snd_packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) :
    (packSem A sep ub B o t).map Prod.snd = (packSem B' sep ub B o t).map Prod.snd := by
  simp only [packSem, snd_bindL, snd_segsL (A := A) (B' := B'), encT, List.map_map, Function.comp_def]

/-- All weights are 1. -/
def Ones (l : List (A × α)) : Prop := ∀ p ∈ l, p.1 = 1

theorem Ones.bindL {l : List (A × α)} {f : α → List (A × β)} (hl : Ones l) (hf : ∀ a, Ones (f a)) : Ones (bindL l f) := by
  intro p hp
  unfold Grp.bindL at hp
  obtain ⟨a, ha, hp⟩ := List.mem_flatMap.1 hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
  simp only [hl a ha, hf _ r hr, mul_one]

theorem ones_map (l : List α) (g : α → β) : Ones (l.map fun t => ((1 : A), g t)) := by
  intro p hp
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hp
  rfl

theorem Ones.foldL {f : ε → β → List (A × β)} (hf : ∀ x s, Ones (f x s)) (xs : List ε) (s : β) : Ones (foldL f xs s) := by
  induction xs generalizing s with
  | nil =>
    intro p hp
    rw [Grp.foldL, List.mem_singleton] at hp
    rw [hp]
  | cons x xs ih => exact Ones.bindL (hf x s) ih

theorem ones_packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) : Ones (packSem A sep ub B o t) := by
  have hs : ∀ items accs, Ones (segsL A sep items accs) := fun items accs =>
    Ones.foldL (fun it s => ones_map _ _) items accs
  refine (hs _ _).bindL fun sR => (ones_map _ _).bindL fun t1 => (hs _ _).bindL fun sC => ones_map _ _

theorem sumL_ones {l : List (ℤ × α)} (h : Ones l) : sumL l (fun _ => 1) = l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [sumL_cons, ih fun q hq => h q (List.mem_cons_of_mem _ hq), h p List.mem_cons_self, List.length_cons]
    push_cast
    ring

theorem foldL_ne_nil {f : ε → β → List (A × β)} {xs : List ε} {s : β} (h : foldL f xs s ≠ []) :
    ∀ x ∈ xs, ∃ s', f x s' ≠ [] := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rw [foldL] at h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨a, ha, r, hr, -⟩ := mem_bindL hp
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨s, List.ne_nil_of_mem ha⟩
    · exact ih (List.ne_nil_of_mem hr) y hy

variable {Γ Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ}

/-- What is simulated are the letters of a run. -/
theorem mem_runL_sim (k : ℕ) (s : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool)) :
    ∀ r ∈ runL θ (simTab θ mu cb) k s, ∃ w : List (Letter S Unit Γ), w.length = k ∧
      r.2.2.2 = fun j => w.reverse.flatMap (fun z => pushOf cb z j) ++ s.2.2 j := by
  induction k generalizing s with
  | zero =>
    intro r hr
    rw [runL, List.replicate_zero, foldL, List.mem_singleton] at hr
    subst hr
    exact ⟨[], rfl, rfl⟩
  | succ k ih =>
    intro r hr
    rw [runL, List.replicate_succ, foldL] at hr
    obtain ⟨a, ha, r', hr', e⟩ := mem_bindL hr
    obtain ⟨op, hop, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hop
    obtain ⟨w, hw, e'⟩ := ih _ r' hr'
    refine ⟨z.1 :: w, by rw [List.length_cons, hw], ?_⟩
    rw [e, e']
    funext j
    simp [Opt.app]

theorem mem_simSem {T : ℕ} {a b : Fin (Fintype.card Q)} {r : A × Outs S} (h : r ∈ simSem θ mu cb T a b) :
    ∃ w : List (Letter S Unit Γ), w.length = T ∧ r.2 = outsOf cb w := by
  obtain ⟨s, hs, z, hz, e⟩ := mem_bindL h
  obtain ⟨w, hw, e'⟩ := mem_runL_sim T _ s hs
  refine ⟨w, hw, ?_⟩
  split_ifs at hz
  · rw [List.mem_singleton] at hz
    rw [e, hz]
    simp only
    rw [e']
    funext j
    simp [outsOf]
  · simp at hz

/-- From a result of a base party. -/
theorem exists_of_pack (hub : 0 < ub) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {wl rl : Option S → List Γ}
    (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) {t : Tree}
    (h : packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t ≠ []) :
    ∃ R C : Option S → Fin (K + K) → List Γ, (∀ s, cat (R s) = wl s) ∧ (∀ s, cat (C s) = rl s) ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p := by
  have hK : 0 < K + K := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  have h3 : packSem ℤ (sepOf cb) ub (bodyOf ρ n key dkey p) out t ≠ [] := by
    intro h0
    have := snd_packSem (A := A) (B' := ℤ) (sepOf cb) ub (bodyOf ρ n key dkey p) out t
    rw [h0, List.map_nil, List.map_eq_nil_iff] at this
    exact h this
  have h4 := sumL_ones (ones_packSem (A := ℤ) (sepOf cb) ub (bodyOf ρ n key dkey p) out t)
  rw [sumL_pack hub hK hρ hwl hrl h1 h2] at h4
  have h5 : ((packSem ℤ (sepOf cb) ub (bodyOf ρ n key dkey p) out t).length : ℤ) ≠ 0 := by
    have := List.length_pos_iff.2 h3
    omega
  rw [← h4] at h5
  obtain ⟨R, -, hR⟩ := Finset.exists_ne_zero_of_sum_ne_zero h5
  obtain ⟨C, -, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero hR
  split_ifs at hC with hc
  · exact ⟨R.words, C.words, hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  · exact absurd rfl hC

theorem sum_wr_le (w : List (Letter S Unit Γ)) : ∑ s, (wr w s).length ≤ w.length := by
  have h1 : ∑ z, (emit w z).length ≤ w.length := by
    unfold emit
    rw [sum_length_proj]
    exact List.reduceOption_length_le w
  refine le_trans ?_ h1
  rw [Fintype.sum_option]
  simp only [wr, List.length_nil, zero_add]
  rw [← Finset.sum_image (f := fun z : Ch S Unit => (emit w z).length) (s := univ) (g := fun s : S => .tp s false)]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro s _ s' _ e
    simpa using e

theorem sum_rdr_le (w : List (Letter S Unit Γ)) : ∑ s, (rdr w s).length ≤ w.length := by
  have h1 : ∑ z, (emit w z).length ≤ w.length := by
    unfold emit
    rw [sum_length_proj]
    exact List.reduceOption_length_le w
  refine le_trans ?_ h1
  let f : Option S → Ch S Unit := fun s => s.elim (.inp ()) fun s => .tp s true
  have hf : ∑ s, (rdr w s).length = ∑ s, (emit w (f s)).length := by
    refine Finset.sum_congr rfl fun s _ => ?_
    cases s <;> simp [f, rdr]
  have inj : Function.Injective f := by
    intro s s' e
    cases s <;> cases s' <;> simp [f] at e ⊢
    exact e
  rw [hf, ← Finset.sum_image (f := fun z : Ch S Unit => (emit w z).length) (s := univ) (g := f)
    fun s _ s' _ e => inj e]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **(i)** The numbers of units of the base parties of the group. -/
theorem count_of_accept (hub : 0 < ub) (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {b : G.Uid (K + K) U0 M.N U1 → UW ub} {t : Tree}
    (h : scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) t ≠ []) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) :
    ∑ b, ((n p b : ℕ) + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  have hmem : Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p ∈
      script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, mem_baseList.2 hp, List.mem_cons_self⟩))
  obtain ⟨t', ht'⟩ := foldL_ne_nil h _ hmem
  have key1 : ∃ R C : Option S → Fin (K + K) → List Γ, ∑ s, (cat (R s)).length ≤ T ∧ ∑ s, (cat (C s)).length ≤ T ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p := by
    revert ht'
    refine Fin.addCases (motive := fun p => insSem θ mu cb kinds T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) t' ≠ [] →
      ∃ R C : Option S → Fin (K + K) → List Γ, ∑ s, (cat (R s)).length ≤ T ∧ ∑ s, (cat (C s)).length ≤ T ∧
      (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧ ∀ b, ucount ub (strOf cb fun s => C s b) = n b p) ?_ ?_ p
    · intro κ ht'
      rw [Fin.addCases_left, insSem, dif_pos ⟨(qn Q _).2, (qn Q _).2⟩] at ht'
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ht'
      obtain ⟨a, ha, r', hr', -⟩ := mem_bindL hr
      obtain ⟨w, hw, ew⟩ := mem_simSem ha
      rw [ew] at hr'
      obtain ⟨R, C, h1, h2, h3, h4⟩ := exists_of_pack (A := A) (T := T) hub (fun s => hρ s _) (wl := wr w) (rl := rdr w)
        (fun s => hw ▸ length_wr w s) (fun s => hw ▸ length_rdr w s) (outsOf_left cb w) (outsOf_right cb w)
        (List.ne_nil_of_mem hr')
      refine ⟨R, C, ?_, ?_, h3, h4⟩
      · simp only [h1]
        exact hw ▸ sum_wr_le w
      · simp only [h2]
        exact hw ▸ sum_rdr_le w
    · intro κ ht'
      rw [Fin.addCases_right, insSem] at ht'
      obtain ⟨R, C, h1, h2, h3, h4⟩ := exists_of_pack (A := A) (T := T) hub (fun s => hρ s _)
        (wl := fun s => if s = none then x κ else []) (rl := fun _ => [])
        (fun s => by split_ifs; exacts [hx κ, Nat.zero_le _]) (fun s => Nat.zero_le _)
        (fun i => inOuts_left cb (x κ) i) (fun i => inOuts_right cb (x κ) i) ht'
      refine ⟨R, C, ?_, ?_, h3, h4⟩
      · simp only [h1]
        rw [Fintype.sum_option]
        simpa using hx κ
      · simp only [h2]
        simp
  obtain ⟨R, C, h1, h2, h3, h4⟩ := key1
  have e1 : ∑ b, (n p b : ℕ) ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => (h3 b).symm]
    exact sum_ucount_le h1
  have e2 : ∑ b, (n b p : ℕ) ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => (h4 b).symm]
    exact sum_ucount_le h2
  rw [Finset.sum_add_distrib]
  omega

/-- The output lists of the transducer of a role. -/
theorem mem_runL_roleTab (L : G.Law A) (p : L.Ro) (B : ℕ) (s : TSt 1 (slList L p).length (cnList L p).length Bool) :
    ∀ r ∈ runL θ (roleTab θ L p) B s, ∃ f : Fin B → Bk L p,
      ∀ j, r.2.2.2 j = (chS L p f ((cnList L p).get j)).reverse ++ s.2.2 j := by
  induction B generalizing s with
  | zero =>
    intro r hr
    rw [runL, List.replicate_zero, foldL, List.mem_singleton] at hr
    subst hr
    exact ⟨Fin.elim0, fun j => by simp [chS, G.chString]⟩
  | succ B ih =>
    intro r hr
    rw [runL, List.replicate_succ, foldL] at hr
    obtain ⟨a, ha, r', hr', e⟩ := mem_bindL hr
    obtain ⟨op, hop, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hop
    obtain ⟨f, hf⟩ := ih _ r' hr'
    refine ⟨Fin.cons z f, fun j => ?_⟩
    rw [e, hf, chS_cons]
    simp [Opt.app]

theorem putsL_ne_nil {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} (h : putsL ub kss strs t ≠ [])
    {P : List (List (List Bool) × List Bool)} (hub : 0 < ub) (h1 : kss = P.map Prod.fst)
    (h2 : strs = P.map fun p => p.2 ++ [true]) : ∀ p ∈ P, ucount ub p.2 = p.1.length := by
  rw [h1, h2, putsL_eq hub] at h
  by_contra hc
  rw [if_neg hc] at h
  exact h rfl

/-- **(ii)** The outcomes of the moves at the roles of the group. -/
theorem outcome_of_accept (hub : 0 < ub) (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    {b : G.Uid (K + K) U0 M.N U1 → UW ub} {t : Tree}
    (h : scriptSem (S := S) θ mu cb kinds T ub
      (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) t ≠ []) {r : M.R} (hr : grp (M.rp r) = g) :
    ∃ ι : Fin (P.num n o r.1 * ub) → (M.kind r.1).I, ∀ ν : (M.kind r.1).CnAt r.2,
      (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / ub := by
  have hmem : roleIns P n o key tg r ∈ script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨r, mem_roleList.2 hr, rfl⟩))
  obtain ⟨t', ht'⟩ := foldL_ne_nil h _ hmem
  rw [roleIns, insSem, hkind] at ht'
  simp only [roleSem] at ht'
  split_ifs at ht' with hs
  swap
  · exact absurd rfl ht'
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ ht'
  obtain ⟨a, ha, z', hz', -⟩ := mem_bindL hz
  obtain ⟨f, hf⟩ := mem_runL_roleTab (M.kind r.1) r.2 _ _ a ha
  have hne : putsL ub ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k))
      (List.ofFn fun j => (a.2.2.2 j).reverse ++ [true]) t' ≠ [] :=
    List.ne_nil_of_mem (mem_encT hz')
  have hkeys : ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) =
      (PN o key r f).map Prod.fst := by
    rw [PN, List.map_map]
    rfl
  have hstr : (List.ofFn fun j => (a.2.2.2 j).reverse ++ [true]) = (PN o key r f).map fun z => z.2 ++ [true] := by
    rw [PN, List.map_map]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp [hf]
  have hcnt := putsL_ne_nil hne hub hkeys hstr
  refine ⟨fun k => (f k).1, fun ν => ?_⟩
  have h1 := hcnt (kNew o key r ν, chS (M.kind r.1) r.2 f ν) (List.mem_map.2 ⟨ν, mem_cnList ν, rfl⟩)
  simp only at h1
  rw [length_kNew, ucount, Nat.add_right_cancel_iff] at h1
  rw [← h1]
  congr 1
  rw [chS, G.length_chString]

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program GROUP: the theorem

For a fixed automaton and a fixed list of roles of laws there is one formula GROUP. Its plain sum at the script of a group
is the value of the group; accepting runs exist only if the numbers of units are bounded.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}

/-- The time of GROUP at a script. -/
def grpTime (bT bub : List Bool) (l : List Ins) : ℕ :=
  (bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) + (l.map (insCost (bval bT) (bval bub))).sum + l.length

/-- **GROUP.** -/
theorem exists_group (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)
    (kinds : List (Σ L : G.Law A, L.Ro)) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds, ∀ i y h, ∃ e : WE, e.val θ = z.1.tab z.2 i y h) :
    ∃ (GROUP : Fm) (κ : ℕ), ∀ {A' K E U0 U1 cap : ℕ} {Gr : Type} [DecidableEq Gr] [Fintype Gr]
      {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr) (key : Cell M U0 U1 → List Bool)
      (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
      (b : G.Uid (K + K) U0 M.N U1 → UW (bval bub)),
      Function.Injective (Sum.elim key dkey) → 0 < bval bub → P.Ok cap → (∀ κ, (x κ).length ≤ bval bT) →
      (∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) → (∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) →
      Plain θ (κ * grpTime bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))
        (.cons GROUP.code (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))) ∧
      pv θ (.cons GROUP.code (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))) =
        G.grpVal mu (bval bT) cb P q x ρ n o grp g b ∧
      (evl θ GROUP (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b)) ≠ [] →
        (∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤
          2 * ((bval bT + (K + K) * (Fintype.card S + 1)) * c / bval bub + (K + K))) ∧
        ∀ r : M.R, grp (M.rp r) = g → ∃ ι : Fin (P.num n o r.1 * bval bub) → (M.kind r.1).I,
          ∀ ν : (M.kind r.1).CnAt r.2,
            (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / bval bub) := by
  obtain ⟨F, κ, hF⟩ := ex_group (S := S) (θ := θ) mu cb kinds (by simp [sepOf])
  refine ⟨F, κ, fun {A' K E U0 U1 cap Gr} _ _ {M} P q x ρ n o grp g key dkey tg bT bub b hkey hub hP hx hρ hkind => ?_⟩
  have h1 := hF bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) (insOk_script hkind b)
  have htab' : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h := fun r =>
    htab ⟨M.kind r.1, r.2⟩ (List.mem_of_getElem? (hkind r))
  have h2 := sumL_script (cb := cb) (kinds := kinds) (tg := tg) hkey hub hP hmu hx hρ hkind htab' (q := q) (o := o) (n := n)
    (grp := grp) (g := g) b
  obtain ⟨p1, p2⟩ := h1.plain
  refine ⟨p1, ?_, fun hacc => ?_⟩
  · rw [p2, ← h2, sumL, List.map_map]
    congr 1
    exact List.map_congr_left fun z _ => by simp
  · have hne : scriptSem (S := S) θ mu cb kinds (bval bT) (bval bub)
        (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) .nil ≠ [] := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hacc
      obtain ⟨-, -, z, hz, -⟩ := h1.evl.1 r hr
      obtain ⟨z', hz', -⟩ := List.mem_map.1 hz
      exact List.ne_nil_of_mem hz'
    exact ⟨fun p hp => count_of_accept hub hx hρ hne hp, fun r hr => outcome_of_accept hub hkind hne hr⟩

end Nc.Grp

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The time of GROUP at the script of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

section lists

theorem sum_le_length_mul {ι : Type*} (l : List ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ l, f i ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, add_comm]
    exact Nat.add_le_add (ih fun i hi => h i (by simp [hi])) (h i (by simp))

/-- Costs of writing, from the number of keys. -/
theorem putCost_le {ub Lc : ℕ} (kss : List (List (List Bool))) (h : ∀ ks ∈ kss, ∀ k ∈ ks, k.length ≤ Lc) :
    putCost ub kss ≤ (kss.map List.length).sum * (330 * (ub + Lc + 1)) + 200 * kss.length := by
  unfold putCost
  induction kss with
  | nil => simp
  | cons ks kss ih =>
    have h1 := ih fun ks' hks => h ks' (by simp [hks])
    have h2 : (ks.map fun k => ub * 90 + k.length * 60 + 330).sum ≤ ks.length * (330 * (ub + Lc + 1)) := by
      refine sum_le_length_mul _ _ _ fun k hk => ?_
      have := h ks (by simp) k hk
      nlinarith
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, add_mul]
    omega

theorem length_filter_lt (U m : ℕ) : ((List.finRange U).filter fun k => k.1 < m).length ≤ m := by
  have hnd : ((List.finRange U).filter fun k => k.1 < m).Nodup := (List.nodup_finRange U).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  calc _ ≤ (range m).card := by
        refine Finset.card_le_card_of_injOn Fin.val ?_ (fun a _ b _ e => Fin.ext e)
        intro k hk
        simpa using hk
    _ = m := Finset.card_range m

theorem length_filterMap_le {α β : Type*} (f : α → Option β) (l : List α) :
    (l.filterMap f).length = (l.filter fun a => (f a).isSome).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    cases h : f a with
    | none => simp [ih]
    | some b => simp [ih]

end lists

section group

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1)
  (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)
  (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ)

/-- The number of copies of units that the parties of the group ever hold. -/
def evG : ℕ := ∑ p ∈ univ.filter (fun p => grp p = g),
  ((Plan.seenAt n o E : Finset (G.Uid (K + K) U0 M.N U1)).filter (Holds (G.hold0 M.np) (G.hold1 M.np) p)).card

/-- The number of units of zeros and of counts. -/
def pdG : ℕ := ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g),
  (1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1

/-- The number of units of a base party at the beginning. -/
def inN (p : Fin (K + K)) : ℕ := ∑ b, ((n p b).1 + (n b p).1)

theorem card_dom : (dom n o grp g : Finset (Cell M U0 U1)).card = evG n o grp g := by
  unfold evG
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ.filter fun p => grp p = g)]
  · refine Finset.sum_congr rfl fun p hp => ?_
    refine Finset.card_bij' (fun c _ => c.2) (fun id _ => (p, id)) ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨h1, h2⟩ := mem_filter.1 hc
      obtain ⟨-, h3, h4⟩ := mem_dom.1 h1
      exact mem_filter.2 ⟨h3, h2 ▸ h4⟩
    · intro id hid
      obtain ⟨h1, h2⟩ := mem_filter.1 hid
      exact mem_filter.2 ⟨mem_dom.2 ⟨(mem_filter.1 hp).2, h1, h2⟩, rfl⟩
    · intro c hc
      exact Prod.ext (mem_filter.1 hc).2.symm rfl
    · intro id _
      rfl
  · intro c hc
    exact mem_filter.2 ⟨mem_univ _, (mem_dom.1 hc).1⟩

variable {qn cb P q x ρ n o grp g key dkey tg}

/-- The channels of the roles of the group. -/
theorem sum_cn_le : ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g),
    ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1) ≤ evG n o grp g := by
  rw [← card_dom]
  let Sg : Finset (Σ r : M.R, Σ _ : (M.kind r.1).CnAt r.2, Fin U1) :=
    (univ.filter fun r : M.R => grp (M.rp r) = g).sigma fun r => univ.sigma fun ν => univ.filter fun k => k ≤ o ⟨r.1, ν.1⟩
  have h1 : ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g),
      ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1) = Sg.card := by
    simp only [Sg]
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have h2 : (univ.filter fun k : Fin U1 => k ≤ o ⟨r.1, ν.1⟩) = Finset.Iic (o ⟨r.1, ν.1⟩) := by
      ext k; simp
    rw [h2, Fin.card_Iic]
  rw [h1]
  refine Finset.card_le_card_of_injOn (fun y => (M.rp y.1, G.Uid.new ⟨y.1.1, y.2.1.1⟩ y.2.2)) ?_ ?_
  · rintro ⟨r, ν, k⟩ hy
    simp only [Sg, Finset.coe_sigma, Finset.mem_coe, mem_filter, mem_univ, true_and, Set.mem_sigma_iff] at hy
    rw [Finset.mem_coe, mem_dom]
    refine ⟨hy.1, ?_, holds_cnAt ν k⟩
    rw [G.Plan.mem_seenAt_end]
    exact Nat.lt_succ_of_le hy.2
  · rintro ⟨⟨y, p⟩, ν, k⟩ _ ⟨⟨y', p'⟩, ν', k'⟩ _ e
    simp only [Prod.mk.injEq, G.Uid.new.injEq, Sigma.mk.injEq] at e
    obtain ⟨e1, ⟨rfl, e2⟩, rfl⟩ := e
    obtain rfl := role_eq_of_rp e1
    have : ν = ν' := Subtype.ext (eq_of_heq e2)
    subst this
    rfl

theorem holds0 (id : G.Uid (K + K) U0 M.N U1) : Holds (G.hold0 M.np) (G.hold1 M.np) (G.hold0 M.np id) id := Or.inl rfl

theorem holds1 (id : G.Uid (K + K) U0 M.N U1) : Holds (G.hold0 M.np) (G.hold1 M.np) (G.hold1 M.np id) id := Or.inr rfl

theorem length_endIns (b : G.Uid (K + K) U0 M.N U1 → UW ub) : (endIns P n o grp g key b).length ≤ evG n o grp g := by
  rw [← card_dom]
  unfold endIns
  rw [length_filterMap_le]
  set l := (((G.allIds (K + K) U0 M.N U1).filter fun id => id ∈ P.cur n o E).filter fun id =>
    (if grp (G.hold0 M.np id) = g then
      if grp (G.hold1 M.np id) = g then some (Ins.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
      else some (Ins.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
    else if grp (G.hold1 M.np id) = g then some (Ins.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
    else none).isSome) with hl
  have hnd : l.Nodup := ((Finset.nodup_toList _).filter _).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card_of_injOn
    (fun id => (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id, id)) ?_ ?_
  · intro id hid
    rw [Finset.mem_coe, List.mem_toFinset, hl, List.mem_filter, List.mem_filter] at hid
    obtain ⟨⟨-, h1⟩, h2⟩ := hid
    have h3 := (G.Plan.mem_cur.1 (of_decide_eq_true h1)).1
    rw [Finset.mem_coe, mem_dom]
    change grp (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id) = g ∧
      id ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np)
        (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id) id
    by_cases h0 : grp (G.hold0 M.np id) = g
    · rw [if_pos h0]
      exact ⟨h0, h3, holds0 id⟩
    · by_cases h1' : grp (G.hold1 M.np id) = g
      · rw [if_neg h0]
        exact ⟨h1', h3, holds1 id⟩
      · simp [h0, h1'] at h2
  · intro id _ id' _ e
    exact (Prod.ext_iff.1 e).2

theorem length_uwBits' {ub : ℕ} (w : UW ub) : (uwBits w).length ≤ ub := by
  cases w <;> simp [uwBits]

theorem cost_endIns {T Lc : ℕ} (hk : ∀ c, (key c).length ≤ Lc) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    ((endIns P n o grp g key b).map (insCost T ub)).sum ≤ evG n o grp g * (2 * (ub + Lc + 1)) := by
  refine (sum_le_length_mul _ _ (2 * (ub + Lc + 1)) ?_).trans (Nat.mul_le_mul_right _ (length_endIns b))
  intro i hi
  unfold endIns at hi
  obtain ⟨id, -, hid⟩ := List.mem_filterMap.1 hi
  have hb := length_uwBits' (b id)
  have h0 := hk (G.hold0 M.np id, id)
  have h1 := hk (G.hold1 M.np id, id)
  split_ifs at hid <;> simp only [Option.some.injEq] at hid <;> subst hid <;> simp only [insCost] <;> omega

theorem cost_role {cap T Lc X : ℕ} (hP : P.Ok cap) (hk : ∀ c, (key c).length ≤ Lc) (r : M.R)
    (hsl : Fintype.card ((M.kind r.1).SlAt r.2) ≤ X) (hcn : Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) :
    insCost T ub (roleIns P n o key tg r) ≤
      ((1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1 +
        ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)) * (330 * (ub + Lc + 1)) + 400 * X + 1 := by
  unfold roleIns
  simp only [insCost]
  have h1 := putCost_le (ub := ub) (Lc := Lc) ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse) (by
    intro ks hks k hk'
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hks
    rw [List.mem_reverse] at hk'
    obtain ⟨id, -, rfl⟩ := List.mem_map.1 hk'
    exact hk _)
  have h2 := putCost_le (ub := ub) (Lc := Lc) ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) (by
    intro ks hks k hk'
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hks
    obtain ⟨id, -, rfl⟩ := List.mem_map.1 hk'
    exact hk _)
  have h3 : (((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse).map List.length).sum ≤
      Fintype.card ((M.kind r.1).SlAt r.2) * P.num n o r.1 := by
    rw [List.map_map]
    refine (sum_le_length_mul _ _ (P.num n o r.1) fun e _ => ?_).trans (le_of_eq ?_)
    · simp only [Function.comp, List.length_reverse, List.length_map]
      rw [G.Plan.length_ids]
      exact hP.card n o ⟨r.1, e.1⟩
    · rw [Finset.length_toList, Finset.card_univ]
  have h4 : (((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)).map List.length).sum ≤
      ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1) := by
    rw [List.map_map, ← Finset.sum_map_toList]
    refine List.sum_le_sum fun ν _ => ?_
    simp only [Function.comp, List.length_map]
    have h5 : ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩) =
        (List.finRange U1).filter fun k => k.1 < (o ⟨r.1, ν.1⟩).1 + 1 := by
      refine List.filter_congr fun k _ => ?_
      rw [decide_eq_decide, Nat.lt_succ_iff]
      rfl
    rw [h5]
    exact length_filter_lt _ _
  rw [List.length_map, Finset.length_toList, Finset.card_univ] at h1 h2
  set sl := Fintype.card ((M.kind r.1).SlAt r.2)
  set W := 330 * (ub + Lc + 1) with hW
  set t := P.num n o r.1
  set cs := ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)
  have h6 : t * (ub + 1) ≤ t * W := Nat.mul_le_mul_left _ (by omega)
  have h7 := Nat.mul_le_mul_right W h3
  have h8 := Nat.mul_le_mul_right W h4
  have h9 : ((1 + sl) * t + cs) * W = t * W + sl * t * W + cs * W := by ring
  rw [h9]
  omega

theorem cost_roles {cap T Lc X : ℕ} (hP : P.Ok cap) (hk : ∀ c, (key c).length ≤ Lc)
    (hsl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X) (hcn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X)
    (hR : Fintype.card M.R ≤ X) :
    (((roleList grp g M).map (roleIns P n o key tg)).map (insCost T ub)).sum ≤
      (pdG P n o grp g + evG n o grp g) * (330 * (ub + Lc + 1)) + X * (400 * X + 1) := by
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  have hfin : (roleList grp g M).toFinset = univ.filter fun r : M.R => grp (M.rp r) = g := by
    ext r
    simp [mem_roleList]
  rw [List.map_map, ← List.sum_toFinset _ hnd, hfin]
  calc _ ≤ ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g), ((((1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1 +
        ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)) * (330 * (ub + Lc + 1))) + (400 * X + 1)) :=
        Finset.sum_le_sum fun r _ => (cost_role hP hk r (hsl r) (hcn r)).trans (le_of_eq (Nat.add_assoc _ _ _))
    _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        refine Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.add_le_add le_rfl sum_cn_le)) (Nat.mul_le_mul_right _ ?_)
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ]; exact hR)

theorem cost_body {Lc X : ℕ} (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (p : Fin (K + K)) :
    bodyCost ub (bodyOf ρ n key dkey p) ≤ inN n p * (330 * (ub + Lc + 1)) + X * X + 401 * X + 1 := by
  unfold bodyCost bodyOf
  simp only
  have h1 := putCost_le (ub := ub) (Lc := Lc) (List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n p b).1).map
      fun k => key (Fin.castAdd A' p, .init p b k)) (by
    intro ks hks k hk'
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hks
    obtain ⟨id, -, rfl⟩ := List.mem_map.1 hk'
    exact hk _)
  have h2 := putCost_le (ub := ub) (Lc := Lc) (List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n b p).1).map
      fun k => if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)) (by
    intro ks hks k hk'
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hks
    obtain ⟨id, -, rfl⟩ := List.mem_map.1 hk'
    split_ifs
    · exact hd _
    · exact hk _)
  have h3 : ((List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n p b).1).map
      fun k => key (Fin.castAdd A' p, .init p b k)).map List.length).sum ≤ ∑ b, (n p b).1 := by
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [Function.comp, List.length_map]
    exact length_filter_lt _ _
  have h4 : ((List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n b p).1).map
      fun k => if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)).map List.length).sum ≤ ∑ b, (n b p).1 := by
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [Function.comp, List.length_map]
    exact length_filter_lt _ _
  have h5 : flen ((univ : Finset (Option S)).toList.map fun s => (List.ofFn fun b => rowFlag (ρ s p) b).reverse) ≤ X * X := by
    unfold flen
    rw [List.map_map]
    refine (sum_le_length_mul _ _ (K + K) fun s _ => ?_).trans ?_
    · simp
    · rw [Finset.length_toList, Finset.card_univ]
      exact Nat.mul_le_mul hS hA
  rw [List.length_ofFn] at h1 h2 ⊢
  set W := 330 * (ub + Lc + 1) with hW
  have h6 := Nat.mul_le_mul_right W h3
  have h7 := Nat.mul_le_mul_right W h4
  have h8 : inN n p * W = (∑ b, (n p b).1) * W + (∑ b, (n b p).1) * W := by
    unfold inN
    rw [Finset.sum_add_distrib, add_mul]
  rw [h8]
  omega

theorem diag_le (p : Fin (K + K)) : ((List.finRange U0).filter fun k => k.1 < (n p p).1).length ≤ inN n p := by
  refine (length_filter_lt _ _).trans ?_
  unfold inN
  exact (Nat.le_add_right _ _).trans (Finset.single_le_sum (f := fun b => (n p b).1 + (n b p).1) (fun _ _ => Nat.zero_le _)
    (mem_univ p))

theorem cost_base {T Lc X : ℕ} (hx : ∀ κ, (x κ).length ≤ T) (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (p : Fin (K + K)) :
    ((baseIns qn cb q x ρ n key dkey p).map (insCost T ub)).sum ≤
      T + inN n p * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1 ∧
    (baseIns qn cb q x ρ n key dkey p).length ≤ 1 + inN n p := by
  have hb := cost_body (ub := ub) (Lc := Lc) (X := X) (ρ := ρ) (n := n) (key := key) (dkey := dkey) hk hd hS hA p
  have hdg := diag_le (n := n) p
  have h1 : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
      Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))).map (insCost T ub)).sum ≤
      inN n p * (330 * (ub + Lc + 1)) := by
    rw [List.map_map]
    refine (sum_le_length_mul _ _ (330 * (ub + Lc + 1)) fun k _ => ?_).trans (Nat.mul_le_mul_right _ hdg)
    simp only [Function.comp, insCost]
    have a1 := hk (Fin.castAdd A' p, .init p p k)
    have a2 := hd (p, k)
    omega
  have h2 : insCost T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) ≤
      T + (inN n p * (330 * (ub + Lc + 1)) + X * X + 401 * X + 1) := by
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [Fin.addCases_left]
      exact Nat.add_le_add_left (cost_body hk hd hS hA _) T
    · rw [Fin.addCases_right]
      refine Nat.add_le_add ?_ (cost_body hk hd hS hA _)
      rw [List.length_reverse, List.length_map]
      exact hx κ
  unfold baseIns
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.sum_cons]
    have h3 : inN n p * (660 * (ub + Lc + 1)) = inN n p * (330 * (ub + Lc + 1)) + inN n p * (330 * (ub + Lc + 1)) := by ring
    rw [h3]
    omega
  · rw [List.length_cons, List.length_map]
    omega

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (c : β → ℕ) :
    ((l.flatMap f).map c).sum = (l.map fun a => ((f a).map c).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem length_roleList_le : (roleList grp g M).length ≤ Fintype.card M.R := by
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_univ _

/-- **The time of GROUP at the script of a group.** -/
theorem script_time_le {cap T Lc X ιb lh ev pd : ℕ} {bT bub : List Bool} (hT : bval bT = T) (hub : bval bub = ub)
    (hlT : bT.length ≤ Lc) (hlub : bub.length ≤ Lc) (hP : P.Ok cap) (hx : ∀ κ, (x κ).length ≤ T)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc) (hS : Fintype.card (Option S) ≤ X)
    (hA : K + K ≤ X) (hR : Fintype.card M.R ≤ X) (hsl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
    (hcn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hι : (baseList (A' := A') grp g).length ≤ ιb) (hιX : ιb ≤ X)
    (hlh : ∀ p : Fin (K + K), grp (Fin.castAdd A' p) = g → ∑ b, ((n p b).1 + (n b p).1) ≤ lh)
    (hev : evG n o grp g ≤ ev) (hpd : pdG P n o grp g ≤ pd) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) +
        ((script qn cb P q x ρ n o grp g key dkey tg b).map (insCost (bval bT) (bval bub))).sum +
        (script qn cb P q x ρ n o grp g key dkey tg b).length ≤
      2 * (Lc + 1) * (T + ub + 2) + ιb * T + (ev + pd + ιb * lh) * (1000 * (ub + Lc + 1)) + 1000 * X ^ 3 := by
  rw [hT, hub]
  have hX : 1 ≤ X := le_trans Fintype.card_pos hS
  -- base parties
  have c1 : (((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map (insCost T ub)).sum ≤
      ιb * (T + lh * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1) := by
    rw [sum_flatMap_map]
    refine (sum_le_length_mul _ _ (T + lh * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1) fun p hp => ?_).trans
      (Nat.mul_le_mul_right _ hι)
    have h1 := (cost_base (qn := qn) (cb := cb) (q := q) (ρ := ρ) (n := n) (ub := ub) (X := X) hx hk hd hS hA p).1
    have h2 : inN n p ≤ lh := hlh p (mem_baseList.1 hp)
    refine h1.trans ?_
    gcongr
  have l1 : ((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).length ≤ ιb * (1 + lh) := by
    rw [List.length_flatMap]
    refine (sum_le_length_mul _ _ (1 + lh) fun p hp => ?_).trans (Nat.mul_le_mul_right _ hι)
    have h1 := (cost_base (qn := qn) (cb := cb) (q := q) (ρ := ρ) (n := n) (ub := ub) (X := X) (T := T) hx hk hd hS hA p).2
    have h2 : inN n p ≤ lh := hlh p (mem_baseList.1 hp)
    omega
  have c2 := cost_roles (ub := ub) (T := T) (X := X) (o := o) (n := n) (tg := tg) (grp := grp) (g := g) hP hk hsl hcn hR
  have l2 : ((roleList grp g M).map (roleIns P n o key tg)).length ≤ X := by
    rw [List.length_map]
    exact length_roleList_le.trans hR
  have c3 := cost_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (T := T) hk b
  have l3 := length_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (key := key) b
  unfold script
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append, List.length_append, List.length_append]
  generalize (((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map (insCost T ub)).sum = C1 at *
  generalize ((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).length = L1 at *
  generalize (((roleList grp g M).map (roleIns P n o key tg)).map (insCost T ub)).sum = C2 at *
  generalize ((roleList grp g M).map (roleIns P n o key tg)).length = L2 at *
  generalize ((endIns P n o grp g key b).map (insCost T ub)).sum = C3 at *
  generalize (endIns P n o grp g key b).length = L3 at *
  generalize evG n o grp g = e at *
  generalize pdG P n o grp g = p at *
  have h0 : (bT.length + 1) * (T + 1) + (bub.length + 1) * (ub + 1) ≤ 2 * (Lc + 1) * (T + ub + 2) := by
    have a1 : (bT.length + 1) * (T + 1) ≤ (Lc + 1) * (T + ub + 2) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : (bub.length + 1) * (ub + 1) ≤ (Lc + 1) * (T + ub + 2) := Nat.mul_le_mul (by omega) (by omega)
    calc _ ≤ (Lc + 1) * (T + ub + 2) + (Lc + 1) * (T + ub + 2) := Nat.add_le_add a1 a2
      _ = _ := by ring
  set W := ub + Lc + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have b1 : ιb * (T + lh * (660 * W) + X * X + 401 * X + 1) ≤ ιb * T + 660 * (ιb * lh * W) + 403 * X ^ 3 := by
    have a1 : ιb * (X * X + 401 * X + 1) ≤ 403 * X ^ 3 := by
      calc ιb * (X * X + 401 * X + 1) ≤ X * (X * X + 401 * (X * X) + X * X) := by
            refine Nat.mul_le_mul hιX ?_
            have : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
            have : 1 ≤ X * X := Nat.one_le_iff_ne_zero.2 (by positivity)
            omega
        _ = 403 * X ^ 3 := by ring
    calc ιb * (T + lh * (660 * W) + X * X + 401 * X + 1) = ιb * T + 660 * (ιb * lh * W) + ιb * (X * X + 401 * X + 1) := by
          ring
      _ ≤ _ := by omega
  have b2 : ιb * (1 + lh) ≤ X ^ 3 + ιb * lh * W := by
    have a1 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    have a3 : ιb * lh ≤ ιb * lh * W := Nat.le_mul_of_pos_right _ hW1
    calc ιb * (1 + lh) = ιb + ιb * lh := by ring
      _ ≤ _ := by omega
  have b3 : (p + e) * (330 * W) + X * (400 * X + 1) ≤ 330 * (pd * W) + 330 * (ev * W) + 401 * X ^ 3 := by
    have a1 : X * (400 * X + 1) ≤ 401 * X ^ 3 := by
      have : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
      have h2 : X * X ≤ X ^ 3 := by
        calc X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ hX
          _ = X ^ 3 := by ring
      calc X * (400 * X + 1) = 400 * (X * X) + X := by ring
        _ ≤ _ := by omega
    have a3 : p * W ≤ pd * W := Nat.mul_le_mul_right _ hpd
    have a4 : e * W ≤ ev * W := Nat.mul_le_mul_right _ hev
    calc (p + e) * (330 * W) + X * (400 * X + 1) = 330 * (p * W) + 330 * (e * W) + X * (400 * X + 1) := by ring
      _ ≤ _ := by omega
  have b4 : e * (2 * W) ≤ 2 * (ev * W) := by
    have a4 : e * W ≤ ev * W := Nat.mul_le_mul_right _ hev
    calc e * (2 * W) = 2 * (e * W) := by ring
      _ ≤ _ := by omega
  have b5 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have b6 : e ≤ ev * W := hev.trans (Nat.le_mul_of_pos_right _ hW1)
  have hfin : (ev + pd + ιb * lh) * (1000 * W) =
      1000 * (ev * W) + 1000 * (pd * W) + 1000 * (ιb * lh * W) := by ring
  rw [hfin]
  omega

end group

end Nc.Grp

end
namespace Nc.Dl
open NS1 NS1.Tree Finset Nc.G Nc.Cut
section Time

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {c : ℕ}

/-- The time of GROUP. -/
theorem grpTimeOK (cb : Option Γ → Fin c → Bool) (qn : Q → ℕ) : GrpTimeOK (S := S) A cb qn := by
  classical
  intro K A' E U0 U1 cap mm M P hP q x ρ n o grp g key dkey tg bT bub b Lc X ιb lh ev hx hk hd hbT hbub hS hK hR hId hSl hCn hι
    hιX hlh hev
  have e1 : Grp.evG n o grp g = evG (fun _ _ => grp) n o g := by
    unfold Grp.evG evG
    refine Finset.sum_congr ?_ fun p _ => ?_
    · ext p; simp
    · first | rfl | congr 1
  have e2 : Grp.pdG P n o grp g = pdG P (fun _ _ => grp) n o g := by
    unfold Grp.pdG pdG
    refine Finset.sum_congr ?_ fun p _ => rfl
    ext p; simp
  have hbase : (Grp.baseList (A' := A') grp g).length ≤ ιb := by
    refine le_trans (le_of_eq ?_) hι
    unfold Grp.baseList
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    congr 1
    ext p
    simp
  have h := Grp.script_time_le (qn := qn) (cb := cb) (q := q) (x := x) (ρ := ρ) (n := n) (o := o) (grp := grp) (g := g)
    (key := key) (dkey := dkey) (tg := tg) (Lc := Lc) (X := X) (ιb := ιb) (lh := lh) (ev := evG (fun _ _ => grp) n o g)
    (pd := pdG P (fun _ _ => grp) n o g) (bT := bT) (bub := bub) rfl rfl hbT hbub hP hx hk hd hS (by omega) hR
    (fun r => (Fintype.card_subtype_le _).trans (hSl _)) (fun r => (Fintype.card_subtype_le _).trans (hCn _)) hbase hιX hlh
    e1.le e2.le b
  have hX1 : 1 ≤ X := by omega
  have h3 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h4 : (evG (fun _ _ => grp) n o g + pdG P (fun _ _ => grp) n o g + ιb * lh) * (1000 * (Grp.bval bub + Lc + 1)) ≤
      1000 * (ev + ιb * lh) * (Grp.bval bub + Lc + 1) := by
    calc _ ≤ (ev + ιb * lh) * (1000 * (Grp.bval bub + Lc + 1)) := Nat.mul_le_mul_right _ (Nat.add_le_add_right hev _)
      _ = _ := by ring
  have h5 : 1000 * X ^ 3 ≤ X ^ 4 * 1000 * (Lc + 1) := by
    calc 1000 * X ^ 3 ≤ 1000 * X ^ 4 := Nat.mul_le_mul_left _ h3
      _ = X ^ 4 * 1000 * 1 := by ring
      _ ≤ X ^ 4 * 1000 * (Lc + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold grpT
  omega

end Time


end Nc.Dl

open NS1
theorem solution {A : Type} [CommRing A] {θ : List Bool → A} (hθ : Paper.Generates θ) {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ]
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] (mu : Nc.Letter S Unit Γ → Matrix Q Q A) {c : ℕ}
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Nc.G.Law A, L.Ro)) :
    ∃ (GROUP : Fm) (κ : ℕ), Nc.Dl.GroupOK θ mu cb kinds (fun z => (Nc.Grp.qn Q z : ℕ)) GROUP κ ∧
      Nc.Dl.GrpTimeOK (S := S) A cb (fun z => (Nc.Grp.qn Q z : ℕ)) := by
  classical
  obtain ⟨GROUP, κ, hG⟩ := Nc.Grp.exists_group (θ := θ) mu cb kinds (fun z q q' => hθ.2 _) (fun z _ i y h => hθ.2 _)
  refine ⟨GROUP, κ, ?_, Nc.Dl.grpTimeOK cb _⟩
  intro A' K E U0 U1 cap Gr _ _ M P q x ρ n o grp g key dkey tg bT bub b h1 h2 h3 h4 h5 h6
  exact hG P q x ρ n o grp g key dkey tg bT bub b h1 h2 h3 h4 h5 h6


