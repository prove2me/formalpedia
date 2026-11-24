-- Prove2me | solution 1 for ValiantBorder.universalGridProjection
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:08:04.926209+00:00
-- url     : https://prove2.me/submissions/775587ce-e60b-47e0-a83a-1de798ce7cba

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_universalAutomaton
import Definitions.Def_ValiantBorder_gridComplete

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026).
Source: `anthropics/formal-math`, revision
11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/Paper/{Universal,UniversalSteps,CircuitPhi,Circuit}.lean`.
The construction uses the weighted universal automaton, its tape semantics and the grid representation of its run polynomial.
Apache-2.0. -/

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

/-! Source module: Nc.RunWord -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Places of letters in runs and in the code of the inputs
-/

set_option linter.unusedSectionVars false

namespace Nc

section Emit

variable {Γ S J : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

theorem emit_appendR (o o' : List (Letter S J Γ)) (z : Ch S J) : emit (o ++ o') z = emit o z ++ emit o' z := by
  unfold emit
  rw [List.reduceOption_append, proj_append]

@[simp] theorem emit_nil (z : Ch S J) : emit ([] : List (Letter S J Γ)) z = [] := rfl

@[simp] theorem emit_none (z : Ch S J) : emit ([none] : List (Letter S J Γ)) z = [] := rfl

theorem emit_some (z z' : Ch S J) (γ : Γ) :
    emit ([some (z', γ)] : List (Letter S J Γ)) z = if z' = z then [γ] else [] := by
  unfold emit
  rw [List.reduceOption_cons_of_some, List.reduceOption_nil, proj_cons, proj_nil]

theorem emit_length_le (o : List (Letter S J Γ)) (z : Ch S J) : (emit o z).length ≤ o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    rw [← List.singleton_append, emit_appendR, List.length_append, List.length_append]
    have : (emit [a] z).length ≤ 1 := by
      rcases a with _ | ⟨z', γ⟩
      · simp
      · rw [emit_some]
        split_ifs <;> simp
    simpa using Nat.add_le_add this ih

/-- The letter that is emitted at a step sits at the place counted before the step. -/
theorem emit_getElem (o : List (Letter S J Γ)) (z : Ch S J) (τ : ℕ) (γ : Γ) (h : o[τ]? = some (some (z, γ))) :
    (emit o z)[(emit (o.take τ) z).length]? = some γ := by
  have hτ : τ < o.length := (List.getElem?_eq_some_iff.1 h).1
  have ho : o = o.take τ ++ ([some (z, γ)] ++ o.drop (τ + 1)) := by
    conv_lhs => rw [← List.take_append_drop τ o, List.drop_eq_getElem_cons hτ]
    rw [(List.getElem?_eq_some_iff.1 h).2]
    rfl
  conv_lhs => rw [ho]
  rw [emit_appendR, emit_appendR, emit_some, if_pos rfl, List.take_append_of_le_length (by simp; omega),
    List.take_take, min_self, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

/-- Every letter of a channel is emitted at some step. -/
theorem exists_emit (o : List (Letter S J Γ)) (z : Ch S J) (p : ℕ) (hp : p < (emit o z).length) :
    ∃ τ γ, τ < o.length ∧ o[τ]? = some (some (z, γ)) ∧ (emit (o.take τ) z).length = p := by
  induction o using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton o a ih =>
    by_cases h : p < (emit o z).length
    · obtain ⟨τ, γ, h1, h2, h3⟩ := ih h
      refine ⟨τ, γ, by simp; omega, ?_, ?_⟩
      · rw [List.getElem?_append_left h1, h2]
      · rw [List.take_append_of_le_length h1.le, h3]
    · rw [emit_appendR, List.length_append] at hp
      rcases a with _ | ⟨z', γ⟩
      · simp at hp
        omega
      · rw [emit_some] at hp
        split_ifs at hp with hz
        · subst hz
          refine ⟨o.length, γ, by simp, by simp, ?_⟩
          rw [List.take_append_of_le_length le_rfl, List.take_length]
          simp at hp
          omega
        · simp at hp
          omega

end Emit

section Code

variable {Γ : Type*}

/-- The words one after the other, each followed by a separator. -/
def wordOf (v : List (List Γ)) : List (Option Γ) := v.flatMap fun l => l.map some ++ [none]

theorem wordOf_cons (l : List Γ) (v : List (List Γ)) : wordOf (l :: v) = l.map some ++ none :: wordOf v := by
  simp [wordOf]

theorem wordOf_append (v v' : List (List Γ)) : wordOf (v ++ v') = wordOf v ++ wordOf v' := by
  simp [wordOf]

theorem length_wordOf (v : List (List Γ)) : (wordOf v).length = (v.map List.length).sum + v.length := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [wordOf_cons]
    simp [ih]
    omega

variable {n : ℕ}

/-- The place of the first letter of word `k`. -/
def base (u : Fin n → List Γ) (k : ℕ) : ℕ := (wordOf ((List.ofFn u).take k)).length

@[simp] theorem base_zero (u : Fin n → List Γ) : base u 0 = 0 := by simp [base, wordOf]

theorem base_succ (u : Fin n → List Γ) (k : Fin n) : base u (k + 1) = base u k + (u k).length + 1 := by
  unfold base
  rw [List.take_add_one, wordOf_append, List.length_append]
  simp [wordOf]
  omega

theorem ofFn_split (u : Fin n → List Γ) (k : Fin n) :
    List.ofFn u = (List.ofFn u).take k ++ u k :: (List.ofFn u).drop (k + 1) := by
  have hk : (k : ℕ) < (List.ofFn u).length := by simp
  conv_lhs => rw [← List.take_append_drop k (List.ofFn u), List.drop_eq_getElem_cons hk]
  simp

theorem wordOf_getElem (u : Fin n → List Γ) (k : Fin n) (p : ℕ) :
    (wordOf (List.ofFn u))[base u k + p]? =
      ((u k).map some ++ none :: wordOf ((List.ofFn u).drop (k + 1)))[p]? := by
  conv_lhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.getElem?_append_right (by simp [base])]
  simp [base]

theorem base_add_lt (u : Fin n → List Γ) (k : Fin n) :
    base u k + (u k).length < (wordOf (List.ofFn u)).length := by
  conv_rhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.length_append, List.length_append, List.length_cons, List.length_map]
  unfold base
  omega

theorem eq_of_prefix (l m : List Γ) (r : List (Option Γ))
    (h : ∀ p ≤ m.length, (l.map some ++ none :: r)[p]? = (m.map some ++ [none])[p]?) : l = m := by
  induction m generalizing l with
  | nil =>
    cases l with
    | nil => rfl
    | cons a l =>
      have := h 0 (by simp)
      simp at this
  | cons b m ih =>
    have h0 := h 0 (by simp)
    cases l with
    | nil => simp at h0
    | cons a l =>
      simp at h0
      subst h0
      rw [ih l fun p hp => ?_]
      have := h (p + 1) (by simpa using hp)
      simpa using this

/-- A code that is read at all places of `v` is the code of `v`. -/
theorem eq_of_read (u v : Fin n → List Γ)
    (h : ∀ k : Fin n, ∀ p ≤ (v k).length,
      (wordOf (List.ofFn u))[base v k + p]? = ((v k).map some ++ [none])[p]?) : u = v := by
  have key : ∀ m : ℕ, ∀ k : Fin n, k.1 = m → u k = v k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rintro k rfl
      have hb : base u k = base v k := by
        unfold base
        congr 2
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_take, List.getElem_ofFn]
          simp only [List.length_take, List.length_ofFn] at h1
          exact ih i (by omega) _ rfl
      refine eq_of_prefix (u k) (v k) (wordOf ((List.ofFn u).drop (k + 1))) fun p hp => ?_
      rw [← wordOf_getElem, hb, h k p hp]
  exact funext fun k => key k k rfl

/-- The one-hot code of the inputs. -/
def code [DecidableEq Γ] (N : ℕ) (u : Fin n → List Γ) (b : Fin N × Option Γ) : Bool :=
  decide ((wordOf (List.ofFn u))[b.1.1]? = some b.2)

end Code

end Nc
end

/-! Source module: Nc.RunGood -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Certificates of matched runs

A run of an automaton on tapes and inputs is certified by the states, the places of the heads and the contents
of the tapes. The certificate of a run is unique, and it exists if and only if the run is matched.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

section Path

variable {F : Type*} [CommRing F] {Q A : Type*} [Fintype Q] [DecidableEq Q]

/-- An entry of a product of matrices is a sum over paths. -/
theorem prod_ofFn_apply (mu : A → Matrix Q Q F) (t : ℕ) (o : Fin t → A) (i e : Q) :
    ((List.ofFn o).map mu).prod i e = ∑ q : Fin (t + 1) → Q,
      if q 0 = i ∧ q (Fin.last t) = e then ∏ τ : Fin t, mu (o τ) (q τ.castSucc) (q τ.succ) else 0 := by
  induction t generalizing i with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) Q).symm.sum_comp]
    simp only [List.ofFn_zero, List.map_nil, List.prod_nil, Matrix.one_apply, Finset.univ_eq_empty,
      Finset.prod_empty, Equiv.funUnique_symm_apply, uniqueElim_const]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  | succ t ih =>
    have hR : (∑ q : Fin (t + 1 + 1) → Q, if q 0 = i ∧ q (Fin.last (t + 1)) = e then
        ∏ τ : Fin (t + 1), mu (o τ) (q τ.castSucc) (q τ.succ) else 0) =
        ∑ q : Fin (t + 1) → Q, if q (Fin.last t) = e then
          mu (o 0) i (q 0) * ∏ τ : Fin t, mu (o τ.succ) (q τ.castSucc) (q τ.succ) else 0 := by
      rw [← (Fin.consEquiv (fun _ => Q)).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun q _ => ?_
        simp only [Fin.consEquiv_apply, Fin.cons_zero, true_and, Fin.prod_univ_succ, Fin.castSucc_zero,
          Fin.cons_succ, ← Fin.succ_last, ← Fin.succ_castSucc]
      · intro b _ hb
        refine Finset.sum_eq_zero fun q _ => if_neg ?_
        rintro ⟨h, -⟩
        exact hb (by simpa using h)
      · intro h
        exact absurd (mem_univ _) h
    rw [List.ofFn_succ, List.map_cons, List.prod_cons, Matrix.mul_apply, hR]
    simp only [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q 0)]
    · simp only [true_and, mul_ite, mul_zero]
    · intro b _ hb
      rw [if_neg (fun h => hb h.1.symm), mul_zero]
    · intro h
      exact absurd (mem_univ _) h

end Path

variable {Γ S Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- The channels whose places start at 0. -/
def Ch.start : Ch S (Fin n) → Bool
  | .tp _ _ => true
  | .inp j => j.1 = 0

/-- The conditions on a certificate: `o` letters, `q` states, `P` places, `c` contents; `x` is the code. -/
structure Good (i e : Q) (x : Fin N × Option Γ → Bool) (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q)
    (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ) : Prop where
  first : q 0 = i
  last : q (Fin.last t) = e
  zero : ∀ z, z.start = true → (P z 0).1 = 0
  step : ∀ z τ, (P z (Fin.succ τ)).1 = (P z (Fin.castSucc τ)).1 + (emit [o τ] z).length
  link : ∀ j j' : Fin n, j'.1 = j.1 + 1 → (P (.inp j') 0).1 = (P (.inp j) (Fin.last t)).1 + 1
  write : ∀ s b τ γ, o τ = some (.tp s b, γ) → c s (P (.tp s b) (Fin.castSucc τ)) = some γ
  blank : ∀ s b p, P (.tp s b) (Fin.last t) ≤ p → c s p = none
  read : ∀ j τ γ, o τ = some (.inp j, γ) → ∃ h : (P (.inp j) (Fin.castSucc τ)).1 < N, x (⟨_, h⟩, some γ) = true
  sep : ∀ j, ∃ h : (P (.inp j) (Fin.last t)).1 < N, x (⟨_, h⟩, none) = true

section Forward

variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}
  {P : Ch S (Fin n) → Fin (t + 1) → Fin M} {c : S → Fin M → Option Γ}

theorem emit_take_succ (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : Fin t) :
    (emit ((List.ofFn o).take (τ + 1)) z).length =
      (emit ((List.ofFn o).take τ) z).length + (emit [o τ] z).length := by
  rw [List.take_add_one, emit_appendR, List.length_append]
  simp

/-- The first place of a channel in a run. -/
def place0 (o : Fin t → Letter S (Fin n) Γ) : Ch S (Fin n) → ℕ
  | .tp _ _ => 0
  | .inp j => base (fun j => emit (List.ofFn o) (.inp j)) j

theorem Good.place {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) (τ : Fin (t + 1)) :
    (P z τ).1 = (P z 0).1 + (emit ((List.ofFn o).take τ) z).length := by
  induction τ using Fin.induction with
  | zero => simp
  | succ τ ih =>
    rw [h.step, ih, Fin.val_succ, emit_take_succ, Fin.val_castSucc]
    omega

theorem Good.place_last {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) :
    (P z (Fin.last t)).1 = (P z 0).1 + (emit (List.ofFn o) z).length := by
  rw [h.place, Fin.val_last, List.take_of_length_le (by simp)]

theorem Good.place_zero {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) :
    (P z 0).1 = place0 o z := by
  rcases z with ⟨s, b⟩ | j
  · exact h.zero _ rfl
  · have key : ∀ m : ℕ, ∀ j : Fin n, j.1 = m → (P (.inp j) 0).1 = place0 o (.inp j) := by
      intro m
      induction m with
      | zero =>
        intro j hj
        rw [h.zero _ (by simp [Ch.start, hj]), place0, hj, base_zero]
      | succ m ih =>
        intro j hj
        have hm : m < n := by have := j.2; omega
        have hb := base_succ (fun j => emit (List.ofFn o) (.inp j)) ⟨m, hm⟩
        rw [h.link ⟨m, hm⟩ j hj, h.place_last, ih ⟨m, hm⟩ rfl, place0, place0, hj, hb]
    exact key j j rfl

theorem Good.contents {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (s : S) (b : Bool) (p : Fin M) :
    c s p = (emit (List.ofFn o) (.tp s b))[p.1]? := by
  by_cases hp : p.1 < (emit (List.ofFn o) (.tp s b)).length
  · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
    rw [List.length_ofFn] at h1
    have ho : o ⟨τ, h1⟩ = some (.tp s b, γ) := by
      simpa [List.getElem?_ofFn, h1] using h2
    have hw := h.write s b ⟨τ, h1⟩ γ ho
    have hP : P (.tp s b) (Fin.castSucc ⟨τ, h1⟩) = p := by
      apply Fin.ext
      rw [h.place, h.zero _ rfl, Fin.val_castSucc, zero_add, h3]
    rw [hP] at hw
    have := emit_getElem _ _ _ _ h2
    rw [h3] at this
    rw [hw, this]
  · rw [List.getElem?_eq_none (by omega), h.blank s b p]
    rw [Fin.le_def, h.place_last, h.zero _ rfl]
    omega

theorem Good.matched (hM : t < M) (h : Good i e (code N u) o q P c) : Matched (List.ofFn o) u := by
  constructor
  · intro s
    apply List.ext_getElem?
    intro p
    by_cases hp : p < M
    · rw [← h.contents s false ⟨p, hp⟩, ← h.contents s true ⟨p, hp⟩]
    · have h1 := emit_length_le (List.ofFn o) (.tp s false)
      have h2 := emit_length_le (List.ofFn o) (.tp s true)
      rw [List.length_ofFn] at h1 h2
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · have : u = fun j => emit (List.ofFn o) (.inp j) := by
      refine eq_of_read u _ fun k p hp => ?_
      rcases hp.lt_or_eq with hp | hp
      · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
        rw [List.length_ofFn] at h1
        have ho : o ⟨τ, h1⟩ = some (.inp k, γ) := by
          simpa [List.getElem?_ofFn, h1] using h2
        obtain ⟨hN, hx⟩ := h.read k ⟨τ, h1⟩ γ ho
        have hP : (P (.inp k) (Fin.castSucc ⟨τ, h1⟩)).1 = base (fun j => emit (List.ofFn o) (.inp j)) k + p := by
          rw [h.place, h.place_zero, Fin.val_castSucc, h3]
          rfl
        have hx' := of_decide_eq_true hx
        simp only [hP] at hx'
        have hg := emit_getElem _ _ _ _ h2
        rw [h3] at hg
        rw [hx', List.getElem?_append_left (by simpa using hp), List.getElem?_map, hg]
        rfl
      · obtain ⟨hN, hx⟩ := h.sep k
        have hP : (P (.inp k) (Fin.last t)).1 = base (fun j => emit (List.ofFn o) (.inp j)) k + p := by
          rw [h.place_last, h.place_zero, hp]
          rfl
        have hx' := of_decide_eq_true hx
        simp only [hP] at hx'
        rw [hx', hp, List.getElem?_append_right (by simp)]
        simp
    intro j
    rw [this]

end Forward

section Backward

variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}

theorem emit_take_le (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : ℕ) :
    (emit ((List.ofFn o).take τ) z).length ≤ (emit (List.ofFn o) z).length := by
  conv_rhs => rw [← List.take_append_drop τ (List.ofFn o), emit_appendR, List.length_append]
  omega

theorem place_lt (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N)
    (hu : ∀ j, emit (List.ofFn o) (.inp j) = u j) (z : Ch S (Fin n)) (τ : ℕ) :
    place0 o z + (emit ((List.ofFn o).take τ) z).length < M := by
  have h1 := emit_take_le o z τ
  rcases z with ⟨s, b⟩ | j
  · have h2 := emit_length_le (List.ofFn o) (.tp s b)
    rw [List.length_ofFn] at h2
    simp only [place0]
    omega
  · have h2 := base_add_lt u j
    have h3 : (fun j => emit (List.ofFn o) (.inp j)) = u := funext hu
    simp only [place0, h3]
    rw [hu] at h1
    omega

theorem exists_good (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N) (h : Matched (List.ofFn o) u)
    (hi : q 0 = i) (he : q (Fin.last t) = e) :
    ∃ (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ), Good i e (code N u) o q P c := by
  have h3 : (fun j => emit (List.ofFn o) (.inp j)) = u := funext h.2
  refine ⟨fun z τ => ⟨_, place_lt hM hN h.2 z τ⟩, fun s p => (emit (List.ofFn o) (.tp s false))[p.1]?,
    hi, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases z with ⟨s, b⟩ | j
    · simp [place0]
    · have : j.1 = 0 := by simpa [Ch.start] using hz
      simp [place0, this]
  · intro z τ
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [emit_take_succ]
    omega
  · intro j j' hj
    simp only [Fin.val_zero, List.take_zero, emit_nil, List.length_nil, add_zero, Fin.val_last, place0, h3]
    rw [List.take_of_length_le (by simp), h.2, hj, base_succ]
  · intro s b τ γ ho
    have hL : (List.ofFn o)[τ.1]? = some (some (.tp s b, γ)) := by simp [ho]
    have := emit_getElem _ _ _ _ hL
    simp only [place0, Fin.val_castSucc, zero_add]
    cases b
    · exact this
    · rw [h.1 s]
      exact this
  · intro s b p hp
    rw [Fin.le_def] at hp
    simp only [place0, Fin.val_last, zero_add] at hp
    rw [List.take_of_length_le (by simp)] at hp
    apply List.getElem?_eq_none
    cases b
    · exact hp
    · rw [h.1 s]
      exact hp
  · intro j τ γ ho
    have hL : (List.ofFn o)[τ.1]? = some (some (.inp j, γ)) := by simp [ho]
    have hg := emit_getElem _ _ _ _ hL
    rw [h.2] at hg
    have hlt := (List.getElem?_eq_some_iff.1 hg).1
    have hb := base_add_lt u j
    simp only [place0, h3, Fin.val_castSucc]
    refine ⟨by omega, ?_⟩
    unfold code
    rw [decide_eq_true_eq, wordOf_getElem, List.getElem?_append_left (by simpa using hlt), List.getElem?_map, hg]
    rfl
  · intro j
    have hb := base_add_lt u j
    have hP : place0 o (.inp j) + (emit ((List.ofFn o).take (Fin.last t).1) (.inp j)).length =
        base u j + (u j).length := by
      simp only [place0, h3, Fin.val_last]
      rw [List.take_of_length_le (by simp), h.2]
    refine ⟨lt_of_eq_of_lt hP (by omega), ?_⟩
    unfold code
    rw [decide_eq_true_eq]
    simp only [hP]
    rw [wordOf_getElem, List.getElem?_append_right (by simp)]
    simp

end Backward

end Nc
end

/-! Source module: Nc.PermCoeff -/
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

/-! Source module: Nc.PermGrid -/
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

/-! Source module: Nc.PermSum -/
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

/-! Source module: Nc.PermPad -/
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

/-! Source module: Nc.LowDegree -/
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

/-! Source module: Nc.PermValiant -/
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

/-! Source module: Ov.Core.Tensor -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Tensors over a finite set of parties

Paper: the subsection "Tensors". A tensor over a set I of parties is an array
with one index for each party. This file defines local maps, restrictions, sums of restrictions,
products, powers, push-forwards (`push`), and spectral points. The field is any field (where more is
needed, it is a hypothesis).
-/

namespace Ov

open Finset

/-- A tensor over the parties I with entries in K: for each party p a finite index set ι p, and an
array. The zero array is allowed. -/
structure Ten (K : Type) (I : Type) where
  ι : I → Type
  [fin : ∀ p, Fintype (ι p)]
  [dec : ∀ p, DecidableEq (ι p)]
  val : (∀ p, ι p) → K

attribute [instance] Ten.fin Ten.dec

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Linear maps on the legs, as matrices: from the legs of t to the legs of s. -/
abbrev Loc (s t : Ten K I) : Type := ∀ p, s.ι p → t.ι p → K

/-- The array obtained from t by the local maps L. -/
def app {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : K :=
  ∑ y : ∀ p, t.ι p, (∏ p, L p (x p) (y p)) * t.val y

/-- s is a restriction of t: s arises from t by local maps. -/
def Restr (s t : Ten K I) : Prop := ∃ L : Loc s t, ∀ x, s.val x = app L x

/-- s is covered by the tensors b k: it is a sum of restrictions of them. There is one
restriction of each b k; it may be 0. -/
def SumRestr {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I) : Prop :=
  ∃ L : ∀ k, Loc s (b k), ∀ x, s.val x = ∑ k, app (L k) x

/-- s and t are restrictions of one another. (The paper identifies such tensors.) -/
def Equi (s t : Ten K I) : Prop := Restr s t ∧ Restr t s

/-- The tensor 1: all legs one-dimensional, the entry 1. -/
def one : Ten K I where
  ι := fun _ => Unit
  val := fun _ => 1

instance : One (Ten K I) := ⟨one⟩

/-- The product (Kronecker product, party by party). -/
def mul (s t : Ten K I) : Ten K I where
  ι := fun p => s.ι p × t.ι p
  val := fun x => s.val (fun p => (x p).1) * t.val (fun p => (x p).2)

instance : Mul (Ten K I) := ⟨mul⟩

/-- The k-th power: indices are k-tuples. -/
def kpow (t : Ten K I) (k : ℕ) : Ten K I where
  ι := fun p => Fin k → t.ι p
  val := fun x => ∏ i, t.val (fun p => x p i)

/-- The product of a finite family. -/
def prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) : Ten K I where
  ι := fun p => ∀ k, (b k).ι p
  val := fun x => ∏ k, (b k).val (fun p => x p k)

/-- The push-forward πt: the index j of a tensor on J is given to the party π j. A party may get several
indices, or none (then its index set has one element). -/
def push (π : J → I) (t : Ten K J) : Ten K I where
  ι := fun q => ∀ j : {j : J // π j = q}, t.ι j.1
  val := fun x => t.val (fun j => x (π j) ⟨j, rfl⟩)

/-- The unit tensor ⟨r⟩_J of size r on J. -/
def unit (K : Type) [Field K] (J : Type) [Fintype J] [DecidableEq J] (r : ℕ) : Ten K J where
  ι := fun _ => Fin r
  val := fun x => if ∀ i j, x i = x j then 1 else 0

/-- The wire ⟨n⟩_pq of dimension n between p and q. If p = q and n > 0 it is equivalent to 1. -/
def wire (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I) : Ten K I :=
  push ![p, q] (unit K (Fin 2) n)

/-- A tensor has rank at most r if it is a restriction of the unit tensor of size r. (If there is a
party, this is the same as being a sum of r products of vectors: `rankLE_iff`.) -/
def RankLE (t : Ten K I) (r : ℕ) : Prop := Restr t (unit K I r)

end Ten

/-- A spectral point over the parties I: a real function F ≥ 0 on the tensors over I that is
multiplicative, with F(1) = 1 and F(s) ≤ ∑ F(b k) whenever s is a sum of restrictions of the b k. This
is the paper's definition, a multiplicative gauge; with the empty family it gives F(0) = 0. -/
structure Spec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  F : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ F t
  one : F 1 = 1
  mul : ∀ s t, F (s * t) = F s * F t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b → F s ≤ ∑ k, F (b k)

namespace Spec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- The paper's d_φ(p,q), the exponent of a wire: log₂ of the value at the wire of dimension 2 between p and q. -/
noncomputable def e (F : Spec K I) (p q : I) : ℝ := Real.logb 2 (F.F (Ten.wire K 2 p q))

end Spec

end Ov
end

/-! Source module: Nc.Rate.Defs -/
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

/-! Source module: Nc.WidePerm -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Grid sums and sums of products of wide clauses as projections

A wide clause is a weight that applies when all literals of a list hold. A sum over bits of a product of wide
clauses is a grid sum, so it is a projection of every family that is complete for grid sums. Grid sums are
permanents if 2 ≠ 0.
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Wide

variable {α θ : Type*} [Fintype α] [DecidableEq α] [Fintype θ] [DecidableEq θ]

/-- The sum over the hidden bits `a` of the product over the clauses: a clause contributes its weight when all
its literals hold, and 1 otherwise. -/
def wideSum (lits : θ → List ((ι ⊕ α) × Bool)) (w : θ → F) (x : ι → Bool) : F :=
  ∑ a : α → Bool, ∏ i, if ∀ l ∈ lits i, Sum.elim x a l.1 = l.2 then w i else 1

/-- The extension with weights `X i` (bit 1) and `1 - c * X i` (bit 0). -/
noncomputable def mlExtC (c : F) (f : (ι → Bool) → F) : MvPolynomial ι F :=
  ∑ u : ι → Bool, C (f u) * ∏ i, if u i then X i else 1 - C c * X i

end Wide

section Proj

variable {F ι α θ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype θ]
  [DecidableEq θ] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {κ : ℕ}

end Proj

end Nc
end

/-! Source module: Nc.FinDom -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over functions on finite domains
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : Type*} [Fintype D] [DecidableEq D] {E : D → Type*} [∀ d, Fintype (E d)] [∀ d, DecidableEq (E d)]
variable {θ : Type*} [Fintype θ] [DecidableEq θ]

/-- The bits of a function: one for every point and value. -/
def hot (g : ∀ d, E d) (p : Σ d, E d) : Bool := decide (g p.1 = p.2)

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (E d)] in
theorem hot_injective : Function.Injective (hot (E := E)) := by
  intro g g' e
  funext d
  have := congrFun e ⟨d, g d⟩
  simp only [hot, decide_true] at this
  exact (of_decide_eq_true this.symm).symm

/-- The sum over all functions of the product over the clauses; a literal about a function is `g d = e` or its
negation. -/
def fdSum (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F) (x : ι → Bool) : F :=
  ∑ g : ∀ d, E d, ∏ i, if ∀ l ∈ lits i, Sum.elim x (hot g) l.1 = l.2 then w i else 1

/-- The clauses that make bits the bits of a function. -/
noncomputable def fdLits (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) :
    θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → List ((ι ⊕ Σ d, E d) × Bool)
  | Sum.inl i => lits i
  | Sum.inr (Sum.inl d) => (univ : Finset (E d)).toList.map fun e => (Sum.inr ⟨d, e⟩, false)
  | Sum.inr (Sum.inr (p, q)) => [(Sum.inr p, true), (Sum.inr q, true)]

/-- Their weights. -/
def fdWt (w : θ → F) : θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → F
  | Sum.inl i => w i
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (p, q)) => if p.1 = q.1 ∧ p ≠ q then 0 else 1

omit [Fintype ι] [DecidableEq ι] [DecidableEq θ] in
theorem fdSum_eq (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F) (x : ι → Bool) :
    fdSum lits w x = wideSum (fdLits lits) (fdWt w) x := by
  unfold fdSum wideSum
  refine Finset.sum_of_injOn hot hot_injective.injOn (fun _ _ => mem_univ _) ?_ ?_
  · intro a _ ha
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    by_cases hex : ∀ d, ∃ e, a ⟨d, e⟩ = true
    · choose g hg using hex
      have hne : a ≠ hot g := fun h => ha ⟨g, mem_univ _, h.symm⟩
      obtain ⟨⟨d, e⟩, he⟩ := Function.ne_iff.1 hne
      have hde : g d ≠ e := by
        rintro rfl
        exact he (by simp [hot, hg])
      have hat : a ⟨d, e⟩ = true := by
        simpa [hot, hde] using he
      have : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ fdLits lits (Sum.inr (Sum.inr q)), Sum.elim x a l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inr q)) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ (⟨d, e⟩, ⟨d, g d⟩)) ?_
        have hpq : (⟨d, e⟩ : Σ d, E d) ≠ ⟨d, g d⟩ := by
          intro h
          exact hde (eq_of_heq (Sigma.mk.inj h).2).symm
        simp [fdLits, fdWt, hat, hg, hpq]
      rw [this, mul_zero, mul_zero]
    · push Not at hex
      obtain ⟨d, hd⟩ := hex
      have : (∏ d : D, if ∀ l ∈ fdLits lits (Sum.inr (Sum.inl d)), Sum.elim x a l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inl d)) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ d) ?_
        rw [if_pos]
        · rfl
        · intro l hl
          simp only [fdLits, List.mem_map, Finset.mem_toList, mem_univ, true_and] at hl
          obtain ⟨e, rfl⟩ := hl
          simpa using hd e
      rw [this, zero_mul, mul_zero]
  · intro g _
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    have h1 : (∏ d : D, if ∀ l ∈ fdLits lits (Sum.inr (Sum.inl d)), Sum.elim x (hot g) l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inl d)) else 1) = 1 := by
      refine Finset.prod_eq_one fun d _ => if_neg fun h => ?_
      have := h (Sum.inr ⟨d, g d⟩, false) (by simp [fdLits])
      simp [hot] at this
    have h2 : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ fdLits lits (Sum.inr (Sum.inr q)), Sum.elim x (hot g) l.1 = l.2 then
            fdWt (E := E) w (Sum.inr (Sum.inr q)) else 1) = 1 := by
      refine Finset.prod_eq_one ?_
      rintro ⟨⟨d, e⟩, ⟨d', e'⟩⟩ _
      split_ifs with h
      · simp only [fdLits, List.forall_mem_cons, Sum.elim_inr, hot, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        simp only [fdWt]
        refine if_neg ?_
        rintro ⟨hd, hne⟩
        subst hd
        exact hne rfl
      · rfl
    rw [h1, h2, mul_one, mul_one]
    rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq θ] in
/-- Clauses whose product does not depend on the function. -/
theorem fdSum_elim {θ' : Type*} [Fintype θ'] (lits : θ → List ((ι ⊕ Σ d, E d) × Bool)) (w : θ → F)
    (lits' : θ' → List ((ι ⊕ Σ d, E d) × Bool)) (w' : θ' → F) (x : ι → Bool) (c : F)
    (h : ∀ g : ∀ d, E d, (∏ i, if ∀ l ∈ lits' i, Sum.elim x (hot g) l.1 = l.2 then w' i else 1) = c) :
    fdSum (Sum.elim lits lits') (Sum.elim w w') x = fdSum lits w x * c := by
  unfold fdSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.prod_sum_type, ← h g]
  rfl

section Proj

variable {F ι D θ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] {E : D → Type}
  [∀ d, Fintype (E d)] [∀ d, DecidableEq (E d)] [Fintype θ] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {κ : ℕ}

end Proj

end Nc
end

/-! Source module: Nc.RunSum -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The value of an automaton is a sum over finite domains
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- The hidden variables: letters, states, places, contents. -/
abbrev RD (S : Type) (n t M : ℕ) : Type := Fin t ⊕ Fin (t + 1) ⊕ (Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)

instance : DecidableEq (RD S n t M) :=
  haveI : DecidableEq ((Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)) := inferInstance
  haveI : DecidableEq (Fin (t + 1) ⊕ (Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)) := instDecidableEqSum
  instDecidableEqSum

/-- Their domains. -/
@[reducible] def RE (Γ S Q : Type) (n t M : ℕ) : RD S n t M → Type
  | .inl _ => Letter S (Fin n) Γ
  | .inr (.inl _) => Q
  | .inr (.inr (.inl _)) => Fin M
  | .inr (.inr (.inr _)) => Option Γ

instance : ∀ d : RD S n t M, Fintype (RE Γ S Q n t M d)
  | .inl _ => inferInstanceAs (Fintype (Letter S (Fin n) Γ))
  | .inr (.inl _) => inferInstanceAs (Fintype Q)
  | .inr (.inr (.inl _)) => inferInstanceAs (Fintype (Fin M))
  | .inr (.inr (.inr _)) => inferInstanceAs (Fintype (Option Γ))

instance : ∀ d : RD S n t M, DecidableEq (RE Γ S Q n t M d)
  | .inl _ => inferInstanceAs (DecidableEq (Letter S (Fin n) Γ))
  | .inr (.inl _) => inferInstanceAs (DecidableEq Q)
  | .inr (.inr (.inl _)) => inferInstanceAs (DecidableEq (Fin M))
  | .inr (.inr (.inr _)) => inferInstanceAs (DecidableEq (Option Γ))

/-- The bits: the code and the hidden bits. -/
abbrev RV (Γ S Q : Type) (n t M N : ℕ) : Type := (Fin N × Option Γ) ⊕ Σ d, RE Γ S Q n t M d

/-- The bit "the letter at step `τ` is `a`". -/
def vEm (τ : Fin t) (a : Letter S (Fin n) Γ) : RV Γ S Q n t M N := .inr ⟨.inl τ, a⟩
/-- The bit "the state before step `τ` is `q`". -/
def vSt (τ : Fin (t + 1)) (q : Q) : RV Γ S Q n t M N := .inr ⟨.inr (.inl τ), q⟩
/-- The bit "the place of `z` before step `τ` is `m`". -/
def vPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) : RV Γ S Q n t M N := .inr ⟨.inr (.inr (.inl (z, τ))), m⟩
/-- The bit "tape `s` holds `x` at place `p`". -/
def vCt (s : S) (p : Fin M) (x : Option Γ) : RV Γ S Q n t M N := .inr ⟨.inr (.inr (.inr (s, p))), x⟩

/-- The rules that carry weights. -/
abbrev RS (Γ S Q : Type) (n t : ℕ) : Type := Fin t × Letter S (Fin n) Γ × Q × Q

/-- The rules that forbid. -/
abbrev RH (Γ S : Type) (n t M : ℕ) : Type :=
  Bool ⊕ Ch S (Fin n) ⊕ (Ch S (Fin n) × Fin t × Fin M × Letter S (Fin n) Γ) ⊕ (Fin n × Fin n × Fin M) ⊕
    (S × Bool × Fin t × Γ × Fin M) ⊕ (S × Bool × Fin M × Fin M) ⊕ (Fin n × Fin t × Γ × Fin M) ⊕ (Fin n × Fin M)

/-- The literals of a rule with a weight. -/
def sLits : RS Γ S Q n t → List (RV Γ S Q n t M N × Bool)
  | (τ, a, q, q') => [(vEm τ a, true), (vSt τ.castSucc q, true), (vSt τ.succ q', true)]

/-- The literals of a rule that forbids. -/
def hLits (i e : Q) : RH Γ S n t M → List (RV Γ S Q n t M N × Bool)
  | .inl false => [(vSt 0 i, false)]
  | .inl true => [(vSt (Fin.last t) e, false)]
  | .inr (.inl z) => if h : 0 < M then [(vPl z 0 ⟨0, h⟩, false)] else []
  | .inr (.inr (.inl (z, τ, m, a))) => (vPl z τ.castSucc m, true) :: (vEm τ a, true) ::
      if h : m.1 + (emit [a] z).length < M then [(vPl z τ.succ ⟨_, h⟩, false)] else []
  | .inr (.inr (.inr (.inl (j, j', m)))) => (vPl (.inp j) (Fin.last t) m, true) ::
      if h : m.1 + 1 < M then [(vPl (.inp j') 0 ⟨_, h⟩, false)] else []
  | .inr (.inr (.inr (.inr (.inl (s, b, τ, γ, m))))) =>
      [(vEm τ (some (.tp s b, γ)), true), (vPl (.tp s b) τ.castSucc m, true), (vCt s m (some γ), false)]
  | .inr (.inr (.inr (.inr (.inr (.inl (s, b, m, p)))))) =>
      [(vPl (.tp s b) (Fin.last t) m, true), (vCt s p none, false)]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, m))))))) =>
      (vEm τ (some (.inp j, γ)), true) :: (vPl (.inp j) τ.castSucc m, true) ::
        if h : m.1 < N then [(.inl (⟨_, h⟩, some γ), false)] else []
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (j, m))))))) => (vPl (.inp j) (Fin.last t) m, true) ::
      if h : m.1 < N then [(.inl (⟨_, h⟩, none), false)] else []

/-- The rules that are in force. -/
def active : RH Γ S n t M → Bool
  | .inr (.inl z) => z.start
  | .inr (.inr (.inr (.inl (j, j', _)))) => j'.1 = j.1 + 1
  | .inr (.inr (.inr (.inr (.inr (.inl (_, _, m, p)))))) => m ≤ p
  | _ => true

section Hard

variable (i e : Q) (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d)

/-- The letters. -/
def gEm (τ : Fin t) : Letter S (Fin n) Γ := g (.inl τ)
/-- The states. -/
def gSt (τ : Fin (t + 1)) : Q := g (.inr (.inl τ))
/-- The places. -/
def gPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) : Fin M := g (.inr (.inr (.inl (z, τ))))
/-- The contents. -/
def gCt (s : S) (p : Fin M) : Option Γ := g (.inr (.inr (.inr (s, p))))

@[simp] theorem elim_vEm (τ : Fin t) (a : Letter S (Fin n) Γ) :
    Sum.elim x (hot g) (vEm τ a) = decide (gEm g τ = a) := rfl
@[simp] theorem elim_vSt (τ : Fin (t + 1)) (q : Q) :
    Sum.elim x (hot g) (vSt τ q) = decide (gSt g τ = q) := rfl
@[simp] theorem elim_vPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) :
    Sum.elim x (hot g) (vPl z τ m) = decide (gPl g z τ = m) := rfl
@[simp] theorem elim_vCt (s : S) (p : Fin M) (y : Option Γ) :
    Sum.elim x (hot g) (vCt s p y) = decide (gCt g s p = y) := rfl

/-- No rule in force is violated. -/
def Hard : Prop := ∀ r : RH Γ S n t M, active r = true → ¬ ∀ l ∈ hLits i e r, Sum.elim x (hot g) l.1 = l.2

theorem good_of_hard (h : Hard i e x g) : Good i e x (gEm g) (gSt g) (gPl g) (gCt g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hLits, active] using h (.inl false)
  · simpa [hLits, active] using h (.inl true)
  · intro z hz
    have hM : 0 < M := (Nat.zero_le _).trans_lt (gPl g z 0).2
    have := h (.inr (.inl z)) hz
    simp [hLits, hM] at this
    rw [this]
  · intro z τ
    have := h (.inr (.inr (.inl (z, τ, gPl g z τ.castSucc, gEm g τ)))) rfl
    by_cases hM : (gPl g z τ.castSucc).1 + (emit [gEm g τ] z).length < M
    · simp [hLits, hM] at this
      rw [this]
    · simp [hLits, hM] at this
  · intro j j' hj
    have := h (.inr (.inr (.inr (.inl (j, j', gPl g (.inp j) (Fin.last t)))))) (by simp [active, hj])
    by_cases hM : (gPl g (.inp j) (Fin.last t)).1 + 1 < M
    · simp [hLits, hM] at this
      rw [this]
    · simp [hLits, hM] at this
  · intro s b τ γ ho
    have := h (.inr (.inr (.inr (.inr (.inl (s, b, τ, γ, gPl g (.tp s b) τ.castSucc)))))) rfl
    simpa [hLits, ho] using this
  · intro s b p hp
    have := h (.inr (.inr (.inr (.inr (.inr (.inl (s, b, gPl g (.tp s b) (Fin.last t), p)))))))
      (by simpa [active] using hp)
    simpa [hLits] using this
  · intro j τ γ ho
    have := h (.inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, gPl g (.inp j) τ.castSucc)))))))) rfl
    by_cases hN : (gPl g (.inp j) τ.castSucc).1 < N
    · refine ⟨hN, ?_⟩
      simpa [hLits, ho, hN] using this
    · simp [hLits, ho, hN] at this
  · intro j
    have := h (.inr (.inr (.inr (.inr (.inr (.inr (.inr (j, gPl g (.inp j) (Fin.last t))))))))) rfl
    by_cases hN : (gPl g (.inp j) (Fin.last t)).1 < N
    · refine ⟨hN, ?_⟩
      simpa [hLits, hN] using this
    · simp [hLits, hN] at this

theorem hard_of_good (h : Good i e x (gEm g) (gSt g) (gPl g) (gCt g)) : Hard i e x g := by
  rintro ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) hr hl
  · simp [hLits, h.first] at hl
  · simp [hLits, h.last] at hl
  · have hM : 0 < M := (Nat.zero_le _).trans_lt (gPl g z 0).2
    simp [hLits, hM] at hl
    exact hl (Fin.ext (h.zero z hr))
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, decide_eq_true_eq] at hl
    obtain ⟨rfl, rfl, hl⟩ := hl
    have hs := h.step z τ
    have hM := (gPl g z τ.succ).2
    rw [hs] at hM
    rw [dif_pos hM] at hl
    simp at hl
    exact hl (Fin.ext hs)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    have hs := h.link j j' (by simpa [active] using hr)
    have hM := (gPl g (.inp j') 0).2
    rw [hs] at hM
    rw [dif_pos hM] at hl
    simp at hl
    exact hl (Fin.ext hs)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, elim_vCt, decide_eq_true_eq,
      decide_eq_false_iff_not] at hl
    obtain ⟨ho, rfl, hl, -⟩ := hl
    exact hl (h.write s b τ γ ho)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vCt, decide_eq_true_eq,
      decide_eq_false_iff_not] at hl
    obtain ⟨rfl, hl, -⟩ := hl
    exact hl (h.blank s b p (by simpa [active] using hr))
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, decide_eq_true_eq] at hl
    obtain ⟨ho, rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.read j τ γ ho
    rw [dif_pos hN] at hl
    simp [hx] at hl
  · simp only [hLits, List.forall_mem_cons, elim_vPl, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.sep j
    rw [dif_pos hN] at hl
    simp [hx] at hl

end Hard

/-- The literals of all rules. -/
def rLits (i e : Q) : RS Γ S Q n t ⊕ RH Γ S n t M → List (RV Γ S Q n t M N × Bool) := Sum.elim sLits (hLits i e)

/-- The weights of all rules. -/
def rWt (mu : Letter S (Fin n) Γ → Matrix Q Q F) : RS Γ S Q n t ⊕ RH Γ S n t M → F :=
  Sum.elim (fun r => mu r.2.1 r.2.2.1 r.2.2.2) fun r => if active r then 0 else 1

theorem prod_soft (mu : Letter S (Fin n) Γ → Matrix Q Q F) (x : Fin N × Option Γ → Bool)
    (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RS Γ S Q n t, if ∀ l ∈ sLits (M := M) (N := N) r, Sum.elim x (hot g) l.1 = l.2 then
      mu r.2.1 r.2.2.1 r.2.2.2 else 1) = ∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ)) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_eq_single (gEm g τ, gSt g (Fin.castSucc τ), gSt g (Fin.succ τ))]
  · rw [if_pos]
    simp [sLits]
  · rintro ⟨a, q, q'⟩ _ hne
    refine if_neg fun h => hne ?_
    simp only [sLits, List.forall_mem_cons, elim_vEm, elim_vSt, decide_eq_true_eq] at h
    rw [h.1, h.2.1, h.2.2.1]
  · intro h
    exact absurd (mem_univ _) h

open scoped Classical in
theorem prod_hard (i e : Q) (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RH Γ S n t M, if ∀ l ∈ hLits i e r, Sum.elim x (hot g) l.1 = l.2 then
      (if active r then (0 : F) else 1) else 1) =
        if Good i e x (gEm g) (gSt g) (gPl g) (gCt g) then 1 else 0 := by
  split_ifs with hg
  · have hh := hard_of_good i e x g hg
    refine Finset.prod_eq_one fun r _ => ?_
    by_cases hr : active r = true
    · rw [if_neg (hh r hr)]
    · simp [hr]
  · have hh : ¬ Hard i e x g := fun h => hg (good_of_hard i e x g h)
    unfold Hard at hh
    push Not at hh
    obtain ⟨r, hr, hl⟩ := hh
    refine Finset.prod_eq_zero (mem_univ r) ?_
    rw [if_pos hl, if_pos hr]

end Nc
end

/-! Source module: Nc.RunPerm -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The sum over runs with finite domains: literals, counts
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset MvPolynomial

section Degree

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Degree

section Count

theorem card_ChN (S : Type) [Fintype S] (n : ℕ) : Fintype.card (Ch S (Fin n)) = 2 * Fintype.card S + n := by
  have e : Ch S (Fin n) ≃ (S × Bool) ⊕ Fin n :=
    { toFun := fun z => match z with
        | .tp s b => .inl (s, b)
        | .inp j => .inr j
      invFun := fun y => match y with
        | .inl (s, b) => .tp s b
        | .inr j => .inp j
      left_inv := fun z => by cases z <;> rfl
      right_inv := fun y => by rcases y with ⟨s, b⟩ | j <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [Fintype Q] {n t M N B : ℕ}

theorem card_letter_le (hΓ : Fintype.card Γ ≤ B) (hS : Fintype.card S ≤ B) (hn : n ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Letter S (Fin n) Γ) ≤ 4 * B ^ 2 := by
  rw [Fintype.card_option, Fintype.card_prod, card_ChN]
  calc (2 * Fintype.card S + n) * Fintype.card Γ + 1 ≤ (2 * B + B) * B + 1 * 1 := by gcongr
    _ ≤ (2 * B + B) * B + B * B := by gcongr
    _ = 4 * B ^ 2 := by ring

theorem card_RD_le (hS : Fintype.card S ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) :
    Fintype.card (RD S n t M) ≤ 6 * B ^ 2 := by
  have ht' : t ≤ B := by omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ChN]
  calc t + (t + 1 + ((2 * Fintype.card S + n) * (t + 1) + Fintype.card S * M))
      ≤ B * 1 + (B * 1 + ((2 * B + B) * B + B * B)) := by
        rw [mul_one]; gcongr
    _ ≤ B * B + (B * B + ((2 * B + B) * B + B * B)) := by gcongr
    _ = 6 * B ^ 2 := by ring

theorem card_RE_le [DecidableEq Γ] [DecidableEq S] [DecidableEq Q] (hΓ : Fintype.card Γ + 1 ≤ B)
    (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Σ d, RE Γ S Q n t M d) ≤ 9 * B ^ 3 := by
  have ht' : t ≤ B := by omega
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  have h : Fintype.card (Σ d, RE Γ S Q n t M d) = t * Fintype.card (Letter S (Fin n) Γ) +
      ((t + 1) * Fintype.card Q + (((2 * Fintype.card S + n) * (t + 1)) * M +
        (Fintype.card S * M) * (Fintype.card Γ + 1))) := by
    rw [Fintype.card_sigma, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have e1 : ∀ τ : Fin t, Fintype.card (RE Γ S Q n t M (.inl τ)) = Fintype.card (Letter S (Fin n) Γ) :=
      fun _ => rfl
    have e2 : ∀ τ : Fin (t + 1), Fintype.card (RE Γ S Q n t M (.inr (.inl τ))) = Fintype.card Q := fun _ => rfl
    have e3 : ∀ z, Fintype.card (RE Γ S Q n t M (.inr (.inr (.inl z)))) = M := fun _ => Fintype.card_fin M
    have e4 : ∀ z, Fintype.card (RE Γ S Q n t M (.inr (.inr (.inr z)))) = Fintype.card Γ + 1 :=
      fun _ => Fintype.card_option
    simp only [e1, e2, e3, e4, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin,
      Fintype.card_prod, card_ChN]
  rw [h]
  calc _ ≤ B * (4 * B ^ 2) + (B * B * 1 + (((2 * B + B) * B) * B + (B * B) * B)) := by
        rw [mul_one]; gcongr
    _ ≤ B * (4 * B ^ 2) + (B * B * B + (((2 * B + B) * B) * B + (B * B) * B)) := by gcongr
    _ = 9 * B ^ 3 := by ring

theorem card_RS_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hB : 1 ≤ B) : Fintype.card (RS Γ S Q n t) ≤ 4 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc _ ≤ B * (4 * B ^ 2 * (B * B)) := by gcongr
    _ = 4 * B ^ 5 := by ring

theorem card_RH_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) : Fintype.card (RH Γ S n t M) ≤ 25 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  have hΓ' : Fintype.card Γ ≤ B := by omega
  have h (k : ℕ) (hk : k ≤ 5) : B ^ k ≤ B ^ 5 := Nat.pow_le_pow_right hB hk
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [card_ChN]
  calc _ ≤ 2 + ((2 * B + B) + ((2 * B + B) * (B * (B * (4 * B ^ 2))) + (B * (B * B) +
        (B * (2 * (B * (B * B))) + (B * (2 * (B * B)) + (B * (B * (B * B)) + B * B)))))) := by gcongr
    _ = 2 * B ^ 0 + 3 * B ^ 1 + 12 * B ^ 5 + 3 * B ^ 3 + 3 * B ^ 4 + B ^ 2 := by ring
    _ ≤ 25 * B ^ 5 := by omega

end Count

section Main

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The total length of the words with their separators. -/
theorem length_wordOf_ofFn {n : ℕ} (u : Fin n → List Γ) :
    (wordOf (List.ofFn u)).length = (∑ j, (u j).length) + n := by
  rw [length_wordOf, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  rfl

end Main

end Nc
end

/-! Source module: Nc.RunOne -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Automata with one input
-/

namespace Nc

open Finset MvPolynomial

set_option linter.unusedSectionVars false

section Rename

variable {S J J' Γ : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  [Fintype J'] [DecidableEq J']

/-- Renaming the inputs. -/
def chEquiv (S : Type) (φ : J ≃ J') : Ch S J ≃ Ch S J' where
  toFun z := match z with
    | .tp s b => .tp s b
    | .inp j => .inp (φ j)
  invFun z := match z with
    | .tp s b => .tp s b
    | .inp j => .inp (φ.symm j)
  left_inv z := by cases z <;> simp
  right_inv z := by cases z <;> simp

/-- Renaming the inputs in letters. -/
def letterEquiv (S Γ : Type) (φ : J ≃ J') : Letter S J Γ ≃ Letter S J' Γ :=
  Equiv.optionCongr (Equiv.prodCongr (chEquiv S φ) (Equiv.refl Γ))

theorem emit_rename (φ : J ≃ J') (o : List (Letter S J Γ)) (z : Ch S J) :
    emit (o.map (letterEquiv S Γ φ)) (chEquiv S φ z) = emit o z := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    rw [List.map_cons, ← List.singleton_append, emit_appendR, ih, ← List.singleton_append (l := o), emit_appendR]
    congr 1
    rcases a with _ | ⟨z', γ⟩
    · rfl
    · have : letterEquiv S Γ φ (some (z', γ)) = some (chEquiv S φ z', γ) := rfl
      rw [this, emit_some, emit_some]
      simp

variable {F : Type*} [CommRing F] {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Renaming the inputs does not change the value. -/
theorem runVal_rename (φ : J ≃ J') (mu : Letter S J' Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J' → List Γ) :
    runVal (fun a => mu (letterEquiv S Γ φ a)) i e t (fun j => u (φ j)) = runVal mu i e t u := by
  unfold runVal
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (letterEquiv S Γ φ)) _ _ fun o => ?_
  have hl : List.ofFn (Equiv.arrowCongr (Equiv.refl (Fin t)) (letterEquiv S Γ φ) o) =
      (List.ofFn o).map (letterEquiv S Γ φ) := by
    rw [List.map_ofFn]
    rfl
  have hm : Matched (List.ofFn o) (fun j => u (φ j)) ↔ Matched ((List.ofFn o).map (letterEquiv S Γ φ)) u := by
    unfold Matched
    refine and_congr (forall_congr' fun s => ?_) ?_
    · have h1 := emit_rename φ (List.ofFn o) (.tp s false)
      have h2 := emit_rename φ (List.ofFn o) (.tp s true)
      rw [← h1, ← h2]
      rfl
    · constructor
      · intro h j
        have h1 := emit_rename φ (List.ofFn o) (.inp (φ.symm j))
        have h2 : chEquiv S φ (.inp (φ.symm j)) = .inp j := by simp [chEquiv]
        have h3 := h (φ.symm j)
        rw [h2] at h1
        rw [h1, h3]
        exact congrArg u (φ.apply_symm_apply j)
      · intro h j
        exact (emit_rename φ (List.ofFn o) (.inp j)).symm.trans (h (φ j))
  rw [hl]
  by_cases h : Matched (List.ofFn o) (fun j => u (φ j))
  · rw [if_pos h, if_pos (hm.1 h), List.map_map]
    rfl
  · rw [if_neg h, if_neg fun h' => h (hm.2 h')]

end Rename

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The one-hot code of a word with an end marker. -/
def code1 (N : ℕ) (u : List Γ) (p : Fin N × Option Γ) : Bool := (u.map some ++ [none])[p.1.1]? = some p.2

end Nc
end

/-! Source module: Nc.RunMn -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Automata with one input: the polynomial of degree at most `N`

Clauses on the input bits allow at most one letter at each place and ask for a letter at each place unless the end
mark came before. The monomial extension then has degree at most `N`, and below the code of a word only this
code is allowed.
-/

namespace Nc

open Finset MvPolynomial

set_option linter.unusedSectionVars false

section Valid

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}

/-- At most one letter at each place; at each place a letter, or the end mark before. -/
structure VOk (x : Fin N × Option Γ → Bool) : Prop where
  one : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
  some : ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true

/-- The letter at a place of a word with its end mark. -/
theorem code1_le {u : List Γ} {p : Fin N} {y : Option Γ} (h : code1 N u (p, y) = true) :
    (u.map some ++ [none])[p.1]? = some y := by simpa [code1] using h

theorem code1_lt {u : List Γ} {p : Fin N} {y : Option Γ} (h : code1 N u (p, y) = true) : p.1 ≤ u.length := by
  have := (List.getElem?_eq_some_iff.1 (code1_le h)).1
  simp at this
  omega

theorem code1_none {u : List Γ} {p : Fin N} (h : code1 N u (p, none) = true) : p.1 = u.length := by
  have h1 := code1_le h
  have h2 := code1_lt h
  rcases h2.lt_or_eq with h3 | h3
  · rw [List.getElem?_append_left (by simpa using h3)] at h1
    simp at h1
  · exact h3

theorem code1_exists (u : List Γ) {p : Fin N} (h : p.1 ≤ u.length) : ∃ y, code1 N u (p, y) = true := by
  have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
  refine ⟨(u.map some ++ [none])[p.1], ?_⟩
  simp [code1, List.getElem?_eq_getElem hlt]

theorem code1_unique {u : List Γ} {p : Fin N} {y y' : Option Γ} (h : code1 N u (p, y) = true)
    (h' : code1 N u (p, y') = true) : y = y' := by
  have h1 := code1_le h
  rw [code1_le h'] at h1
  exact (Option.some.inj h1).symm

theorem vOk_code1 (u : List Γ) (hu : u.length + 1 ≤ N) : VOk (code1 N u) := by
  refine ⟨fun p y y' h h' => code1_unique h h', fun p => ?_⟩
  by_cases hp : p.1 ≤ u.length
  · exact Or.inl (code1_exists u hp)
  · refine Or.inr ⟨⟨u.length, by omega⟩, ?_, ?_⟩
    · rw [Fin.lt_def]
      simp only
      omega
    · simp [code1]

/-- Below the code of a word only this code is allowed. -/
theorem eq_code1 {x : Fin N × Option Γ → Bool} (hx : VOk x) {u : List Γ}
    (hle : ∀ b, x b = true → code1 N u b = true) : x = code1 N u := by
  funext b
  obtain ⟨p, y⟩ := b
  rcases hc : code1 N u (p, y) with _ | _
  · by_contra h
    rw [Bool.not_eq_false] at h
    rw [hle _ h] at hc
    cases hc
  · rcases hx.some p with ⟨y', hy'⟩ | ⟨p', hp', h'⟩
    · rw [code1_unique hc (hle _ hy')]
      exact hy'
    · have h1 := code1_none (hle _ h')
      have h2 := code1_lt hc
      rw [Fin.lt_def] at hp'
      omega

theorem card_ones_le {x : Fin N × Option Γ → Bool} (hx : VOk x) : #{b | x b = true} ≤ N := by
  have : #{b | x b = true} ≤ #(univ : Finset (Fin N)) := by
    refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_
    rintro ⟨p, y⟩ h ⟨p', y'⟩ h' e
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h' e
    subst e
    rw [hx.one p y y' h h']
  simpa using this

theorem card_ones_code1 (u : List Γ) (hu : u.length + 1 ≤ N) : #{b | code1 N u b = true} = u.length + 1 := by
  have : #(univ : Finset (Fin (u.length + 1))) = #{b | code1 N u b = true} := by
    refine Finset.card_bij (fun k _ => (⟨k.1, by omega⟩, (u.map some ++ [none])[k.1]'(by
      have := k.2; simp; omega))) ?_ ?_ ?_
    · intro k _
      have hlt : k.1 < (u.map some ++ [none]).length := by
        have := k.2
        simp
        omega
      simp [code1, List.getElem?_eq_getElem hlt]
    · intro k _ k' _ e
      have := congrArg (fun b => b.1.1) e
      exact Fin.ext this
    · rintro ⟨p, y⟩ h
      simp only [mem_filter, mem_univ, true_and] at h
      have h2 := code1_lt h
      have h1 := code1_le h
      refine ⟨⟨p.1, by omega⟩, mem_univ _, ?_⟩
      have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
      rw [List.getElem?_eq_getElem hlt] at h1
      simp [Option.some.inj h1]
  simpa using this.symm

end Valid

section Rules

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {n t M N : ℕ}

/-- The rules on the input bits. -/
abbrev RC (Γ : Type) (N : ℕ) : Type := (Fin N × Option Γ × Option Γ) ⊕ Fin N

/-- Their literals. -/
noncomputable def cLits : RC Γ N → List (RV Γ S Q n t M N × Bool)
  | .inl (p, y, y') => [(.inl (p, y), true), (.inl (p, y'), true)]
  | .inr p => ((univ : Finset (Option Γ)).toList.map fun y => (.inl (p, y), false)) ++
      ((univ : Finset (Fin N)).filter (· < p)).toList.map fun p' => (.inl (p', none), false)

/-- Their weights. -/
def cRWt : RC Γ N → F
  | .inl (_, y, y') => if y = y' then 1 else 0
  | .inr _ => 0

open scoped Classical in
theorem prod_valid (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RC Γ N, if ∀ l ∈ cLits r, Sum.elim x (hot g) l.1 = l.2 then (cRWt r : F) else 1) =
      if VOk x then 1 else 0 := by
  rw [Fintype.prod_sum_type]
  split_ifs with hx
  · rw [Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · intro p _
      refine if_neg fun h => ?_
      rcases hx.some p with ⟨y, hy⟩ | ⟨p', hp', h'⟩
      · have := h (.inl (p, y), false) (by simp [cLits])
        simp [hy] at this
      · have := h (.inl (p', none), false) (by simp [cLits, hp'])
        simp [h'] at this
    · rintro ⟨p, y, y'⟩ _
      split_ifs with h
      · simp only [cLits, List.forall_mem_cons, Sum.elim_inl] at h
        exact if_pos (hx.one p y y' h.1 h.2.1)
      · rfl
  · have hx' : ¬ ((∀ p y y', x (p, y) = true → x (p, y') = true → y = y') ∧
        ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true) := fun h => hx ⟨h.1, h.2⟩
    by_cases h1 : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
    · have h2 : ¬ ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true := fun h => hx' ⟨h1, h⟩
      push Not at h2
      obtain ⟨p, h3, h4⟩ := h2
      have : (∏ p : Fin N, if ∀ l ∈ cLits (S := S) (Q := Q) (n := n) (t := t) (M := M) (.inr p : RC Γ N),
          Sum.elim x (hot g) l.1 = l.2 then (cRWt (.inr p : RC Γ N) : F) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ p) ?_
        rw [if_pos]
        · rfl
        · intro l hl
          simp only [cLits, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and, mem_filter] at hl
          rcases hl with ⟨y, rfl⟩ | ⟨p', hp', rfl⟩
          · simpa using h3 y
          · simpa using h4 p' hp'
      rw [this, mul_zero]
    · push Not at h1
      obtain ⟨p, y, y', h3, h4, hne⟩ := h1
      have : (∏ q : Fin N × Option Γ × Option Γ,
          if ∀ l ∈ cLits (S := S) (Q := Q) (n := n) (t := t) (M := M) (.inl q : RC Γ N),
          Sum.elim x (hot g) l.1 = l.2 then (cRWt (.inl q : RC Γ N) : F) else 1) = 0 := by
        refine Finset.prod_eq_zero (mem_univ (p, y, y')) ?_
        rw [if_pos]
        · exact if_neg hne
        · intro l hl
          simp only [cLits, List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · simpa using h3
          · simpa using h4
      rw [this, zero_mul]

open scoped Classical in
/-- The sum over finite domains with the clauses on the input bits. -/
theorem fdSum_valid (lits : RS Γ S Q n t ⊕ RH Γ S n t M → List (RV Γ S Q n t M N × Bool))
    (w : RS Γ S Q n t ⊕ RH Γ S n t M → F) (x : Fin N × Option Γ → Bool) :
    fdSum (Sum.elim lits cLits) (Sum.elim w (cRWt : RC Γ N → F)) x = if VOk x then fdSum lits w x else 0 := by
  rw [fdSum_elim lits w cLits cRWt x (if VOk x then 1 else 0)]
  · split_ifs <;> simp
  · intro g
    rw [← prod_valid (F := F) x g]
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hr : ∀ l ∈ cLits r, Sum.elim x (hot g) l.1 = l.2
    · rw [if_pos hr]
      exact (if_pos hr).symm
    · rw [if_neg hr]
      exact (if_neg hr).symm

end Rules

section Monomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial extension along the line through a 0/1 point. -/
theorem line_mnExt (f : (ι → Bool) → F) (u : ι → Bool) :
    line (fun j => if u j then (1 : F) else 0) (mlExtC 0 f) = ∑ b : ι → Bool,
      if ∀ j, b j = true → u j = true then Polynomial.C (f b) * Polynomial.X ^ #{j | b j = true} else 0 := by
  unfold mlExtC
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ j, line (fun j => if u j then (1 : F) else 0) (if b j then X j else 1 - C 0 * X j) =
      if b j then (if u j then Polynomial.X else 0) else 1 := by
    intro j
    split_ifs <;> simp_all [line]
  have hC : line (fun j => if u j then (1 : F) else 0) (C (f b)) = Polynomial.C (f b) := by
    simp [line]
  rw [map_mul, map_prod, hC, Finset.prod_congr rfl fun j _ => h1 j]
  split_ifs with h
  · congr 1
    have h2 : ∀ j, (if b j then (if u j then (Polynomial.X : Polynomial F) else 0) else 1) =
        if b j = true then Polynomial.X else 1 := by
      intro j
      by_cases hb : b j = true
      · simp [hb, h j hb]
      · simp [hb]
    rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  · push Not at h
    obtain ⟨j, hb, hu⟩ := h
    rw [Finset.prod_eq_zero (mem_univ j), mul_zero]
    rw [if_pos hb, if_neg hu]

/-- The degree of the monomial extension. -/
theorem totalDegree_mnExt (f : (ι → Bool) → F) {d : ℕ} (hd : ∀ b, f b ≠ 0 → #{j | b j = true} ≤ d) :
    (mlExtC 0 f).totalDegree ≤ d := by
  unfold mlExtC
  refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
  by_cases hb : f b = 0
  · rw [hb, map_zero, zero_mul, totalDegree_zero]
    exact Nat.zero_le _
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (le_trans ?_ (hd b hb))
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact (totalDegree_X j).le
    · simp

end Monomial

section Main

variable {F : Type} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

end Main

end Nc
end

/-! Source module: Nc.End.Run -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Values of automata: names of inputs, change of rings
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {A : Type*} [CommRing A] {Γ S Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- Change of rings. -/
theorem runVal_map {J : Type*} [DecidableEq J] [Fintype J] {K : Type*} [CommRing K] (φ : A →+* K)
    (mu : Letter S J Γ → Matrix Q Q A) (i e : Q) (t : ℕ) (u : J → List Γ) :
    runVal (fun a => (mu a).map φ) i e t u = φ (runVal mu i e t u) := by
  unfold runVal
  rw [map_sum]
  refine sum_congr rfl fun o _ => ?_
  have h : ∀ L : List (Letter S J Γ), (L.map fun a => (mu a).map φ).prod = ((L.map mu).prod).map φ := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, Matrix.map_mul]
  split_ifs
  · rw [h, Matrix.map_apply]
  · rw [map_zero]

end Nc
end

/-! Source module: Paper.Grids -/
section
namespace Paper
open Finset Nc MvPolynomial
/-- A clause sum: the sum over the bits of the product over the clauses of the weight of the clause if all its
literals hold, and 1 otherwise. -/
noncomputable def clauseSum {R V K : Type} [CommRing R] [Fintype V] [DecidableEq V] [Fintype K]
    (lits : K → List (V × Bool)) (wt : K → R) : R :=
  ∑ x : V → Bool, ∏ κ, if ∀ l ∈ lits κ, x l.1 = l.2 then wt κ else 1

/-- A clause sum is a projection of every family that is complete for grid sums. -/
theorem clauses_of_complete {F : Type} [Field F] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {c : ℕ}
    (hG : GridComplete F G c) {ι V K : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (lits : K → List (V × Bool)) (hne : ∀ κ, lits κ ≠ []) (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b)
    (wt : K → MvPolynomial ι F) (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : c * ∑ κ, (lits κ).length ≤ S) :
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧ aeval M (G S) = clauseSum lits wt := by
  classical
  let N := Σ κ, Fin (lits κ).length
  let v : N → V := fun n => ((lits n.1).get n.2).1
  let W : N → Bool → Bool → MvPolynomial ι F := fun n x r =>
    if r then (if x = ((lits n.1).get n.2).2 then (if n.2.1 = 0 then wt n.1 - 1 else 1) else 0) else 1
  let o : K → Option ι := fun κ => if h : ∃ i, wt κ = X i then some h.choose else none
  have hwt' : ∀ κ, wt κ ∈ affIn (F := F) (o κ) := by
    intro κ
    by_cases h : ∃ i, wt κ = X i
    · have key : ∀ i, wt κ = X i → wt κ ∈ affIn (F := F) (some i) := fun i e => by
        rw [e]
        exact Submodule.subset_span (by simp)
      rw [show o κ = some h.choose from dif_pos h]
      exact key _ h.choose_spec
    · obtain ⟨a, ha⟩ := (hwt κ).resolve_left h
      rw [ha]
      exact C_mem_affIn _ _
  have hv : Function.Surjective v := by
    intro b
    obtain ⟨κ, l, hl, rfl⟩ := hocc b
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨⟨κ, i⟩, rfl⟩
  have hW : ∀ n x r, W n x r ∈ affIn (F := F) (o n.1) := fun n x r => by
    simp only [W]
    split_ifs
    · exact Submodule.sub_mem _ (hwt' _) (one_mem_affIn _)
    · exact one_mem_affIn _
    · exact Submodule.zero_mem _
    · exact one_mem_affIn _
  obtain ⟨M, hM, he⟩ := hG v (fun n : N => n.1) hv (fun κ => ⟨⟨κ, ⟨0, List.length_pos_iff.2 (hne κ)⟩⟩, rfl⟩) W o
    hW S (by simpa [N] using hS)
  · refine ⟨M, hM, he.trans (Finset.sum_congr rfl fun x _ => ?_)⟩
    have hp : ∀ r : K → Bool, ∏ n : N, W n (x (v n)) (r n.1) =
        ∏ κ, ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) (r κ) := fun r => Fintype.prod_sigma _
    simp only [hp]
    rw [← Fintype.prod_sum fun κ b => ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) b]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have hpos := List.length_pos_iff.2 (hne κ)
    rw [Fintype.sum_bool]
    simp only [W, if_true, Bool.false_eq_true, if_false, Finset.prod_const_one]
    by_cases hall : ∀ l ∈ lits κ, x l.1 = l.2
    · rw [if_pos hall]
      have : ∀ i : Fin (lits κ).length, x ((lits κ).get i).1 = ((lits κ).get i).2 := fun i => hall _ (List.get_mem _ _)
      simp only [v, this, if_true]
      rw [Finset.prod_eq_single (⟨0, hpos⟩ : Fin (lits κ).length)]
      · simp
      · intro i _ hi
        exact if_neg fun h => hi (Fin.ext h)
      · simp
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨l, hl, hne'⟩ := hall
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hne'), zero_add]


end Paper
end

/-! Source module: Paper.CircuitPhi -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, proof of Lemma lem:circuit: the clause sum Φ
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset MvPolynomial Nc

section Assignments

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- **Paper: proof of Lemma lem:circuit, one assignment.** "So there is exactly one assignment for each matched sequence
and each sequence of states": an assignment g that violates no clause gives a matched sequence with the first and last
state, and each of these comes from exactly one. -/
theorem lem_circuit_assignment (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q) :
    ((Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e) →
      ∃! g : ∀ d, RE Γ S Q n t M d, (gEm g = o ∧ gSt g = q) ∧ Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g)) ∧
    ∀ g : ∀ d, RE Γ S Q n t M d, gEm g = o → gSt g = q → Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) →
      Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e := by
  refine ⟨fun ⟨h, hi, he⟩ => ?_, fun g h1 h2 hg => h1 ▸ h2 ▸ ⟨hg.matched (by omega), hg.first, hg.last⟩⟩
  obtain ⟨P, c, hg⟩ := exists_good hM hN h hi he
  refine existsUnique_of_exists_of_unique ⟨fun d => match d with
    | .inl τ => o τ
    | .inr (.inl τ) => q τ
    | .inr (.inr (.inl (z, τ))) => P z τ
    | .inr (.inr (.inr (s, p))) => c s p, ⟨rfl, rfl⟩, hg⟩ ?_
  rintro g g' ⟨⟨a1, a2⟩, hg⟩ ⟨⟨a1', a2'⟩, hg'⟩
  have h1 := a1.trans a1'.symm
  have h2 := a2.trans a2'.symm
  funext d
  rcases d with τ | τ | ⟨z, τ⟩ | ⟨s, p⟩
  · exact congrFun h1 τ
  · exact congrFun h2 τ
  · refine Fin.ext ?_
    have e1 := hg.place z τ
    have e2 := hg'.place z τ
    rw [hg.place_zero] at e1
    rw [hg'.place_zero, ← h1] at e2
    exact e1.trans e2.symm
  · have e1 := hg.contents s false p
    have e2 := hg'.contents s false p
    rw [← h1] at e2
    exact e1.trans e2.symm

/-- **Paper: proof of Lemma lem:circuit, the value at a code.** The sum over the assignments at the code of an input is
the value of the automaton on it. -/
theorem lem_circuit_value (mu : Letter S (Fin n) Γ → Matrix Q Q F) (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) :
    fdSum (rLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e) (rWt mu) (code N u) = runVal mu i e t u := by
  classical
  have hl : fdSum (rLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e) (rWt mu) (code N u) = ∑ g : ∀ d, RE Γ S Q n t M d,
      if Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) then
        ∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ)) else 0 := by
    unfold fdSum
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Fintype.prod_sum_type]
    have h1 := prod_soft mu (code N u) g
    have h2 := prod_hard (F := F) i e (code N u) g
    refine Eq.trans (b := (∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ))) *
      if Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) then 1 else 0) ?_ (by simp)
    refine congrArg₂ (· * ·) ?_ ?_
    · exact h1
    · refine Eq.trans ?_ h2
      refine Finset.prod_congr rfl fun r _ => ?_
      by_cases hr : ∀ l ∈ hLits i e r, Sum.elim (code N u) (hot g) l.1 = l.2
      · rw [if_pos hr]
        exact if_pos hr
      · rw [if_neg hr]
        exact if_neg hr
  have hr : runVal mu i e t u = ∑ y : (Fin t → Letter S (Fin n) Γ) × (Fin (t + 1) → Q),
      if Matched (List.ofFn y.1) u ∧ y.2 0 = i ∧ y.2 (Fin.last t) = e then
        ∏ τ, mu (y.1 τ) (y.2 (Fin.castSucc τ)) (y.2 (Fin.succ τ)) else 0 := by
    unfold runVal
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : Matched (List.ofFn o) u
    · rw [if_pos ho, prod_ofFn_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [ho]
    · simp [ho]
  rw [hl, hr, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun g _ => (gEm g, gSt g)) ?_ ?_ ?_ ?_
  · intro g hg
    rw [mem_filter] at hg ⊢
    exact ⟨mem_univ _, (lem_circuit_assignment i e u hM hN _ _).2 g rfl rfl hg.2⟩
  · intro g hg g' hg' heq
    rw [mem_filter] at hg hg'
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    exact ((lem_circuit_assignment i e u hM hN _ _).1 ((lem_circuit_assignment i e u hM hN _ _).2 g' rfl rfl hg'.2)).unique
      ⟨⟨h1, h2⟩, hg.2⟩ ⟨⟨rfl, rfl⟩, hg'.2⟩
  · rintro ⟨o, q⟩ hy
    rw [mem_filter] at hy
    obtain ⟨g, ⟨⟨h1, h2⟩, hg⟩, -⟩ := (lem_circuit_assignment i e u hM hN o q).1 hy.2
    exact ⟨g, by rw [mem_filter]; exact ⟨mem_univ _, hg⟩, by rw [h1, h2]⟩
  · intros
    rfl

end Assignments

section Inputs

variable {R : Type} [CommRing R] {ι α κ : Type}

/-- One more clause for every variable of the code: if its bit is 1 its weight is the variable. -/
def withInputs (lits : κ → List ((ι ⊕ α) × Bool)) : κ ⊕ ι → List ((ι ⊕ α) × Bool) :=
  Sum.elim lits fun b => [(Sum.inl b, true)]

/-- The weights: constants, and the variables of the code. -/
noncomputable def inputWeights (w : κ → R) : κ ⊕ ι → MvPolynomial ι R := Sum.elim (fun k => C (w k)) X

theorem clauseSum_inputs {F : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype κ]
    (lits : κ → List ((ι ⊕ α) × Bool)) (w : κ → F) :
    clauseSum (withInputs lits) (inputWeights w) = mlExtC 0 (wideSum lits w) := by
  classical
  unfold clauseSum mlExtC wideSum
  rw [← (Equiv.sumArrowEquivProdArrow ι α Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.prod_sum_type, map_prod]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun b _ => ?_)
  · have e : (Equiv.sumArrowEquivProdArrow ι α Bool).symm (x, a) = Sum.elim x a := rfl
    simp only [withInputs, inputWeights, Sum.elim_inl, e]
    rw [apply_ite (C : F → MvPolynomial ι F), map_one]
    split_ifs <;> rfl
  · cases hx : x b <;> simp [withInputs, inputWeights, hx]

end Inputs

theorem card_clauses {a b c d p i : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype p] [Fintype i] :
    Fintype.card ((((a ⊕ b) ⊕ c) ⊕ d ⊕ p × p) ⊕ i) = Fintype.card a + Fintype.card b + Fintype.card c +
      (Fintype.card d + Fintype.card p * Fintype.card p) + Fintype.card i := by
  simp only [Fintype.card_sum, Fintype.card_prod]

theorem literal_bound {B N I E R₁ R₂ R₃ D IE : ℕ} (hB : 1 ≤ B) (hN : N ≤ B) (hE : E ≤ 9 * B ^ 3) (h1 : R₁ ≤ 4 * B ^ 5)
    (h2 : R₂ ≤ 25 * B ^ 5) (hD : D ≤ 6 * B ^ 2) (h3 : R₃ ≤ 2 * B ^ 3) (hI : I ≤ B * B) (hIE : IE = I + E + 3) :
    (R₁ + R₂ + R₃ + (D + E * E) + I) * IE ≤ 1600 * B ^ 9 := by
  have p := fun k (hk : k ≤ 6) => Nat.pow_le_pow_right (show 0 < B from hB) hk
  have h5 := p 5 (by norm_num)
  have h33 := p 3 (by norm_num)
  have h22 := p 2 (by norm_num)
  have hBB : B * B = B ^ 2 := (pow_two B).symm
  have hE2 : E * E ≤ 81 * B ^ 6 := by
    calc E * E ≤ (9 * B ^ 3) * (9 * B ^ 3) := Nat.mul_le_mul hE hE
      _ = 81 * B ^ 6 := by ring
  have h23 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have h03 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
  calc (R₁ + R₂ + R₃ + (D + E * E) + I) * IE ≤ 120 * B ^ 6 * (13 * B ^ 3) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 1600 * B ^ 9 := by ring_nf; omega

variable {F : Type} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Lemma lem:circuit, Φ.** A clause sum with at most 1600 B⁹ literals, weights that are constants or
variables, degree at most N, and the automaton's value at the code of every word of fewer than N symbols: what the proof
uses of Φ. ("It has degree at most n, and at the code of a word it takes that word's value ... This has v^O(1) literals.")
B is the sum of the numbers of steps, places, states, symbols and tapes. That Φ is the printed sum over words is not
stated. -/
theorem lem_circuit_phi (mu : Letter S Unit Γ → Matrix Q Q F) (i e : Q) (t N : ℕ) :
    ∃ (V K : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype K) (_ : DecidableEq K)
      (lits : K → List (V × Bool)) (wt : K → MvPolynomial (Fin N × Option Γ) F),
      (∀ κ, lits κ ≠ []) ∧ (∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b) ∧ (∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) ∧
      ∑ κ, (lits κ).length ≤ 1600 * (t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2) ^ 9 ∧
      (clauseSum lits wt).totalDegree ≤ N ∧
      ∀ u : List Γ, u.length + 1 ≤ N →
        eval (fun b => if code1 N u b then (1 : F) else 0) (clauseSum lits wt) = runVal mu i e t fun _ => u := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B, B = t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 := ⟨_, rfl⟩
  rw [← hBdef]
  have hB : 1 ≤ B := by omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = N + t + 1 := ⟨_, rfl⟩
  let φ : Fin 1 ≃ Unit := Equiv.ofUnique (Fin 1) Unit
  let mu' : Letter S (Fin 1) Γ → Matrix Q Q F := fun a => mu (letterEquiv S Γ φ a)
  have cE := card_RE_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hB
  have cD := card_RD_le (S := S) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) hB
  have cS := card_RS_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB
  have cH := card_RH_le (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB
  have cI : Fintype.card (Fin N × Option Γ) ≤ B * B := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact Nat.mul_le_mul (by omega) (by omega)
  have cV : Fintype.card (RC Γ N) ≤ 2 * B ^ 3 := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    have h1 : N ≤ B := by omega
    have h2 : Fintype.card Γ + 1 ≤ B := by omega
    have h3 : B ≤ B ^ 3 := Nat.le_self_pow (by omega) B
    calc _ ≤ B * (B * B) + B := by gcongr
      _ = B ^ 3 + B := by ring
      _ ≤ 2 * B ^ 3 := by omega
  let L := Sum.elim (rLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (N := N) i e) cLits
  let W : (RS Γ S Q 1 t ⊕ RH Γ S 1 t M) ⊕ RC Γ N → F := Sum.elim (rWt mu') cRWt
  have hM0 : 0 < M := by omega
  have hE0 : ∀ d : RD S 1 t M, Nonempty (RE Γ S Q 1 t M d)
    | .inl _ => ⟨(none : Letter S (Fin 1) Γ)⟩
    | .inr (.inl _) => ⟨i⟩
    | .inr (.inr (.inl _)) => ⟨⟨0, hM0⟩⟩
    | .inr (.inr (.inr _)) => ⟨(none : Option Γ)⟩
  have hle : ∀ d, Fintype.card (RE Γ S Q 1 t M d) ≤ Fintype.card (Σ d, RE Γ S Q 1 t M d) := fun d =>
    Fintype.card_le_of_injective (Sigma.mk d) sigma_mk_injective
  obtain ⟨f, hf⟩ : ∃ f, f = fdSum L W := ⟨_, rfl⟩
  have hphi : clauseSum (withInputs (fdLits L)) (inputWeights (fdWt W)) = mlExtC 0 f := by
    rw [clauseSum_inputs, hf, show fdSum L W = wideSum (fdLits L) (fdWt W) from funext fun x => fdSum_eq L W x]
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, withInputs (fdLits L), inputWeights (fdWt W),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ((((r | r) | r) | d | ⟨p, q⟩) | b)
    · simp [withInputs, fdLits, L, rLits, sLits]
    · rcases r with ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) <;>
        simp [withInputs, fdLits, L, rLits, hLits, hM0]
    · rcases r with ⟨p, y, y'⟩ | p <;> simp [withInputs, fdLits, L, cLits, Finset.univ_eq_empty_iff]
    · have := hE0 d
      simp [withInputs, fdLits, Finset.univ_eq_empty_iff, not_isEmpty_iff, this]
    · simp [withInputs, fdLits]
    · simp [withInputs]
  · rintro (b | ⟨d, x⟩)
    · exact ⟨.inr b, (Sum.inl b, true), by simp [withInputs], rfl⟩
    · exact ⟨.inl (.inr (.inl d)), (Sum.inr ⟨d, x⟩, false), by simp [withInputs, fdLits], rfl⟩
  · rintro (k | b)
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨b, rfl⟩
  · obtain ⟨IE, hIE⟩ : ∃ x, x = Fintype.card (Fin N × Option Γ) + Fintype.card (Σ d, RE Γ S Q 1 t M d) + 3 := ⟨_, rfl⟩
    have hlen : ∀ κ, (withInputs (fdLits L) κ).length ≤ IE := by
      rintro ((((r | r) | r) | d | ⟨p, q⟩) | b)
      · simp [withInputs, fdLits, L, rLits, sLits]
        omega
      · rcases r with ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) <;>
          simp [withInputs, fdLits, L, rLits, hLits] <;> (try split_ifs) <;> (try simp) <;> omega
      · rcases r with ⟨p, y, y'⟩ | p
        · simp [withInputs, fdLits, L, cLits]
          omega
        · have h1 : ((univ : Finset (Fin N)).filter (· < p)).card ≤ N := (Finset.card_filter_le _ _).trans (by simp)
          have h2 : N + (Fintype.card Γ + 1) ≤ Fintype.card (Fin N × Option Γ) + 1 := by
            rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
            have hN1 : 1 ≤ N := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
            obtain ⟨N', hN'⟩ := Nat.exists_eq_add_of_le hN1
            subst hN'
            have h9 := Nat.le_mul_of_pos_right N' (Nat.succ_pos (Fintype.card Γ))
            rw [Nat.succ_eq_add_one] at h9
            rw [add_mul, one_mul]
            omega
          simp [withInputs, fdLits, L, cLits]
          omega
      · have := hle d
        simp [withInputs, fdLits]
        omega
      · simp [withInputs, fdLits]
        omega
      · simp [withInputs]
        omega
    refine (Finset.sum_le_card_nsmul _ _ IE fun κ _ => hlen κ).trans ?_
    rw [smul_eq_mul, Finset.card_univ]
    rw [card_clauses]
    exact literal_bound hB (by omega) cE cS cH cD cV cI hIE
  · rw [hphi]
    refine totalDegree_mnExt f fun b hb => ?_
    rw [hf, fdSum_valid] at hb
    by_cases hx : VOk b
    · exact card_ones_le hx
    · rw [if_neg hx] at hb
      exact absurd rfl hb
  · intro u hu
    have hv : ∀ b, f b = if VOk b then fdSum (rLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (N := N) i e)
        (rWt mu') b else 0 := by
      intro b
      rw [hf, fdSum_valid]
    rw [hphi]
    have hcode : code N (fun _ : Fin 1 => u) = code1 N u := by
      funext b
      simp [code, code1, wordOf]
    have hval : f (code1 N u) = runVal mu i e t fun _ => u := by
      rw [hv, if_pos (vOk_code1 u hu), ← hcode, lem_circuit_value mu' i e (fun _ => u) (by omega)
        (by rw [length_wordOf_ofFn]; simpa using hu)]
      exact runVal_rename φ mu i e t fun _ => u
    have hline : line (fun b => if code1 N u b then (1 : F) else 0) (mlExtC 0 f) =
        Polynomial.C (runVal mu i e t fun _ => u) * Polynomial.X ^ (u.length + 1) := by
      rw [line_mnExt, Finset.sum_eq_single (code1 N u)]
      · rw [if_pos fun _ h => h, hval, card_ones_code1 u hu]
      · intro b _ hne
        split_ifs with h
        · have h0 : f b = 0 := by
            rw [hv]
            exact if_neg fun hx => hne (eq_code1 hx h)
          rw [h0, map_zero, zero_mul]
        · rfl
      · intro h
        exact absurd (mem_univ _) h
    rw [← eval_one_line, hline]
    simp

end Paper
end

/-! Source module: Nc.End.Thm -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The substitution that names letters by bits
-/

set_option linter.unusedSectionVars false

namespace NS1

open Finset MvPolynomial

variable {A : Type} [CommRing A]

/-- The substitution that names the letters by bits. -/
noncomputable def letS (K : Type*) [Field K] {Γ : Type*} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ) :
    Fin N × Option Γ → MvPolynomial (Fin N × Option Bool) K := fun q =>
  match q.2 with
  | none => X (q.1, none)
  | some γ => if γ = bt true then X (q.1, some true) else if γ = bt false then X (q.1, some false) else 0

theorem eval_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ} (hb : Function.Injective bt)
    (N : ℕ) (w : List Bool) (q : Fin N × Option Γ) :
    eval (codeB K N w) (letS K bt N q) =
      if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0 := by
  obtain ⟨p, o⟩ := q
  have hw : Nc.wordOf (List.ofFn fun _ : Fin 1 => w.map bt) = w.map (some ∘ bt) ++ [none] := by
    simp [Nc.wordOf]
  have hcode : Nc.code N (fun _ : Fin 1 => w.map bt) (p, o) =
      decide ((w.map (some ∘ bt) ++ [none])[(p : ℕ)]? = some o) := by
    unfold Nc.code
    rw [hw]
  have hmap : w.map (some ∘ bt) ++ [none] = (w.map some ++ [none]).map (Option.map bt) := by
    simp
  have hget : ∀ o' : Option Γ, ((w.map (some ∘ bt) ++ [none])[(p : ℕ)]? = some o') ↔
      ∃ x, (w.map some ++ [none])[(p : ℕ)]? = some x ∧ Option.map bt x = o' := by
    intro o'
    rw [hmap, List.getElem?_map, Option.map_eq_some_iff]
  rw [hcode]
  simp only [decide_eq_true_eq, hget]
  rcases o with _ | γ
  · simp only [letS, eval_X, codeB]
    refine if_congr ⟨fun h => ⟨_, h, rfl⟩, ?_⟩ rfl rfl
    rintro ⟨x, h1, h2⟩
    rw [Option.map_eq_none_iff] at h2
    rw [h1, h2]
  · have hx : ∀ b : Bool, γ = bt b → ((∃ x, (w.map some ++ [none])[(p : ℕ)]? = some x ∧
        Option.map bt x = some γ) ↔ (w.map some ++ [none])[(p : ℕ)]? = some (some b)) := by
      intro b hγ
      constructor
      · rintro ⟨x, h1, h2⟩
        rw [Option.map_eq_some_iff] at h2
        obtain ⟨y, rfl, h3⟩ := h2
        rw [h1, hb (h3.trans hγ)]
      · intro h
        exact ⟨_, h, by rw [hγ]; rfl⟩
    by_cases h1 : γ = bt true
    · simp only [letS, if_pos h1, eval_X, codeB]
      exact if_congr (hx true h1).symm rfl rfl
    · by_cases h2 : γ = bt false
      · simp only [letS, if_neg h1, if_pos h2, eval_X, codeB]
        exact if_congr (hx false h2).symm rfl rfl
      · simp only [letS, if_neg h1, if_neg h2, map_zero]
        rw [if_neg]
        rintro ⟨x, -, h3⟩
        rw [Option.map_eq_some_iff] at h3
        obtain ⟨y, -, h4⟩ := h3
        cases y
        · exact h2 h4.symm
        · exact h1 h4.symm

theorem isAffine_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    (q : Fin N × Option Γ) : Nc.IsAffine (letS K bt N q) := by
  have hX : ∀ j : Fin N × Option Bool, Nc.IsAffine (X j : MvPolynomial (Fin N × Option Bool) K) := fun j =>
    Or.inr ⟨j, 1, 0, by simp⟩
  obtain ⟨p, o⟩ := q
  rcases o with _ | γ
  · exact hX _
  · simp only [letS]
    split_ifs
    · exact hX _
    · exact hX _
    · exact Or.inl ⟨0, by simp⟩

theorem totalDegree_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    (q : Fin N × Option Γ) : (letS K bt N q).totalDegree ≤ 1 := by
  obtain ⟨p, o⟩ := q
  rcases o with _ | γ
  · simp only [letS]
    exact (totalDegree_X _).le
  · simp only [letS]
    split_ifs
    · exact (totalDegree_X _).le
    · exact (totalDegree_X _).le
    · simp

theorem totalDegree_aeval_le {K : Type*} [Field K] {σ τ : Type*} (p : MvPolynomial σ K)
    (f : σ → MvPolynomial τ K) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finsetSum_le fun d hd => ?_
  refine (totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap K (MvPolynomial τ K) (coeff d p)).totalDegree = 0 := totalDegree_C _
  rw [h0, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have h1 : ∀ i ∈ d.support, (f i ^ d i).totalDegree ≤ d i := fun i _ => by
    refine (totalDegree_pow _ _).trans ?_
    calc d i * (f i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = d i := mul_one _
  refine (sum_le_sum h1).trans ?_
  exact le_totalDegree hd

theorem eval_aeval' {K : Type*} [Field K] {σ τ : Type*} (x : τ → K) (f : σ → MvPolynomial τ K)
    (p : MvPolynomial σ K) : eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
  have h : ((eval x).comp (aeval f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom) =
      eval fun i => eval x (f i) := by
    apply ringHom_ext
    · intro r; simp
    · intro i; simp
  exact DFunLike.congr_fun h p

theorem eval_sub {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ}
    (hb : Function.Injective bt) (N : ℕ) (w : List Bool) (p : MvPolynomial (Fin N × Option Γ) K) :
    eval (codeB K N w) (aeval (letS K bt N) p) =
      eval (fun q => if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0) p := by
  have e1 : (fun q => eval (codeB K N w) (letS K bt N q)) =
      fun q => if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0 := by
    funext q
    exact eval_letS hb N w q
  exact (eval_aeval' (codeB K N w) (letS K bt N) p).trans (congrArg (fun g => eval g p) e1)

end NS1
end

/-! Source module: Nc.End.PermThm -/
section
namespace NS1
open Finset MvPolynomial
theorem eval_code1 {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ}
    (hb : Function.Injective bt) (N : ℕ) (w : List Bool) (p : MvPolynomial (Fin N × Option Γ) K) :
    eval (codeB K N w) (aeval (letS K bt N) p) =
      eval (fun q => if Nc.code1 N (w.map bt) q then (1 : K) else 0) p := by
  rw [eval_sub hb]
  congr 2
  funext q
  simp [Nc.code, Nc.code1, Nc.wordOf]

/-- A substitution of affine polynomials followed by the naming of letters by bits is affine. -/
theorem isAffine_aeval_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    {p : MvPolynomial (Fin N × Option Γ) K} (hp : Nc.IsAffine p) : Nc.IsAffine (aeval (letS K bt N) p) := by
  rcases hp with ⟨b, rfl⟩ | ⟨i, a, b, rfl⟩
  · exact Or.inl ⟨b, by simp [algebraMap_eq]⟩
  · rw [map_add, map_mul, aeval_C, aeval_C, aeval_X]
    rcases isAffine_letS (K := K) bt N i with ⟨b', hb'⟩ | ⟨j, a', b', hb'⟩
    · exact Or.inl ⟨a * b' + b, by simp [hb']⟩
    · exact Or.inr ⟨j, a * a', a * b' + b, by simp [hb']; ring⟩


end NS1
end

/-! Source module: NS1.Main -/
section
namespace NS1
theorem lt_two_pow_lg (n : ℕ) : n < 2 ^ lg n := Nat.lt_pow_succ_log_self (by norm_num) n

theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := Nat.succ_le_succ (Nat.log_mono_right h)

theorem lg_pow_le {n k : ℕ} (hk : 1 ≤ k) : lg (n ^ k) ≤ k * lg n := by
  have h1 : n ^ k < 2 ^ (k * lg n) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (lt_two_pow_lg n) (by omega)
  unfold lg at h1 ⊢
  refine Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow' ?_ h1)
  have : 1 * 1 ≤ k * (Nat.log 2 n + 1) := Nat.mul_le_mul hk (by omega)
  omega

theorem le_lg_pow {n k : ℕ} (hn : n ≠ 0) : k * (lg n - 1) + 1 ≤ lg (n ^ k) := by
  unfold lg
  rw [Nat.add_sub_cancel]
  refine Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) ?_)
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) k

theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) h)

theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn

/-- Powers of the logarithm are small. -/
theorem poly_lg (c k : ℕ) : ∃ n₀, ∀ n, n₀ ≤ n → c * lg n ^ k ≤ n := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
  have h2 : ∀ᶠ L : ℕ in Filter.atTop, (L : ℝ) ^ k / 2 ^ L < 1 / (2 * (c + 1)) :=
    h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 h2
  refine ⟨2 ^ L₀ + 1, fun n hn => ?_⟩
  have hp : 1 ≤ 2 ^ L₀ := Nat.one_le_two_pow
  have hn0 : n ≠ 0 := by omega
  have hL : L₀ ≤ lg n := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have h3 := hL₀ (lg n) hL
  have h4 := two_pow_lg_le hn0
  have hlg : 1 ≤ lg n := by unfold lg; omega
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  have h5 : (c : ℝ) * (lg n : ℝ) ^ k ≤ 2 ^ (lg n - 1) := by
    have e : (2 : ℝ) ^ lg n = 2 * 2 ^ (lg n - 1) := by
      have : lg n = lg n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [e] at h3
    have : (0 : ℝ) ≤ (lg n : ℝ) ^ k := by positivity
    nlinarith
  have h6 : c * lg n ^ k ≤ 2 ^ (lg n - 1) := by exact_mod_cast h5
  exact h6.trans h4


end NS1
end

/-! Source module: NS1.Scale -/
section
namespace NS1
theorem pow_le_pow {u a b : ℕ} (hu : 1 ≤ u) (h : a ≤ b) : u ^ a ≤ u ^ b := Nat.pow_le_pow_right hu h

end NS1
end

/-! Source module: Nc.Acc.Prog -/
section
namespace NS1
theorem length_tbits (z : Tree) : (tbits z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [tbits, List.length_cons, List.length_append, iha, ihb, Tree.size]


end NS1
end

/-! Source module: Paper.Circuit -/
section
set_option linter.unusedSectionVars false

namespace Paper

open Finset NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem wordG_self {Γ : Type} (b : Γ) (z : Tree) : Nc.Dl.wordG b b z = List.replicate z.size b := by
  induction z with
  | nil => rfl
  | cons x y ihx ihy =>
    rw [Nc.Dl.wordG, ihx, ihy, List.replicate_append_replicate, Tree.size]
    rw [show x.size + y.size + 1 = (x.size + y.size) + 1 from rfl, List.replicate_succ]

theorem wordG_bits {Γ : Type} (f : Bool → Γ) (z : Tree) :
    Nc.Dl.wordG (f false) (f true) z = (tbits z).map f := by
  induction z with
  | nil => rfl
  | cons x y ihx ihy => simp only [tbits, Nc.Dl.wordG, List.map_cons, List.map_append, ihx, ihy]

/-- In a nonzero ring the two symbols of a universal automaton are different: with one symbol the words of two plain
instances of equal size, with the values 1 and 0, would be equal. -/
theorem universal_symbols_ne [Nontrivial A] {S Γ Q : Type} [Fintype S] [DecidableEq S] [Fintype Γ] [DecidableEq Γ]
    [Fintype Q] [DecidableEq Q] {mu : Nc.Letter S Unit Γ → Matrix Q Q A} {i e : Q} {b0 b1 : Γ} {C : ℕ}
    (h : ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
      Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z) : b0 ≠ b1 := by
  intro hb
  subst hb
  obtain ⟨c1, hc1⟩ : ∃ c, c = (Fm.quote .nil).code := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = Fm.fail.code := ⟨_, rfl⟩
  have e1 : Ev θ (Fm.ofTree (Tree.cons c1 c2).hd) (Tree.cons c1 c2).tl [Run.det 1 .nil] := by
    show Ev θ (Fm.ofTree c1) c2 _
    rw [hc1, Fm.ofTree_code]
    exact .quote _ _
  have e2 : Ev θ (Fm.ofTree (Tree.cons c2 c1).hd) (Tree.cons c2 c1).tl [] := by
    show Ev θ (Fm.ofTree c2) c1 _
    rw [hc2, Fm.ofTree_code]
    exact .fail _
  have hs : (Tree.cons c2 c1).size = (Tree.cons c1 c2).size := by simp only [Tree.size]; omega
  obtain ⟨t, ht⟩ : ∃ t, t = C * ((Tree.cons c1 c2).size + 1) * lg ((Tree.cons c1 c2).size + 1) ^ 2 := ⟨_, rfl⟩
  have h1 := h 1 (.cons c1 c2) t ⟨e1.hl, by rw [e1.evl]; simp [Run.det]⟩ ht.ge
  have h2 := h 1 (.cons c2 c1) t ⟨e2.hl, by rw [e2.evl]; simp⟩ (by rw [hs]; exact ht.ge)
  simp only [wordG_self, hs] at h1 h2
  rw [h1, pv, pv, e1.evl, e2.evl] at h2
  simp [pval, Run.det] at h2

open MvPolynomial in
/-- **Paper: proof of Lemma lem:circuit, Φ for the universal automaton.** "By Corollary cor:clauses a circuit for the
permanent gives one for Φ ... By Proposition prop:universal its value is pv(z) at the code of a plain z": an affine
projection of every family that is complete for clause sums, of degree at most n = v^(H−32)+1, with these values. The
symbols of other letters than the two of words of trees are set to 0. -/
theorem lem_circuit_universal (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      Nc.GridComplete F G κ → ∀ v m, v₀ ≤ v → v ^ B₀ ≤ m →
      ∃ Mat : Fin m × Fin m → MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) F,
        (∀ q, Nc.IsAffine (Mat q)) ∧ (aeval Mat (G m)).totalDegree ≤ v ^ (H - 32) + 1 ∧
        ∀ z : Tree, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
          eval (codeB F (v ^ (H - 32) + 1) (tbits z)) (aeval Mat (G m)) = algebraMap A F (pv θ z) := by
  obtain ⟨S, Γ, Q, _, _, _, _, _, _, mu, i, e, b0, b1, C, huni⟩ := ValiantBorder.universalAutomaton θ hθ
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ := poly_lg (2 * C * (H + 1) ^ 2) 2
  refine ⟨9 * (H + 2) + 1, 1600 * κ + cs + n₀ + 4, Nat.succ_pos _, fun F _ _ G hG v m hv hm => ?_⟩
  have : Nontrivial A := (algebraMap A F).domain_nontrivial
  have hb : Function.Injective fun b => if b = true then b1 else b0 := by
    have hne := universal_symbols_ne huni
    intro x y hxy
    rcases x <;> rcases y <;> simp_all [eq_comm]
  obtain ⟨bt, hbt⟩ : ∃ bt : Bool → Γ, bt = fun b => if b = true then b1 else b0 := ⟨_, rfl⟩
  rw [← hbt] at hb
  obtain ⟨n, hn⟩ : ∃ n, n = v ^ (H - 32) + 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = v ^ (H + 1) := ⟨_, rfl⟩
  rw [← hn]
  obtain ⟨V, K, _, _, _, _, lits, wt, hne, hocc, hwt, hlit, hdeg, hev⟩ :=
    lem_circuit_phi (fun a => (mu a).map (algebraMap A F)) i e t n
  have hv1 : 1 ≤ v := by omega
  have hsize : κ * ∑ k, (lits k).length ≤ m := by
    have e1 : t + n + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 ≤ v ^ (H + 2) := by
      have a1 : v ^ (H - 32) ≤ v ^ (H + 1) := pow_le_pow hv1 (by omega)
      have a2 : v ≤ v ^ (H + 1) := Nat.le_self_pow (by omega) v
      have a3 : v ^ (H + 2) = v ^ (H + 1) * v := pow_succ _ _
      have a4 : v ^ (H + 1) * 4 ≤ v ^ (H + 1) * v := Nat.mul_le_mul_left _ (by omega)
      omega
    calc κ * ∑ k, (lits k).length ≤ κ * (1600 * (v ^ (H + 2)) ^ 9) :=
          Nat.mul_le_mul_left _ (hlit.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e1 9)))
      _ = 1600 * κ * v ^ (9 * (H + 2)) := by rw [← pow_mul, Nat.mul_comm (H + 2) 9]; ring
      _ ≤ v * v ^ (9 * (H + 2)) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (9 * (H + 2) + 1) := (pow_succ' _ _).symm
      _ ≤ m := hm
  obtain ⟨Mat, hMat, he⟩ := clauses_of_complete hG lits hne hocc wt hwt hsize
  have e0 : aeval (fun q => aeval (letS F bt n) (Mat q)) (G m) = aeval (letS F bt n) (aeval Mat (G m)) :=
    (comp_aeval_apply Mat (aeval (letS F bt n)) (G m)).symm
  refine ⟨fun q => aeval (letS F bt n) (Mat q), fun q => isAffine_aeval_letS bt n (hMat q), ?_, fun z hz hpl => ?_⟩
  · rw [e0, he]
    exact (totalDegree_aeval_le _ _ (totalDegree_letS bt n)).trans hdeg
  · rw [e0, he, eval_code1 hb, hev _ (by rw [List.length_map, length_tbits]; omega),
      Nc.runVal_map (algebraMap A F) mu i e _ _]
    refine congrArg _ ?_
    have hw : (tbits z).map bt = Nc.Dl.wordG b0 b1 z := by
      rw [← wordG_bits bt z, hbt]
      rfl
    rw [hw]
    refine huni (v ^ H) z t hpl ?_
    have h1 : z.size + v ^ H ≤ 2 * v ^ H := by
      have := hz.trans (pow_le_pow hv1 (show H - 32 ≤ H by omega))
      omega
    have h2 : lg (z.size + v ^ H) ≤ (H + 1) * lg v := by
      refine (lg_mono (h1.trans ?_)).trans (lg_pow_le (by omega))
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ (by omega)
    calc C * (z.size + v ^ H) * lg (z.size + v ^ H) ^ 2 ≤ C * (2 * v ^ H) * ((H + 1) * lg v) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 2)
      _ = v ^ H * (2 * C * (H + 1) ^ 2 * lg v ^ 2) := by ring
      _ ≤ v ^ H * v := Nat.mul_le_mul_left _ (hn₀ v (by omega))
      _ = t := by rw [ht, pow_succ]

end Paper
end

open NS1 MvPolynomial
theorem solution {A : Type} [CommRing A] {θ : List Bool → A} (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      ValiantBorder.GridComplete F G κ → ∀ v m, v₀ ≤ v → v ^ B₀ ≤ m →
      ∃ Mat : Fin m × Fin m → MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) F,
        (∀ q, ValiantBorder.IsAffine (Mat q)) ∧ (aeval Mat (G m)).totalDegree ≤ v ^ (H - 32) + 1 ∧
        ∀ z : Tree, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
          eval (codeB F (v ^ (H - 32) + 1) (tbits z)) (aeval Mat (G m)) = algebraMap A F (pv θ z) := Paper.lem_circuit_universal hθ hH κ
