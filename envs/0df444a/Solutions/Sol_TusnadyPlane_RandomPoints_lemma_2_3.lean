-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:35:55.08889+00:00
-- url     : https://prove2.me/submissions/2b5e3ac4-6348-4a7d-8784-49ba6f8793c9

import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Process.Adapted
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_TusnadyPlane_RandomPoints_localExperiment
universe u

section
theorem ite_eq_left {α : Sort*} {p : Prop} {_ : Decidable p} {a b : α} (h : p) : (if p then a else b) = a :=
  if_pos h

end

section
/-!
# Oscillation, midpoint, and Lemma 2.1 of the manuscript (vertical comparison)

Auditor's supplement (not part of the audited archive).

Section 2.1 of the manuscript defines, for a function `f` of the height and a vertical
interval `B`,

`osc_B f = max_B f - min_B f`,   `mid_B f = (max_B f + min_B f) / 2`,

where the extrema are over `y ∈ B`. All functions considered there take finitely many values,
so the extrema exist. Here `max_B f` and `min_B f` are `sSup (f '' B)` and `sInf (f '' B)`;
`maxOn_mem` and `minOn_mem` show that for a function with finitely many values on a nonempty
`B` they are attained, i.e. they are the maximum and the minimum. `osc_const_mul` is the
manuscript's "Clearly `osc_B (c f) = |c| osc_B f` for real `c`"; with these definitions of
the extrema it holds for every `B` and every `f`. `osc_neg` is its case `c = -1`, the
manuscript's "`osc_B (-g) = osc_B g`".

`osc_add_le` is the triangle inequality `osc_B (f + g) ≤ osc_B f + osc_B g`. It is proved as
in the manuscript, "because the maximum of `f+g` on `B` is at most `max_B f + max_B g`, and
its minimum is at least `min_B f + min_B g`": these two facts are `maxOn_add_le` and
`add_minOn_le`. `osc_sum_le` is the triangle inequality for finite sums. (The reverse
triangle inequality is in `StepOsc.lean`.)

Section 2.2 cuts `J` into blocks (`block`, `iUnion_block`, `block_disjoint`) and sets
`R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`, the inner region. `iUnion_inner_blocks` shows that the
union `B_2 ∪ ⋯ ∪ B_{b-1}` of the inner blocks is the interval `[s + L, s + (b-1) L)`, and
`inner_blocks_nonempty` that this interval is not empty when `b ≥ 3`.

`vertical_comparison` is **Lemma 2.1** as stated: for `J` cut into `b` blocks
`B_1, …, B_b` of equal length, from bottom to top, and `f` with finitely many values on `J`,

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof is the one of the manuscript, sentence by sentence:

* `maxOn_sub_minOn_le_osc`, `maxOn_sub_minOn_eq`: the first display. Its first line is
  `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`,
  and its second line is the same with `B_1` and `B_b` exchanged. "Since `J` contains `B_1`
  and `B_b`", the inequality holds, and the equality holds because "the extrema of `f` on a
  block `B` are `mid_B f ± ½ osc_B f`" (`maxOn_eq_mid_add`, `minOn_eq_mid_sub`);
* `half_osc_add_abs_mid_sub_le`: "Taking the larger of the two right-hand sides,
  `osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`";
* `osc_mono`: "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`";
* `vertical_comparison_sets`: "Adding these `b-2` inequalities and twice the last display
  proves (4)."

It uses nothing about the blocks except that they are nonempty subsets of `J`
(`vertical_comparison_sets`). This file does not use the archive.
-/

namespace R56Audit

noncomputable section

variable {α : Type*}

/-- `max_B f`, as a supremum. -/
def maxOn (B : Set α) (f : α → ℝ) : ℝ := sSup (f '' B)

/-- `min_B f`, as an infimum. -/
def minOn (B : Set α) (f : α → ℝ) : ℝ := sInf (f '' B)

/-- The oscillation `osc_B f = max_B f - min_B f` of display (3). -/
def osc (B : Set α) (f : α → ℝ) : ℝ := maxOn B f - minOn B f

/-- The midpoint `mid_B f = (max_B f + min_B f) / 2` of display (3). -/
def mid (B : Set α) (f : α → ℝ) : ℝ := (maxOn B f + minOn B f) / 2

lemma le_maxOn {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    f y ≤ maxOn B f :=
  le_csSup hf.bddAbove (Set.mem_image_of_mem f hy)

lemma minOn_le {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    minOn B f ≤ f y :=
  csInf_le hf.bddBelow (Set.mem_image_of_mem f hy)

lemma maxOn_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, f y ≤ c) :
    maxOn B f ≤ c := by
  apply csSup_le (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

lemma le_minOn {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, c ≤ f y) :
    c ≤ minOn B f := by
  apply le_csInf (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/-- The extrema are `mid_B f ± osc_B f / 2`. -/
lemma maxOn_eq_mid_add (B : Set α) (f : α → ℝ) : maxOn B f = mid B f + osc B f / 2 := by
  unfold mid osc; ring

lemma minOn_eq_mid_sub (B : Set α) (f : α → ℝ) : minOn B f = mid B f - osc B f / 2 := by
  unfold mid osc; ring

/-- A difference of two values on `B` is at most the oscillation. -/
lemma sub_le_osc {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y y' : α} (hy : y ∈ B)
    (hy' : y' ∈ B) : f y - f y' ≤ osc B f := by
  have h1 := le_maxOn hf hy
  have h2 := minOn_le hf hy'
  unfold osc
  linarith

/-- The oscillation is the least bound for the differences of two values on `B`. -/
lemma osc_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ}
    (h : ∀ y ∈ B, ∀ y' ∈ B, f y - f y' ≤ c) : osc B f ≤ c := by
  have h1 : maxOn B f ≤ minOn B f + c := by
    apply maxOn_le hB
    intro y hy
    have : f y - c ≤ minOn B f := le_minOn hB (fun y' hy' => by linarith [h y hy y' hy'])
    linarith
  unfold osc
  linarith

/-- The extrema over a subset lie between the extrema over the set. -/
lemma maxOn_mono {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : maxOn A f ≤ maxOn B f :=
  maxOn_le hA fun _ hy => le_maxOn hf (hAB hy)

lemma minOn_anti {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : minOn B f ≤ minOn A f :=
  le_minOn hA fun _ hy => minOn_le hf (hAB hy)

lemma maxOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    maxOn B f = maxOn B g := by
  unfold maxOn
  rw [Set.image_congr h]

lemma minOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    minOn B f = minOn B g := by
  unfold minOn
  rw [Set.image_congr h]

lemma mid_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) : mid B f = mid B g := by
  unfold mid
  rw [maxOn_congr h, minOn_congr h]

/-- "Clearly `osc_B (c f) = |c| osc_B f` for real `c`." With the extrema defined as `sSup` and
`sInf`, this needs no hypothesis on `B` or on `f`. -/
theorem osc_const_mul (B : Set α) (f : α → ℝ) (c : ℝ) :
    osc B (fun y => c * f y) = |c| * osc B f := by
  unfold osc maxOn minOn
  simp only [sSup_image', sInf_image']
  rcases le_total 0 c with hc | hc
  · -- `c ≥ 0`: the maximum and the minimum are multiplied by `c`
    rw [← Real.mul_iSup_of_nonneg hc, ← Real.mul_iInf_of_nonneg hc, abs_of_nonneg hc]
    ring
  · -- `c ≤ 0`: the maximum of `c f` is `c` times the minimum of `f`, and conversely
    rw [← Real.mul_iInf_of_nonpos hc, ← Real.mul_iSup_of_nonpos hc, abs_of_nonpos hc]
    ring

/-- Adding a constant adds it to the maximum. -/
lemma maxOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : maxOn B (fun y => f y + c) = maxOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · exact maxOn_le hB fun y hy => by linarith [le_maxOn hf hy]
  · have : maxOn B f ≤ maxOn B (fun y => f y + c) - c :=
      maxOn_le hB fun y hy => by linarith [le_maxOn hfc hy]
    linarith

/-- Adding a constant adds it to the minimum. -/
lemma minOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : minOn B (fun y => f y + c) = minOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · have : minOn B (fun y => f y + c) - c ≤ minOn B f :=
      le_minOn hB fun y hy => by linarith [minOn_le hfc hy]
    linarith
  · exact le_minOn hB fun y hy => by linarith [minOn_le hf hy]

/-- Adding a constant `c` adds `c` to the midpoint. -/
lemma mid_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : mid B (fun y => f y + c) = mid B f + c := by
  unfold mid
  rw [maxOn_add_const hB hf, minOn_add_const hB hf]
  ring

/-- The triangle inequality for finite sums. -/
lemma osc_sum_le {ι : Type*} (s : Finset ι) {B : Set α} {f : ι → α → ℝ} (hB : B.Nonempty)
    (hf : ∀ k ∈ s, ((f k) '' B).Finite) :
    osc B (fun y => ∑ k ∈ s, f k y) ≤ ∑ k ∈ s, osc B (f k) :=
  osc_le hB fun y hy y' hy' => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k hk => sub_le_osc (hf k hk) hy hy'

/-- "By the triangle inequality for the oscillation,
`Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`": `b` times the oscillation of the average of
`b` functions is at most the sum of their oscillations. -/
lemma card_mul_osc_avg_le {ι : Type*} [Fintype ι] [Nonempty ι] {B : Set α} {f : ι → α → ℝ}
    (hB : B.Nonempty) (hf : ∀ k, ((f k) '' B).Finite) :
    (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι) ≤
      ∑ k, osc B (f k) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `Σ_k f_k` is `b` times the average, and `osc_B (b f) = b osc_B f`
  have hsum : (fun y => ∑ k, f k y) =
      fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι) := by
    funext y
    field_simp
  calc (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι)
      = osc B (fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι)) := by
        rw [osc_const_mul, abs_of_pos hc]
    _ = osc B (fun y => ∑ k, f k y) := by rw [← hsum]
    _ ≤ ∑ k, osc B (f k) := osc_sum_le Finset.univ hB fun k _ => hf k

/-! ### Blocks -/

/-- The block `B_{ℓ+1} = [s + ℓ L, s + (ℓ+1) L)` of the vertical interval
`J = [s, s + b L)`: closed at the bottom, open at the top. Blocks are numbered from `0` here
and from `1` in the manuscript. -/
def block (s L : ℝ) (ℓ : ℕ) : Set ℝ := Set.Ico (s + ℓ * L) (s + (ℓ + 1) * L)

lemma block_nonempty (s : ℝ) {L : ℝ} (hL : 0 < L) (ℓ : ℕ) : (block s L ℓ).Nonempty :=
  ⟨s + ℓ * L, ⟨le_rfl, by nlinarith⟩⟩

lemma block_subset (s : ℝ) {L : ℝ} (hL : 0 < L) {b ℓ : ℕ} (hℓ : ℓ < b) :
    block s L ℓ ⊆ Set.Ico s (s + b * L) := by
  rintro y ⟨h1, h2⟩
  have h0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hb : (ℓ : ℝ) + 1 ≤ b := by exact_mod_cast hℓ
  constructor
  · nlinarith
  · nlinarith

/-! ### Lemma 2.1 -/

/-- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`": the oscillation
on a nonempty subset `A` of `J` is at most the oscillation on `J`. -/
lemma osc_mono {A J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAJ : A ⊆ J)
    (hf : (f '' J).Finite) : osc A f ≤ osc J f := by
  -- the extrema of `f` on `A` lie between its extrema on `J`
  have h1 := maxOn_mono hA hAJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The inequality in the first display of the proof of Lemma 2.1, for two nonempty subsets
`A` (the bottom block `B_1`) and `C` (the top block `B_b`) of `J`: "Since `J` contains `B_1`
and `B_b`, \[…\] `osc_J f ≥ max_{B_b} f - min_{B_1} f`". With `A` and `C` exchanged, it is the
inequality "`osc_J f ≥ max_{B_1} f - min_{B_b} f`" of the second line. -/
lemma maxOn_sub_minOn_le_osc {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hC : C.Nonempty)
    (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) : maxOn C f - minOn A f ≤ osc J f := by
  -- the maximum on `C` is at most the maximum on `J`, and the minimum on `A` is at least the
  -- minimum on `J`
  have h1 := maxOn_mono hC hCJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The equality in the first display of the proof of Lemma 2.1, for two sets `A` (the bottom
block `B_1`) and `C` (the top block `B_b`): since "the extrema of `f` on a block `B` are
`mid_B f ± ½ osc_B f`",
"`max_{B_b} f - min_{B_1} f = (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`".
With `A` and `C` exchanged, it is the equality of the second line of that display: its
right-hand side `(osc_{B_b} f + osc_{B_1} f)/2 + (mid_{B_1} f - mid_{B_b} f)` is the
manuscript's `(osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`. -/
lemma maxOn_sub_minOn_eq (A C : Set α) (f : α → ℝ) :
    maxOn C f - minOn A f = (osc A f + osc C f) / 2 + (mid C f - mid A f) := by
  -- `max_C f = mid_C f + ½ osc_C f` and `min_A f = mid_A f - ½ osc_A f`
  rw [maxOn_eq_mid_add C f, minOn_eq_mid_sub A f]
  ring

/-- The first part of the proof of Lemma 2.1, for two nonempty subsets `A` (the bottom block
`B_1`) and `C` (the top block `B_b`) of `J`:
"`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`". -/
theorem half_osc_add_abs_mid_sub_le {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty)
    (hC : C.Nonempty) (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) :
    (osc A f + osc C f) / 2 + |mid C f - mid A f| ≤ osc J f := by
  -- the first line of the first display, `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`
  have h1 : (osc A f + osc C f) / 2 + (mid C f - mid A f) ≤ osc J f :=
    (maxOn_sub_minOn_eq A C f).symm.trans_le (maxOn_sub_minOn_le_osc hA hC hAJ hCJ hf)
  -- the second line, `osc_J f ≥ max_{B_1} f - min_{B_b} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`: the two blocks exchanged
  have h2 : (osc A f + osc C f) / 2 - (mid C f - mid A f) ≤ osc J f := by
    have h := (maxOn_sub_minOn_eq C A f).symm.trans_le
      (maxOn_sub_minOn_le_osc hC hA hCJ hAJ hf)
    linarith
  -- "Taking the larger of the two right-hand sides"
  rcases le_total 0 (mid C f - mid A f) with H | H
  · rw [abs_of_nonneg H]
    exact h1
  · rw [abs_of_nonpos H]
    linarith

/-- **Lemma 2.1** for arbitrary nonempty subsets `B_1, …, B_b` of a set `J` in place of the
blocks of an interval: if `f` has finitely many values on `J`, then

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof of the manuscript uses nothing else about the blocks. -/
theorem vertical_comparison_sets {b : ℕ} (hb : 2 ≤ b) (J : Set α) (B : Fin b → Set α)
    (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (f : α → ℝ) (hf : (f '' J).Finite) :
    ∑ ℓ : Fin b, osc (B ℓ) f +
        2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f := by
  classical
  -- the bottom block and the top block are different blocks
  have hfirst : (⟨0, by omega⟩ : Fin b) ≠ ⟨b - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  -- "`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`"
  have h2 := half_osc_add_abs_mid_sub_le (hne (⟨0, by omega⟩ : Fin b))
    (hne (⟨b - 1, by omega⟩ : Fin b)) (hsub _) (hsub _) hf
  -- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`."
  have h1 : ∀ ℓ, osc (B ℓ) f ≤ osc J f := fun ℓ => osc_mono (hne ℓ) (hsub ℓ) hf
  have hrest : ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩,
      osc (B ℓ) f ≤ ((b : ℝ) - 2) * osc J f := by
    calc ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc (B ℓ) f
        ≤ ∑ _ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc J f :=
          Finset.sum_le_sum fun ℓ _ => h1 ℓ
      _ = ((b : ℝ) - 2) * osc J f := by
          rw [Finset.sum_const, Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : ((b - 1 - 1 : ℕ) : ℝ) = (b : ℝ) - 2 := by
            rw [Nat.sub_sub, Nat.cast_sub hb]
            norm_num
          rw [this]
  -- "Adding these `b-2` inequalities and twice the last display proves (4)."
  have e1 := Finset.add_sum_erase Finset.univ (fun ℓ : Fin b => osc (B ℓ) f)
    (Finset.mem_univ (⟨0, by omega⟩ : Fin b))
  have e2 := Finset.add_sum_erase (Finset.univ.erase (⟨0, by omega⟩ : Fin b))
    (fun ℓ : Fin b => osc (B ℓ) f) (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩)
  linarith

/-- **Lemma 2.1 (vertical comparison)**, display (4). Partition `J = [s, s + b L)` into
blocks `B_1, …, B_b` of equal length `L`, from bottom to top, and let `f` be a function on
`J` with finitely many values. Then

`b · osc_J f ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

Only `b ≥ 2` is used (the manuscript has `b ≥ 3` throughout). -/
theorem vertical_comparison {b : ℕ} (hb : 2 ≤ b) (s : ℝ) {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (hf : (f '' Set.Ico s (s + b * L)).Finite) :
    ∑ ℓ : Fin b, osc (block s L ℓ) f +
        2 * |mid (block s L (b - 1)) f - mid (block s L 0) f| ≤
      b * osc (Set.Ico s (s + b * L)) f :=
  vertical_comparison_sets hb (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt) f hf

end

end R56Audit
end

section
namespace Oscillation
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The normalized average on a finite set. -/
def finAvg (f : α → ℝ) : ℝ := (∑ x, f x) / Fintype.card α

lemma finAvg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : finAvg f = finAvg g := by
  unfold finAvg
  congr 1
  exact Finset.sum_congr rfl (fun x _ ↦ h x)

@[simp] lemma finAvg_const [Nonempty α] (c : ℝ) : finAvg (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finAvg, hc]

lemma finAvg_add (f g : α → ℝ) : finAvg (fun x ↦ f x + g x) = finAvg f + finAvg g := by
  simp [finAvg, Finset.sum_add_distrib, add_div]

lemma finAvg_sub (f g : α → ℝ) : finAvg (fun x ↦ f x - g x) = finAvg f - finAvg g := by
  simp [finAvg, Finset.sum_sub_distrib, sub_div]

lemma finAvg_mul_const (f : α → ℝ) (c : ℝ) : finAvg (fun x ↦ f x * c) = finAvg f * c := by
  simp only [finAvg, ← Finset.sum_mul]
  ring

lemma finAvg_const_mul (c : ℝ) (f : α → ℝ) : finAvg (fun x ↦ c * f x) = c * finAvg f := by
  simp only [finAvg, ← Finset.mul_sum]
  ring

lemma finAvg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : finAvg f ≤ finAvg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma finAvg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ finAvg f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma finAvg_equiv (e : α ≃ β) (f : β → ℝ) : finAvg (fun x ↦ f (e x)) = finAvg f := by
  rw [finAvg, finAvg, Fintype.card_congr e, e.sum_comp]

lemma finAvg_prod (f : α × β → ℝ) :
    finAvg f = finAvg (fun x : α ↦ finAvg (fun y : β ↦ f (x,y))) := by
  simp only [finAvg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma integral_uniform_eq_finAvg [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) : (∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure) = finAvg f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finAvg]
  ring

lemma finAvg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    finAvg (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, finAvg (f i) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]

lemma finAvg_div_const (f : α → ℝ) (c : ℝ) :
    finAvg (fun x ↦ f x / c) = finAvg f / c := by
  simp only [finAvg, ← Finset.sum_div]
  ring

lemma finAvg_finAvg_comm (f : α → β → ℝ) :
    finAvg (fun x ↦ finAvg (f x)) = finAvg (fun y ↦ finAvg (fun x ↦ f x y)) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end
end Oscillation
end

section
/-!
# Exponential bounds for the Riesz-product remainder

The lemmas below use genuine measure-theoretic expectations.  In particular,
the conditional result assumes zero conditional means and bounded increments,
and derives the exponential estimate rather than assuming it.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace Riesz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → ℝ}

section Conditional

variable [StandardBorelSpace Ω] [IsProbabilityMeasure μ]

end Conditional

end Riesz
end

section
/-! Bounded differences for actual finite independent coordinates. -/
namespace Oscillation
noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped NNReal
set_option maxHeartbeats 800000

variable {α : Type*} [Fintype α] [Nonempty α]

end
end Oscillation
end

section
/-!
# Iterating the coefficient Laplace bound across shapes

For nonnegative factors bounded by one, a conditional expectation bound at each
layer implies a product expectation bound. The factors may share all previously
exposed randomness; they are not assumed independent across layers.
-/

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

end Riesz

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

end Riesz
end

section
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end
end Oscillation
end

section
/-! One-directional accumulation of the actual finite conditional drift. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

end
end Oscillation
end

section
/-! The genuine finite endpoint-counting model and its oscillation potential. -/

namespace Oscillation

noncomputable section
open Finset

end
end Oscillation
end

section
/-!
# Point sets and probability interfaces for the direct Riesz proof

The basic point-set definitions and measure-theoretic proofs are extracted from
`Tusnady/Random.lean` and `Tusnady/PaperBasics.lean` in the audited v8 project
`review/tusnady-v8-verify-20261002-r_n7w581/Tusnady`.
This module imports only Mathlib; no random-walk, spectral-gap, or discrepancy
lower-bound result from the old development is used.
-/

open MeasureTheory Function Finset

namespace Riesz.PointSets

noncomputable abbrev μI : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure μI := ⟨by simp [μI, Real.volume_Icc]⟩

lemma unitSq_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1) = μI.prod μI := by
  rw [Set.Icc_prod_eq, Measure.volume_eq_prod, μI, Measure.prod_restrict]
  simp

/-! ### From colorings of the plane and anchored rectangles to colorings of `X` -/

/-! ### Theorem 1.1 -/

/-! ### Random points -/


/-- The law of one uniform point of `[0,1]²` is a probability measure. -/
instance : IsProbabilityMeasure ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1)) := by
  rw [unitSq_eq]; infer_instance

end Riesz.PointSets
end

section
/-!
# Cell averages as conditional expectations

A countable measurable cell index determines a partition sigma-algebra.  On
each positive-measure fiber, conditional expectation is exactly the integral
over that fiber divided by its measure. Null fibers are removed only on an
explicit almost-everywhere set; no positivity assumption is made on all cells.
-/

open MeasureTheory
open scoped ENNReal

namespace Riesz

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {mι : MeasurableSpace ι}
  {μ : Measure Ω} {p : Ω → ι} {f : Ω → ℝ}

end Riesz

namespace Riesz

open PointSets

/-- Right-closed grid cells. The point zero lies in a separate null fiber
under the uniform measure on the unit interval. -/
noncomputable def gridIndex (n : ℕ) (x : ℝ) : ℤ := ⌈(n : ℝ) * x⌉ - 1

noncomputable abbrev gridSigma (n : ℕ) : MeasurableSpace ℝ :=
  (inferInstance : MeasurableSpace ℤ).comap (gridIndex n)

theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) := by
  exact ((measurable_const.mul measurable_id).ceil.sub_const 1)

end Riesz
end

section
/-!
# The one-dimensional profile used in the direct Riesz proof

`profile` is the primitive `w` from Section 2 of the manuscript.  It is extended by
zero outside the unit interval.  The lemmas in this file establish its actual
pointwise and integral properties; they are not hypotheses of a surrogate model.
-/

namespace Riesz

noncomputable section

end
end Riesz

namespace Riesz
noncomputable section
open Finset

end
end Riesz

namespace Riesz
noncomputable section

end
end Riesz
end

section
/-!
# Rare-set occupancy under genuine iid sampling

The probability measure is `Measure.pi (fun _ : Fin n => μ)`. No independence
or occupancy conclusion is postulated: product-event probabilities follow from
`Measure.pi_pi_finset`, and all exceptional-set choices are union bounded.
-/

namespace Riesz.Occupancy

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [MeasurableSpace α]

open PointSets

end Riesz.Occupancy
end

section
/-!
# Finite moment and Laplace bounds

The conditional distribution in the one-rectangle argument is finite: after the
old digits and vertical weights are fixed, the new horizontal digits range over
finitely many possibilities.  The theorems below apply to arbitrary finite
probability weights, not just the uniform distribution.
-/

namespace Riesz.Moments

open scoped BigOperators

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

variable {Ω : Type*} [Fintype Ω]

noncomputable def expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * X ω

@[simp] lemma expectation_const (μ : FiniteLaw Ω) (a : ℝ) :
    expectation μ (fun _ ↦ a) = a := by
  simp only [expectation, ← Finset.sum_mul, μ.total, one_mul]

end Riesz.Moments
end

section
/-!
# The finite law of one dyadically averaged profile

The support `Fin 4 × Fin m` is the first two horizontal bits followed by the
remaining bits (`m = 2^(L-2)`).  `profile_cell_average` identifies each value
below with the integral average of the actual continuous profile on its cell.
-/

namespace Riesz
noncomputable section
open Finset Moments

end
end Riesz
end

section
/-!
# Refinement of the actual uniform grids

The right-closed cell convention is preserved at every level, including at
cell boundaries. Thus refinement holds pointwise, before discarding null
endpoints in the conditional-average identities.
-/

open MeasureTheory

namespace Riesz

/-- The coarse index is integer division of the fine index. -/
theorem gridIndex_mul_ediv (n m : ℕ) (hm : 0 < m) (x : ℝ) :
    gridIndex (n * m) x / (m : ℤ) = gridIndex n x := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc := Int.ceil_eq_iff.mp (rfl : ⌈(n : ℝ) * x⌉ = ⌈(n : ℝ) * x⌉)
  apply le_antisymm
  · have hb : ⌈((n * m : ℕ) : ℝ) * x⌉ ≤ ⌈(n : ℝ) * x⌉ * (m : ℤ) := by
      apply Int.ceil_le.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hc.2 hmr.le]
    have hb' : gridIndex (n * m) x < (gridIndex n x + 1) * (m : ℤ) := by
      simpa only [gridIndex, sub_add_cancel] using
        (show ⌈((n * m : ℕ) : ℝ) * x⌉ - 1 < ⌈(n : ℝ) * x⌉ * (m : ℤ) by omega)
    have := (Int.ediv_lt_iff_lt_mul hmz).mpr hb'
    omega
  · apply (Int.le_ediv_iff_mul_le hmz).mpr
    have hb : (⌈(n : ℝ) * x⌉ - 1) * (m : ℤ) <
        ⌈((n * m : ℕ) : ℝ) * x⌉ := by
      apply Int.lt_ceil.mpr
      push_cast
      nlinarith [mul_lt_mul_of_pos_right hc.1 hmr]
    simp only [gridIndex]
    omega

/-- Every coarse-grid event is a fine-grid event. -/
theorem gridSigma_le_mul (n m : ℕ) (hm : 0 < m) :
    gridSigma n ≤ gridSigma (n * m) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (fun k : ℤ ↦ k / (m : ℤ))
    (measurable_of_countable _)
  funext x
  exact (gridIndex_mul_ediv n m hm x).symm

/-- Refinement for arbitrary divisible positive grid sizes. -/
theorem gridSigma_mono_of_dvd {n m : ℕ} (hm : 0 < m) (hnm : n ∣ m) :
    gridSigma n ≤ gridSigma m := by
  obtain ⟨k, rfl⟩ := hnm
  exact gridSigma_le_mul n k (Nat.pos_of_mul_pos_left hm)

/-- The sigma-algebras of dyadic grids form an increasing sequence. -/
theorem dyadic_gridSigma_mono : Monotone (fun r : ℕ ↦ gridSigma (2 ^ r)) := by
  intro r s hrs
  exact gridSigma_mono_of_dvd (pow_pos (by norm_num) _) (Nat.pow_dvd_pow 2 hrs)

/-- The filtration generated by right-closed dyadic cells on the real line. -/
noncomputable def dyadicFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq r := gridSigma (2 ^ r)
  mono' := dyadic_gridSigma_mono
  le' r := (measurable_gridIndex (2 ^ r)).comap_le

@[simp] theorem dyadicFiltration_apply (r : ℕ) :
    dyadicFiltration r = gridSigma (2 ^ r) := rfl

/-- Every `L`th dyadic level is again a filtration. -/
noncomputable def spacedDyadicFiltration (L : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq j := gridSigma (2 ^ (j * L))
  mono' := fun _ _ hij ↦ dyadic_gridSigma_mono (Nat.mul_le_mul_right L hij)
  le' j := (measurable_gridIndex (2 ^ (j * L))).comap_le

@[simp] theorem spacedDyadicFiltration_apply (L j : ℕ) :
    spacedDyadicFiltration L j = gridSigma (2 ^ (j * L)) := rfl

open PointSets

end Riesz
end

section
/-!
# The distribution of the actual finite grid index

These identities connect uniform real samples with the finite laws used by the
moment argument. The cell endpoints use the same right-closed convention as
`CellAverages`; the exceptional complement of `(0,1]` is handled by its null measure.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal


end
end Riesz
end

section
/-!
# Conditional fresh blocks for independent real samples

The coarse cells are the actual grid cells of all sample coordinates. The
product identities derive conditional independence from the product measure;
no independence between different shape levels is assumed.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal

/-- The information in the first `k` horizontal cells for every sample point. -/
def sampleGridIndex (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => gridIndex k (x i)

abbrev sampleGridSigma (n k : ℕ) : MeasurableSpace (Fin n → ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → ℤ)).comap (sampleGridIndex n k)

lemma measurable_sampleGridIndex (n k : ℕ) : Measurable (sampleGridIndex n k) := by
  exact measurable_pi_iff.mpr (fun i => (measurable_gridIndex k).comp (measurable_pi_apply i))


lemma sampleGridSigma_le_mul (n k m : ℕ) (hm : 0 < m) :
    sampleGridSigma n k ≤ sampleGridSigma n (k * m) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun b : Fin n → ℤ => fun i => b i / (m : ℤ)) (measurable_of_countable _)
  funext x i
  exact (gridIndex_mul_ediv k m hm (x i)).symm


end
end Riesz
end

section
/-!
# Taking the finite union over every coloring

This file connects the fixed-coloring probability estimate to the actual bad
event for arbitrary index colorings. It does not assume that the coloring was
chosen independently of the point set.
-/

namespace Riesz.PointSets
noncomputable section
open MeasureTheory Finset
open scoped ENNReal

end
end Riesz.PointSets
end

section
/-! The finite endpoint model is realized by genuine uniform real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
open scoped BigOperators

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset MeasureTheory

end
end Oscillation
end

section
/-! Actual truncated base-b stages on iid horizontal real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Riesz Riesz.PointSets

lemma sampleGridSigma_mono_pow (n b : ℕ) (hb : 0 < b) :
    Monotone (fun j ↦ sampleGridSigma n (b ^ j)) := by
  intro i j hij
  change sampleGridSigma n (b^i) ≤ sampleGridSigma n (b^j)
  have he : b ^ j = b ^ i * b ^ (j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [he]
  exact sampleGridSigma_le_mul n (b^i) (b^(j-i)) (pow_pos hb _)

def stageFiltration (n b h : ℕ) (hb : 0 < b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq j := sampleGridSigma n (b ^ min j h)
  mono' := fun _i _j hij ↦ sampleGridSigma_mono_pow n b hb (min_le_min_right h hij)
  le' j := (measurable_sampleGridIndex n (b ^ min j h)).comap_le

@[simp] lemma stageFiltration_apply (n b h : ℕ) (hb : 0 < b) (j : ℕ) :
    stageFiltration n b h hb j = sampleGridSigma n (b ^ min j h) := rfl

end
end Oscillation
end

section
namespace Riesz.Moments

open scoped BigOperators

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]


/-- The sample space of `n` genuinely independent draws, built as an iterated product. -/
def SampleSpace (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => SampleSpace Ω n × Ω

instance sampleSpaceFintype (Ω : Type*) [Fintype Ω] (n : ℕ) :
    Fintype (SampleSpace Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance

end Riesz.Moments
end

section
/-!
# From recursive independent samples to finite vectors

The weighted-moment proof uses an iterated binary product sample space. This
module identifies it with ordinary vectors and derives the normalized finite
sum needed by the conditional fresh-digit law. No moment or Laplace conclusion
is introduced as an assumption.
-/

namespace Riesz.Moments

open scoped BigOperators


/-- The recursive sample space is exactly the space of length-`n` vectors. -/
noncomputable def sampleSpaceEquiv (Ω : Type u) : (n : ℕ) → SampleSpace Ω n ≃ (Fin n → Ω)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    ((Equiv.prodCongr (sampleSpaceEquiv Ω n) (Equiv.refl Ω)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))

@[simp] lemma sampleSpaceEquiv_castSucc (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1))
    (i : Fin n) :
    sampleSpaceEquiv Ω (n + 1) ω i.castSucc = sampleSpaceEquiv Ω n ω.1 i := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

@[simp] lemma sampleSpaceEquiv_last (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1)) :
    sampleSpaceEquiv Ω (n + 1) ω (Fin.last n) = ω.2 := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 (Fin.last n) = _
  exact Fin.snoc_last _ _

variable {Ω : Type u} [Fintype Ω]

end Riesz.Moments
end

section
/-! A finite, shifted Khintchine bound derived from genuine product moments. -/
namespace Oscillation
noncomputable section
open scoped BigOperators
open Riesz.Moments
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open scoped BigOperators
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 300000

end
end Oscillation
end

section
/-! Average the child functions before comparing their maximum, as in r15. -/
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
/-! Summing the actual row gains gives the full oscillation drift. -/
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
/-! The actual horizontal sampling process and its compensated exponential bound. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets
open scoped ENNReal

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open MeasureTheory Riesz.PointSets

end
end Oscillation
end

section

end

section
/-!
# Fact 2.2 of the manuscript (sums of symmetric variables), for real random variables

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables. Suppose that
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` for every `i`, where `σ > 0`. Then
`E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

Symmetric variables are "variables that have the same distribution as their negatives": the
hypothesis on `X_i` is `IdentDistrib (X i) (fun ω => -X i ω) μ μ`. The proof is the one of
Appendix A.1: the shift does not hurt; two moments; from moments to the absolute value
(Hölder with exponents `3/2` and `3`).

`fact_2_2_general` is the statement for random variables on an arbitrary probability space.
(`fact_2_2_uniform` in `UniformDigits.lean` is the special case of functions of independent
uniform digits, which is the form in which Lemma 2.3 uses the fact.) This file uses Mathlib
only, not the archive.

The three steps of Appendix A.1, with `X = Σ_i X_i`:

* the shift does not hurt: `identDistrib_sum_neg` (`X` and `-X` have the same distribution),
  `integral_abs_add_eq_integral_abs_sub` (`E|θ + X| = E|θ - X|`) and
  `integral_abs_le_integral_abs_add_of_symm` (`E|θ + X| ≥ E|X|`);
* two moments: `integral_pow_eq_zero_of_symm` (`E X_i = 0`, and also `E X_i³ = 0`),
  `sum_moments` (`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`) and `sum_fourth_moment_le`
  (`E X⁴ ≤ 3m²σ⁴`). The proof of `sum_moments` is by induction on the number of variables
  (one variable is added at a time, with `moments_add_of_indepFun`), not by expanding `X⁴`
  and counting the surviving terms as the manuscript does. The manuscript's term
  `6 Σ_{i<j} E X_i² E X_j²` appears in the evaluated form `3m(m-1)σ⁴`, which is the same
  number because every `E X_i² = σ²` and there are `m(m-1)/2` pairs `i < j`;
* from moments to the absolute value: `integral_sq_le_rpow_mul_rpow` (Hölder's inequality,
  `E X² ≤ (E|X|)^{2/3} (E X⁴)^{1/3}`), `integral_sq_pow_three_le` (its cube,
  `(E X²)³ ≤ (E|X|)² E X⁴`) and `mul_sqrt_le_of_moments` (the arithmetic).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory

noncomputable section

section General

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The shift does not hurt -/

/-- Independent symmetric variables are jointly symmetric: the families `(X_i)` and `(-X_i)`
have the same joint law, namely the product of the common marginal laws. -/
lemma identDistrib_neg_of_iIndepFun {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => -X i ω) μ μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  have hnX : ∀ i, AEMeasurable (fun ω => -X i ω) μ := fun i => (hsymm i).aemeasurable_snd
  have hneg : iIndepFun (fun i ω => -X i ω) μ :=
    hindep.comp (fun _ x => -x) fun _ => measurable_neg
  refine ⟨aemeasurable_pi_iff.mpr hX, aemeasurable_pi_iff.mpr hnX, ?_⟩
  rw [hindep.map_fun_eq_pi_map hX, hneg.map_fun_eq_pi_map hnX]
  congr 1
  funext i
  exact (hsymm i).map_eq

/-- A finite sum `X` of independent symmetric variables is symmetric: `X` and `-X` have the
same distribution. -/
lemma identDistrib_sum_neg {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω => ∑ i, X i ω) (fun ω => -∑ i, X i ω) μ μ := by
  have hsum : Measurable fun v : ι → ℝ => ∑ i, v i :=
    Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i
  have h := (identDistrib_neg_of_iIndepFun X hindep hsymm).comp hsum
  simpa only [Function.comp_def, Finset.sum_neg_distrib] using h

/-- **The shift does not hurt**, the equality (Appendix A.1): "So `X` and `-X` have the same
distribution, and `E|θ + X| = E|θ - X|`." The lemma is the second half of this sentence, for
a real random variable `X` that has the same distribution as `-X`. (The first half, for
`X = Σ_i X_i`, is `identDistrib_sum_neg`.) No integrability hypothesis is needed, because
identically distributed functions have the same integral (`IdentDistrib.integral_eq`). -/
lemma integral_abs_add_eq_integral_abs_sub {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (θ : ℝ) :
    ∫ ω, |θ + X ω| ∂μ = ∫ ω, |θ - X ω| ∂μ := by
  -- apply the measurable function `x ↦ |θ + x|` to `X` and to `-X`
  have hg : Measurable fun x : ℝ => |θ + x| :=
    (continuous_const.add continuous_id).abs.measurable
  have h := (hsymm.comp hg).integral_eq
  simpa only [Function.comp_def, sub_eq_add_neg] using h

/-- **The shift does not hurt** (Appendix A.1): `E|θ + X| ≥ E|X|` for a symmetric integrable
variable `X`. "Averaging the two and using `|θ + x| + |θ - x| ≥ 2|x|` gives
`E|θ + X| ≥ E|X|`." The two are `E|θ + X|` and `E|θ - X|`, which are equal by
`integral_abs_add_eq_integral_abs_sub`. -/
lemma integral_abs_le_integral_abs_add_of_symm [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (hX : Integrable X μ) (θ : ℝ) :
    ∫ ω, |X ω| ∂μ ≤ ∫ ω, |θ + X ω| ∂μ := by
  have hp : Integrable (fun ω => |θ + X ω|) μ := ((integrable_const θ).add hX).abs
  have hm : Integrable (fun ω => |θ - X ω|) μ := ((integrable_const θ).sub hX).abs
  -- `|θ + x| + |θ - x| ≥ 2|x|`, by the triangle inequality
  have hpoint : ∀ ω, |X ω| ≤ (|θ + X ω| + |θ - X ω|) / 2 := by
    intro ω
    have h := abs_sub (θ + X ω) (θ - X ω)
    have e : θ + X ω - (θ - X ω) = 2 * X ω := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  -- average `E|θ + X|` and `E|θ - X|`, which are equal
  calc ∫ ω, |X ω| ∂μ ≤ ∫ ω, (|θ + X ω| + |θ - X ω|) / 2 ∂μ :=
        integral_mono hX.abs ((hp.add hm).div_const 2) hpoint
    _ = (∫ ω, |θ + X ω| ∂μ + ∫ ω, |θ - X ω| ∂μ) / 2 := by
        rw [integral_div, integral_add hp hm]
    _ = ∫ ω, |θ + X ω| ∂μ := by
        rw [← integral_abs_add_eq_integral_abs_sub hsymm θ]
        ring

/-! ### Two moments -/

/-- A symmetric real random variable has vanishing odd moments: `E Y^k = 0` for odd `k`.

The case `k = 1` is the mean, because `Y ω ^ 1` is `Y ω` (`pow_one`). So this lemma covers
the manuscript's "Every `X_i` is symmetric and has a finite second moment, so `E X_i = 0`",
and there is no separate lemma for the mean; `sum_moments` uses the cases `k = 1` and
`k = 3`. No moment hypothesis is needed: if `Y ^ k` is not integrable, then its integral is
`0` by Mathlib's convention. -/
lemma integral_pow_eq_zero_of_symm {Y : Ω → ℝ} (h : IdentDistrib Y (fun ω => -Y ω) μ μ) {k : ℕ}
    (hk : Odd k) : ∫ ω, Y ω ^ k ∂μ = 0 := by
  have h1 := (h.comp (measurable_id.pow_const k)).integral_eq
  simp only [Function.comp_apply, id_eq, hk.neg_pow, integral_neg] at h1
  linarith

/-- On a finite measure space, a real function with an integrable fourth power has integrable
lower powers. -/
lemma integrable_pow_of_integrable_pow_four [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (h4 : Integrable (fun ω => Y ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Y ω ^ k) μ := by
  have h4' : Integrable (fun ω => ‖Y ω‖ ^ 4) μ := by
    simpa only [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using h4
  have hk' := integrable_norm_pow_of_le hY.aestronglyMeasurable hk h4'
  refine (integrable_norm_iff (hY.pow_const k).aestronglyMeasurable).mp ?_
  simpa only [norm_pow] using hk'

/-- **Two moments, one step.** Let `Y` and `T` be independent with finite fourth moments, and
let `E Y = E Y³ = 0`. Then `(Y + T)⁴` is integrable, `E (Y + T)² = E Y² + E T²` and
`E (Y + T)⁴ = E Y⁴ + 6 E Y² E T² + E T⁴`. -/
lemma moments_add_of_indepFun [IsFiniteMeasure μ] {Y T : Ω → ℝ} (hYT : IndepFun Y T μ)
    (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ)
    (hY4 : Integrable (fun ω => Y ω ^ 4) μ) (hT4 : Integrable (fun ω => T ω ^ 4) μ)
    (hY1 : ∫ ω, Y ω ∂μ = 0) (hY3 : ∫ ω, Y ω ^ 3 ∂μ = 0) :
    Integrable (fun ω => (Y ω + T ω) ^ 4) μ ∧
      ∫ ω, (Y ω + T ω) ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, T ω ^ 2 ∂μ ∧
      ∫ ω, (Y ω + T ω) ^ 4 ∂μ =
        ∫ ω, Y ω ^ 4 ∂μ + 6 * ((∫ ω, Y ω ^ 2 ∂μ) * ∫ ω, T ω ^ 2 ∂μ) + ∫ ω, T ω ^ 4 ∂μ := by
  -- the mixed moments `E(Y^a T^b)` are finite and factor
  have hint : ∀ a b : ℕ, a ≤ 4 → b ≤ 4 → Integrable (fun ω => Y ω ^ a * T ω ^ b) μ :=
    fun a b ha hb =>
      (hYT.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integrable_mul
        (integrable_pow_of_integrable_pow_four hY hY4 ha)
        (integrable_pow_of_integrable_pow_four hT hT4 hb)
  have hfac : ∀ a b : ℕ, ∫ ω, Y ω ^ a * T ω ^ b ∂μ = (∫ ω, Y ω ^ a ∂μ) * ∫ ω, T ω ^ b ∂μ :=
    fun a b => hYT.integral_fun_comp_mul_comp hY hT
      (measurable_id.pow_const a).aestronglyMeasurable
      (measurable_id.pow_const b).aestronglyMeasurable
  have hY1' : ∫ ω, Y ω ^ 1 ∂μ = 0 := by simpa only [pow_one] using hY1
  have hY2 := integrable_pow_of_integrable_pow_four hY hY4 (k := 2) (by norm_num)
  have hT2 := integrable_pow_of_integrable_pow_four hT hT4 (k := 2) (by norm_num)
  have i11 := (hint 1 1 (by norm_num) (by norm_num)).const_mul 2
  have i31 := (hint 3 1 (by norm_num) (by norm_num)).const_mul 4
  have i22 := (hint 2 2 (by norm_num) (by norm_num)).const_mul 6
  have i13 := (hint 1 3 (by norm_num) (by norm_num)).const_mul 4
  -- the binomial expansions, with every mixed term in the form `Y ^ a * T ^ b`
  have e2 : (fun ω => (Y ω + T ω) ^ 2) =
      fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1) + T ω ^ 2 := by
    funext ω
    ring
  have e4 : (fun ω => (Y ω + T ω) ^ 4) = fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3) + T ω ^ 4 := by
    funext ω
    ring
  have s1 : Integrable (fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1)) μ := hY2.add i11
  have t1 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1)) μ := hY4.add i31
  have t2 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2)) μ := t1.add i22
  have t3 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3)) μ := t2.add i13
  refine ⟨?_, ?_, ?_⟩
  · rw [e4]
    exact t3.add hT4
  · rw [e2, integral_add s1 hT2, integral_add hY2 i11, integral_const_mul, hfac, hY1']
    ring
  · rw [e4, integral_add t3 hT4, integral_add t2 i13, integral_add t1 i22, integral_add hY4 i31,
      integral_const_mul, integral_const_mul, integral_const_mul, hfac 3 1, hfac 2 2, hfac 1 3,
      hY1', hY3]
    ring

/-- **Two moments** (Appendix A.1). For independent symmetric variables with `E X_i² = σ²` and
finite fourth moments, the sum `X` over a set of `m` indices has a finite fourth moment,
`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`.

The proof is by induction on the number of variables (one variable is added at a time, with
`moments_add_of_indepFun`), not by expanding `X⁴` and counting the surviving terms as the
manuscript does. The manuscript's term `6 Σ_{i<j} E X_i² E X_j²` appears here in the
evaluated form `3m(m-1)σ⁴`, which is the same number because every `E X_i² = σ²` and there
are `m(m-1)/2` pairs `i < j`. -/
lemma sum_moments [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (s : Finset ι) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) μ ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = s.card * σ ^ 2 ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ =
        ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ + 3 * s.card * (s.card - 1) * σ ^ 4 := by
  classical
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨ihi, ih2, ih4⟩ := ih
    have hT : AEMeasurable (fun ω => ∑ j ∈ s, X j ω) μ :=
      Finset.aemeasurable_fun_sum s fun j _ => hX j
    -- the new variable is independent of the partial sum
    have hYT : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hindep.indepFun_finsetSum_of_notMem₀ hX hi).symm
      have e : (∑ j ∈ s, X j) = fun ω => ∑ j ∈ s, X j ω := by
        funext ω
        simp
      rwa [e] at h
    -- its odd moments vanish by symmetry
    obtain ⟨hi4, hm2, hm4⟩ := moments_add_of_indepFun hYT (hX i) hT (h4i i) ihi
      (by simpa using integral_pow_eq_zero_of_symm (hsymm i) (k := 1) (by decide))
      (integral_pow_eq_zero_of_symm (hsymm i) (by decide))
    simp only [Finset.sum_insert hi]
    refine ⟨hi4, ?_, ?_⟩
    · rw [hm2, h2 i, ih2, Finset.card_insert_of_notMem hi]
      push_cast
      ring
    · rw [hm4, h2 i, ih2, ih4, Finset.card_insert_of_notMem hi]
      push_cast
      ring

/-- **Two moments** (Appendix A.1), the bound on the fourth moment: if moreover
`E X_i⁴ ≤ 3σ⁴`, then `E X⁴ ≤ 3mσ⁴ + 3m(m-1)σ⁴ = 3m²σ⁴`. -/
lemma sum_fourth_moment_le [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ ≤ 3 * (s.card * σ ^ 2) ^ 2 := by
  have hsum : ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ ≤ s.card * (3 * σ ^ 4) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul s _ _ fun i _ => h4 i
  rw [(sum_moments X hindep hsymm h2 h4i s).2.2]
  linarith

/-! ### From moments to the absolute value -/

/-- **Hölder's inequality with exponents `3/2` and `3`** (Appendix A.1), applied to the factors
`|Y|^{2/3}` and `|Y|^{4/3}`: `E Y² ≤ (E|Y|)^{2/3} (E Y⁴)^{1/3}`. -/
lemma integral_sq_le_rpow_mul_rpow [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    ∫ ω, Y ω ^ 2 ∂μ ≤ (∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ) := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by norm_num [Real.holderConjugate_iff]
  have habs : AEMeasurable (fun ω => |Y ω|) μ := continuous_abs.measurable.comp_aemeasurable hY
  have h1 : Integrable (fun ω => |Y ω|) μ := by
    simpa only [pow_one] using
      (integrable_pow_of_integrable_pow_four hY h4 (k := 1) (by norm_num)).abs
  -- the two factors are nonnegative, their product is `Y²`
  have hf0 : ∀ ω, 0 ≤ |Y ω| ^ (2 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hg0 : ∀ ω, 0 ≤ |Y ω| ^ (4 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hfg : ∀ ω, |Y ω| ^ (2 / 3 : ℝ) * |Y ω| ^ (4 / 3 : ℝ) = Y ω ^ 2 := fun ω => by
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by norm_num), ← sq_abs,
      ← Real.rpow_natCast]
    norm_num
  -- the first factor to the power `3/2` is `|Y|`, the second to the power `3` is `Y⁴`
  have hfp : ∀ ω, (|Y ω| ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = |Y ω| := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hgq : ∀ ω, (|Y ω| ^ (4 / 3 : ℝ)) ^ (3 : ℝ) = Y ω ^ 4 := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _), ← (by decide : Even 4).pow_abs, ← Real.rpow_natCast]
    norm_num
  have hfm : MemLp (fun ω => |Y ω| ^ (2 / 3 : ℝ)) (ENNReal.ofReal (3 / 2)) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hf0 _), hfp] using h1
  have hgm : MemLp (fun ω => |Y ω| ^ (4 / 3 : ℝ)) (ENNReal.ofReal 3) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hg0 _), hgq] using h4
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) hfm hgm
  simp only [hfg, hfp, hgq] at h
  rwa [show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] at h

/-- **From moments to the absolute value** (Appendix A.1): the cube of Hölder's inequality,
`(E Y²)³ ≤ (E|Y|)² E Y⁴`, in other words `E|Y| ≥ (E Y²)^{3/2} / (E Y⁴)^{1/2}`. -/
lemma integral_sq_pow_three_le [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    (∫ ω, Y ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
  have hA : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have hQ : 0 ≤ ∫ ω, Y ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have hV : 0 ≤ ∫ ω, Y ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  calc (∫ ω, Y ω ^ 2 ∂μ) ^ 3
      ≤ ((∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hV (integral_sq_le_rpow_mul_rpow hY h4) 3
    _ = (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
        rw [mul_pow, ← Real.rpow_natCast (_ ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hA,
          ← Real.rpow_natCast (_ ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hQ]
        norm_num

end General

/-- The arithmetic at the end of Appendix A.1, with `A = E|X|` and `Q = E X⁴`: if
`(mσ²)³ ≤ A² Q` and `Q ≤ 3(mσ²)²`, then `A ≥ σ √(m/3)`. -/
lemma mul_sqrt_le_of_moments {m σ A Q : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ) (hA : 0 ≤ A)
    (h2 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * Q) (h4 : Q ≤ 3 * (m * σ ^ 2) ^ 2) :
    σ * Real.sqrt (m / 3) ≤ A := by
  have hkey : σ ^ 2 * (m / 3) ≤ A ^ 2 := by
    -- the claim is trivial for `m = 0`; for `m > 0` divide by `3m²σ⁴ > 0`
    rcases hm.eq_or_lt with rfl | hpos
    · rw [zero_div, mul_zero]
      exact sq_nonneg A
    · have hc : 0 < 3 * (m ^ 2 * σ ^ 4) := by positivity
      have h1 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * (3 * (m * σ ^ 2) ^ 2) :=
        h2.trans (mul_le_mul_of_nonneg_left h4 (sq_nonneg A))
      refine le_of_mul_le_mul_left ?_ hc
      linarith
  calc σ * Real.sqrt (m / 3) = Real.sqrt (σ ^ 2 * (m / 3)) := by
        rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
    _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hkey
    _ = A := Real.sqrt_sq hA

/-! ### Fact 2.2 -/

/-- **Fact 2.2 (sums of symmetric variables).** Let `X_i`, `i ∈ ι` (a finite index set with
`m` elements), be independent symmetric real random variables on a probability space, with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` (in particular the fourth moments are finite), where
`σ > 0`. Then `E|θ + Σ_i X_i| ≥ σ √(m/3)` for every real `θ`. -/
theorem fact_2_2_general {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ)
    (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2)
    (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4)
    (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ := by
  have hS : AEMeasurable (fun ω => ∑ i, X i ω) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hsymm i).aemeasurable_fst
  -- two moments: `X = Σ_i X_i` has `E X² = mσ²` and `E X⁴ ≤ 3m²σ⁴`; in particular `E|X| < ∞`
  obtain ⟨hS4, hm2, -⟩ := sum_moments X hindep hsymm h2 h4i Finset.univ
  have hm4 := sum_fourth_moment_le X hindep hsymm h2 h4i h4 Finset.univ
  rw [Finset.card_univ] at hm2 hm4
  have hS1 : Integrable (fun ω => ∑ i, X i ω) μ := by
    simpa only [pow_one] using
      integrable_pow_of_integrable_pow_four hS hS4 (k := 1) (by norm_num)
  -- the shift does not hurt: `E|θ + X| ≥ E|X|`
  have hshift : ∫ ω, |∑ i, X i ω| ∂μ ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ :=
    integral_abs_le_integral_abs_add_of_symm (identDistrib_sum_neg X hindep hsymm) hS1 θ
  -- from moments to the absolute value: `(E X²)³ ≤ (E|X|)² E X⁴`, so `E|X| ≥ σ √(m/3)`
  have hH := integral_sq_pow_three_le hS hS4
  rw [hm2] at hH
  exact (mul_sqrt_le_of_moments (Nat.cast_nonneg _) hσ (integral_nonneg fun ω => abs_nonneg _)
    hH hm4).trans hshift

end

end R56Audit
end

section
/-!
# Fact 2.2 for functions of independent uniform digits

Auditor's supplement (not part of the audited archive).

In the local experiment of Section 2.3 the randomness consists of independent uniform digits.
`fact_2_2_uniform` is Fact 2.2 (`fact_2_2_general`) in this setting: the probability space is
`ι → D` with the law `digitLaw ι D` of independent uniform digits, where `D` carries the
discrete σ-algebra. Its expectation is the finite average `Oscillation.finAvg`
(`integral_digitLaw`), the digits are independent (`ProbabilityTheory.iIndepFun_pi`), and a
function of one digit that is negated by a permutation of the digits is symmetric
(`identDistrib_coord_neg`).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Oscillation

noncomputable section

/-! ### Independent uniform digits -/

section Uniform

variable {ι D : Type*} [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D]

/-- The law of independent uniform digits: the product over `ι` of the uniform law on `D`. -/
abbrev digitLaw (ι D : Type*) [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D] :
    Measure (ι → D) :=
  Measure.pi fun _ : ι => (PMF.uniformOfFintype D).toMeasure

/-- The law of a function of one of the independent uniform digits. -/
lemma map_digitLaw_coord {β : Type*} [MeasurableSpace β] (i : ι) {g : D → β}
    (hg : Measurable g) :
    Measure.map (fun r : ι → D => g (r i)) (digitLaw ι D) =
      Measure.map g (PMF.uniformOfFintype D).toMeasure := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := Measure.map_map (μ := digitLaw ι D) hg h.measurable
  rw [h.map_eq] at h1
  exact h1.symm

variable [MeasurableSingletonClass D]

/-- The uniform law on a finite set is invariant under permutations. -/
lemma map_equiv_uniform (e : D ≃ D) :
    (PMF.uniformOfFintype D).toMeasure.map e = (PMF.uniformOfFintype D).toMeasure := by
  refine Measure.ext_of_singleton fun a => ?_
  have hpre : e ⁻¹' {a} = {e.symm a} := by
    ext d
    simp [Equiv.eq_symm_apply]
  rw [Measure.map_apply .of_discrete (measurableSet_singleton a), hpre,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- Independent uniform digits are jointly uniform: the product of the uniform laws on `D` is
the uniform law on `ι → D`. -/
lemma digitLaw_eq_uniform [DecidableEq ι] :
    digitLaw ι D = (PMF.uniformOfFintype (ι → D)).toMeasure := by
  refine Measure.ext_of_singleton fun r => ?_
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton r),
    PMF.uniformOfFintype_apply]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]

/-- For independent uniform digits the expectation is the finite average. -/
lemma integral_digitLaw [DecidableEq ι] (f : (ι → D) → ℝ) :
    ∫ r, f r ∂digitLaw ι D = finAvg f := by
  rw [digitLaw_eq_uniform, integral_uniform_eq_finAvg]

/-- The expectation of a function of one of the independent uniform digits. -/
lemma integral_digitLaw_coord (i : ι) (g : D → ℝ) :
    ∫ r, g (r i) ∂digitLaw ι D = finAvg g := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := integral_map h.aemeasurable (f := g) (Measurable.of_discrete.aestronglyMeasurable)
  rw [h.map_eq, integral_uniform_eq_finAvg] at h1
  exact h1.symm

/-- A function of one of the independent uniform digits that is negated by a permutation of
the digits is symmetric. -/
lemma identDistrib_coord_neg (i : ι) (g : D → ℝ) (φ : D ≃ D) (hφ : ∀ d, g (φ d) = -g d) :
    IdentDistrib (fun r : ι → D => g (r i)) (fun r => -g (r i)) (digitLaw ι D)
      (digitLaw ι D) := by
  have hg : Measurable g := .of_discrete
  have hng : Measurable fun d => -g d := .of_discrete
  have e : (fun d => -g d) = g ∘ φ := by
    funext d
    exact (hφ d).symm
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable,
    (hng.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  rw [map_digitLaw_coord i hg, map_digitLaw_coord i hng, e,
    ← Measure.map_map hg .of_discrete, map_equiv_uniform]

end Uniform

/-- **Fact 2.2 for functions of independent uniform digits.** The probability space is the
finite product `ι → D` with the uniform law (`Oscillation.finAvg` is the expectation),
`X_i = x_i(r_i)` is a function of the `i`-th digit, and the symmetry of `X_i` is witnessed
by a permutation `φ_i` of the digits with `x_i ∘ φ_i = -x_i`. This is an instance of
`fact_2_2_general`. -/
theorem fact_2_2_uniform {ι D : Type*} [Fintype ι] [DecidableEq ι] [Fintype D] [Nonempty D]
    (x : ι → D → ℝ) (φ : ι → D ≃ D) (hφ : ∀ i d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4) (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ finAvg (fun r : ι → D => |θ + ∑ i, x i (r i)|) := by
  -- the digits carry the discrete σ-algebra, and `ι → D` the law of independent uniform digits
  let _ : MeasurableSpace D := ⊤
  have h := fact_2_2_general (μ := digitLaw ι D) (fun i r => x i (r i))
    (iIndepFun_pi (X := x) fun _ => Measurable.of_discrete.aemeasurable)
    (fun i => identDistrib_coord_neg i (x i) (φ i) (hφ i)) hσ
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 2).trans (h2 i))
    (fun _ => Integrable.of_finite)
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 4).trans_le (h4 i)) θ
  rwa [integral_digitLaw] at h

end

end R56Audit
end

section
/-!
# Fact 2.2 of the manuscript, in the form used by Lemma 2.3

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`. Then `E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

The fact itself, for real random variables on any probability space, is `fact_2_2_general`
in `SymmetricSumsGeneral.lean`. This file states it in the setting of Lemma 2.3: the
probability space is a finite product `Fin n → D` with the uniform law (`D` is the set of
digits, and `Oscillation.finAvg` is the expectation), `X_i = x_i(r_i)` is a function of the
`i`-th digit, and "symmetric" is witnessed by a permutation `φ_i` of the digits with
`x_i ∘ φ_i = -x_i` (`exists_symm_perm_iff`: this is exactly symmetry of the distribution).

* `symmetric_sum_abs`: the sum runs over the points of a set `S`, and the shift `θ` may
  depend on the digits of the other points: the conditioning step of the proof of Lemma 2.3
  ("condition on the children of all other points"). Proved from `fact_2_2_uniform`, the
  instance of `fact_2_2_general` for independent uniform digits, applied for every value of
  the other digits.
* `fact_2_2`: the case of a constant shift.
* `finAvg_mul_coord`, `finAvg_coord`, `finAvg_eq_zero_of_symm`: a digit is uniform and
  independent of the other digits; a symmetric function of a digit has mean zero (used for
  display (7)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ} {D : Type*} [Fintype D]

/-! ### The uniform law on a finite product: one coordinate is independent of the others -/

/-- `(r, d) ↦ (r with r_i := d, r_i)` is an involution of `(Fin n → D) × D`. -/
def updateEquiv (i : Fin n) : ((Fin n → D) × D) ≃ ((Fin n → D) × D) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    rcases p with ⟨r, d⟩
    simp
  right_inv p := by
    rcases p with ⟨r, d⟩
    simp

/-- Resampling one coordinate does not change an average. -/
lemma finAvg_update [Nonempty D] (i : Fin n) (F : (Fin n → D) → ℝ) :
    finAvg (fun r => finAvg (fun d => F (Function.update r i d))) = finAvg F := by
  have h1 := finAvg_prod (fun p : (Fin n → D) × D => F (Function.update p.1 i p.2))
  have h2 := finAvg_equiv (updateEquiv i) (fun p : (Fin n → D) × D => F p.1)
  have h3 := finAvg_prod (fun p : (Fin n → D) × D => F p.1)
  have h4 : finAvg (fun r : Fin n → D => finAvg (fun _ : D => F r)) = finAvg F :=
    finAvg_congr fun r => finAvg_const _
  rw [← h1]
  exact h2.trans (h3.trans h4)

/-- A function of the `i`-th digit is independent of a function that does not depend on
it. -/
lemma finAvg_mul_coord [Nonempty D] (i : Fin n) (g : D → ℝ) (Y : (Fin n → D) → ℝ)
    (hY : ∀ r d, Y (Function.update r i d) = Y r) :
    finAvg (fun r => g (r i) * Y r) = finAvg g * finAvg Y := by
  rw [← finAvg_update i]
  simp only [Function.update_self, hY]
  simp_rw [finAvg_mul_const]
  rw [finAvg_const_mul]

/-- The `i`-th digit is uniform. -/
lemma finAvg_coord [Nonempty D] (i : Fin n) (g : D → ℝ) :
    finAvg (fun r : Fin n → D => g (r i)) = finAvg g := by
  have h := finAvg_mul_coord i g (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa using h

lemma finAvg_neg' {α : Type*} [Fintype α] (f : α → ℝ) :
    finAvg (fun x => -f x) = -finAvg f := by
  have := finAvg_const_mul (-1) f
  simpa using this

/-- A symmetric function of a uniform digit has mean zero. -/
lemma finAvg_eq_zero_of_symm (φ : D ≃ D) (g : D → ℝ) (h : ∀ d, g (φ d) = -g d) :
    finAvg g = 0 := by
  have h1 := finAvg_equiv φ g
  simp only [h] at h1
  rw [finAvg_neg'] at h1
  linarith

/-! ### Sums of independent symmetric jumps -/

/-- `Σ_{i ∈ S} x_i(r_i)`: the sum of the jumps of the points in `S`. -/
def jumpSum (S : Finset (Fin n)) (x : Fin n → D → ℝ) (r : Fin n → D) : ℝ :=
  ∑ i ∈ S, x i (r i)

/-- The digits of the points of `S` and the digits of the other points. -/
def splitDigits (S : Finset (Fin n)) (D : Type*) :
    (Fin n → D) ≃ ({i // i ∈ S} → D) × ({i // i ∉ S} → D) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ S) (fun _ => D)

omit [Fintype D] in
lemma splitDigits_symm_mem (S : Finset (Fin n)) (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D))
    (i : {i // i ∈ S}) : (splitDigits S D).symm p i = p.1 i := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, i.2]

omit [Fintype D] in
lemma splitDigits_symm_notMem (S : Finset (Fin n))
    (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D)) {i : Fin n} (hi : i ∉ S) :
    (splitDigits S D).symm p i = p.2 ⟨i, hi⟩ := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, hi]

/-- **Fact 2.2 (sums of symmetric variables)**, in the form in which Lemma 2.3 uses it: the
jumps `X_i = x_i(r_i)`, `i ∈ S`, are functions of independent uniform digits, and the shift
`θ` may depend on the digits of the other points. If the jumps are symmetric with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`, then `E|θ + Σ_{i ∈ S} X_i| ≥ σ √(m/3)`, where `m = |S|`.

"Now condition on the children of all other points \[…\]. This fixes \[…\] the number `θ`.
The children of the `m_R` points of `R^in` are independent of the conditioning, so the jumps
in `D` are still independent and symmetric. \[…\] So Fact 2.2 applies to `θ + D`, with
`m = m_R`." The proof does exactly this: for every value of the other digits, it applies
`fact_2_2_uniform`, the instance of Fact 2.2 (`fact_2_2_general`) for independent uniform
digits. -/
theorem symmetric_sum_abs [Nonempty D] (S : Finset (Fin n)) (x : Fin n → D → ℝ)
    (φ : Fin n → D ≃ D) (hφ : ∀ i ∈ S, ∀ d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∀ i ∈ S, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i ∈ S, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4)
    (θ : (Fin n → D) → ℝ)
    (hθ : ∀ r r' : Fin n → D, (∀ i, i ∉ S → r i = r' i) → θ r = θ r') :
    σ * Real.sqrt (S.card / 3) ≤ finAvg (fun r : Fin n → D => |θ r + jumpSum S x r|) := by
  classical
  rcases hσ.eq_or_lt with rfl | hσpos
  · rw [zero_mul]
    exact finAvg_nonneg fun _ => abs_nonneg _
  -- condition on the digits of the points outside `S`
  rw [← finAvg_equiv (splitDigits S D).symm, finAvg_prod, finAvg_finAvg_comm]
  have hne : Nonempty ({i // i ∉ S} → D) := ⟨fun _ => Classical.arbitrary D⟩
  refine le_trans (le_of_eq (finAvg_const (α := {i // i ∉ S} → D) _).symm) (finAvg_mono fun rO => ?_)
  -- the shift is now a number
  have hconst : ∀ rS : {i // i ∈ S} → D,
      θ ((splitDigits S D).symm (rS, rO)) =
        θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)) := fun rS =>
    hθ _ _ fun i hi => by rw [splitDigits_symm_notMem S _ hi, splitDigits_symm_notMem S _ hi]
  have hsum : ∀ rS : {i // i ∈ S} → D,
      jumpSum S x ((splitDigits S D).symm (rS, rO)) = ∑ i : {i // i ∈ S}, x i (rS i) := by
    intro rS
    unfold jumpSum
    rw [← Finset.sum_coe_sort S (fun i => x i ((splitDigits S D).symm (rS, rO) i))]
    exact Finset.sum_congr rfl fun i _ => by rw [splitDigits_symm_mem]
  -- Fact 2.2 for the digits of the points of `S`
  have hF := fact_2_2_uniform (fun i : {i // i ∈ S} => x i) (fun i : {i // i ∈ S} => φ i)
    (fun i d => hφ i i.2 d) hσpos (fun i => h2 i i.2) (fun i => h4 i i.2)
    (θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)))
  rw [Fintype.card_coe] at hF
  refine hF.trans (le_of_eq (finAvg_congr fun rS => ?_))
  rw [hconst rS, hsum rS]

end

end R56Audit
end

section
/-!
# Lemma 2.3 of the manuscript (local gain), as stated: every integer base, continuous heights

Auditor's supplement (not part of the audited archive).

**The local experiment** (Section 2.3). Fix one rectangle `R = I × J`. All colors `χ_i`, all
heights `V_i`, and the position of every point relative to `I` (to the left of `I`, in `I`,
or to the right of `I`) are fixed. Each point in `I` falls into one of the children
`C_1, …, C_b` of `I`, uniformly at random and independently of the other points.

Here the data are `ε : Fin n → ℝ` with `|ε i| = 1` (the colors), `V : Fin n → ℝ` (the
heights), `side : Fin n → Side` (the positions relative to `I`), and the outcome of the
experiment is `r : Fin n → Fin b`: the point `i`, if it lies in `I`, falls into the child
`C_{r i + 1}`. The digits of the points outside `I` are present in the sample space but
nothing depends on them (`childAvg_congr`). The expectation is the uniform average
`Oscillation.finAvg` over `r`.

| Manuscript | Here |
| --- | --- |
| weight `w_i` of `P_i` in `I`: `1`, `1/2`, `0` | `oldWeight (side i)` |
| `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}`, display (2) | `endpointAvg ε V side y` |
| child function `a_k` | `childAvg ε V side r k` |
| their average `ā(y) = (1/b) Σ_k a_k(y)` | `childMean ε V side r y` |
| `J`, cut into blocks `B_1, …, B_b` | `Set.Ico s (s + b * L)`, `block s L ℓ` for `ℓ < b` |
| the points of `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})` | `S = innerPoints b V side s L` |
| their number `m_R` | `S.card` |
| jump `X_i = χ_i (b + 1 - 2r) / (2b)` | `jump b ε i d`, with `d = r - 1` |
| `D`, the sum of the jumps of the points of `R^in` | `jumpSum S (jump b ε) r` |
| `g`, "the function `ā` without these jumps" | `withoutJumps b ε V side S r` |

`mem_innerPoints_iff` shows that `innerPoints` consists of the points of `I` whose height
lies in `B_2 ∪ ⋯ ∪ B_{b-1}`.

`local_gain` is **Lemma 2.3**: in the local experiment,

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + (1/4) √(m_R)`.

The proof is the manuscript's, in its four steps. Every display of the proof is stated in
this file, except for one expression in Step 2, which occurs in a proof only. The list says
which definition or statement is which display. Where a display is a chain of relations, the
list says which statement is which link of the chain, or that the statement is the relation
between the two ends of the chain.

* **Step 1: averaging the children.** The first display defines `ā`: it is the definition
  `childMean`. The triangle inequality (`card_mul_osc_avg_le`) and Lemma 2.1
  (`vertical_comparison`), applied to `f = ā`, give display (5): `display_5`.
* **Step 2: the weights in `ā`.** `sum_childWeight` is the display on the weight of a point
  in `ā`: for a point of `I` in the child `C_r`, this weight is the right-hand side
  `1/2 + (b + 1 - 2r) / (2b)` of the display, the old weight `1/2` plus a deviation (and a
  point outside `I` keeps its old weight). The left-hand side `((b - r) + 1/2) / b` of the
  display is a step of the proof of `sum_childWeight`, not a statement. Display (6) is
  `display_6`; `childMean_eq` is the same statement with the right-hand side written as one
  step function. The jumps are symmetric (`jump_rev`), and this gives display (7):
  `finAvg_childMean`.
* **Step 3: taking expectations.** `osc_endpointAvg_le` is the display
  `E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,
  stated as the inequality `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` between its two ends: the two
  equalities hold by the definition of `osc` and the linearity of `E`, and the inequality in
  the middle is `maxOn_endpointAvg_le` and `finAvg_minOn_childMean_le`. Taking expectations
  in (5) gives display (8): `display_8`.
* **Step 4: the gain.** `withoutJumps_eq` is the display that defines `g`, and `offset_eq` is
  the display `mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`. In
  the rest of the step `r = d + 1` is the index of the child and `σ² = (b² - 1) / (12 b²)`.
  * The sentences before the next display: `jump_sq_eq` is `X_i² = (r - (b+1)/2)² / b²`;
    `finAvg_childIndex` and `finAvg_childIndex_sq` are the mean `(b+1)/2` and the second
    moment `(b+1)(2b+1)/6` of `r`; `finAvg_childIndex_var` is its variance,
    `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12` (both equalities); and `abs_jump_le` is
    `|X_i| ≤ (b-1)/(2b)`.
  * The display on the moments of the jumps: `finAvg_jump_sq` is `E X_i² = σ²`. The chain
    `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴` is `finAvg_jump_fourth_le_sq` (its
    first inequality) and `sq_mul_sigma_sq_le` (its second inequality and its equality);
    `finAvg_jump_fourth_le` is the inequality `E X_i⁴ ≤ 3σ⁴` between its two ends.
  * The last display,
    `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`:
    `expected_offset_ge_sigma` is its first inequality, by Fact 2.2 (`symmetric_sum_abs`, an
    application of `fact_2_2_general`); `sigma_mul_sqrt_eq` is its equality;
    `sqrt_sq_sub_one_div_ge` is its last inequality; `sqrt_div_eight_le` is the equality and
    the last inequality together, `σ √(m/3) ≥ √m / 8`; and `expected_offset_ge` is the
    inequality between the two ends of the display.

"Together with (8), this proves the inequality of the lemma": `local_gain` is proved from
`display_8` and `expected_offset_ge`.

**Blocks of an interval, and arbitrary sets of heights.** `display_5`, `display_8`,
`offset_eq`, `expected_offset_ge_sigma` and `expected_offset_ge` are stated as in the
manuscript, for the blocks `B_1, …, B_b` of an interval `J` and the points of `R^in`. The
first four are proved from statements of the same form for sets of heights in place of the
blocks:

* `display_5` from `avg_comparison_core`, and `display_8` from `expected_comparison_core`
  (which is proved from `avg_comparison_core` and `osc_endpointAvg_le`). These two are stated
  for nonempty subsets `B_1, …, B_b` of a set `J` of heights, with the inequality of
  Lemma 2.1 as a hypothesis; for the blocks of an interval this hypothesis is
  `vertical_comparison`.
* `offset_eq` from `offset_core`, and `expected_offset_ge_sigma` from
  `expected_offset_core_sigma` (which is proved from `offset_core` and Fact 2.2). These two
  are stated for nonempty sets `B_1, …, B_b` of heights and a set `S` of points of `I` whose
  heights lie above all of `B_1` and at or below all of `B_b`; for the blocks of an interval
  and the points of `R^in` this hypothesis is `innerPoints_between_blocks`.

`expected_offset_ge` is proved from `expected_offset_ge_sigma` and `sqrt_div_eight_le`. In
the same way `expected_offset_core`, the same inequality for sets of heights, is proved from
`expected_offset_core_sigma` and `sqrt_div_eight_le`. Display (6) does not involve the
blocks: `display_6` is proved from `childMean_eq`.

So the same steps serve for intervals and for sampled heights: `local_gain_core`, proved
from `expected_comparison_core` and `expected_offset_core`, and `local_gain_sets` are
Lemma 2.3 in this generality.

`EndpointAverage.lean` proves that `endpointAvg` and `childAvg` are the endpoint averages
`(F(I⁻, y) + F(I⁺, y)) / 2` of `I` and of its children (first equality of display (2)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Step functions of the height -/

/-- The function `y ↦ Σ_i c_i 1{V_i ≤ y}` of the height. The manuscript's functions of the
height are of this form up to an additive constant; those of Lemma 2.3 (`endpointAvg`,
`childAvg` and their average) are exactly of this form. -/
def stepFn (V : Fin n → ℝ) (c : Fin n → ℝ) (y : ℝ) : ℝ := ∑ i, if V i ≤ y then c i else 0

lemma stepFn_add (V c c' : Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => c i + c' i) y = stepFn V c y + stepFn V c' y := by
  unfold stepFn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_sum {ι : Type*} (s : Finset ι) (V : Fin n → ℝ) (c : ι → Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => ∑ k ∈ s, c k i) y = ∑ k ∈ s, stepFn V (c k) y := by
  unfold stepFn
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_div (V c : Fin n → ℝ) (t : ℝ) (y : ℝ) :
    stepFn V (fun i => c i / t) y = stepFn V c y / t := by
  unfold stepFn
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_congr (V : Fin n → ℝ) {c c' : Fin n → ℝ} (h : ∀ i, c i = c' i) (y : ℝ) :
    stepFn V c y = stepFn V c' y := by
  unfold stepFn
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- "They take finitely many values". -/
lemma stepFn_image_finite (V c : Fin n → ℝ) (B : Set ℝ) : ((stepFn V c) '' B).Finite := by
  classical
  refine (Set.finite_range (fun T : Finset (Fin n) => ∑ i ∈ T, c i)).subset ?_
  rintro _ ⟨y, -, rfl⟩
  refine ⟨Finset.univ.filter (fun i => V i ≤ y), ?_⟩
  simp only [stepFn]
  rw [Finset.sum_filter]

/-- Below all the heights that carry a nonzero coefficient, the function vanishes. -/
lemma stepFn_eq_zero (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → y < V i) :
    stepFn V c y = 0 := by
  unfold stepFn
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · by_contra hc
    exact absurd hi (not_le.mpr (h i hc))
  · rfl

/-- Above all the heights that carry a nonzero coefficient, the function is the sum of the
coefficients. -/
lemma stepFn_eq_sum (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → V i ≤ y) :
    stepFn V c y = ∑ i, c i := by
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · by_contra hc
    exact hi (h i (fun h0 => hc (by rw [h0])))

lemma finAvg_stepFn {α : Type*} [Fintype α] [Nonempty α] (V : Fin n → ℝ) (c : α → Fin n → ℝ)
    (y : ℝ) :
    finAvg (fun r => stepFn V (c r) y) = stepFn V (fun i => finAvg (fun r => c r i)) y := by
  unfold stepFn
  rw [finAvg_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · exact finAvg_const 0

/-! ### The local experiment -/

/-- The position of a point relative to the horizontal interval `I`. -/
inductive Side
  | left
  | inside
  | right
  deriving DecidableEq

/-- The weight `w_i` of a point in `I`: `1` to the left of `I`, `1/2` in `I`, `0` to the
right of `I`. -/
def oldWeight : Side → ℝ
  | .left => 1
  | .inside => 1 / 2
  | .right => 0

/-- The weight of a point in the child `C_{k+1}` of `I`. A point outside `I` lies on the same
side of every child. A point of `I` in the child `C_{r+1}` lies to the left of `C_{k+1}` if
`r < k`, in it if `r = k`, and to the right of it if `r > k`. -/
def childWeight {b : ℕ} (sd : Side) (r k : Fin b) : ℝ :=
  match sd with
  | .left => 1
  | .inside => if r < k then 1 else if r = k then 1 / 2 else 0
  | .right => 0

/-- The endpoint average `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}` of `I`, display (2): the old
function. -/
def endpointAvg (ε V : Fin n → ℝ) (side : Fin n → Side) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i))

/-- The endpoint average `a_{k+1}` of the child `C_{k+1}`: a child function. -/
def childAvg {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b)
    (k : Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * childWeight (side i) (r i) k)

/-- The points of the inner region `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`: the points of `I` whose
height lies in `[s + L, s + (b-1) L)`. -/
def innerPoints (b : ℕ) (V : Fin n → ℝ) (side : Fin n → Side) (s L : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L)

/-! ### Step 1: averaging the children -/

/-- `ā`: the average of the child functions, `ā(y) = (1/b) Σ_k a_k(y)`. -/
def childMean {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b) : ℝ → ℝ :=
  fun y => (∑ k : Fin b, childAvg ε V side r k y) / b

/-- "They take finitely many values": `ā` is a step function of the height, like the child
functions. -/
lemma childMean_image_finite {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (A : Set ℝ) : ((childMean ε V side r) '' A).Finite := by
  have h : childMean ε V side r =
      stepFn V (fun i => (∑ k : Fin b, ε i * childWeight (side i) (r i) k) / b) := by
    funext y
    unfold childMean childAvg
    rw [stepFn_div, stepFn_sum]
  rw [h]
  exact stepFn_image_finite V _ A

/-- **Display (5)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`): for every outcome of the local
experiment,

`Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} ā + 2 |mid_{B_b} ā - mid_{B_1} ā|`.

`display_5` is the case of the blocks of an interval. -/
theorem avg_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f)
    (r : Fin n → Fin b) :
    ∑ ℓ : Fin b, osc (B ℓ) (childMean ε V side r) +
        2 * |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)| ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  have hJ : J.Nonempty := (hne ⟨0, hb0⟩).mono (hsub ⟨0, hb0⟩)
  -- "By the triangle inequality for the oscillation,
  -- `Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`."
  have h1 : (b : ℝ) * osc J (childMean ε V side r) ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
    have h := card_mul_osc_avg_le (ι := Fin b) (B := J)
      (f := fun k => childAvg ε V side r k) hJ (fun k => stepFn_image_finite V _ _)
    rw [Fintype.card_fin] at h
    exact h
  -- "So Lemma 2.1, applied to `f = ā`, gives" display (5)
  exact (hcomp _ (childMean_image_finite ε V side r J)).trans h1

/-! ### Step 2: the weights in `ā` -/

/-- "So its weight in `ā` is `((b - r) + 1/2) / b = 1/2 + (b + 1 - 2r) / (2b)`": the average
over the `b` children of the weight of a point is its old weight plus a deviation, which
vanishes for points outside `I`. -/
lemma sum_childWeight {b : ℕ} (hb : 0 < b) (sd : Side) (r : Fin b) :
    (∑ k : Fin b, childWeight sd r k) / b =
      oldWeight sd + (if sd = Side.inside then ((b : ℝ) - 1 - 2 * (r : ℕ)) / (2 * b) else 0) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  cases sd with
  | left =>
    simp only [childWeight, oldWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, reduceCtorEq, ite_false, add_zero]
    field_simp
  | right =>
    simp [childWeight, oldWeight]
  | inside =>
    simp only [childWeight, oldWeight, ite_true]
    have hsplit : ∀ k : Fin b, (if r < k then (1 : ℝ) else if r = k then 1 / 2 else 0) =
        (if r < k then (1 : ℝ) else 0) + (if r = k then 1 / 2 else 0) := by
      intro k
      by_cases h1 : r < k
      · have h2 : r ≠ k := ne_of_lt h1
        simp [h1, h2]
      · simp [h1]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ r (fun _ => (1 / 2 : ℝ)),
      ite_eq_left (Finset.mem_univ r), Finset.sum_boole]
    have hcard : (Finset.univ.filter (fun k : Fin b => r < k)).card = b - 1 - r := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hcard]
    have hr : (r : ℕ) + 1 ≤ b := r.isLt
    have hcast : ((b - 1 - (r : ℕ) : ℕ) : ℝ) = (b : ℝ) - 1 - (r : ℕ) := by
      have h : (b - 1 - (r : ℕ)) + (r : ℕ) + 1 = b := by omega
      have h' := congrArg (Nat.cast : ℕ → ℝ) h
      push_cast at h'
      linarith
    rw [hcast]
    field_simp
    ring

/-- The jump `X_i = χ_i (b + 1 - 2r) / (2b)` of a point of `I` in the child `C_r`, written
with `d = r - 1 ∈ {0, …, b-1}`: the deviation of its weight in `ā` from its old weight `1/2`,
multiplied by its color. -/
def jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) : ℝ :=
  ε i * (((b : ℝ) - 1 - 2 * (d : ℕ)) / (2 * b))

/-- Display (6) with its right-hand side written as one step function,
`ā(y) = Σ_i (χ_i w_i + 1{U_i ∈ I} X_i) 1{V_i ≤ y}`: the function `ā` "counts each point with
the average of its weights in the `b` children", which is its old weight for a point outside
`I` and "its old weight `1/2` plus a deviation" for a point in `I`. See `display_6` for the
manuscript's form. -/
lemma childMean_eq {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y =
      stepFn V (fun i => ε i * oldWeight (side i) +
        (if side i = Side.inside then jump b ε i (r i) else 0)) y := by
  unfold childMean childAvg
  rw [← stepFn_sum, ← stepFn_div]
  refine stepFn_congr V (fun i => ?_) y
  rw [← Finset.mul_sum, mul_div_assoc, sum_childWeight hb, mul_add]
  unfold jump
  split_ifs <;> ring

/-- "So `b + 1 - 2r` is uniform on the symmetric set `{1 - b, 3 - b, …, b - 1}`, and the `X_i`
are independent and symmetric, whatever the colors are": reversing the order of the children
changes the sign of the jump. -/
lemma jump_rev (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) :
    jump b ε i (Fin.revPerm d) = -jump b ε i d := by
  have hd : (d : ℕ) + 1 ≤ b := d.isLt
  have hcast : (((Fin.rev d : Fin b) : ℕ) : ℝ) = (b : ℝ) - 1 - (d : ℕ) := by
    rw [Fin.val_rev]
    have h : (b - ((d : ℕ) + 1)) + (d : ℕ) + 1 = b := by omega
    have h' := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h'
    linarith
  unfold jump
  rw [Fin.revPerm_apply, hcast]
  ring

/-- "In particular `E X_i = 0`", because the jumps are symmetric. -/
lemma finAvg_jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) : finAvg (jump b ε i) = 0 :=
  finAvg_eq_zero_of_symm Fin.revPerm (jump b ε i) (jump_rev b ε i)

/-- **Display (7)**: "In particular `E X_i = 0`, and (6) gives"

`E ā(y) = a(y)` "for every height `y`". -/
lemma finAvg_childMean {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (y : ℝ) :
    finAvg (fun r : Fin n → Fin b => childMean ε V side r y) = endpointAvg ε V side y := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  simp_rw [childMean_eq hb]
  rw [finAvg_stepFn]
  unfold endpointAvg
  refine stepFn_congr V (fun i => ?_) y
  rw [finAvg_add, finAvg_const]
  by_cases hs : side i = Side.inside
  · -- the jump of a point in `I` has expectation zero
    simp only [hs, ite_true]
    rw [finAvg_coord i (jump b ε i), finAvg_jump, add_zero]
  · simp only [hs, ite_false]
    rw [finAvg_const, add_zero]

/-! ### Step 3: taking expectations -/

/-- "The expectation of a maximum is at least the maximum of the expectations": by display
(7), `E max_B ā ≥ max_B a` for every nonempty set `B` of heights. -/
lemma maxOn_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    maxOn B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => maxOn B (childMean ε V side r)) := by
  apply maxOn_le hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => le_maxOn (childMean_image_finite ε V side r B) hy

/-- "\[…\] and the expectation of a minimum is at most the minimum of the expectations": by
display (7), `E min_B ā ≤ min_B a` for every nonempty set `B` of heights. -/
lemma finAvg_minOn_childMean_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    finAvg (fun r : Fin n → Fin b => minOn B (childMean ε V side r)) ≤
      minOn B (endpointAvg ε V side) := by
  apply le_minOn hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => minOn_le (childMean_image_finite ε V side r B) hy

/-- "So (7) gives, for every `ℓ`,"

`E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,

here for every nonempty set `B` of heights in place of `B_ℓ`. -/
lemma osc_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    osc B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => osc B (childMean ε V side r)) := by
  have hmax := maxOn_endpointAvg_le hb ε V side hB
  have hmin := finAvg_minOn_childMean_le hb ε V side hB
  unfold osc
  rw [finAvg_sub]
  linarith

/-- **Display (8)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`):

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

`display_8` is the case of the blocks of an interval. -/
theorem expected_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f) :
    ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b =>
          |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k)) := by
  have hb0 : 0 < b := by omega
  -- "Taking expectations in (5)"
  have hE := finAvg_mono (avg_comparison_core hb ε V side J B hne hsub hcomp)
  rw [finAvg_add, finAvg_sum, finAvg_const_mul] at hE
  -- `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` for every `ℓ`
  have hblocks : ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) ≤
      ∑ ℓ : Fin b, finAvg (fun r : Fin n → Fin b => osc (B ℓ) (childMean ε V side r)) :=
    Finset.sum_le_sum fun ℓ _ => osc_endpointAvg_le hb0 ε V side (hne ℓ)
  linarith

/-- **Display (8).** "Taking expectations in (5), we get"

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

"The first term on the right is what the horizontal strips had. The second term is the
gain." -/
theorem display_8 {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) :=
  expected_comparison_core hb ε V side (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt)
    (fun f hf => vertical_comparison hb s hL f hf)

/-! ### Step 4: the gain

In the manuscript `D` is the sum of the jumps of the points of `R^in`, and `g` is `ā` without
these jumps. In the statements below a set `S` of points of `I` takes the place of the set of
the points of `R^in`: `D = jumpSum S (jump b ε) r` (`jumpSum` is defined in
`SymmetricSums.lean`) and `g = withoutJumps b ε V side S r`. -/

/-- `g`: "the function `ā` without these jumps", the jumps of the points of `S`. Like `ā` in
`childMean_eq`, it is written as one step function; see `withoutJumps_eq` for the
manuscript's form. -/
def withoutJumps (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    (r : Fin n → Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i) +
    (if side i = Side.inside ∧ i ∉ S then jump b ε i (r i) else 0))

/-- "They take finitely many values": `g` is a step function of the height. -/
lemma withoutJumps_image_finite (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (S : Finset (Fin n)) (r : Fin n → Fin b) (A : Set ℝ) :
    ((withoutJumps b ε V side S r) '' A).Finite :=
  stepFn_image_finite V _ A

/-- "The heights of the points of `R^in` lie above `B_1` and below `B_b`": above every
height of the bottom block `B_1 = block s L 0`, and at or below every height of the top block
`B_b = block s L (b - 1)`. -/
lemma innerPoints_between_blocks {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side)
    (s L : ℝ) :
    ∀ i ∈ innerPoints b V side s L, side i = Side.inside ∧
      (∀ y ∈ block s L 0, y < V i) ∧ (∀ y ∈ block s L (b - 1), V i ≤ y) := by
  intro i hi
  have hi' : side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L := by
    simpa [innerPoints] using hi
  refine ⟨hi'.1, fun y hy => ?_, fun y hy => ?_⟩
  · have h2 : y < s + ((0 : ℕ) + 1 : ℝ) * L := hy.2
    simp only [Nat.cast_zero, zero_add, one_mul] at h2
    linarith [hi'.2.1]
  · have h2 : s + ((b - 1 : ℕ) : ℝ) * L ≤ y := hy.1
    rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one] at h2
    linarith [hi'.2.2]

/-- By display (6), `ā` is `g` plus the jumps of the points of `S`, for every set `S` of
points of `I`: `ā(y) = g(y) + Σ_{i ∈ S, V_i ≤ y} X_i`, where the last sum is written as a
step function. -/
lemma childMean_eq_withoutJumps_add {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y = withoutJumps b ε V side S r y +
      stepFn V (fun i => if i ∈ S then jump b ε i (r i) else 0) y := by
  rw [childMean_eq hb]
  unfold withoutJumps
  rw [← stepFn_add]
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : i ∈ S
  · simp [hi, hS i hi]
  · simp [hi]

/-- "So by (6), their jumps do not enter `ā` on `B_1`": `ā(y) = g(y)` at every height `y`
below the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_of_lt {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, y < V i) :
    childMean ε V side r y = withoutJumps b ε V side S r y := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_zero, add_zero]
  exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "\[…\] and they add the constant `D` to `ā` on `B_b`": `ā(y) = g(y) + D` at every height
`y` at or above the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_add_jumpSum_of_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, V i ≤ y) :
    childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_sum]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, jumpSum]
  · exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "`mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`", for
nonempty sets `B_1, …, B_b` of heights and any set `S` of points of `I` whose heights lie
above all of `B_1` and at or below all of `B_b`. `offset_eq` is the case of the blocks of an
interval and the points of `R^in`. -/
theorem offset_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y))
    (r : Fin n → Fin b) :
    mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
        mid (B ⟨0, by omega⟩) (childMean ε V side r) =
      (mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) +
      jumpSum S (jump b ε) r := by
  have hb0 : 0 < b := by omega
  have hI : ∀ i ∈ S, side i = Side.inside := fun i hi => (hS i hi).1
  -- "That is, `ā = g` on `B_1` and `ā = g + D` on `B_b`."
  have hbot : ∀ y ∈ B ⟨0, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y := fun y hy =>
    childMean_eq_withoutJumps_of_lt hb0 ε V side S hI r fun i hi => (hS i hi).2.1 y hy
  have htop : ∀ y ∈ B ⟨b - 1, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r :=
    fun y hy => childMean_eq_withoutJumps_add_jumpSum_of_le hb0 ε V side S hI r
      fun i hi => (hS i hi).2.2 y hy
  -- "Adding the constant `D` to a function adds `D` to its midpoint"
  rw [mid_congr hbot, mid_congr htop,
    mid_add_const (hne _) (withoutJumps_image_finite b ε V side S r _)]
  ring

/-- "Now condition on the children of all other points in `I` \[…\]. This fixes the function
`g`": `g` depends on the outcome only through the children of the points of `I` that are
not in `S`. -/
lemma withoutJumps_congr (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    {r r' : Fin n → Fin b} (h : ∀ i, side i = Side.inside → i ∉ S → r i = r' i) :
    withoutJumps b ε V side S r = withoutJumps b ε V side S r' := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : side i = Side.inside ∧ i ∉ S
  · rw [h i hi.1 hi.2]
  · simp [hi]

/-! ### Step 4: the moments of the jumps

"By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`. Here `r` has
mean `(b+1)/2` and second moment `(b+1)(2b+1)/6`, so its variance is
`(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`. Also `|X_i| ≤ (b-1)/(2b)`." These sentences are
`jump_sq_eq`, then `finAvg_childIndex`, `finAvg_childIndex_sq` and `finAvg_childIndex_var`,
then `abs_jump_le`. In this file the digit `d = r - 1` is uniform on `{0, …, b-1}`, and the
index `r` of the child is written `d + 1`.

The display that follows these sentences,

`E X_i² = (b²-1)/(12b²) =: σ²`,   `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`,

is `finAvg_jump_sq`, then `finAvg_jump_fourth_le_sq` (the first inequality of the chain) and
`sq_mul_sigma_sq_le` (its second inequality and its equality). `finAvg_jump_fourth_le` is
the inequality between the two ends of the chain.

`sum_centered_sq` is the same variance written with the digit `d`:
`X_i² = (b - 1 - 2d)² / (4b²)`, and `(1/b) Σ_d (b - 1 - 2d)² / 4 = (b² - 1) / 12`. The proofs
below do not use it. -/

/-- `Σ_{d=0}^{N-1} d = N (N - 1) / 2`. -/
lemma sum_range_id_real (N : ℕ) : ∑ d ∈ Finset.range N, (d : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{d=0}^{N-1} d² = N (N - 1) (2N - 1) / 6`. -/
lemma sum_range_sq_real (N : ℕ) :
    ∑ d ∈ Finset.range N, (d : ℝ) ^ 2 = (N : ℝ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- "By definition, `X_i² = (r - (b+1)/2)² / b²`", where `r = d + 1` is the index of the
child: the jump is `X_i = χ_i (b + 1 - 2r) / (2b)`, and `χ_i² = 1`. That `r` is uniform on
`{1, …, b}` is expressed in the next lemmas by the average `finAvg` over the digit `d`. -/
lemma jump_sq_eq {b : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) (d : Fin b) :
    jump b ε i d ^ 2 = ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 / (b : ℝ) ^ 2 := by
  have hε2 : ε i ^ 2 = 1 := by rw [← sq_abs, hε i]; norm_num
  unfold jump
  rw [mul_pow, hε2]
  ring

/-- "Here `r` has mean `(b+1)/2`": the mean of the index `r = d + 1` of the child. -/
lemma finAvg_childIndex {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((d : ℕ) : ℝ) + 1) = ((b : ℝ) + 1) / 2 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r = Σ_{r=0}^{b} r = b (b + 1) / 2`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) = (b : ℝ) * ((b : ℝ) + 1) / 2 := by
    have h := sum_range_id_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => (d : ℝ) + 1) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] and second moment `(b+1)(2b+1)/6`": the mean of `r²` for the index `r = d + 1` of
the child. -/
lemma finAvg_childIndex_sq {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => (((d : ℕ) : ℝ) + 1) ^ 2) = ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r² = Σ_{r=0}^{b} r² = b (b + 1) (2b + 1) / 6`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) ^ 2 =
      (b : ℝ) * ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
    have h := sum_range_sq_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((d : ℝ) + 1) ^ 2) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] so its variance is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`": the variance of the
index `r = d + 1` of the child is its second moment minus the square of its mean (the first
equality), and this number is `(b² - 1) / 12` (the second equality). -/
lemma finAvg_childIndex_var {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2) =
        ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 ∧
      ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 = ((b : ℝ) ^ 2 - 1) / 12 := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  refine ⟨?_, by ring⟩
  -- `(r - μ)² = r² - 2μ r + μ²` for the mean `μ = (b+1)/2`
  have hexp : ∀ d : Fin b, ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 =
      (((d : ℕ) : ℝ) + 1) ^ 2 - ((b : ℝ) + 1) * (((d : ℕ) : ℝ) + 1) + ((b : ℝ) + 1) ^ 2 / 4 :=
    fun d => by ring
  -- take expectations, and use the mean and the second moment of `r`
  rw [finAvg_congr hexp, finAvg_add, finAvg_sub, finAvg_const_mul, finAvg_const,
    finAvg_childIndex_sq hb, finAvg_childIndex hb]
  ring

/-- `E X_i² = (b² - 1) / (12 b²) =: σ²`, the first formula of the display on the moments of
the jumps: `X_i² = (r - (b+1)/2)² / b²` (`jump_sq_eq`), and the variance of `r` is
`(b² - 1) / 12` (`finAvg_childIndex_var`). -/
lemma finAvg_jump_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 2) = ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
  -- "By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`."
  rw [finAvg_congr (jump_sq_eq ε hε i), finAvg_div_const]
  -- the variance of `r` is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`
  rw [(finAvg_childIndex_var hb).1, (finAvg_childIndex_var hb).2, div_div]

/-- `|X_i| ≤ (b - 1) / (2b)`. -/
lemma abs_jump_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n)
    (d : Fin b) : |jump b ε i d| ≤ ((b : ℝ) - 1) / (2 * b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hd0 : (0 : ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
  have hd1 : ((d : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast d.isLt
  unfold jump
  rw [abs_mul, hε i, one_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * b)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- The first inequality of the chain for the fourth moment, `E X_i⁴ ≤ ((b-1)/(2b))² σ²`,
where `σ² = (b² - 1) / (12 b²)`: `X_i⁴ ≤ ((b-1)/(2b))² X_i²` because `|X_i| ≤ (b-1)/(2b)`
(`abs_jump_le`), and `E X_i² = σ²` (`finAvg_jump_sq`). -/
lemma finAvg_jump_fourth_le_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
  -- `X_i⁴ ≤ ((b-1)/(2b))² X_i²`, because `|X_i| ≤ (b-1)/(2b)`
  have hpt : ∀ d : Fin b, jump b ε i d ^ 4 ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 := by
    intro d
    have h1 : jump b ε i d ^ 2 ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_jump_le hb ε hε i d) 2
    have h2 : (0 : ℝ) ≤ jump b ε i d ^ 2 := sq_nonneg _
    calc jump b ε i d ^ 4 = jump b ε i d ^ 2 * jump b ε i d ^ 2 := by ring
      _ ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h2
  -- take expectations, and use `E X_i² = σ²`
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ finAvg (fun d : Fin b => (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2) :=
        finAvg_mono hpt
    _ = (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
        rw [finAvg_const_mul, finAvg_jump_sq hb ε hε i]

/-- The rest of the chain for the fourth moment,
`((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`. The
inequality holds because `(b - 1)² ≤ b² - 1` for `b ≥ 1` and `σ² ≥ 0`, and the equality
because `(b² - 1) / (4b²) = 3σ²`. -/
lemma sq_mul_sigma_sq_le {b : ℕ} (hb : 0 < b) :
    (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ≤
        ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ∧
      ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) =
        3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  refine ⟨?_, by ring⟩
  -- `σ² ≥ 0`
  have hs : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  -- `((b-1)/(2b))² ≤ (b²-1)/(4b²)`, because `(b - 1)² ≤ b² - 1` for `b ≥ 1`
  have hk : (((b : ℝ) - 1) / (2 * b)) ^ 2 ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) := by
    rw [div_pow, show (2 * (b : ℝ)) ^ 2 = 4 * (b : ℝ) ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  exact mul_le_mul_of_nonneg_right hk hs

/-- `E X_i⁴ ≤ 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`: the inequality between the two ends of
the chain `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, whose links are
`finAvg_jump_fourth_le_sq` and `sq_mul_sigma_sq_le`. This is the fourth-moment hypothesis of
Fact 2.2. -/
lemma finAvg_jump_fourth_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 :=
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        finAvg_jump_fourth_le_sq hb ε hε i
    _ ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        (sq_mul_sigma_sq_le hb).1
    _ = 3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := (sq_mul_sigma_sq_le hb).2

/-! ### Step 4: the last display

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

where `σ² = (b² - 1) / (12 b²)`. The first inequality is `expected_offset_ge_sigma`, the
equality is `sigma_mul_sqrt_eq`, the last inequality is `sqrt_sq_sub_one_div_ge`, and
`expected_offset_ge` is the inequality between the two ends of the display.
`sqrt_div_eight_le` is the equality and the last inequality together. -/

/-- The equality of the last display, `σ √(m/3) = (√(b² - 1) / (6b)) √m`, where
`σ² = (b² - 1) / (12 b²)`. -/
lemma sigma_mul_sqrt_eq {b : ℕ} (hb : 0 < b) (m : ℕ) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) =
      Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnum : (0 : ℝ) ≤ (b : ℝ) ^ 2 - 1 := by nlinarith
  -- `√(12 b²) √3 = √(36 b²) = 6b`
  have h6 : Real.sqrt (12 * (b : ℝ) ^ 2) * Real.sqrt 3 = 6 * b := by
    rw [← Real.sqrt_mul (by positivity), show 12 * (b : ℝ) ^ 2 * 3 = (6 * b) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  -- `σ = √(b² - 1) / √(12 b²)` and `√(m/3) = √m / √3`
  rw [Real.sqrt_div hnum, Real.sqrt_div (Nat.cast_nonneg m), div_mul_div_comm, h6]
  ring

/-- The last inequality of the last display, `(√(b² - 1) / (6b)) √m ≥ √m / 8`, "because
`16 (b² - 1) ≥ 9 b²` for `b ≥ 2`". -/
lemma sqrt_sq_sub_one_div_ge {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  -- "because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`"
  have h16 : 9 * (b : ℝ) ^ 2 ≤ 16 * ((b : ℝ) ^ 2 - 1) := by nlinarith
  -- so `3b/4 ≤ √(b² - 1)`, that is, `1/8 ≤ √(b² - 1) / (6b)`
  have h34 : 3 * (b : ℝ) / 4 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    apply Real.le_sqrt_of_sq_le
    linarith [show (3 * (b : ℝ) / 4) ^ 2 = 9 * (b : ℝ) ^ 2 / 16 by ring]
  have hc : (1 : ℝ) / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- multiply by `√m ≥ 0`
  calc Real.sqrt m / 8 = 1 / 8 * Real.sqrt m := by ring
    _ ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

/-- `σ √(m/3) ≥ √m / 8` for `σ² = (b² - 1) / (12 b²)` and `b ≥ 2`: the equality and the last
inequality of the last display together (`sigma_mul_sqrt_eq`, `sqrt_sq_sub_one_div_ge`). -/
lemma sqrt_div_eight_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) := by
  -- `σ √(m/3) = (√(b² - 1) / (6b)) √m`
  rw [sigma_mul_sqrt_eq (by omega) m]
  -- `(√(b² - 1) / (6b)) √m ≥ √m / 8`
  exact sqrt_sq_sub_one_div_ge hb m

/-- The first inequality of the last display, `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m/3)` with
`σ² = (b² - 1) / (12 b²)`, for nonempty sets `B_1, …, B_b` of heights and any set `S` of `m`
points of `I` whose heights lie above all of `B_1` and at or below all of `B_b`. Fact 2.2
(`symmetric_sum_abs`) is applied to the jumps of the points of `S`.
`expected_offset_ge_sigma` is the case of the blocks of an interval and the points of
`R^in`. -/
theorem expected_offset_core_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty)
    (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)|) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  -- `σ² = (b² - 1) / (12 b²)`
  have hs2 : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb0
    nlinarith
  have hσ2 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 =
      ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := Real.sq_sqrt hs2
  have hσ4 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 4 =
      (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hσ2]
  -- "This fixes the function `g`, and hence the number `θ`."
  have hθ : ∀ r r' : Fin n → Fin b, (∀ i, i ∉ S → r i = r' i) →
      mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) =
        mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r') -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r') := by
    intro r r' h
    rw [withoutJumps_congr b ε V side S fun i _ hi => h i hi]
  -- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
  -- children of the other points cannot reduce it": `E|θ + D| ≥ σ √(m/3)`
  have hF : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) + jumpSum S (jump b ε) r|) :=
    symmetric_sum_abs S (jump b ε) (fun _ => Fin.revPerm)
      (fun i _ d => jump_rev b ε i d) (Real.sqrt_nonneg _)
      (fun i _ => by rw [hσ2]; exact finAvg_jump_sq hb0 ε hε i)
      (fun i _ => by rw [hσ4]; exact finAvg_jump_fourth_le hb0 ε hε i)
      (fun r => mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) hθ
  -- `mid_{B_b} ā - mid_{B_1} ā = θ + D`
  rw [finAvg_congr fun r => congrArg abs (offset_core hb ε V side B hne S hS r)]
  exact hF

/-- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
children of the other points cannot reduce it. Conditionally, and hence also without the
conditioning,"

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3)`,

where `σ² = (b² - 1) / (12 b²)`: the first inequality of the last display. -/
theorem expected_offset_ge_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) *
        Real.sqrt ((innerPoints b V side s L).card / 3) ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  expected_offset_core_sigma hb ε hε V side (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (innerPoints b V side s L)
    (innerPoints_between_blocks hb V side s L)

/-- The last display of the proof,

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b² - 1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

"because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`." The statement is the inequality between the two
ends of this display. The first inequality of the display is `expected_offset_ge_sigma`; its
equality and its last inequality are `sigma_mul_sqrt_eq` and `sqrt_sq_sub_one_div_ge`, which
together are `sqrt_div_eight_le`. -/
theorem expected_offset_ge {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (innerPoints b V side s L).card / 8 ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  (sqrt_div_eight_le hb (innerPoints b V side s L).card).trans
    (expected_offset_ge_sigma hb ε hε V side s hL)

/-! ### Lemma 2.3 -/

/-- **Lemma 2.3 (local gain).** In the local experiment,

`E Σ_{k=1}^{b} osc_J a_k ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} a + (1/4) √(m_R)`,

for every integer `b ≥ 2` (the manuscript has `b ≥ 3`), all colors, all heights (ties
allowed), and all positions relative to `I`. The proof is the last sentence of the
manuscript's proof: it combines display (8) (`display_8`: Steps 1–3, with Lemma 2.1) and the
last display (`expected_offset_ge`: Step 4, with Fact 2.2). -/
theorem local_gain {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        (1 / 4) * Real.sqrt (innerPoints b V side s L).card ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) := by
  have h8 := display_8 hb ε V side s hL
  have h4 := expected_offset_ge hb ε hε V side s hL
  -- "Together with (8), this proves the inequality of the lemma."
  linarith

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.L23

open TusnadyPlane.RandomPoints

def sideOf (c : Fin 3) : R56Audit.Side :=
  if c.val = 0 then .left else if c.val = 1 then .inside else .right

theorem oldWeight_eq (c : Fin 3) : oldWeight c = R56Audit.oldWeight (sideOf c) := by
  fin_cases c <;> simp [oldWeight, sideOf, R56Audit.oldWeight]

theorem childWeight_eq {b : ℕ} (c : Fin 3) (r k : Fin b) :
    childWeight c r.val k.val = R56Audit.childWeight (sideOf c) r k := by
  have h1 : (r.val < k.val) ↔ r < k := Iff.rfl
  have h2 : (r.val = k.val) ↔ r = k := Fin.val_inj
  fin_cases c
  · simp [childWeight, sideOf, R56Audit.childWeight]
  · simp [childWeight, sideOf, R56Audit.childWeight, h1, h2]
  · simp [childWeight, sideOf, R56Audit.childWeight]

theorem block_eq (lo hi : ℝ) (b : ℕ) (k : ℕ) :
    block lo hi b k = R56Audit.block lo ((hi - lo) / b) k := by
  unfold block R56Audit.block
  simp only [mul_div_assoc]

end TusnadyPlane.Dev.L23

namespace TusnadyPlane.RandomPoints

open TusnadyPlane.Dev.L23 in
theorem chk_lemma_2_3 (n b : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b)
    (lo hi : ℝ) (hJ : lo < hi) (d : LocalData n) (hd : Function.Injective d.height) :
    (∑ l : Fin b, oscillation (block lo hi b l.val) (oldFunction d)) +
      (1/4 : ℝ) * Real.sqrt (localInnerCount d lo hi b) ≤
        localExpectedOscillation d lo hi b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hL : 0 < (hi - lo) / b := div_pos (by linarith) hbR
  have hJ' : lo + b * ((hi - lo) / b) = hi := by field_simp; ring
  have hε : ∀ i, |sign (d.color i)| = 1 := by
    intro i; cases d.color i <;> simp [sign]
  have hold : oldFunction d =
      R56Audit.endpointAvg (fun i => sign (d.color i)) d.height (fun i => sideOf (d.category i)) := by
    funext y
    simp only [oldFunction, R56Audit.endpointAvg, R56Audit.stepFn, oldWeight_eq]
  have hchild : ∀ (r : Fin n → Fin b) (k : Fin b), childFunction d r k =
      R56Audit.childAvg (fun i => sign (d.color i)) d.height (fun i => sideOf (d.category i)) r k := by
    intro r k
    funext y
    simp only [childFunction, R56Audit.childAvg, R56Audit.stepFn, childWeight_eq]
  have hinner : localInnerCount d lo hi b =
      (R56Audit.innerPoints b d.height (fun i => sideOf (d.category i)) lo ((hi - lo) / b)).card := by
    unfold localInnerCount R56Audit.innerPoints
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
    have hside : sideOf (d.category i) = R56Audit.Side.inside ↔ (d.category i).val = 1 := by
      have := (d.category i).isLt
      unfold sideOf
      split_ifs <;> simp_all
    rw [hside]
    have e2 : hi - (hi - lo) / b = lo + ((b : ℝ) - 1) * ((hi - lo) / b) := by field_simp; ring
    rw [e2]
  have hexp : localExpectedOscillation d lo hi b = Oscillation.finAvg (fun r : Fin n → Fin b =>
      ∑ k : Fin b, R56Audit.osc (Set.Ico lo (lo + b * ((hi - lo) / b)))
        (R56Audit.childAvg (fun i => sign (d.color i)) d.height (fun i => sideOf (d.category i)) r k)) := by
    unfold localExpectedOscillation Oscillation.finAvg
    rw [hJ', div_eq_inv_mul]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    congr 1
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hchild]
    rfl
  have h := R56Audit.local_gain (b := b) (by omega) (fun i => sign (d.color i)) hε d.height
    (fun i => sideOf (d.category i)) lo hL
  rw [hexp, hinner, hold]
  simp only [block_eq]
  exact h

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_lemma_2_3 := @TusnadyPlane.RandomPoints.chk_lemma_2_3
