-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:27:59.26088+00:00
-- url     : https://prove2.me/submissions/0c2ce353-ebf8-4d60-8dbf-85a694b90de3

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_TusnadyPlane_RandomPoints_oscillation

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

/-- The extrema over a subset lie between the extrema over the set. -/
lemma maxOn_mono {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : maxOn A f ≤ maxOn B f :=
  maxOn_le hA fun _ hy => le_maxOn hf (hAB hy)

lemma minOn_anti {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : minOn B f ≤ minOn A f :=
  le_minOn hA fun _ hy => minOn_le hf (hAB hy)

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
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.L21

open TusnadyPlane.RandomPoints in
theorem block_eq (lo hi : ℝ) (b : ℕ) (k : ℕ) :
    block lo hi b k = R56Audit.block lo ((hi - lo) / b) k := by
  unfold block R56Audit.block
  simp only [mul_div_assoc]

end TusnadyPlane.Dev.L21

namespace TusnadyPlane.RandomPoints

theorem chk_lemma_2_1 (b : ℕ) (hb : 3 ≤ b) (lo hi : ℝ) (hJ : lo < hi)
    (f : ℝ → ℝ) (hf : (f '' Set.Ico lo hi).Finite) :
    (∑ k : Fin b, oscillation (block lo hi b k.val) f) +
      2 * |midpoint (block lo hi b (b-1)) f - midpoint (block lo hi b 0) f| ≤
        (b : ℝ) * oscillation (Set.Ico lo hi) f := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hL : 0 < (hi - lo) / b := div_pos (by linarith) hbR
  have hJ' : lo + b * ((hi - lo) / b) = hi := by field_simp; ring
  have h := R56Audit.vertical_comparison (b := b) (by omega) lo hL f (by rw [hJ']; exact hf)
  rw [hJ'] at h
  simp only [TusnadyPlane.Dev.L21.block_eq]
  exact h

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_lemma_2_1 := @TusnadyPlane.RandomPoints.chk_lemma_2_1
