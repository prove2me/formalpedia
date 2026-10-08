-- Prove2me | solution 1 for RobinsonFP.Convergence.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:36:44.790659+00:00
-- url     : https://prove2.me/submissions/edb158e6-35d2-4397-9d7d-89db5ef13cc1

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology


namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rb_le_vmax [Nonempty ι] (w : ι → ℝ) (i : ι) : w i ≤ vmax w :=
  Finset.le_sup' w (Finset.mem_univ i)

theorem rb_vmax_le [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, w i ≤ c) : vmax w ≤ c :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem rb_vmin_le [Nonempty ι] (w : ι → ℝ) (i : ι) : vmin w ≤ w i :=
  Finset.inf'_le w (Finset.mem_univ i)

theorem rb_le_vmin [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, c ≤ w i) : c ≤ vmin w :=
  Finset.le_inf' _ _ (fun i _ => h i)

theorem rb_exists_eq_vmax [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmax w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_exists_eq_vmin [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmin w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_vmax_neg [Nonempty ι] (w : ι → ℝ) : vmax (fun i => - w i) = - vmin w := by
  apply le_antisymm
  · apply rb_vmax_le
    intro i
    have := rb_vmin_le w i
    linarith
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmin w
    have := rb_le_vmax (fun i => - w i) i
    linarith

theorem rb_vmin_neg [Nonempty ι] (w : ι → ℝ) : vmin (fun i => - w i) = - vmax w := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmax w
    have := rb_vmin_le (fun i => - w i) i
    linarith
  · apply rb_le_vmin
    intro i
    have := rb_le_vmax w i
    linarith

theorem rb_gap_step [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    vmax (V t) - vmin (U t) ≤ vmax (V (t + 1)) - vmin (U (t + 1)) := by
  obtain ⟨i, j, hi, hj, hU, hV⟩ := h.2 t
  have e1 : V (t + 1) i = V t i + A i j := by simpa using congrFun hV i
  have e2 : U (t + 1) j = U t j + A i j := by simpa using congrFun hU j
  have h1 := rb_le_vmax (V (t + 1)) i
  have h2 := rb_vmin_le (U (t + 1)) j
  linarith

theorem rb_gap_mono [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) :
    Monotone (fun t => vmax (V t) - vmin (U t)) :=
  monotone_nat_of_le_succ (fun t => rb_gap_step h t)

theorem rb_gap_nonneg [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    0 ≤ vmax (V t) - vmin (U t) := by
  have := rb_gap_mono h (Nat.zero_le t)
  have h0 : vmax (V 0) - vmin (U 0) = 0 := by rw [h.1]; ring
  simp only at this
  linarith
theorem rb_lemma1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, -ε ≤ (vmax (V t) - vmin (U t)) / t := by
  intro ε hε
  refine Filter.Eventually.of_forall (fun t => ?_)
  exact le_trans (neg_nonpos.2 hε.le) (div_nonneg (rb_gap_nonneg hUV t) (Nat.cast_nonneg t))

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, -ε ≤ (vmax (V t) - vmin (U t)) / t := by
  exact rb_lemma1 A U V hUV
