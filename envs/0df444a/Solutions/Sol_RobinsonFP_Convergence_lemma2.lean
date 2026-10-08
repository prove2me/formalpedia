-- Prove2me | solution 1 for RobinsonFP.Convergence.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:36:45.803445+00:00
-- url     : https://prove2.me/submissions/6e6fd339-d6de-490f-9ff0-d2fee92b6fb4

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
theorem rb_U_lip [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) {a : ℝ} (ha : ∀ i j, |A i j| ≤ a)
    (j : κ) (t₂ d : ℕ) : |U (t₂ + d) j - U t₂ j| ≤ a * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨i, j', _, _, hU, _⟩ := h.2 (t₂ + d)
    have e : U (t₂ + (d + 1)) j = U (t₂ + d) j + A i j := by
      have := congrFun hU j
      simpa [← add_assoc] using this
    have h1 := abs_le.mp ih
    have h2 := abs_le.mp (ha i j)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith

theorem rb_V_lip [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) {a : ℝ} (ha : ∀ i j, |A i j| ≤ a)
    (i : ι) (t₂ d : ℕ) : |V (t₂ + d) i - V t₂ i| ≤ a * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨i', j, _, _, _, hV⟩ := h.2 (t₂ + d)
    have e : V (t₂ + (d + 1)) i = V (t₂ + d) i + A i j := by
      have := congrFun hV i
      simpa [← add_assoc] using this
    have h1 := abs_le.mp ih
    have h2 := abs_le.mp (ha i j)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith

theorem rb_lemma2 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (U (s + t)) - vmin (U (s + t)) ≤ 2 * a * t ∧
      vmax (V (s + t)) - vmin (V (s + t)) ≤ 2 * a * t := by
  have ha0 : 0 ≤ a :=
    le_trans (abs_nonneg _) (ha (Classical.arbitrary ι) (Classical.arbitrary κ))
  constructor
  · obtain ⟨j, hj⟩ := rb_exists_eq_vmax (U (s + t))
    obtain ⟨t₂, h1, h2, h3⟩ := hcol j
    obtain ⟨d, hd⟩ : ∃ d, s + t = t₂ + d := ⟨s + t - t₂, by omega⟩
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast (by omega : d ≤ t)
    have had : a * d ≤ a * t := mul_le_mul_of_nonneg_left hdt ha0
    have hlj := abs_le.mp (rb_U_lip hUV ha j t₂ d)
    have key : ∀ k, U (s + t) j - 2 * a * t ≤ U (s + t) k := by
      intro k
      have hk := abs_le.mp (rb_U_lip hUV ha k t₂ d)
      have hmin := rb_vmin_le (U t₂) k
      rw [hd]
      linarith
    have := rb_le_vmin key
    linarith
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmin (V (s + t))
    obtain ⟨t₁, h1, h2, h3⟩ := hrow i
    obtain ⟨d, hd⟩ : ∃ d, s + t = t₁ + d := ⟨s + t - t₁, by omega⟩
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast (by omega : d ≤ t)
    have had : a * d ≤ a * t := mul_le_mul_of_nonneg_left hdt ha0
    have hli := abs_le.mp (rb_V_lip hUV ha i t₁ d)
    have key : ∀ k, V (s + t) k ≤ V (s + t) i + 2 * a * t := by
      intro k
      have hk := abs_le.mp (rb_V_lip hUV ha k t₁ d)
      have hmax := rb_le_vmax (V t₁) k
      rw [hd]
      linarith
    have := rb_vmax_le key
    linarith

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (U (s + t)) - vmin (U (s + t)) ≤ 2 * a * t ∧
      vmax (V (s + t)) - vmin (V (s + t)) ≤ 2 * a * t := by
  exact rb_lemma2 A a ha U V hUV s t hrow hcol
