-- Prove2me | solution 1 for RobinsonFP.Convergence.limsup_liminf_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:37:42.263985+00:00
-- url     : https://prove2.me/submissions/a31885af-958e-4d4b-a240-d68b6289259e

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
theorem rb_limsup_liminf [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      vmin (U t) / t ≤ v + ε ∧ v - ε ≤ vmax (V t) / t := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hvx, hvy⟩ := hsol
  intro ε hε
  have hup : ∀ t : ℕ, ∑ j, y j * U t j ≤ ∑ j, y j * U 0 j + t * v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      obtain ⟨i, j, _, _, hU, _⟩ := hUV.2 t
      have e : ∀ l, U (t + 1) l = U t l + A i l := fun l => by simpa using congrFun hU l
      have h1 : ∑ l, y l * U (t + 1) l = ∑ l, y l * U t l + ∑ l, A i l * y l := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [e l]; ring
      have h2 : ∑ l, A i l * y l ≤ v := by
        rw [← hvy]
        exact rb_le_vmax (fun i => ∑ j, A i j * y j) i
      push_cast
      linarith
  have hlow : ∀ t : ℕ, ∑ i, x i * V 0 i + t * v ≤ ∑ i, x i * V t i := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      obtain ⟨i, j, _, _, _, hV⟩ := hUV.2 t
      have e : ∀ l, V (t + 1) l = V t l + A l j := fun l => by simpa using congrFun hV l
      have h1 : ∑ l, x l * V (t + 1) l = ∑ l, x l * V t l + ∑ l, A l j * x l := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [e l]; ring
      have h2 : v ≤ ∑ l, A l j * x l := by
        rw [← hvx]
        exact rb_vmin_le (fun j => ∑ i, A i j * x i) j
      push_cast
      linarith
  have hmin : ∀ t, vmin (U t) ≤ ∑ j, y j * U t j := by
    intro t
    calc vmin (U t) = ∑ j, y j * vmin (U t) := by rw [← Finset.sum_mul, hy1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (rb_vmin_le _ j) (hy0 j)
  have hmax : ∀ t, ∑ i, x i * V t i ≤ vmax (V t) := by
    intro t
    calc ∑ i, x i * V t i ≤ ∑ i, x i * vmax (V t) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (rb_le_vmax _ i) (hx0 i)
      _ = vmax (V t) := by rw [← Finset.sum_mul, hx1, one_mul]
  set C1 : ℝ := ∑ j, y j * U 0 j with hC1
  set C2 : ℝ := ∑ i, x i * V 0 i with hC2
  have ev1 := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat C1)).2 ε hε
  have ev2 := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (-C2))).2 ε hε
  filter_upwards [ev1, ev2, eventually_gt_atTop 0] with t h1 h2 ht
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  rw [div_lt_iff₀ htr] at h1 h2
  constructor
  · rw [div_le_iff₀ htr]
    have := hmin t
    have := hup t
    nlinarith
  · rw [le_div_iff₀ htr]
    have := hmax t
    have := hlow t
    nlinarith

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      vmin (U t) / t ≤ v + ε ∧ v - ε ≤ vmax (V t) / t := by
  exact rb_limsup_liminf A U V hUV x y v hsol
