-- Prove2me | solution 1 for RobinsonFP.Convergence.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:36:46.587306+00:00
-- url     : https://prove2.me/submissions/36f58bd7-a6be-40fa-8d65-6654bdcfc5e3

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
theorem rb_ineq1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∀ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ κ,
      vmin (fun j => ∑ i, A i j * x i) ≤ vmax (fun i => ∑ j, A i j * y j) := by
  intro x hx y hy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  calc vmin (fun j => ∑ i, A i j * x i) = ∑ j, y j * vmin (fun j => ∑ i, A i j * x i) := by
        rw [← Finset.sum_mul, hy1, one_mul]
    _ ≤ ∑ j, y j * (∑ i, A i j * x i) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (rb_vmin_le (fun j => ∑ i, A i j * x i) j) (hy0 j)
    _ = ∑ j, ∑ i, y j * (A i j * x i) := by simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, y j * (A i j * x i) := Finset.sum_comm
    _ = ∑ i, x i * (∑ j, A i j * y j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
    _ ≤ ∑ i, x i * vmax (fun i => ∑ j, A i j * y j) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (rb_le_vmax (fun i => ∑ j, A i j * y j) i) (hx0 i)
    _ = vmax (fun i => ∑ j, A i j * y j) := by rw [← Finset.sum_mul, hx1, one_mul]
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
theorem rb_vmin_V_le_vmax_U [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (T : ℕ) :
    vmin (V T) ≤ vmax (U T) := by
  choose i j hi hj hU hV using h.2
  have hUf : ∀ t l, U t l = U 0 l + ∑ τ ∈ Finset.range t, A (i τ) l := by
    intro t l
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have := congrFun (hU t) l
      simp at this
      linarith
  have hVf : ∀ t l, V t l = V 0 l + ∑ σ ∈ Finset.range t, A l (j σ) := by
    intro t l
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have := congrFun (hV t) l
      simp at this
      linarith
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · obtain ⟨i0, h0⟩ := rb_exists_eq_vmax (V 0)
    have j0 : κ := Classical.arbitrary κ
    exact (rb_vmin_le _ i0).trans (h0.le.trans (h.1.symm.le.trans
      ((rb_vmin_le _ j0).trans (rb_le_vmax _ j0))))
  · have e1 : (T : ℝ) * vmin (V T) ≤ ∑ τ ∈ Finset.range T, V T (i τ) := by
      calc (T : ℝ) * vmin (V T) = ∑ τ ∈ Finset.range T, vmin (V T) := by simp
        _ ≤ _ := Finset.sum_le_sum fun τ _ => rb_vmin_le _ _
    have e2 : ∑ σ ∈ Finset.range T, U T (j σ) ≤ (T : ℝ) * vmax (U T) := by
      calc ∑ σ ∈ Finset.range T, U T (j σ) ≤ ∑ σ ∈ Finset.range T, vmax (U T) :=
            Finset.sum_le_sum fun σ _ => rb_le_vmax _ _
        _ = _ := by simp
    have e3 : ∑ τ ∈ Finset.range T, V 0 (i τ) ≤ (T : ℝ) * vmax (V 0) := by
      calc ∑ τ ∈ Finset.range T, V 0 (i τ) ≤ ∑ τ ∈ Finset.range T, vmax (V 0) :=
            Finset.sum_le_sum fun τ _ => rb_le_vmax _ _
        _ = _ := by simp
    have e4 : (T : ℝ) * vmin (U 0) ≤ ∑ σ ∈ Finset.range T, U 0 (j σ) := by
      calc (T : ℝ) * vmin (U 0) = ∑ σ ∈ Finset.range T, vmin (U 0) := by simp
        _ ≤ _ := Finset.sum_le_sum fun σ _ => rb_vmin_le _ _
    have e5 : ∑ τ ∈ Finset.range T, V T (i τ) = ∑ τ ∈ Finset.range T, V 0 (i τ)
        + ∑ τ ∈ Finset.range T, ∑ σ ∈ Finset.range T, A (i τ) (j σ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun τ _ => hVf T (i τ))
    have e6 : ∑ σ ∈ Finset.range T, U T (j σ) = ∑ σ ∈ Finset.range T, U 0 (j σ)
        + ∑ σ ∈ Finset.range T, ∑ τ ∈ Finset.range T, A (i τ) (j σ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun σ _ => hUf T (j σ))
    have e7 : ∑ σ ∈ Finset.range T, ∑ τ ∈ Finset.range T, A (i τ) (j σ)
        = ∑ τ ∈ Finset.range T, ∑ σ ∈ Finset.range T, A (i τ) (j σ) := Finset.sum_comm
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have h1 : (T : ℝ) * vmin (U 0) = T * vmax (V 0) := by rw [h.1]
    have : (T : ℝ) * vmin (V T) ≤ (T : ℝ) * vmax (U T) := by linarith
    exact le_of_mul_le_mul_left this hTpos

theorem rb_lemma3 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (V (s + t)) - vmin (U (s + t)) ≤ 4 * a * t := by
  obtain ⟨h1, h2⟩ := rb_lemma2 A a ha U V hUV s t hrow hcol
  have := rb_vmin_V_le_vmax_U hUV (s + t)
  linarith

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (V (s + t)) - vmin (U (s + t)) ≤ 4 * a * t := by
  exact rb_lemma3 A a ha U V hUV s t hrow hcol
