-- Prove2me | solution 1 for TalagrandConc.Subsequences.lemma_7_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:47:11.03999+00:00
-- url     : https://prove2.me/submissions/f97459a1-7f0b-484b-a0cb-ef0eba9b74c9

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal


namespace TalagrandConc.Subsequences

/-- Generic sum bound: on `U_A(x)`, `Σ_{i∈J} s_i ≥ card {i ∈ J ; y_i ≠ x_i}` for a witness `y`. -/
lemma sum_ge_card_ne {Ω : Type*} [DecidableEq Ω] {N : ℕ} (x y : Fin N → Ω) (s : Fin N → ℝ)
    (hs : ∀ i, s i = 0 ∨ s i = 1) (hxy : ∀ i, s i = 0 → x i = y i) (J : Finset (Fin N)) :
    ((J.filter fun i => y i ≠ x i).card : ℝ) ≤ ∑ i ∈ J, s i := by
  have h0 : ∀ i, 0 ≤ s i := fun i => by rcases hs i with h | h <;> simp [h]
  calc ((J.filter fun i => y i ≠ x i).card : ℝ)
      = ∑ i ∈ J.filter (fun i => y i ≠ x i), s i := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter] at hi
        rcases hs i with h | h
        · exact absurd (hxy i h).symm hi.2
        · simp [h]
    _ ≤ ∑ i ∈ J, s i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => h0 i)

/-- Generic bound on the convex hull: for `s ∈ V_{A(a)}(x)`,
`L x - a ≤ √(card J) * √(Σ s_i²)`, provided `J` is a "configuration" witness for `x`. -/
lemma core_bound {Ω : Type*} [DecidableEq Ω] {N : ℕ} (L : (Fin N → Ω) → ℕ) (a : ℝ) (x : Fin N → Ω)
    (J : Finset (Fin N))
    (hJ : ∀ y, y ∈ levelSet L a → (L x : ℝ) ≤ L y + ((J.filter fun i => y i ≠ x i).card : ℝ)) :
    ∀ s ∈ TalagrandConc.ConvexHull.V (levelSet L a) x,
      (L x : ℝ) - a ≤ Real.sqrt J.card * Real.sqrt (∑ i, s i ^ 2) := by
  intro s hs
  -- the halfspace
  let C : Set (Fin N → ℝ) := {s | (L x : ℝ) - a ≤ ∑ i ∈ J, s i}
  have hlin : IsLinearMap ℝ (fun s : Fin N → ℝ => ∑ i ∈ J, s i) :=
    ⟨fun u v => Finset.sum_add_distrib, fun c u => by simp [Finset.mul_sum]⟩
  have hC : Convex ℝ C := convex_halfSpace_ge hlin _
  have hUC : TalagrandConc.ConvexHull.U (levelSet L a) x ⊆ C := by
    intro t ht
    obtain ⟨ht01, y, hy, hxy⟩ := ht
    show (L x : ℝ) - a ≤ ∑ i ∈ J, t i
    have h1 := hJ y hy
    have h2 := sum_ge_card_ne x y t ht01 hxy J
    have h3 : (L y : ℝ) ≤ a := hy
    linarith
  have hsC : s ∈ C := convexHull_min hUC hC hs
  have h4 : (L x : ℝ) - a ≤ ∑ i ∈ J, s i := hsC
  -- Cauchy–Schwarz
  have h5 : (∑ i ∈ J, s i) ^ 2 ≤ (J.card : ℝ) * ∑ i ∈ J, s i ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) s
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using this
  have h6 : ∑ i ∈ J, s i ^ 2 ≤ ∑ i, s i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have h7 : ∑ i ∈ J, s i ≤ Real.sqrt ((J.card : ℝ) * ∑ i ∈ J, s i ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt h5)
  rw [Real.sqrt_mul (Nat.cast_nonneg _)] at h7
  calc (L x : ℝ) - a ≤ ∑ i ∈ J, s i := h4
    _ ≤ Real.sqrt J.card * Real.sqrt (∑ i ∈ J, s i ^ 2) := h7
    _ ≤ Real.sqrt J.card * Real.sqrt (∑ i, s i ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h6) (Real.sqrt_nonneg _)

/-- ENNReal packaging: from a real bound on `V`, get `L x ≤ a + K * f_c`. -/
lemma ennreal_bound {Ω : Type*} {N : ℕ} (L : (Fin N → Ω) → ℕ) (a : ℝ) (ha : 0 < a)
    (x : Fin N → Ω) (A : Set (Fin N → Ω)) (K : ℝ) (hK : 0 < K)
    (hV : ∀ s ∈ TalagrandConc.ConvexHull.V A x, (L x : ℝ) - a ≤ K * Real.sqrt (∑ i, s i ^ 2)) :
    ((L x : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal a + ENNReal.ofReal K * TalagrandConc.ConvexHull.fc A x := by
  have h1 : ((L x : ℕ) : ℝ≥0∞) = ENNReal.ofReal (L x : ℝ) := by simp
  have h2 : (L x : ℝ) ≤ a + max ((L x : ℝ) - a) 0 := by
    have := le_max_left ((L x : ℝ) - a) 0; linarith
  have h3 : ENNReal.ofReal (L x : ℝ) ≤ ENNReal.ofReal a + ENNReal.ofReal (max ((L x : ℝ) - a) 0) := by
    rw [← ENNReal.ofReal_add ha.le (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal h2
  rw [h1]
  refine le_trans h3 (add_le_add le_rfl ?_)
  by_cases hla : (L x : ℝ) - a ≤ 0
  · rw [max_eq_right hla]; simp
  push_neg at hla
  rw [max_eq_left hla.le]
  have hK0 : ENNReal.ofReal K ≠ 0 := by simpa using hK
  have hKt : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [mul_comm, ← ENNReal.div_le_iff hK0 hKt, ← ENNReal.ofReal_div_of_pos hK]
  unfold TalagrandConc.ConvexHull.fc
  refine le_iInf₂ fun s hs => ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ hK]
  have := hV s hs
  linarith [this]

/-- Monotonicity of `t ↦ (t - a)/√t` on `(0, ∞)`. -/
lemma ratio_mono (a w t : ℝ) (ha : 0 < a) (hw : 0 < w) (hwt : w ≤ t) :
    (w - a) / Real.sqrt w ≤ (t - a) / Real.sqrt t := by
  have ht : 0 < t := lt_of_lt_of_le hw hwt
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [sub_div, sub_div, Real.div_sqrt, Real.div_sqrt]
  have e1 : Real.sqrt w ≤ Real.sqrt t := Real.sqrt_le_sqrt hwt
  have e2 : a / Real.sqrt t ≤ a / Real.sqrt w :=
    div_le_div_of_nonneg_left ha.le hsw e1
  linarith

/-- Part (7.1.2) in generic form. -/
lemma lower_bound_fc {Ω : Type*} {N : ℕ} (L : (Fin N → Ω) → ℕ) (a : ℝ) (ha : 0 < a)
    (x : Fin N → Ω) (A : Set (Fin N → Ω))
    (hV : ∀ s ∈ TalagrandConc.ConvexHull.V A x,
      (L x : ℝ) - a ≤ Real.sqrt (L x) * Real.sqrt (∑ i, s i ^ 2)) :
    ∀ v : ℝ, a + v ≤ (L x : ℝ) →
      ENNReal.ofReal (v / Real.sqrt (a + v)) ≤ TalagrandConc.ConvexHull.fc A x := by
  intro v hv
  unfold TalagrandConc.ConvexHull.fc
  refine le_iInf₂ fun s hs => ?_
  apply ENNReal.ofReal_le_ofReal
  by_cases hv0 : v ≤ 0
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hv0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  push_neg at hv0
  have hw : 0 < a + v := by linarith
  have hL : 0 < (L x : ℝ) := lt_of_lt_of_le hw hv
  have h1 : v / Real.sqrt (a + v) = (a + v - a) / Real.sqrt (a + v) := by ring_nf
  rw [h1]
  refine le_trans (ratio_mono a (a + v) (L x) ha hw hv) ?_
  rw [div_le_iff₀ (Real.sqrt_pos.2 hL)]
  have := hV s hs
  linarith

/-! ### Longest increasing subsequence facts -/

lemma lis_bddAbove {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    BddAbove {p : ℕ | ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)} := by
  refine ⟨N, fun p ⟨i, hi, _⟩ => ?_⟩
  simpa using Fintype.card_le_of_injective i hi.injective

lemma lis_nonempty {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    ({p : ℕ | ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)}).Nonempty :=
  ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0⟩

lemma lis_spec {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    ∃ i : Fin (lis x) → Fin N, StrictMono i ∧ Monotone (x ∘ i) :=
  Nat.sSup_mem (lis_nonempty x) (lis_bddAbove x)

lemma le_lis {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) {p : ℕ}
    (i : Fin p → Fin N) (hi : StrictMono i) (hm : Monotone (x ∘ i)) : p ≤ lis x :=
  le_csSup (lis_bddAbove x) ⟨i, hi, hm⟩

/-- `lis` is a configuration function (with the explicit witness set). -/
lemma lis_config {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    ∃ J : Finset (Fin N), J.card = lis x ∧
      ∀ y : Fin N → α, (J.filter fun i => y i = x i).card ≤ lis y := by
  obtain ⟨i, hi, hm⟩ := lis_spec x
  refine ⟨Finset.univ.map ⟨i, hi.injective⟩, by simp, fun y => ?_⟩
  let G := (Finset.univ.map ⟨i, hi.injective⟩).filter (fun k => y k = x k)
  let e := G.orderEmbOfFin rfl
  refine le_lis y e e.strictMono fun k l hkl => ?_
  have hek : e k ∈ G := G.orderEmbOfFin_mem rfl k
  have hel : e l ∈ G := G.orderEmbOfFin_mem rfl l
  obtain ⟨hek1, hek2⟩ := Finset.mem_filter.1 hek
  obtain ⟨hel1, hel2⟩ := Finset.mem_filter.1 hel
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hek1 hel1
  obtain ⟨m, hmk⟩ := hek1
  obtain ⟨m', hml⟩ := hel1
  have hle : e k ≤ e l := e.monotone hkl
  rw [← hmk, ← hml] at hle
  have hmm : m ≤ m' := hi.le_iff_le.1 hle
  show y (e k) ≤ y (e l)
  rw [hek2, hel2, ← hmk, ← hml]
  exact hm hmm

/-- Talagrand (1995), Lemma 7.1.1. -/
theorem lemma_7_1_1_core {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    ((lis x : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal a + TalagrandConc.ConvexHull.fc (levelSet lis a) x * ENNReal.ofReal (Real.sqrt (lis x)) ∧
      ∀ v : ℝ, a + v ≤ (lis x : ℝ) →
        ENNReal.ofReal (v / Real.sqrt (a + v)) ≤ TalagrandConc.ConvexHull.fc (levelSet lis a) x := by
  obtain ⟨J, hJc, hJ⟩ := lis_config x
  have hJ' : ∀ y, y ∈ levelSet lis a →
      (lis x : ℝ) ≤ lis y + ((J.filter fun i => y i ≠ x i).card : ℝ) := by
    intro y _
    have h1 := hJ y
    have h2 := Finset.card_filter_add_card_filter_not (s := J) (fun i => y i = x i)
    rw [hJc] at h2
    have h3 : (lis x : ℝ) = ((J.filter fun i => y i = x i).card : ℝ) +
        ((J.filter fun i => ¬ y i = x i).card : ℝ) := by exact_mod_cast h2.symm
    rw [h3]
    have h4 : ((J.filter fun i => y i = x i).card : ℝ) ≤ lis y := by exact_mod_cast h1
    simp only [ne_eq]
    linarith
  have hV := core_bound lis a x J hJ'
  rw [hJc] at hV
  constructor
  · by_cases hL : (lis x : ℝ) - a ≤ 0
    · have : ((lis x : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal a := by
        rw [show ((lis x : ℕ) : ℝ≥0∞) = ENNReal.ofReal (lis x : ℝ) by simp]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      exact le_trans this le_self_add
    · push_neg at hL
      have hLpos : 0 < (lis x : ℝ) := by linarith
      rw [mul_comm]
      exact ennreal_bound lis a ha x _ _ (Real.sqrt_pos.2 hLpos) hV
  · exact lower_bound_fc lis a ha x _ hV

end TalagrandConc.Subsequences

open TalagrandConc.Subsequences


theorem solution {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    ((lis x : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal a + TalagrandConc.ConvexHull.fc (levelSet lis a) x * ENNReal.ofReal (Real.sqrt (lis x)) ∧
      ∀ v : ℝ, a + v ≤ (lis x : ℝ) →
        ENNReal.ofReal (v / Real.sqrt (a + v)) ≤ TalagrandConc.ConvexHull.fc (levelSet lis a) x := by
  exact lemma_7_1_1_core a ha x
