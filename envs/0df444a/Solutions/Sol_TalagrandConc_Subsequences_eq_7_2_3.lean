-- Prove2me | solution 1 for TalagrandConc.Subsequences.eq_7_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:50:58.011987+00:00
-- url     : https://prove2.me/submissions/02079395-de25-43d6-92de-2f594b8da7f8

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


/-! ### Longest common subsequence facts -/

lemma lcs_bddAbove {α : Type*} {N N' : ℕ} (x : Fin N → α) (y : Fin N' → α) :
    BddAbove {p : ℕ | ∃ i : Fin p → Fin N, ∃ j : Fin p → Fin N',
      StrictMono i ∧ StrictMono j ∧ ∀ l, x (i l) = y (j l)} := by
  refine ⟨N, fun p ⟨i, j, hi, _, _⟩ => ?_⟩
  simpa using Fintype.card_le_of_injective i hi.injective

lemma lcs_nonempty {α : Type*} {N N' : ℕ} (x : Fin N → α) (y : Fin N' → α) :
    ({p : ℕ | ∃ i : Fin p → Fin N, ∃ j : Fin p → Fin N',
      StrictMono i ∧ StrictMono j ∧ ∀ l, x (i l) = y (j l)}).Nonempty :=
  ⟨0, Fin.elim0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩

lemma lcs_spec {α : Type*} {N N' : ℕ} (x : Fin N → α) (y : Fin N' → α) :
    ∃ i : Fin (lcs x y) → Fin N, ∃ j : Fin (lcs x y) → Fin N',
      StrictMono i ∧ StrictMono j ∧ ∀ l, x (i l) = y (j l) :=
  Nat.sSup_mem (lcs_nonempty x y) (lcs_bddAbove x y)

lemma le_lcs {α : Type*} {N N' : ℕ} (x : Fin N → α) (y : Fin N' → α) {p : ℕ}
    (i : Fin p → Fin N) (j : Fin p → Fin N') (hi : StrictMono i) (hj : StrictMono j)
    (h : ∀ l, x (i l) = y (j l)) : p ≤ lcs x y :=
  le_csSup (lcs_bddAbove x y) ⟨i, j, hi, hj, h⟩

lemma castAdd_ne_natAdd {N N' : ℕ} (a : Fin N) (b : Fin N') :
    Fin.castAdd N' a ≠ Fin.natAdd N b := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- `lcsJoint` is a configuration function with a witness set of size `2 L(x)`. -/
lemma lcsJoint_config {α : Type*} [DecidableEq α] {N N' : ℕ} (z : Fin (N + N') → α) :
    ∃ J : Finset (Fin (N + N')), J.card = 2 * lcsJoint z ∧
      ∀ w : Fin (N + N') → α,
        lcsJoint z ≤ lcsJoint w + (J.filter fun k => w k ≠ z k).card := by
  obtain ⟨i, j, hi, hj, hij⟩ := lcs_spec (fun i : Fin N => z (Fin.castAdd N' i))
    (fun j : Fin N' => z (Fin.natAdd N j))
  set p := lcsJoint z with hp
  let f1 : Fin p ↪ Fin (N + N') := ⟨fun l => Fin.castAdd N' (i l),
    (Fin.castAdd_injective N N').comp hi.injective⟩
  let f2 : Fin p ↪ Fin (N + N') := ⟨fun l => Fin.natAdd N (j l),
    (Fin.natAdd_injective N' N).comp hj.injective⟩
  have hdisj : ∀ (A B : Finset (Fin p)), Disjoint (A.map f1) (B.map f2) := by
    intro A B
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_map] at hk1 hk2
    obtain ⟨a, _, rfl⟩ := hk1
    obtain ⟨b, _, hb⟩ := hk2
    exact castAdd_ne_natAdd (i a) (j b) hb.symm
  refine ⟨Finset.univ.map f1 ∪ Finset.univ.map f2, ?_, fun w => ?_⟩
  · rw [Finset.card_union_of_disjoint (hdisj _ _)]
    simp [two_mul]
  -- the good indices
  let good : Fin p → Prop := fun l =>
    w (Fin.castAdd N' (i l)) = z (Fin.castAdd N' (i l)) ∧
      w (Fin.natAdd N (j l)) = z (Fin.natAdd N (j l))
  let G := Finset.univ.filter good
  let e := G.orderEmbOfFin rfl
  have hG : G.card ≤ lcsJoint w := by
    refine le_lcs _ _ (i ∘ e) (j ∘ e) (hi.comp e.strictMono) (hj.comp e.strictMono) fun l => ?_
    have hm : e l ∈ G := G.orderEmbOfFin_mem rfl l
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hm
    simp only [Function.comp]
    rw [h1, h2]
    exact hij (e l)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p))) good
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  let B1 := Finset.univ.filter fun l : Fin p => w (Fin.castAdd N' (i l)) ≠ z (Fin.castAdd N' (i l))
  let B2 := Finset.univ.filter fun l : Fin p => w (Fin.natAdd N (j l)) ≠ z (Fin.natAdd N (j l))
  have hbad : (Finset.univ.filter fun l => ¬ good l).card ≤ B1.card + B2.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le B1 B2)
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, good] at hl
    simp only [B1, B2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsub : B1.map f1 ∪ B2.map f2 ⊆
      (Finset.univ.map f1 ∪ Finset.univ.map f2).filter fun k => w k ≠ z k := by
    intro k hk
    rw [Finset.mem_filter]
    rw [Finset.mem_union, Finset.mem_map, Finset.mem_map] at hk
    rcases hk with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
    · refine ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _ (Finset.mem_univ _)), ?_⟩
      exact (Finset.mem_filter.1 hl).2
    · refine ⟨Finset.mem_union_right _ (Finset.mem_map_of_mem _ (Finset.mem_univ _)), ?_⟩
      exact (Finset.mem_filter.1 hl).2
  have hcard : B1.card + B2.card ≤
      ((Finset.univ.map f1 ∪ Finset.univ.map f2).filter fun k => w k ≠ z k).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint (hdisj _ _), Finset.card_map, Finset.card_map] at this
  have hGc : G.card = (Finset.univ.filter good).card := rfl
  have hp' : p = lcsJoint z := rfl
  omega

/-- Talagrand (1995), Eq. (7.2.3). -/
theorem eq_7_2_3_core {N N' : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin (N + N') → unitInterval) :
    ((lcsJoint x : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal a + ENNReal.ofReal (2 * Real.sqrt 2) * TalagrandConc.ConvexHull.fc (levelSet lcsJoint a) x *
        ENNReal.ofReal (Real.sqrt (lcsJoint x)) := by
  obtain ⟨J, hJc, hJ⟩ := lcsJoint_config x
  have hJ' : ∀ y, y ∈ levelSet lcsJoint a →
      (lcsJoint x : ℝ) ≤ lcsJoint y + ((J.filter fun i => y i ≠ x i).card : ℝ) := by
    intro y _
    exact_mod_cast hJ y
  have hV := core_bound lcsJoint a x J hJ'
  by_cases hL : (lcsJoint x : ℝ) - a ≤ 0
  · have : ((lcsJoint x : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal a := by
      rw [show ((lcsJoint x : ℕ) : ℝ≥0∞) = ENNReal.ofReal (lcsJoint x : ℝ) by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact le_trans this le_self_add
  push_neg at hL
  have hLpos : 0 < (lcsJoint x : ℝ) := by linarith
  have hK : 0 < 2 * Real.sqrt 2 * Real.sqrt (lcsJoint x) := by positivity
  have hV' : ∀ s ∈ TalagrandConc.ConvexHull.V (levelSet lcsJoint a) x,
      (lcsJoint x : ℝ) - a ≤ (2 * Real.sqrt 2 * Real.sqrt (lcsJoint x)) * Real.sqrt (∑ i, s i ^ 2) := by
    intro s hs
    refine le_trans (hV s hs) ?_
    have hJr : (J.card : ℝ) = 2 * (lcsJoint x : ℝ) := by rw [hJc]; push_cast; ring
    rw [hJr, Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 ≤ 2 * Real.sqrt 2 := by
      have := Real.sqrt_nonneg 2; linarith
    have hs0 := Real.sqrt_nonneg (∑ i, s i ^ 2)
    have hl0 := Real.sqrt_nonneg (lcsJoint x : ℝ)
    nlinarith [mul_nonneg hl0 hs0]
  have := ennreal_bound lcsJoint a ha x _ _ hK hV'
  rw [ENNReal.ofReal_mul (by positivity), mul_right_comm] at this
  exact this

end TalagrandConc.Subsequences

open TalagrandConc.Subsequences


theorem solution {N N' : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin (N + N') → unitInterval) :
    ((lcsJoint x : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal a + ENNReal.ofReal (2 * Real.sqrt 2) * TalagrandConc.ConvexHull.fc (levelSet lcsJoint a) x *
        ENNReal.ofReal (Real.sqrt (lcsJoint x)) := by
  exact eq_7_2_3_core a ha x
