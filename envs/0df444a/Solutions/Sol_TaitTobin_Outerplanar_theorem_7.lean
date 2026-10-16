-- Prove2me | solution 1 for TaitTobin.Outerplanar.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T16:35:47.96073+00:00
-- url     : https://prove2.me/submissions/810764b2-44ce-4973-adff-c47fd083e303

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Theorems.Thm_TaitTobin_Outerplanar_B_empty
import Theorems.Thm_TaitTobin_Outerplanar_subgraph_fan_of_universal
set_option autoImplicit false

/-! Part A: spectral helpers and planarity transport (for TaitTobin.Planar.theorem_15). -/

open Matrix in
theorem wk9_transpose {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA

open Matrix in
theorem wk9_parseval {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ y = ∑ j, (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) *
      (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ y) := by
  have := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
  rw [dotProduct_comm x y, ← this]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_comm y]

open Matrix in
theorem wk9_eigdot {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (j : n) (x : n → ℝ) :
    WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ x) =
      hA.eigenvalues j * (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, wk9_transpose hA, dotProduct_comm,
    hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul, dotProduct_comm]

open Matrix in
theorem wk9_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, h⟩ * (x ⬝ᵥ x) := by
  rw [wk9_parseval hA x (A *ᵥ x), wk9_parseval hA x x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [wk9_eigdot]
  have hj : hA.eigenvalues j ≤ hA.eigenvalues₀ ⟨0, h⟩ := by
    unfold Matrix.IsHermitian.eigenvalues
    exact hA.eigenvalues₀_antitone (by rw [Fin.le_def]; exact Nat.zero_le _)
  nlinarith [mul_le_mul_of_nonneg_right hj
    (mul_self_nonneg (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x))]

open Matrix in
theorem wk9_exists {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) :
    ∃ v : n → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = hA.eigenvalues₀ ⟨0, h⟩ • v := by
  obtain ⟨j, hj⟩ : ∃ j : n, j = (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h⟩ :=
    ⟨_, rfl⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · have horth := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal j j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at horth
    simpa using horth
  · rw [hA.mulVec_eigenvectorBasis]
    congr 1
    rw [hj]
    simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

open Matrix in
theorem wk9_quad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ i, ∑ j, (if G.Adj i j then x i * x j else 0) := by
  simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

open Matrix in
theorem wk9_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i : V) :
    (G.adjMatrix ℝ *ᵥ x) i = ∑ j, (if G.Adj i j then x j else 0) := by
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

open Matrix in
theorem wk9_eq {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hsym : Aᵀ = A) (lam : ℝ)
    (H : ∀ y : n → ℝ, y ⬝ᵥ (A *ᵥ y) ≤ lam * (y ⬝ᵥ y)) (x : n → ℝ)
    (hx : x ⬝ᵥ (A *ᵥ x) = lam * (x ⬝ᵥ x)) : A *ᵥ x = lam • x := by
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ x - lam • x := ⟨_, rfl⟩
  have hsymd : ∀ u z : n → ℝ, u ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ u) := by
    intro u z
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hp : w ⬝ᵥ (A *ᵥ x) - lam * (w ⬝ᵥ x) = w ⬝ᵥ w := by
    conv_rhs => rw [hw]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    conv_lhs => rw [hw]
  have hK := H w
  have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have key : ∀ t : ℝ, 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w)) ≤ 0 := by
    intro t
    have h1 := H (x + t • w)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at h1
    rw [hsymd x w, dotProduct_comm x w] at h1
    have e1 : t * (w ⬝ᵥ (A *ᵥ x)) - lam * (t * (w ⬝ᵥ x)) = t * (w ⬝ᵥ w) := by
      rw [← hp]; ring
    nlinarith [h1, hx, e1]
  have hw0 : w ⬝ᵥ w = 0 := by
    by_contra hne
    have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hne)
    obtain ⟨K, hKd⟩ : ∃ K, K = lam * (w ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by linarith
    have h2 := key ((w ⬝ᵥ w) / (K + 1))
    have hK1 : 0 < K + 1 := by linarith
    have e : (w ⬝ᵥ w) / (K + 1) * (K + 1) = w ⬝ᵥ w := div_mul_cancel₀ _ hK1.ne'
    obtain ⟨t, ht⟩ : ∃ t, t = (w ⬝ᵥ w) / (K + 1) := ⟨_, rfl⟩
    rw [← ht] at h2 e
    have htpos : 0 < t := by rw [ht]; positivity
    have : w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w) = -K := by linarith
    rw [this] at h2
    nlinarith [mul_pos htpos hpos, mul_pos htpos htpos]
  have : w = 0 := dotProduct_self_eq_zero.mp hw0
  rw [hw] at this
  exact sub_eq_zero.mp this

section TTSpec

open WangKangXue.SpectralTuran Matrix

-- Quadratic form bound.
open Classical in
theorem tt_Q_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hV : 0 < Fintype.card V) (x : V → ℝ) :
    (∑ i, ∑ j, (if G.Adj i j then x i * x j else 0)) ≤ specRad G * ∑ i, x i * x i := by
  have h := wk9_le (G.isHermitian_adjMatrix ℝ) hV x
  rw [wk9_quad] at h
  unfold specRad
  rw [dif_pos hV]
  simpa [dotProduct] using h

-- A nonnegative eigenvector for the spectral radius, in row form.
open Classical in
theorem tt_nonneg_eig {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hV : 0 < Fintype.card V) :
    ∃ x : V → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i * x i = 1) ∧
      ∀ i, (∑ j, (if G.Adj i j then x j else 0)) = specRad G * x i := by
  obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) hV
  have hsr : specRad G = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hV⟩ := by
    unfold specRad; rw [dif_pos hV]
  set L := (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hV⟩ with hL
  have hLe := wk9_le (G.isHermitian_adjMatrix ℝ) hV
  rw [← hL] at hLe
  obtain ⟨x, hxd⟩ : ∃ x : V → ℝ, x = fun i => |v i| := ⟨_, rfl⟩
  have hx0 : ∀ i, 0 ≤ x i := by intro i; rw [hxd]; exact abs_nonneg _
  have hxx : x ⬝ᵥ x = 1 := by
    rw [← hvv, hxd]
    simp only [dotProduct, abs_mul_abs_self]
  have hq : L ≤ x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
    have : v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) = L := by
      rw [hv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    rw [← this, wk9_quad, wk9_quad]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs
    · rw [hxd]; simp only [← abs_mul]; exact le_abs_self _
    · exact le_rfl
  have heq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = L * (x ⬝ᵥ x) := by
    have := hLe x
    rw [hxx, mul_one] at this ⊢
    linarith
  have hev := wk9_eq _ (wk9_transpose (G.isHermitian_adjMatrix ℝ)) L hLe x heq
  refine ⟨x, hx0, by simpa [dotProduct] using hxx, fun i => ?_⟩
  have := congrFun hev i
  rw [wk9_row] at this
  rw [hsr, this]
  simp

-- Gain from extra edges.
open Classical in
theorem tt_gain {V : Type*} [Fintype V] (G' G'' : SimpleGraph V) (hle : G' ≤ G'')
    (y : V → ℝ) (hy : ∀ i, 0 ≤ y i) (a b : V) (hab : G''.Adj a b) (hab' : ¬ G'.Adj a b) :
    (∑ i, ∑ j, (if G'.Adj i j then y i * y j else 0)) + 2 * (y a * y b) ≤
      ∑ i, ∑ j, (if G''.Adj i j then y i * y j else 0) := by
  set D : V → V → ℝ := fun i j =>
    (if G''.Adj i j then y i * y j else 0) - (if G'.Adj i j then y i * y j else 0) with hD
  have hD0 : ∀ i j, 0 ≤ D i j := by
    intro i j
    simp only [hD]
    by_cases h1 : G'.Adj i j
    · rw [if_pos (hle h1), if_pos h1]; simp
    · rw [if_neg h1]
      split_ifs
      · simpa using mul_nonneg (hy i) (hy j)
      · simp
  have hne : a ≠ b := G''.ne_of_adj hab
  have hrow : ∀ i, D i (if i = a then b else a) ≤ ∑ j, D i j := fun i =>
    Finset.single_le_sum (fun j _ => hD0 i j) (Finset.mem_univ _)
  have h2 : D a b + D b a ≤ ∑ i, D i (if i = a then b else a) := by
    have := Finset.add_le_sum (f := fun i => D i (if i = a then b else a)) (fun i _ => hD0 _ _)
      (Finset.mem_univ a) (Finset.mem_univ b) hne
    simpa [hne.symm] using this
  have h3 : ∑ i, D i (if i = a then b else a) ≤ ∑ i, ∑ j, D i j :=
    Finset.sum_le_sum (fun i _ => hrow i)
  have hDa : D a b = y a * y b := by
    simp only [hD]; rw [if_pos hab, if_neg hab']; ring
  have hDb : D b a = y a * y b := by
    simp only [hD]
    rw [if_pos hab.symm, if_neg (fun h => hab' h.symm)]; ring
  rw [hDa, hDb] at h2
  have hsplit : ∑ i, ∑ j, D i j = (∑ i, ∑ j, (if G''.Adj i j then y i * y j else 0)) -
      ∑ i, ∑ j, (if G'.Adj i j then y i * y j else 0) := by
    simp only [hD, Finset.sum_sub_distrib]
  linarith

end TTSpec


section TTTopo

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_punct_ball (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (Metric.ball p r \ {p}) := by
  have hmem : ∀ d : ℝ × ℝ, |d.1| < r → |d.2| < r → p + d ∈ Metric.ball p r := by
    intro d h1 h2
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
    exact max_lt (by simpa using h1) (by simpa using h2)
  have hr2 : r / 2 < r := by linarith
  have hr2' : |r / 2| < r := by rw [abs_of_pos (by linarith)]; exact hr2
  have hr2'' : |-(r / 2)| < r := by rw [abs_neg]; exact hr2'
  have h0 : |(0:ℝ)| < r := by simpa using hr
  let R : Set (ℝ × ℝ) := Metric.ball p r ∩ (Set.Ioi p.1 ×ˢ (Set.univ : Set ℝ))
  let L : Set (ℝ × ℝ) := Metric.ball p r ∩ (Set.Iio p.1 ×ˢ (Set.univ : Set ℝ))
  let U : Set (ℝ × ℝ) := Metric.ball p r ∩ ((Set.univ : Set ℝ) ×ˢ Set.Ioi p.2)
  let D : Set (ℝ × ℝ) := Metric.ball p r ∩ ((Set.univ : Set ℝ) ×ˢ Set.Iio p.2)
  have cR : Convex ℝ R := (convex_ball p r).inter ((convex_Ioi _).prod convex_univ)
  have cL : Convex ℝ L := (convex_ball p r).inter ((convex_Iio _).prod convex_univ)
  have cU : Convex ℝ U := (convex_ball p r).inter (convex_univ.prod (convex_Ioi _))
  have cD : Convex ℝ D := (convex_ball p r).inter (convex_univ.prod (convex_Iio _))
  have hset : Metric.ball p r \ {p} = ((U ∪ R) ∪ L) ∪ D := by
    ext z
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_prod, Set.mem_Ioi, Set.mem_Iio, Set.mem_univ, true_and, and_true, U, R, L, D]
    constructor
    · rintro ⟨hz, hne⟩
      have : z.1 ≠ p.1 ∨ z.2 ≠ p.2 := by
        by_contra h
        push Not at h
        exact hne (Prod.ext h.1 h.2)
      rcases this with h | h
      · rcases lt_or_gt_of_ne h with h | h
        · exact Or.inl (Or.inr ⟨hz, h⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h⟩))
      · rcases lt_or_gt_of_ne h with h | h
        · exact Or.inr ⟨hz, h⟩
        · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
    · rintro (((⟨hz, h⟩ | ⟨hz, h⟩) | ⟨hz, h⟩) | ⟨hz, h⟩)
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
      · exact ⟨hz, fun e => by rw [e] at h; exact lt_irrefl _ h⟩
  rw [hset]
  have pUR : (p + (r / 2, r / 2)) ∈ U ∩ R := by
    refine ⟨⟨hmem _ hr2' hr2', ?_⟩, ⟨hmem _ hr2' hr2', ?_⟩⟩ <;> simp <;> linarith
  have pUL : (p + (-(r / 2), r / 2)) ∈ U ∩ L := by
    refine ⟨⟨hmem _ hr2'' hr2', ?_⟩, ⟨hmem _ hr2'' hr2', ?_⟩⟩ <;> simp <;> linarith
  have pRD : (p + (r / 2, -(r / 2))) ∈ R ∩ D := by
    refine ⟨⟨hmem _ hr2' hr2'', ?_⟩, ⟨hmem _ hr2' hr2'', ?_⟩⟩ <;> simp <;> linarith
  have h1 : IsPreconnected (U ∪ R) :=
    IsPreconnected.union (p + (r / 2, r / 2)) pUR.1 pUR.2 cU.isPreconnected cR.isPreconnected
  have h2 : IsPreconnected ((U ∪ R) ∪ L) :=
    IsPreconnected.union (p + (-(r / 2), r / 2)) (Or.inl pUL.1) pUL.2 h1 cL.isPreconnected
  exact IsPreconnected.union (p + (r / 2, -(r / 2))) (Or.inl (Or.inr pRD.1)) pRD.2 h2
    cD.isPreconnected

theorem tt_punct (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hc : IsPreconnected U) (p : ℝ × ℝ) :
    IsPreconnected (U \ {p}) := by
  by_cases hp : p ∈ U
  swap
  · rwa [Set.diff_singleton_eq_self hp]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU p hp
  have hB := tt_punct_ball p r hr
  have hB' : Metric.ball p r \ {p} ⊆ U \ {p} := Set.diff_subset_diff_left hball
  have key : ∀ u v : Set (ℝ × ℝ), IsOpen u → IsOpen v → U \ {p} ⊆ u ∪ v →
      (U \ {p}) ∩ (u ∩ v) = ∅ → Metric.ball p r \ {p} ⊆ u → (U \ {p} ⊆ u ∨ U \ {p} ⊆ v) := by
    intro u v hu hv hsub hdisj hBu
    have hpv : p ∉ v := by
      intro hpv
      obtain ⟨δ, hδ, hδv⟩ := Metric.isOpen_iff.1 hv p hpv
      set ρ := min δ r with hρ
      have hρ0 : 0 < ρ := lt_min hδ hr
      have hz0 : (p + (ρ / 2, 0)) ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
        refine max_lt ?_ ?_
        · simp only [Real.norm_eq_abs]; rw [abs_of_pos (by linarith)]; linarith
        · simpa using hρ0
      have hz0v : (p + (ρ / 2, 0)) ∈ v := hδv (Metric.ball_subset_ball (min_le_left _ _) hz0)
      have hz0B : (p + (ρ / 2, 0)) ∈ Metric.ball p r \ {p} := by
        refine ⟨Metric.ball_subset_ball (min_le_right _ _) hz0, ?_⟩
        intro e
        have := congrArg Prod.fst e
        simp at this
        linarith
      have hz0u := hBu hz0B
      have : (p + (ρ / 2, 0)) ∈ (U \ {p}) ∩ (u ∩ v) := ⟨hB' hz0B, hz0u, hz0v⟩
      rw [hdisj] at this
      exact this
    have hcov : U ⊆ (u ∪ Metric.ball p r) ∪ v := by
      intro z hz
      by_cases hzp : z = p
      · subst hzp; exact Or.inl (Or.inr (Metric.mem_ball_self hr))
      · rcases hsub ⟨hz, hzp⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    have hdis : U ∩ ((u ∪ Metric.ball p r) ∩ v) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro z ⟨hz, hzu, hzv⟩
      have hzp : z ≠ p := fun e => hpv (e ▸ hzv)
      have hzs : z ∈ (U \ {p}) := ⟨hz, hzp⟩
      have hzu' : z ∈ u := by
        rcases hzu with h | h
        · exact h
        · exact hBu ⟨h, hzp⟩
      have : z ∈ (U \ {p}) ∩ (u ∩ v) := ⟨hzs, hzu', hzv⟩
      rw [hdisj] at this
      exact this
    rcases isPreconnected_iff_subset_of_disjoint.1 hc _ _ (hu.union Metric.isOpen_ball) hv
      hcov hdis with h | h
    · left
      intro z hz
      rcases h hz.1 with h' | h'
      · exact h'
      · exact hBu ⟨h', hz.2⟩
    · right
      intro z hz
      exact h hz.1
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  have hBsub := (isPreconnected_iff_subset_of_disjoint.1 hB) u v hu hv (hB'.trans hsub)
    (Set.eq_empty_of_subset_empty
      ((Set.inter_subset_inter_left _ hB').trans hdisj.le))
  rcases hBsub with hBu | hBv
  · exact key u v hu hv hsub hdisj hBu
  · have := key v u hv hu (by rwa [Set.union_comm]) (by rwa [Set.inter_comm v u]) hBv
    exact this.symm

end TTTopo

section TTTopo2

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_punct_finite (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hc : IsPreconnected U)
    (F : Set (ℝ × ℝ)) (hF : F.Finite) : IsPreconnected (U \ F) := by
  have key : ∀ s : Finset (ℝ × ℝ), IsPreconnected (U \ (↑s : Set (ℝ × ℝ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hc
    | insert a s ha ih =>
      have hopen : IsOpen (U \ (↑s : Set (ℝ × ℝ))) := hU.sdiff s.finite_toSet.isClosed
      have e : U \ (↑(insert a s) : Set (ℝ × ℝ)) = (U \ ↑s) \ {a} := by
        ext z
        simp only [Finset.coe_insert, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Finset.mem_coe]
        tauto
      rw [e]
      exact tt_punct _ hopen ih a
  obtain ⟨s, rfl⟩ := hF.exists_finset_coe
  exact key s

theorem tt_img_compact {W : Type} [Finite W] {H : SimpleGraph W} (D : PlaneDrawing H) :
    IsCompact (drawingImage D) := by
  unfold drawingImage
  refine (Set.finite_range D.vertex).isCompact.union ?_
  refine isCompact_iUnion (fun a => isCompact_iUnion (fun b => isCompact_iUnion (fun h => ?_)))
  exact isCompact_range (D.arc h).continuous

theorem tt_outer_extend {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V}
    {H : SimpleGraph W} (D : PlaneDrawing H) (D' : PlaneDrawing G) (R : ℝ) (F : Set (ℝ × ℝ))
    (hF : F.Finite) (hFpos : ∀ z ∈ F, R + 1 ≤ z.1 ∧ z.2 = 0)
    (hbd : ∀ z ∈ drawingImage D, ‖z‖ ≤ R)
    (hsub : drawingImage D' ⊆ drawingImage D ∪ F)
    (hD : ∀ a, D.vertex a ∈ closure (outerFace D)) :
    ∀ z ∈ Set.range D.vertex ∪ F, z ∈ closure (outerFace D') := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hz with ⟨a, rfl⟩ | hzF
  · have hza : ‖D.vertex a‖ ≤ R := hbd _ (by unfold drawingImage; exact Or.inl ⟨a, rfl⟩)
    obtain ⟨q, hq, hdq⟩ := Metric.mem_closure_iff.1 (hD a) (min ε 1) (lt_min hε one_pos)
    obtain ⟨hq1, hq2⟩ := hq
    have hdq1 : dist (D.vertex a) q < 1 := lt_of_lt_of_le hdq (min_le_right _ _)
    have hqF : q ∉ F := by
      intro hqF
      have h1 := (hFpos q hqF).1
      have h2 : ‖q‖ ≤ ‖D.vertex a‖ + dist (D.vertex a) q := by
        have : q = D.vertex a + (q - D.vertex a) := by abel
        calc ‖q‖ = ‖D.vertex a + (q - D.vertex a)‖ := by rw [← this]
          _ ≤ ‖D.vertex a‖ + ‖q - D.vertex a‖ := norm_add_le _ _
          _ = ‖D.vertex a‖ + dist (D.vertex a) q := by rw [dist_comm, dist_eq_norm]
      have h3 : q.1 ≤ ‖q‖ := (le_abs_self _).trans (by simpa using norm_fst_le q)
      linarith
    refine ⟨q, ⟨?_, ?_⟩, lt_of_lt_of_le hdq (min_le_left _ _)⟩
    · intro hq'
      rcases hsub hq' with h | h
      · exact hq1 h
      · exact hqF h
    · have hopen : IsOpen (drawingImage D)ᶜ := (tt_img_compact D).isClosed.isOpen_compl
      have hCopen : IsOpen (connectedComponentIn (drawingImage D)ᶜ q) := hopen.connectedComponentIn
      have hCpre : IsPreconnected (connectedComponentIn (drawingImage D)ᶜ q) :=
        isPreconnected_connectedComponentIn
      have hqC : q ∈ connectedComponentIn (drawingImage D)ᶜ q := mem_connectedComponentIn hq1
      have hCF := tt_punct_finite _ hCopen hCpre F hF
      have hsubset : connectedComponentIn (drawingImage D)ᶜ q \ F ⊆
          connectedComponentIn (drawingImage D')ᶜ q := by
        refine hCF.subset_connectedComponentIn ⟨hqC, hqF⟩ ?_
        intro y hy hy'
        rcases hsub hy' with h | h
        · exact connectedComponentIn_subset _ _ hy.1 h
        · exact hy.2 h
      intro hbdd
      apply hq2
      have h1 : Bornology.IsBounded (connectedComponentIn (drawingImage D)ᶜ q \ F) :=
        hbdd.subset hsubset
      have hFb : Bornology.IsBounded F := hF.isBounded
      refine (h1.union hFb).subset ?_
      intro y hy
      by_cases hyF : y ∈ F
      · exact Or.inr hyF
      · exact Or.inl ⟨hy, hyF⟩
  · have hz := hFpos z hzF
    let b : ℝ × ℝ := (z.1, ε / 2)
    let Q : Set (ℝ × ℝ) := Set.Ioi R ×ˢ Set.Ioi (0 : ℝ)
    have hbQ : b ∈ Q := ⟨by simp [b]; linarith [hz.1], by simp [b]; linarith⟩
    have hQsub : Q ⊆ (drawingImage D')ᶜ := by
      intro y hy hy'
      rcases hsub hy' with h | h
      · have h1 := hbd y h
        have h2 : y.1 ≤ ‖y‖ := (le_abs_self _).trans (by simpa using norm_fst_le y)
        have h3 : R < y.1 := hy.1
        linarith
      · have := (hFpos y h).2
        have h4 : 0 < y.2 := hy.2
        linarith
    have hQpre : IsPreconnected Q := ((convex_Ioi R).prod (convex_Ioi (0:ℝ))).isPreconnected
    refine ⟨b, ⟨hQsub hbQ, ?_⟩, ?_⟩
    · intro hbdd
      have h1 : Bornology.IsBounded Q :=
        hbdd.subset (hQpre.subset_connectedComponentIn hbQ hQsub)
      obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.1 h1)
      have hmem : (max (C + 1) (R + 1), (1 : ℝ)) ∈ Q :=
        ⟨show R < max (C + 1) (R + 1) from lt_max_of_lt_right (by linarith), show (0:ℝ) < 1 from one_pos⟩
      have := hC _ hmem
      have h2 : max (C + 1) (R + 1) ≤ ‖(max (C + 1) (R + 1), (1 : ℝ))‖ :=
        (le_abs_self _).trans (by simpa using norm_fst_le (max (C + 1) (R + 1), (1 : ℝ)))
      have h3 : C + 1 ≤ max (C + 1) (R + 1) := le_max_left _ _
      linarith
    · rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · simp [b, hε]
      · simp only [b, Real.dist_eq, hz.2]
        rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
        linarith

end TTTopo2


section TTPull

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_drawing_bounded {W : Type} [Finite W] {H : SimpleGraph W} (D : PlaneDrawing H) :
    ∃ R : ℝ, (∀ a, ‖D.vertex a‖ ≤ R) ∧
      ∀ (a b : W) (h : H.Adj a b) (t : unitInterval), ‖D.arc h t‖ ≤ R := by
  have hK : IsCompact (Set.range D.vertex ∪
      ⋃ (a : W) (b : W) (h : H.Adj a b), Set.range (D.arc h)) := by
    refine (Set.finite_range D.vertex).isCompact.union ?_
    refine isCompact_iUnion (fun a => isCompact_iUnion (fun b => isCompact_iUnion (fun h => ?_)))
    exact isCompact_range (D.arc h).continuous
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun a => ?_, fun a b h t => ?_⟩
  · have := hR (Set.mem_union_left _ (Set.mem_range_self a))
    simpa using this
  · have := hR (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b,
      Set.mem_iUnion.2 ⟨h, Set.mem_range_self t⟩⟩⟩))
    simpa using this

open Classical in
theorem tt_pull_draw {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (g : V → W) (S : Set V) (hinj : Set.InjOn g S)
    (hS : ∀ x y, G.Adj x y → x ∈ S)
    (hadj : ∀ x y, G.Adj x y → H.Adj (g x) (g y)) (D : PlaneDrawing H) (R : ℝ)
    (hRv : ∀ a, ‖D.vertex a‖ ≤ R) (hRa : ∀ (a b : W) (h : H.Adj a b) (t : unitInterval),
      ‖D.arc h t‖ ≤ R) :
    ∃ D' : PlaneDrawing G, (∀ x, x ∈ S → D'.vertex x = D.vertex (g x)) ∧
      (∃ far : V → ℝ × ℝ, (∀ x, R + 1 ≤ (far x).1 ∧ (far x).2 = 0) ∧
        ∀ x, x ∉ S → D'.vertex x = far x) ∧
      ∀ (x y : V) (h : G.Adj x y) (t : unitInterval), D'.arc h t = D.arc (hadj x y h) t := by
  set e := Finite.equivFin V
  have hfar : ∀ x : V, R < ‖((R + 1 + ((e x : ℕ) : ℝ), (0:ℝ)) : ℝ × ℝ)‖ := by
    intro x
    have h1 := norm_fst_le ((R + 1 + ((e x : ℕ) : ℝ), (0:ℝ)) : ℝ × ℝ)
    have h2 : R + 1 + ((e x : ℕ) : ℝ) ≤ ‖R + 1 + ((e x : ℕ) : ℝ)‖ := by
      rw [Real.norm_eq_abs]; exact le_abs_self _
    have h3 : (0:ℝ) ≤ ((e x : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only at h1
    linarith
  refine ⟨{
    vertex := fun x => if x ∈ S then D.vertex (g x) else (R + 1 + ((e x : ℕ) : ℝ), 0)
    vertex_injective := ?_
    arc := fun {x y} h => (D.arc (hadj x y h)).cast (if_pos (hS x y h)) (if_pos (hS y x h.symm))
    arc_injective := ?_
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }, ?_, ⟨fun x => (R + 1 + ((e x : ℕ) : ℝ), 0), ?_, ?_⟩, ?_⟩
  · intro x y hxy
    simp only at hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · rw [if_pos hx, if_pos hy] at hxy
      exact hinj hx hy (D.vertex_injective hxy)
    · rw [if_pos hx, if_neg hy] at hxy
      have := hRv (g x)
      rw [hxy] at this
      exact absurd this (not_le.2 (hfar y))
    · rw [if_neg hx, if_pos hy] at hxy
      have := hRv (g y)
      rw [← hxy] at this
      exact absurd this (not_le.2 (hfar x))
    · rw [if_neg hx, if_neg hy] at hxy
      have h1 := congrArg Prod.fst hxy
      simp only [add_right_inj, Nat.cast_inj] at h1
      exact e.injective (Fin.ext h1)
  · intro x y h
    simpa [Path.cast_coe] using D.arc_injective (hadj x y h)
  · intro x y h
    apply Path.ext
    funext t
    have := congrArg (fun γ : Path _ _ => γ t) (D.arc_reverse (hadj x y h))
    simpa [Path.cast_coe] using this
  · intro x y h t z hz
    simp only [Path.cast_coe] at hz
    by_cases hzS : z ∈ S
    · rw [if_pos hzS] at hz
      rcases D.arc_avoids_vertices (hadj x y h) t (g z) hz with h1 | h1
      · exact Or.inl (hinj hzS (hS x y h) h1)
      · exact Or.inr (hinj hzS (hS y x h.symm) h1)
    · rw [if_neg hzS] at hz
      have := hRa _ _ (hadj x y h) t
      rw [hz] at this
      exact absurd this (not_le.2 (hfar z))
  · intro x y x' y' h k s t hst
    simp only [Path.cast_coe] at hst
    rcases D.arcs_meet_only_at_endpoints (hadj x y h) (hadj x' y' k) s t hst with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
    · exact Or.inl ⟨hinj (hS x y h) (hS x' y' k) h1,
        hinj (hS y x h.symm) (hS y' x' k.symm) h2⟩
    · exact Or.inr (Or.inl ⟨hinj (hS x y h) (hS y' x' k.symm) h1,
        hinj (hS y x h.symm) (hS x' y' k) h2⟩)
    · exact Or.inr (Or.inr h3)
  · intro x hx
    simp [hx]
  · intro x
    constructor
    · simp only
      have : (0:ℝ) ≤ ((e x : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · rfl
  · intro x hx
    simp [hx]
  · intro x y h t
    simp [Path.cast_coe]

open Classical in
theorem tt_outer_pull {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (g : V → W) (S : Set V) (hinj : Set.InjOn g S)
    (hS : ∀ x y, G.Adj x y → x ∈ S)
    (hadj : ∀ x y, G.Adj x y → H.Adj (g x) (g y)) (hH : IsOuterplanar H) :
    IsOuterplanar G := by
  obtain ⟨D, hD⟩ := hH
  obtain ⟨R, hRv, hRa⟩ := tt_drawing_bounded D
  obtain ⟨D', hv1, ⟨far, hfar, hv2⟩, ha⟩ := tt_pull_draw G H g S hinj hS hadj D R hRv hRa
  have hbd : ∀ z ∈ drawingImage D, ‖z‖ ≤ R := by
    intro z hz
    rcases hz with ⟨a, rfl⟩ | hz
    · exact hRv a
    · obtain ⟨a, b, h, t, rfl⟩ : ∃ a b, ∃ h : H.Adj a b, ∃ t, D.arc h t = z := by
        simp only [Set.mem_iUnion, Set.mem_range] at hz
        obtain ⟨a, b, h, t, ht⟩ := hz
        exact ⟨a, b, h, t, ht⟩
      exact hRa a b h t
  have hFfin : (Set.range far).Finite := Set.finite_range far
  have hsub : drawingImage D' ⊆ drawingImage D ∪ Set.range far := by
    intro z hz
    rcases hz with ⟨x, rfl⟩ | hz
    · by_cases hx : x ∈ S
      · rw [hv1 x hx]
        exact Or.inl (Or.inl ⟨g x, rfl⟩)
      · rw [hv2 x hx]
        exact Or.inr ⟨x, rfl⟩
    · obtain ⟨a, b, h, t, rfl⟩ : ∃ a b, ∃ h : G.Adj a b, ∃ t, D'.arc h t = z := by
        simp only [Set.mem_iUnion, Set.mem_range] at hz
        obtain ⟨a, b, h, t, ht⟩ := hz
        exact ⟨a, b, h, t, ht⟩
      rw [ha]
      refine Or.inl (Or.inr ?_)
      simp only [Set.mem_iUnion, Set.mem_range]
      exact ⟨_, _, hadj a b h, t, rfl⟩
  have key := tt_outer_extend D D' R (Set.range far) hFfin
    (fun z ⟨x, hx⟩ => hx ▸ hfar x) hbd hsub hD
  refine ⟨D', fun x => ?_⟩
  apply key
  by_cases hx : x ∈ S
  · rw [hv1 x hx]; exact Or.inl ⟨g x, rfl⟩
  · rw [hv2 x hx]; exact Or.inr ⟨x, rfl⟩

end TTPull


section TTFanGeom

-- Sorted chord geometry on the parabola y = x^2.
theorem tt_L1 (a b c d s t : ℝ) (hab : a < b) (hcd : c < d) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hX : a + s * (b - a) = c + t * (d - c))
    (hY : a ^ 2 + s * (b ^ 2 - a ^ 2) = c ^ 2 + t * (d ^ 2 - c ^ 2)) :
    (a = c ∧ b = d) ∨ (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := by
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = a + s * (b - a) := ⟨_, rfl⟩
  have hXc : X = c + t * (d - c) := by rw [hXd]; exact hX
  have haX : a < X := by rw [hXd]; nlinarith
  have hXb : X < b := by rw [hXd]; nlinarith
  have hcX : c < X := by rw [hXc]; nlinarith
  have hXd' : X < d := by rw [hXc]; nlinarith
  have h1 : (X - a) * (b - X) = (a ^ 2 + s * (b ^ 2 - a ^ 2)) - X ^ 2 := by
    rw [hXd]; ring
  have h2 : (X - c) * (d - X) = (c ^ 2 + t * (d ^ 2 - c ^ 2)) - X ^ 2 := by
    rw [hXc]; ring
  have hf : (X - a) * (b - X) = (X - c) * (d - X) := by rw [h1, h2, hY]
  -- alpha = a + b - c - d
  have hell : (a + b - c - d) * X = a * b - c * d := by nlinarith [hf]
  have hA : (c - a) * (b - c) = (a + b - c - d) * (c - X) := by
    have : (c - a) * (b - c) = (a + b - c - d) * c - (a * b - c * d) := by ring
    rw [this, ← hell]; ring
  have hB : (d - a) * (b - d) = (a + b - c - d) * (d - X) := by
    have : (d - a) * (b - d) = (a + b - c - d) * d - (a * b - c * d) := by ring
    rw [this, ← hell]; ring
  by_cases hα : a + b - c - d = 0
  · rw [hα, zero_mul] at hA hB
    left
    have hc : c = a ∨ c = b := by
      rcases mul_eq_zero.1 hA with h | h
      · left; linarith
      · right; linarith
    have hd : d = a ∨ d = b := by
      rcases mul_eq_zero.1 hB with h | h
      · left; linarith
      · right; linarith
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exfalso; linarith
    · exact ⟨hc.symm, hd.symm⟩
    · exfalso; linarith
    · exfalso; linarith
  · have hneg : ((c - a) * (b - c)) * ((d - a) * (b - d)) < 0 := by
      rw [hA, hB]
      have : (a + b - c - d) * (c - X) * ((a + b - c - d) * (d - X)) =
          (a + b - c - d) ^ 2 * ((c - X) * (d - X)) := by ring
      rw [this]
      have hp : 0 < (a + b - c - d) ^ 2 := by positivity
      have hq : (c - X) * (d - X) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      exact mul_neg_of_pos_of_neg hp hq
    rcases mul_neg_iff.1 hneg with ⟨hApos, hBneg⟩ | ⟨hAneg, hBpos⟩
    · right; left
      have h1 : a < c ∧ c < b := by
        rcases mul_pos_iff.1 hApos with ⟨x, y⟩ | ⟨x, y⟩
        · exact ⟨by linarith, by linarith⟩
        · exfalso; linarith
      refine ⟨h1.1, h1.2, ?_⟩
      by_contra hcon
      push Not at hcon
      have : 0 ≤ (d - a) * (b - d) := mul_nonneg (by linarith) (by linarith)
      linarith
    · right; right
      have h1 : a < d ∧ d < b := by
        rcases mul_pos_iff.1 hBpos with ⟨x, y⟩ | ⟨x, y⟩
        · exact ⟨by linarith, by linarith⟩
        · exfalso; linarith
      refine ⟨?_, h1.1, h1.2⟩
      by_contra hcon
      push Not at hcon
      have : 0 ≤ (c - a) * (b - c) := mul_nonneg (by linarith) (by linarith)
      linarith

end TTFanGeom

section TTFan

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_L2 (p q r u s t : ℝ) (hpq : p ≠ q) (hru : r ≠ u) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hX : p + s * (q - p) = r + t * (u - r))
    (hY : p ^ 2 + s * (q ^ 2 - p ^ 2) = r ^ 2 + t * (u ^ 2 - r ^ 2)) :
    (p = r ∧ q = u) ∨ (p = u ∧ q = r) ∨
    (min p q < min r u ∧ min r u < max p q ∧ max p q < max r u) ∨
    (min r u < min p q ∧ min p q < max r u ∧ max r u < max p q) := by
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hru with h2 | h2
  · rcases tt_L1 p q r u s t h1 h2 hs0 hs1 ht0 ht1 hX hY with ⟨e1, e2⟩ | h | h
    · exact Or.inl ⟨e1, e2⟩
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 p q u r s (1 - t) h1 h2 hs0 hs1 (by linarith) (by linarith)
      (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inr (Or.inl ⟨e1, e2⟩)
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 q p r u (1 - s) t h1 h2 (by linarith) (by linarith) ht0 ht1
      (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inr (Or.inl ⟨e2, e1⟩)
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 q p u r (1 - s) (1 - t) h1 h2 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inl ⟨e2, e1⟩
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inr h))

theorem tt_inter_nat (n1 n1' n2 n2' : ℕ)
    (h1 : n1 ≠ n1' ∧ (n1 = 0 ∨ n1' = 0 ∨ n1 + 1 = n1' ∨ n1' + 1 = n1))
    (h2 : n2 ≠ n2' ∧ (n2 = 0 ∨ n2' = 0 ∨ n2 + 1 = n2' ∨ n2' + 1 = n2)) :
    ¬ (min (n1 : ℝ) n1' < min (n2 : ℝ) n2' ∧ min (n2 : ℝ) n2' < max (n1 : ℝ) n1' ∧
        max (n1 : ℝ) n1' < max (n2 : ℝ) n2') ∧
    ¬ (min (n2 : ℝ) n2' < min (n1 : ℝ) n1' ∧ min (n1 : ℝ) n1' < max (n2 : ℝ) n2' ∧
        max (n2 : ℝ) n2' < max (n1 : ℝ) n1') := by
  simp only [← Nat.cast_min, ← Nat.cast_max, Nat.cast_lt]
  omega

/-- The point of the parabola `y = x²` with abscissa `t`. -/
def ttQ (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

/-- The straight segment from `p` to `q` as a path. -/
def ttSeg (p q : ℝ × ℝ) : Path p q where
  toFun t := p + (t : ℝ) • (q - p)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem ttSeg_apply (p q : ℝ × ℝ) (t : unitInterval) :
    ttSeg p q t = p + (t : ℝ) • (q - p) := rfl

/-- Abscissa of a fan vertex: the hub is at `0`, path vertex `b` at `b + 1`. -/
def ttTau {m : ℕ} : Fin 1 ⊕ Fin m → ℕ
  | Sum.inl _ => 0
  | Sum.inr b => (b : ℕ) + 1

def ttVx {m : ℕ} (v : Fin 1 ⊕ Fin m) : ℝ × ℝ := ttQ ((ttTau v : ℕ) : ℝ)

theorem tt_tau_inj {m : ℕ} : Function.Injective (ttTau (m := m)) := by
  intro v w h
  rcases v with a | b <;> rcases w with c | d
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp [ttTau] at h
  · simp [ttTau] at h
  · simp only [ttTau, add_left_inj] at h
    exact congrArg Sum.inr (Fin.ext h)

theorem tt_vx_inj {m : ℕ} : Function.Injective (ttVx (m := m)) := by
  intro v w h
  apply tt_tau_inj
  have := congrArg Prod.fst h
  simp only [ttVx, ttQ] at this
  exact_mod_cast this

theorem tt_fan_adj {m : ℕ} {v w : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w) :
    ttTau v ≠ ttTau w ∧ (ttTau v = 0 ∨ ttTau w = 0 ∨ ttTau v + 1 = ttTau w ∨
      ttTau w + 1 = ttTau v) := by
  rcases v with a | b <;> rcases w with c | d
  · have h' : (⊤ : SimpleGraph (Fin 1)).Adj a c := h
    exact absurd (Subsingleton.elim a c) h'.ne
  · exact ⟨by simp [ttTau], Or.inl rfl⟩
  · exact ⟨by simp [ttTau], Or.inr (Or.inl rfl)⟩
  · have h' : (SimpleGraph.pathGraph m).Adj b d := h
    rw [SimpleGraph.pathGraph_adj] at h'
    simp only [ttTau]
    omega

theorem tt_unit_cases (s : unitInterval) : s = 0 ∨ s = 1 ∨ (0 < (s : ℝ) ∧ (s : ℝ) < 1) := by
  rcases eq_or_lt_of_le s.2.1 with h | h
  · left; exact Subtype.ext h.symm
  rcases eq_or_lt_of_le s.2.2 with h' | h'
  · right; left; exact Subtype.ext h'
  · right; right; exact ⟨h, h'⟩

theorem tt_seg_fst (a b : ℝ) (t : unitInterval) :
    (ttSeg (ttQ a) (ttQ b) t).1 = a + (t : ℝ) * (b - a) := by
  rw [ttSeg_apply]; simp [ttQ]

theorem tt_seg_snd (a b : ℝ) (t : unitInterval) :
    (ttSeg (ttQ a) (ttQ b) t).2 = a ^ 2 + (t : ℝ) * (b ^ 2 - a ^ 2) := by
  rw [ttSeg_apply]; simp [ttQ]

theorem tt_inside (p q z t : ℝ) (hpq : p ≠ q) (ht0 : 0 < t) (ht1 : t < 1)
    (hx : p + t * (q - p) = z) (hy : p ^ 2 + t * (q ^ 2 - p ^ 2) = z ^ 2) : False := by
  have h1 : t * (1 - t) * (q - p) ^ 2 = 0 := by
    rw [← hx] at hy
    nlinarith [hy]
  have hne : q - p ≠ 0 := sub_ne_zero.2 hpq.symm
  have h2 : 0 < t * (1 - t) * (q - p) ^ 2 := by
    have : 0 < 1 - t := by linarith
    positivity
  linarith

theorem tt_seg_above (a b : ℝ) (t : unitInterval) :
    ((ttSeg (ttQ a) (ttQ b) t).1) ^ 2 ≤ (ttSeg (ttQ a) (ttQ b) t).2 := by
  rw [tt_seg_fst, tt_seg_snd]
  have h0 : 0 ≤ (t : ℝ) := t.2.1
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (b - a),
    mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) (sq_nonneg (b - a))]

end TTFan

section TTFanDraw

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_vx_fst {m : ℕ} (z : Fin 1 ⊕ Fin m) : (ttVx z).1 = ((ttTau z : ℕ) : ℝ) := rfl
theorem tt_vx_snd {m : ℕ} (z : Fin 1 ⊕ Fin m) : (ttVx z).2 = ((ttTau z : ℕ) : ℝ) ^ 2 := rfl

theorem tt_segV_fst {m : ℕ} (v w : Fin 1 ⊕ Fin m) (t : unitInterval) :
    (ttSeg (ttVx v) (ttVx w) t).1 =
      ((ttTau v : ℕ) : ℝ) + (t : ℝ) * (((ttTau w : ℕ) : ℝ) - ((ttTau v : ℕ) : ℝ)) :=
  tt_seg_fst _ _ t

theorem tt_segV_snd {m : ℕ} (v w : Fin 1 ⊕ Fin m) (t : unitInterval) :
    (ttSeg (ttVx v) (ttVx w) t).2 =
      ((ttTau v : ℕ) : ℝ) ^ 2 + (t : ℝ) * (((ttTau w : ℕ) : ℝ) ^ 2 - ((ttTau v : ℕ) : ℝ) ^ 2) :=
  tt_seg_snd _ _ t

theorem tt_seg_inj (p q : ℝ × ℝ) (hne : p ≠ q) : Function.Injective (ttSeg p q) := by
  intro s t hst
  simp only [ttSeg_apply, add_right_inj] at hst
  exact Subtype.ext (smul_left_injective ℝ (sub_ne_zero.2 hne.symm) hst)

theorem tt_not_vertex_inside {m : ℕ} {x y : Fin 1 ⊕ Fin m}
    (k : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj x y)
    (z : Fin 1 ⊕ Fin m) (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ttSeg (ttVx x) (ttVx y) t ≠ ttVx z := by
  intro hz
  obtain ⟨hxy, -⟩ := tt_fan_adj k
  have hpq : ((ttTau x : ℕ) : ℝ) ≠ ((ttTau y : ℕ) : ℝ) := by exact_mod_cast hxy
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  rw [tt_segV_fst, tt_vx_fst] at hx
  rw [tt_segV_snd, tt_vx_snd] at hy
  exact tt_inside _ _ _ (t : ℝ) hpq ht0 ht1 hx hy

theorem tt_avoid {m : ℕ} {v w : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w)
    (t : unitInterval) (z : Fin 1 ⊕ Fin m) (hz : ttSeg (ttVx v) (ttVx w) t = ttVx z) :
    z = v ∨ z = w := by
  rcases tt_unit_cases t with rfl | rfl | ⟨h0, h1⟩
  · left
    rw [Path.source] at hz
    exact (tt_vx_inj hz).symm
  · right
    rw [Path.target] at hz
    exact (tt_vx_inj hz).symm
  · exact absurd hz (tt_not_vertex_inside h z t h0 h1)

theorem tt_meet {m : ℕ} {v w x y : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w)
    (k : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj x y)
    (s t : unitInterval)
    (hst : ttSeg (ttVx v) (ttVx w) s = ttSeg (ttVx x) (ttVx y) t) :
    (v = x ∧ w = y) ∨ (v = y ∧ w = x) ∨ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) := by
  have hX := congrArg Prod.fst hst
  have hY := congrArg Prod.snd hst
  rw [tt_segV_fst, tt_segV_fst] at hX
  rw [tt_segV_snd, tt_segV_snd] at hY
  obtain ⟨hvw, hvw'⟩ := tt_fan_adj h
  obtain ⟨hxy, hxy'⟩ := tt_fan_adj k
  have hpq : ((ttTau v : ℕ) : ℝ) ≠ ((ttTau w : ℕ) : ℝ) := by exact_mod_cast hvw
  have hru : ((ttTau x : ℕ) : ℝ) ≠ ((ttTau y : ℕ) : ℝ) := by exact_mod_cast hxy
  rcases tt_unit_cases s with hs | hs | ⟨hs0, hs1⟩ <;>
    rcases tt_unit_cases t with ht | ht | ⟨ht0, ht1⟩
  · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inl ht⟩)
  · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inr ht⟩)
  · exfalso
    have e : ttSeg (ttVx v) (ttVx w) s = ttVx v := by rw [hs]; exact Path.source _
    exact tt_not_vertex_inside k v t ht0 ht1 (hst.symm.trans e)
  · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inl ht⟩)
  · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inr ht⟩)
  · exfalso
    have e : ttSeg (ttVx v) (ttVx w) s = ttVx w := by rw [hs]; exact Path.target _
    exact tt_not_vertex_inside k w t ht0 ht1 (hst.symm.trans e)
  · exfalso
    have e : ttSeg (ttVx x) (ttVx y) t = ttVx x := by rw [ht]; exact Path.source _
    exact tt_not_vertex_inside h x s hs0 hs1 (hst.trans e)
  · exfalso
    have e : ttSeg (ttVx x) (ttVx y) t = ttVx y := by rw [ht]; exact Path.target _
    exact tt_not_vertex_inside h y s hs0 hs1 (hst.trans e)
  · rcases tt_L2 _ _ _ _ (s : ℝ) (t : ℝ) hpq hru hs0 hs1 ht0 ht1 hX hY with
      ⟨e1, e2⟩ | ⟨e1, e2⟩ | h3 | h3
    · exact Or.inl ⟨tt_tau_inj (by exact_mod_cast e1), tt_tau_inj (by exact_mod_cast e2)⟩
    · exact Or.inr (Or.inl ⟨tt_tau_inj (by exact_mod_cast e1), tt_tau_inj (by exact_mod_cast e2)⟩)
    · exact absurd h3 (tt_inter_nat _ _ _ _ ⟨hvw, hvw'⟩ ⟨hxy, hxy'⟩).1
    · exact absurd h3 (tt_inter_nat _ _ _ _ ⟨hvw, hvw'⟩ ⟨hxy, hxy'⟩).2

noncomputable def ttFanDraw (m : ℕ) :
    PlaneDrawing (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)) where
  vertex := ttVx
  vertex_injective := tt_vx_inj
  arc := fun {v w} _ => ttSeg (ttVx v) (ttVx w)
  arc_injective := fun {v w} h =>
    tt_seg_inj _ _ (fun e => (SimpleGraph.ne_of_adj _ h) (tt_vx_inj e))
  arc_reverse := by
    intro v w h
    apply Path.ext
    funext t
    show ttSeg (ttVx w) (ttVx v) t = ttSeg (ttVx v) (ttVx w) (unitInterval.symm t)
    rw [ttSeg_apply, ttSeg_apply, unitInterval.coe_symm_eq]
    ext <;> simp <;> ring
  arc_avoids_vertices := fun {v w} h t z hz => tt_avoid h t z hz
  arcs_meet_only_at_endpoints := fun {v w x y} h k s t hst => tt_meet h k s t hst

theorem tt_fan_above {m : ℕ} (z : ℝ × ℝ) (hz : z ∈ drawingImage (ttFanDraw m)) :
    z.1 ^ 2 ≤ z.2 := by
  rcases hz with ⟨a, rfl⟩ | hz
  · exact le_of_eq (by simp [ttFanDraw, ttVx, ttQ])
  · simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨a, b, h, t, rfl⟩ := hz
    exact tt_seg_above _ _ t

theorem tt_fan_outer (m : ℕ) :
    IsOuterplanar (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)) := by
  refine ⟨ttFanDraw m, fun v => ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t0 : ℝ := ((ttTau v : ℕ) : ℝ) with ht0
  set b : ℝ × ℝ := (t0, t0 ^ 2 - ε / 2) with hb
  let Ray : Set (ℝ × ℝ) := ({t0} : Set ℝ) ×ˢ Set.Iic (t0 ^ 2 - ε / 2)
  have hbRay : b ∈ Ray := ⟨rfl, Set.mem_Iic.2 le_rfl⟩
  have hRsub : Ray ⊆ (drawingImage (ttFanDraw m))ᶜ := by
    intro z hz hz'
    have h1 := tt_fan_above z hz'
    have h2 : z.1 = t0 := hz.1
    have h3 : z.2 ≤ t0 ^ 2 - ε / 2 := hz.2
    rw [h2] at h1
    linarith
  have hRpre : IsPreconnected Ray := (convex_singleton t0 |>.prod (convex_Iic _)).isPreconnected
  refine ⟨b, ⟨hRsub hbRay, ?_⟩, ?_⟩
  · intro hbdd
    have h1 : Bornology.IsBounded Ray :=
      hbdd.subset (hRpre.subset_connectedComponentIn hbRay hRsub)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h1
    have hmem : (t0, min (t0 ^ 2 - ε / 2) (-C - 1)) ∈ Ray :=
      ⟨rfl, Set.mem_Iic.2 (min_le_left _ _)⟩
    have := hC _ hmem
    have h2 : |min (t0 ^ 2 - ε / 2) (-C - 1)| ≤ ‖(t0, min (t0 ^ 2 - ε / 2) (-C - 1))‖ := by
      simpa using norm_snd_le (t0, min (t0 ^ 2 - ε / 2) (-C - 1))
    have h3 : min (t0 ^ 2 - ε / 2) (-C - 1) ≤ -C - 1 := min_le_right _ _
    have h4 := neg_abs_le (min (t0 ^ 2 - ε / 2) (-C - 1))
    linarith
  · rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · simp [hb, ttFanDraw, ttVx, ttQ, ht0, hε]
    · simp only [hb, ttFanDraw, ttVx, ttQ, Real.dist_eq, ht0]
      rw [show ((ttTau v : ℕ) : ℝ) ^ 2 - (((ttTau v : ℕ) : ℝ) ^ 2 - ε / 2) = ε / 2 by ring,
        abs_of_pos (by linarith)]
      linarith

end TTFanDraw

section TTGlue

open WangKangXue.SpectralTuran Matrix RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

open Matrix in
theorem wkx_quad_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (G'.adjMatrix ℝ *ᵥ (v ∘ e.symm)) = v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) := by
  rw [wk9_quad, wk9_quad]
  symm
  refine Fintype.sum_equiv e.toEquiv _ _ (fun i => ?_)
  refine Fintype.sum_equiv e.toEquiv _ _ (fun j => ?_)
  have h : G'.Adj (e i) (e j) ↔ G.Adj i j := e.map_adj_iff
  by_cases hij : G.Adj i j
  · simp [Function.comp, hij, h.2 hij]
  · simp [hij, mt h.1 hij]

open Matrix in
theorem wkx_dot_iso {V V' : Type*} [Fintype V] [Fintype V'] (e : V ≃ V') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = v ⬝ᵥ v := by
  simp only [dotProduct]
  symm
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

open Matrix in
theorem wkx_specRad_le_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G ≤ specRad G' := by
  classical
  unfold specRad
  by_cases h : 0 < Fintype.card V
  · have h' : 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_pos h, dif_pos h']
    obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) h
    have hle := wk9_le (G'.isHermitian_adjMatrix ℝ) h' (v ∘ e.symm)
    have h2 : (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = 1 := by
      rw [show (v ∘ e.symm) = v ∘ e.toEquiv.symm from rfl, wkx_dot_iso, hvv]
    rw [wkx_quad_iso e v, h2, hv, dotProduct_smul, smul_eq_mul, hvv] at hle
    simpa using hle
  · have h' : ¬ 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_neg h, dif_neg h']

theorem wkx_specRad_eq_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G = specRad G' :=
  le_antisymm (wkx_specRad_le_of_iso e) (wkx_specRad_le_of_iso e.symm)

-- Quadratic form from the row equations.
open Classical in
theorem tt_Q_of_row {V : Type*} [Fintype V] (G : SimpleGraph V) (y : V → ℝ) (μ : ℝ)
    (hrow : ∀ i, (∑ j, if G.Adj i j then y j else 0) = μ * y i) :
    (∑ i, ∑ j, (if G.Adj i j then y i * y j else 0)) = μ * ∑ i, y i * y i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (∑ j, (if G.Adj i j then y i * y j else 0)) =
      y i * ∑ j, (if G.Adj i j then y j else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  rw [this, hrow i]
  ring

-- Row form gives the matrix eigen-equation.
open Classical in
theorem tt_mulVec_of_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (y : V → ℝ) (hrow : ∀ i, (∑ j, if G.Adj i j then y j else 0) = specRad G * y i) :
    (G.adjMatrix ℝ).mulVec y = specRad G • y := by
  funext i
  rw [wk9_row, hrow i]
  simp

-- Strict increase: an extra edge from a positive entry to a zero entry.
open Classical in
theorem tt_strict {W : Type*} [Fintype W] [DecidableEq W] (G' G'' : SimpleGraph W)
    (hle : G' ≤ G'') (y : W → ℝ) (hy : ∀ i, 0 ≤ y i) (μ : ℝ)
    (hrow : ∀ i, (∑ j, if G'.Adj i j then y j else 0) = μ * y i)
    (a b : W) (hab : G''.Adj a b) (ha : 0 < y a) (hb : y b = 0) : μ < specRad G'' := by
  have hV : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨a⟩
  have hnn : ∀ i, 0 ≤ ∑ j, (if G'.Adj i j then y j else 0) := fun i =>
    Finset.sum_nonneg (fun j _ => by split_ifs; exact hy j; exact le_rfl)
  have hμ : 0 ≤ μ := by
    by_contra hneg
    push Not at hneg
    have h1 := hrow a
    have : μ * y a < 0 := mul_neg_of_neg_of_pos hneg ha
    linarith [hnn a]
  have hab' : ¬ G'.Adj a b := by
    intro h
    have h1 := hrow b
    rw [hb, mul_zero] at h1
    have h2 : (if G'.Adj b a then y a else 0) ≤ ∑ j, (if G'.Adj b j then y j else 0) :=
      Finset.single_le_sum (f := fun j => if G'.Adj b j then y j else 0)
        (fun j _ => by split_ifs; exact hy j; exact le_rfl) (Finset.mem_univ a)
    rw [if_pos h.symm] at h2
    linarith
  have hμ1 : 0 < μ + 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = y a / (μ + 1) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; exact div_pos ha hμ1
  obtain ⟨z, hz⟩ : ∃ z : W → ℝ, z = fun i => y i + (if i = b then t else 0) := ⟨_, rfl⟩
  have hz0 : ∀ i, 0 ≤ z i := fun i => by
    rw [hz]; dsimp only; split_ifs <;> linarith [hy i]
  have hzy : ∀ i, y i ≤ z i := fun i => by
    rw [hz]; dsimp only; split_ifs <;> linarith
  have hza : z a = y a := by
    rw [hz]; dsimp only; rw [if_neg (G''.ne_of_adj hab)]; ring
  have hzb : z b = t := by
    rw [hz]; dsimp only; rw [if_pos rfl, hb]; ring
  have hzz : ∑ i, z i * z i = ∑ i, y i * y i + t * t := by
    have : ∀ i, z i * z i = y i * y i + (if i = b then t * t else 0) := by
      intro i
      rw [hz]; dsimp only
      by_cases hi : i = b
      · subst hi; rw [if_pos rfl, if_pos rfl, hb]; ring
      · rw [if_neg hi, if_neg hi]; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hQy := tt_Q_of_row G' y μ hrow
  have hQ'z : (∑ i, ∑ j, (if G'.Adj i j then y i * y j else 0)) ≤
      ∑ i, ∑ j, (if G'.Adj i j then z i * z j else 0) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs
    · exact mul_le_mul (hzy i) (hzy j) (hy j) (hz0 i)
    · exact le_rfl
  have hgain := tt_gain G' G'' hle z hz0 a b hab hab'
  have hQ'' := tt_Q_le G'' hV z
  rw [hza, hzb] at hgain
  rw [hzz] at hQ''
  by_contra hcon
  push Not at hcon
  have hY0 : 0 ≤ ∑ i, y i * y i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h2 : specRad G'' * (∑ i, y i * y i + t * t) ≤ μ * (∑ i, y i * y i + t * t) :=
    mul_le_mul_of_nonneg_right hcon (by positivity)
  have h3 : 2 * (y a * t) ≤ μ * (t * t) := by nlinarith
  have h4 : 2 * y a ≤ μ * t := by
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_right hc htpos]
  have h5 : μ * t < y a := by
    have e : t * (μ + 1) = y a := by rw [ht]; field_simp
    nlinarith
  linarith

-- Extension by zero along an embedding keeps the row equations.
open Classical in
theorem tt_ext {V W : Type*} [Fintype V] [Fintype W] (f : V ↪ W) (G : SimpleGraph V)
    (u : V → ℝ) (μ : ℝ) (hrow : ∀ a, (∑ b, if G.Adj a b then u b else 0) = μ * u a) :
    (∀ a, Function.extend f u 0 (f a) = u a) ∧
    (∀ i, (¬ ∃ a, f a = i) → Function.extend f u 0 i = 0) ∧
    (∑ i, Function.extend f u 0 i * Function.extend f u 0 i = ∑ a, u a * u a) ∧
    ∀ i, (∑ j, @ite ℝ ((G.map f).Adj i j) (Classical.propDecidable _)
      (Function.extend f u 0 j) 0) = μ * Function.extend f u 0 i := by
  have h1 : ∀ a, Function.extend f u 0 (f a) = u a := fun a => f.injective.extend_apply u 0 a
  have h2 : ∀ i, (¬ ∃ a, f a = i) → Function.extend f u 0 i = 0 := fun i hi => by
    rw [Function.extend_apply' _ _ _ hi]; rfl
  refine ⟨h1, h2, ?_, ?_⟩
  · symm
    refine Fintype.sum_of_injective f f.injective _ _ (fun i hi => ?_) (fun a => ?_)
    · rw [h2 i (by simpa [Set.mem_range] using hi)]; ring
    · rw [h1]
  · intro i
    by_cases hi : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [h1, ← hrow a]
      symm
      refine Fintype.sum_of_injective f f.injective _ _ (fun j hj => ?_) (fun b => ?_)
      · rw [h2 j (by simpa [Set.mem_range] using hj)]; simp
      · rw [SimpleGraph.map_adj_apply, h1]
    · rw [h2 i hi, mul_zero]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg]
      intro hij
      rw [SimpleGraph.map_adj] at hij
      obtain ⟨a, b, _, ha, _⟩ := hij
      exact hi ⟨a, ha⟩

-- A normalised nonnegative Perron vector.
open Classical in
theorem tt_normalized {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ 1) ∧ (∃ x, v x = 1) ∧
      ∀ i, (∑ j, if G.Adj i j then v j else 0) = specRad G * v i := by
  have hV : 0 < Fintype.card (Fin n) := by simpa using hn
  obtain ⟨x, hx0, hxx, hrow⟩ := tt_nonneg_eig G hV
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ x ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hM : 0 < x i0 := by
    by_contra h
    push Not at h
    have h0 : ∀ i, x i = 0 := fun i =>
      le_antisymm ((hi0 i (Finset.mem_univ _)).trans h) (hx0 i)
    simp [h0] at hxx
  refine ⟨fun i => x i / x i0, fun i => div_nonneg (hx0 i) hM.le,
    fun i => (div_le_one hM).2 (hi0 i (Finset.mem_univ _)), ⟨i0, div_self hM.ne'⟩,
    fun i => ?_⟩
  have e : (∑ j, if G.Adj i j then x j / x i0 else 0) =
      (∑ j, if G.Adj i j then x j else 0) / x i0 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  simp only
  rw [e, hrow i]
  ring


theorem tt_fan_adj_lr (n : ℕ) (a : Fin 1) (b : Fin (n - 1)) :
    (fan n).Adj (Sum.inl a) (Sum.inr b) := trivial

theorem tt_fan_adj_rl (n : ℕ) (a : Fin 1) (b : Fin (n - 1)) :
    (fan n).Adj (Sum.inr b) (Sum.inl a) := trivial

theorem tt_fan_outer' (n : ℕ) : IsOuterplanar (fan n) := tt_fan_outer (n - 1)

-- The spectral radius of `K₁ + P_{n-1}` grows.
open Classical in
theorem tt_fan_lower (n : ℕ) (K : ℝ) (hK : 0 < K) (hn : 16 * K ^ 2 + 3 ≤ (n : ℝ)) :
    K < specRad (fan n) := by
  have hn1 : 1 ≤ n := by
    have : (1:ℝ) ≤ n := by nlinarith [sq_nonneg K]
    exact_mod_cast this
  have hm : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1]; norm_num
  have hV : 0 < Fintype.card (Fin 1 ⊕ Fin (n - 1)) := by simp
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 4 * K := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  obtain ⟨y, hy⟩ : ∃ y : Fin 1 ⊕ Fin (n - 1) → ℝ,
      y = Sum.elim (fun _ => M) (fun _ => 1) := ⟨_, rfl⟩
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i; rw [hy]; rcases i with a | b
    · simp only [Sum.elim_inl]; exact hM0.le
    · simp
  have hF0 : ∀ i j, 0 ≤ (if (fan n).Adj i j then y i * y j else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hy0 i) (hy0 j)
    · exact le_rfl
  have hR0 : ∀ i, 0 ≤ ∑ j, (if (fan n).Adj i j then y i * y j else 0) := fun i =>
    Finset.sum_nonneg (fun j _ => hF0 i j)
  have hyl0 : y (Sum.inl 0) = M := by rw [hy]; simp
  have hyr : ∀ b, y (Sum.inr b) = 1 := by intro b; rw [hy]; simp
  have hQlow : 2 * (((n - 1 : ℕ) : ℝ) * M) ≤
      ∑ i, ∑ j, (if (fan n).Adj i j then y i * y j else 0) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one]
    have e1 : ((n - 1 : ℕ) : ℝ) * M ≤
        ∑ j, (if (fan n).Adj (Sum.inl 0) j then y (Sum.inl 0) * y j else 0) := by
      rw [Fintype.sum_sum_type]
      have h1 : (∑ b : Fin (n - 1), (if (fan n).Adj (Sum.inl 0) (Sum.inr b) then
          y (Sum.inl 0) * y (Sum.inr b) else 0)) = ((n - 1 : ℕ) : ℝ) * M := by
        simp only [if_pos (tt_fan_adj_lr n 0 _), hyl0, hyr, mul_one, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2 : 0 ≤ ∑ a : Fin 1, (if (fan n).Adj (Sum.inl 0) (Sum.inl a) then
          y (Sum.inl 0) * y (Sum.inl a) else 0) :=
        Finset.sum_nonneg (fun a _ => hF0 _ _)
      linarith
    have e3 : ((n - 1 : ℕ) : ℝ) * M ≤ ∑ b : Fin (n - 1),
        ∑ j, (if (fan n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0) := by
      have hb : ∀ b : Fin (n - 1), M ≤
          ∑ j, (if (fan n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0) := by
        intro b
        have := Finset.single_le_sum (f := fun j =>
          if (fan n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0)
          (fun j _ => hF0 _ _) (Finset.mem_univ (Sum.inl 0))
        simp only [if_pos (tt_fan_adj_rl n 0 b), hyl0, hyr, one_mul] at this ⊢
        exact this
      calc ((n - 1 : ℕ) : ℝ) * M = ∑ b : Fin (n - 1), M := by simp
        _ ≤ _ := Finset.sum_le_sum (fun b _ => hb b)
    linarith
  have hyy : ∑ i, y i * y i = M * M + ((n - 1 : ℕ) : ℝ) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one, hy]
    simp
  have hQ := tt_Q_le (fan n) hV y
  rw [hyy] at hQ
  have hpos : 0 < M * M + ((n - 1 : ℕ) : ℝ) := by positivity
  by_contra hcon
  push Not at hcon
  have h1 : specRad (fan n) * (M * M + ((n - 1 : ℕ) : ℝ)) ≤
      K * (M * M + ((n - 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hcon hpos.le
  rw [hm] at h1 hQlow hQ
  rw [hM] at h1 hQlow hQ
  have h4 : K * (16 * K ^ 2 + 3) ≤ K * n := mul_le_mul_of_nonneg_left hn hK.le
  nlinarith [h4, pow_pos hK 3, hQ, hQlow, h1]

-- `λ(K₁ + P_{n-1}) ≤ λ(G)` for every outerplanar maximiser.
open Classical in
theorem tt_fan_le_max {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsSpecMax IsOuterplanar G) : specRad (fan n) ≤ specRad G := by
  have hc : Fintype.card (Fin n) = Fintype.card (Fin 1 ⊕ Fin (n - 1)) := by simp; omega
  obtain ⟨e, -⟩ : ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)), True :=
    ⟨Fintype.equivOfCardEq hc, trivial⟩
  have hB : IsOuterplanar ((fan n).comap e) :=
    tt_outer_pull _ (fan n) e Set.univ e.injective.injOn (fun _ _ _ => trivial)
      (fun _ _ h => h) (tt_fan_outer' n)
  have iso : (fan n).comap e ≃g fan n := { toEquiv := e, map_rel_iff' := Iff.rfl }
  rw [← wkx_specRad_eq_of_iso iso]
  exact hG.2 _ hB

-- Strict growth of `λ(K₁ + P_{m-1})` in `m`.
open Classical in
theorem tt_fan_lt (k n : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    specRad (fan k) < specRad (fan n) := by
  have hV : 0 < Fintype.card (Fin 1 ⊕ Fin (k - 1)) := by simp
  obtain ⟨u, hu0, huu, hurow⟩ := tt_nonneg_eig (fan k) hV
  -- the hub entry is positive
  have hhub : 0 < u (Sum.inl 0) := by
    rcases (hu0 (Sum.inl 0)).lt_or_eq with h | h
    · exact h
    exfalso
    have h1 := hurow (Sum.inl 0)
    rw [← h, mul_zero] at h1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      split_ifs; exact hu0 j; exact le_rfl)).mp h1
    have hall : ∀ j, u j = 0 := by
      intro j
      rcases j with a | b
      · have : a = 0 := Subsingleton.elim _ _
        rw [this]; exact h.symm
      · have := hz (Sum.inr b) (Finset.mem_univ _)
        rwa [if_pos (tt_fan_adj_lr k 0 b)] at this
    simp [hall] at huu
  have hle2 : k - 1 ≤ n - 1 := by omega
  let f : (Fin 1 ⊕ Fin (k - 1)) ↪ (Fin 1 ⊕ Fin (n - 1)) :=
    Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hle2)
  obtain ⟨h1, h2, -, hrow⟩ := tt_ext f (fan k) u (specRad (fan k)) hurow
  have hmap : (fan k).map f ≤ fan n := by
    intro p q hpq
    rw [SimpleGraph.map_adj] at hpq
    obtain ⟨a, b, hab, rfl, rfl⟩ := hpq
    rcases a with a | a <;> rcases b with b | b
    · exact hab
    · exact trivial
    · exact trivial
    · show (SimpleGraph.pathGraph (n - 1)).Adj _ _
      have hab' : (SimpleGraph.pathGraph (k - 1)).Adj a b := hab
      rw [SimpleGraph.pathGraph_adj] at hab' ⊢
      simpa [f] using hab'
  have hlt : k - 1 < n - 1 := by omega
  refine tt_strict ((fan k).map f) (fan n) hmap (Function.extend f u 0) ?_ _ hrow
    (Sum.inl 0) (Sum.inr ⟨k - 1, hlt⟩) (tt_fan_adj_lr n 0 _) ?_ ?_
  · intro i
    by_cases hi : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := hi; rw [h1]; exact hu0 a
    · rw [h2 i hi]
  · have := h1 (Sum.inl 0)
    simp only [f] at this ⊢
    rw [show (Function.Embedding.sumMap (Function.Embedding.refl (Fin 1)) (Fin.castLEEmb hle2))
      (Sum.inl 0) = Sum.inl 0 from rfl] at this
    rw [this]; exact hhub
  · apply h2
    rintro ⟨a, ha⟩
    rcases a with a | a
    · simp [f] at ha
    · simp [f, Fin.ext_iff] at ha
      omega

-- Restriction of a maximiser to the support of its Perron vector.
open Classical in
theorem tt_restrict {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : IsSpecMax IsOuterplanar G)
    (v : Fin n → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (x : Fin n) (hx : v x = 1)
    (hrow : ∀ i, (∑ j, if G.Adj i j then v j else 0) = specRad G * v i) :
    ∃ k : ℕ, ∃ H : SimpleGraph (Fin k), ∃ u : Fin k → ℝ,
      IsSpecMax IsOuterplanar H ∧ specRad H = specRad G ∧
      (∀ i, 0 < u i) ∧ (∀ i, u i ≤ 1) ∧ (∃ x, u x = 1) ∧
      (∀ i, (∑ j, if H.Adj i j then u j else 0) = specRad H * u i) ∧
      k = (Finset.univ.filter (fun i => 0 < v i)).card := by
  set S := Finset.univ.filter (fun i => 0 < v i) with hS
  set k := S.card
  let σ : Fin k ↪o Fin n := S.orderEmbOfFin rfl
  have hσS : ∀ a, σ a ∈ S := fun a => S.orderEmbOfFin_mem rfl a
  have hσr : ∀ i ∈ S, ∃ a, σ a = i := by
    intro i hi
    have : i ∈ Set.range σ := by
      rw [show (Set.range σ) = (S : Set (Fin n)) from S.range_orderEmbOfFin rfl]; exact hi
    exact this
  have hxS : x ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hx]; norm_num⟩
  obtain ⟨a0, ha0⟩ := hσr x hxS
  have hk : 0 < k := Finset.card_pos.2 ⟨x, hxS⟩
  have hkc : 0 < Fintype.card (Fin k) := by simpa using hk
  have hnc : 0 < Fintype.card (Fin n) := by simpa using (Fin.pos x)
  let H : SimpleGraph (Fin k) := G.comap σ
  let u : Fin k → ℝ := fun a => v (σ a)
  have hupos : ∀ a, 0 < u a := fun a => by
    have := hσS a
    rw [hS, Finset.mem_filter] at this
    exact this.2
  have hrowH : ∀ a, (∑ b, if H.Adj a b then u b else 0) = specRad G * u a := by
    intro a
    rw [← hrow (σ a)]
    refine Fintype.sum_of_injective σ σ.injective _ _ (fun j hj => ?_) (fun b => rfl)
    have hjS : j ∉ S := fun hj' => hj (hσr j hj')
    rw [hS, Finset.mem_filter] at hjS
    have : v j = 0 := le_antisymm (not_lt.1 (fun h => hjS ⟨Finset.mem_univ _, h⟩)) (hv0 j)
    simp [this]
  have hHouter : IsOuterplanar H :=
    tt_outer_pull H G σ Set.univ σ.injective.injOn (fun _ _ _ => trivial) (fun _ _ h => h) hG.1
  -- padding: every outerplanar graph on `Fin k` has `λ ≤ λ(G)`
  have hpad : ∀ H' : SimpleGraph (Fin k), IsOuterplanar H' → specRad H' ≤ specRad G := by
    intro H' hH'
    let σe : Fin k ↪ Fin n := σ.toEmbedding
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    let g : Fin n → Fin k := Function.invFun σe
    have hg : ∀ a, g (σe a) = a := Function.leftInverse_invFun σe.injective
    have hP : IsOuterplanar (H'.map σe) := by
      refine tt_outer_pull (H'.map σe) H' g (Set.range σe) ?_ ?_ ?_ hH'
      · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
        rw [hg, hg] at hab; rw [hab]
      · intro p q hpq
        rw [SimpleGraph.map_adj] at hpq
        obtain ⟨a, b, _, rfl, rfl⟩ := hpq
        exact ⟨a, rfl⟩
      · intro p q hpq
        rw [SimpleGraph.map_adj] at hpq
        obtain ⟨a, b, hab, rfl, rfl⟩ := hpq
        rw [hg, hg]; exact hab
    obtain ⟨y', hy0, hyy, hyrow⟩ := tt_nonneg_eig H' hkc
    obtain ⟨-, -, hsq, hrow''⟩ := tt_ext σe H' y' (specRad H') hyrow
    have hQ := tt_Q_le (H'.map σe) hnc (Function.extend σe y' 0)
    rw [tt_Q_of_row _ _ _ hrow'', hsq, hyy] at hQ
    have := hG.2 _ hP
    linarith
  have hGH : specRad G ≤ specRad H := by
    have hQ := tt_Q_le H hkc u
    rw [tt_Q_of_row _ _ _ hrowH] at hQ
    have hpos : 0 < ∑ i, u i * u i :=
      Finset.sum_pos (fun i _ => mul_pos (hupos i) (hupos i)) ⟨a0, Finset.mem_univ _⟩
    nlinarith
  have hHG : specRad H ≤ specRad G := hpad H hHouter
  have heq : specRad H = specRad G := le_antisymm hHG hGH
  refine ⟨k, H, u, ⟨hHouter, fun H' hH' => (hpad H' hH').trans hGH⟩, heq, hupos,
    fun a => hv1 _, ⟨a0, by simp only [u]; rw [ha0, hx]⟩, ?_, rfl⟩
  intro a
  rw [heq]
  exact hrowH a

-- The positive case: a universal vertex, then compare with `K₁ + P_{n-1}`.
open Classical in
theorem tt_core {n : ℕ}
    (hsub : ∀ (G : SimpleGraph (Fin n)), IsOuterplanar G → ∀ x : Fin n,
      (∀ y : Fin n, y ≠ x → G.Adj x y) →
      ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)),
        ∀ a b : Fin n, G.Adj a b → (fan n).Adj (e a) (e b))
    (G : SimpleGraph (Fin n)) (hG : IsSpecMax IsOuterplanar G)
    (v : Fin n → ℝ) (hpos : ∀ i, 0 < v i)
    (hrow : ∀ i, (∑ j, if G.Adj i j then v j else 0) = specRad G * v i)
    (x : Fin n) (hxu : ∀ y : Fin n, y ≠ x → G.Adj x y) :
    Nonempty (G ≃g fan n) := by
  obtain ⟨e, he⟩ := hsub G hG.1 x hxu
  have hB : IsOuterplanar ((fan n).comap e) :=
    tt_outer_pull _ (fan n) e Set.univ e.injective.injOn (fun _ _ _ => trivial)
      (fun _ _ h => h) (tt_fan_outer' n)
  have hle : G ≤ (fan n).comap e := fun a b h => he a b h
  have hlam := hG.2 _ hB
  have hnc : 0 < Fintype.card (Fin n) := by simpa using (Fin.pos x)
  have hGB : G = (fan n).comap e := by
    by_contra hne
    obtain ⟨a, b, hab, hab'⟩ : ∃ a b, ((fan n).comap e).Adj a b ∧ ¬ G.Adj a b := by
      by_contra hc
      push Not at hc
      exact hne (le_antisymm hle (fun a b h => hc a b h))
    have hg := tt_gain G ((fan n).comap e) hle v (fun i => (hpos i).le) a b hab hab'
    have hQ := tt_Q_le ((fan n).comap e) hnc v
    rw [tt_Q_of_row G v _ hrow] at hg
    have hvv : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have h3 : specRad ((fan n).comap e) * ∑ i, v i * v i ≤ specRad G * ∑ i, v i * v i :=
      mul_le_mul_of_nonneg_right hlam hvv
    nlinarith [mul_pos (hpos a) (hpos b)]
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro a b
  rw [hGB]
  exact Iff.rfl

-- Forward direction from the positive case.
open Classical in
theorem tt_forward (N1 : ℕ) (hN1 : 3 ≤ N1)
    (good : ∀ m ≥ N1, ∀ H : SimpleGraph (Fin m), IsSpecMax IsOuterplanar H →
      ∀ u : Fin m → ℝ, (∀ i, 0 < u i) → (∀ i, u i ≤ 1) → (∃ x, u x = 1) →
      (∀ i, (∑ j, if H.Adj i j then u j else 0) = specRad H * u i) →
      Nonempty (H ≃g fan m))
    (n : ℕ) (hn : 16 * (N1 : ℝ) ^ 2 + 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsSpecMax IsOuterplanar G) : Nonempty (G ≃g fan n) := by
  have hN1r : (3:ℝ) ≤ N1 := by exact_mod_cast hN1
  have hNn : N1 < n := by
    have : (N1 : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hn0 : 0 < n := by omega
  obtain ⟨v, hv0, hv1, ⟨x, hx⟩, hrow⟩ := tt_normalized G hn0
  have hB : (N1 : ℝ) < specRad G := by
    have h1 := tt_fan_lower n N1 (by positivity) hn
    have h2 := tt_fan_le_max (by omega) G hG
    linarith
  by_cases hall : ∀ i, 0 < v i
  · exact good n hNn.le G hG v hall hv1 ⟨x, hx⟩ hrow
  · exfalso
    obtain ⟨k, H, u, hH, hHG, hu0, hu1, hux, hurow, hk⟩ :=
      tt_restrict G hG v hv0 hv1 x hx hrow
    have hkn : k < n := by
      rw [hk]
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      calc (Finset.univ.filter (fun i => 0 < v i)).card < (Finset.univ : Finset (Fin n)).card :=
            Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, Finset.mem_univ _, not_lt.2 hi⟩)
        _ = n := by simp
    have hGk : specRad G ≤ k := by
      have h1 := hrow x
      rw [hx, mul_one] at h1
      rw [← h1, hk]
      have : (∑ j, if G.Adj x j then v j else 0) ≤
          ∑ j, (if 0 < v j then (1:ℝ) else 0) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        by_cases hj : 0 < v j
        · rw [if_pos hj]; split_ifs
          · exact hv1 j
          · exact zero_le_one
        · rw [if_neg hj]
          have : v j = 0 := le_antisymm (not_lt.1 hj) (hv0 j)
          split_ifs <;> simp [this]
      rw [Finset.sum_boole] at this
      exact this
    by_cases hkN : N1 ≤ k
    · obtain ⟨φ⟩ := good k hkN H hH u hu0 hu1 hux hurow
      have e1 : specRad H = specRad (fan k) := wkx_specRad_eq_of_iso φ
      have e2 := tt_fan_lt k n (by omega) hkn
      have e3 := tt_fan_le_max (by omega) G hG
      linarith
    · have : (k : ℝ) < N1 := by exact_mod_cast (by omega : k < N1)
      linarith

end TTGlue

section TTMain

open WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

-- Assembly: Theorem 7 from `B_empty` and the structure lemma for a dominating vertex.
open Classical in
theorem tt_main
    (hB : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      IsSpecMax IsOuterplanar G →
      ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
        (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
          ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hsub : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsOuterplanar G → ∀ (x : Fin n),
      (∀ y : Fin n, y ≠ x → G.Adj x y) →
      ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)),
        ∀ a b : Fin n, G.Adj a b → (fan n).Adj (e a) (e b)) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ G : SimpleGraph (Fin n),
      IsSpecMax IsOuterplanar G ↔ Nonempty (G ≃g fan n) := by
  obtain ⟨NB, hNB⟩ := hB
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, N1 = max NB 3 := ⟨_, rfl⟩
  have good : ∀ m ≥ N1, ∀ H : SimpleGraph (Fin m),
      IsSpecMax IsOuterplanar H →
      ∀ u : Fin m → ℝ, (∀ i, 0 < u i) → (∀ i, u i ≤ 1) → (∃ x, u x = 1) →
      (∀ i, (∑ j, if H.Adj i j then u j else 0) = specRad H * u i) →
      Nonempty (H ≃g fan m) := by
    intro m hm H hH u hpos hle1 hux hrow
    obtain ⟨x, hx⟩ := hux
    have hmv := tt_mulVec_of_row H u hrow
    have hxu := hNB m (by omega) H hH u hmv hpos hle1 x hx
    exact tt_core (fun G hG x hx => hsub G hG x hx) H hH u hpos hrow x hxu
  have hN3 : 3 ≤ N1 := by omega
  refine ⟨16 * N1 ^ 2 + 3, fun n hn G => ?_⟩
  have hnr : 16 * (N1 : ℝ) ^ 2 + 3 ≤ n := by exact_mod_cast hn
  constructor
  · exact tt_forward N1 hN3 good n hnr G
  · rintro ⟨φ⟩
    have hGpl : IsOuterplanar G :=
      tt_outer_pull G (fan n) φ Set.univ φ.injective.injOn (fun _ _ _ => trivial)
        (fun _ _ h => φ.map_adj_iff.2 h) (tt_fan_outer' n)
    obtain ⟨Gs, hGs_mem, hGs_max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun H : SimpleGraph (Fin n) => IsOuterplanar H)) specRad
      ⟨G, Finset.mem_filter.2 ⟨Finset.mem_univ _, hGpl⟩⟩
    have hGs : IsSpecMax IsOuterplanar Gs :=
      ⟨(Finset.mem_filter.1 hGs_mem).2,
        fun H hH => hGs_max H (Finset.mem_filter.2 ⟨Finset.mem_univ _, hH⟩)⟩
    obtain ⟨ψ⟩ := tt_forward N1 hN3 good n hnr Gs hGs
    have χ : G ≃g Gs := φ.trans ψ.symm
    exact ⟨hGpl, fun H hH => (hGs.2 H hH).trans (le_of_eq (wkx_specRad_eq_of_iso χ).symm)⟩

end TTMain

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar in
theorem solution : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G ↔ Nonempty (G ≃g fan n) :=
  tt_main TaitTobin.Outerplanar.B_empty TaitTobin.Outerplanar.subgraph_fan_of_universal
