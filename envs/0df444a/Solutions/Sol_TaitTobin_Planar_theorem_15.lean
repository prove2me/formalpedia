-- Prove2me | solution 1 for TaitTobin.Planar.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:21:38.081759+00:00
-- url     : https://prove2.me/submissions/9654f6d9-af57-4a75-8422-6833812edcc6

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_11
import Theorems.Thm_TaitTobin_Planar_lemma_13
import Theorems.Thm_TaitTobin_Planar_lemma_14
import Theorems.Thm_TaitTobin_Planar_subgraph_bookPath_of_universal

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

section TTPlanar

open RobertsonSeymour1986.GM5

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

-- Pull a plane drawing back along a map that is injective on the vertices meeting edges;
-- the other vertices are placed far away.
open Classical in
theorem tt_planar_pull {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (g : V → W) (S : Set V) (hinj : Set.InjOn g S)
    (hS : ∀ x y, G.Adj x y → x ∈ S)
    (hadj : ∀ x y, G.Adj x y → H.Adj (g x) (g y)) (hH : IsPlanar H) : IsPlanar G := by
  obtain ⟨D⟩ := hH
  obtain ⟨R, hRv, hRa⟩ := tt_drawing_bounded D
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
    arcs_meet_only_at_endpoints := ?_ }⟩
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

end TTPlanar
section TTBook

open RobertsonSeymour1986.GM5

/-- Vertex positions: the two hubs at `(0, 1)` and `(0, -1)`, path vertex `b` at `(b + 1, 0)`. -/
def ttP {m : ℕ} : Fin 2 ⊕ Fin m → ℝ × ℝ
  | Sum.inl a => (0, 1 - 2 * ((a : ℕ) : ℝ))
  | Sum.inr b => (((b : ℕ) : ℝ) + 1, 0)

/-- The straight segment from `p` to `q` as a path. -/
def ttSeg (p q : ℝ × ℝ) : Path p q where
  toFun t := p + (t : ℝ) • (q - p)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem ttSeg_apply (p q : ℝ × ℝ) (t : unitInterval) :
    ttSeg p q t = p + (t : ℝ) • (q - p) := rfl

theorem tt_join_adj_ll {m : ℕ} (a a' : Fin 2) :
    (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      (Sum.inl a) (Sum.inl a') ↔ a ≠ a' := by
  show (⊤ : SimpleGraph (Fin 2)).Adj a a' ↔ a ≠ a'
  simp

theorem tt_join_adj_rr {m : ℕ} (b b' : Fin m) :
    (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      (Sum.inr b) (Sum.inr b') ↔ (b.val + 1 = b'.val ∨ b'.val + 1 = b.val) := by
  show (SimpleGraph.pathGraph m).Adj b b' ↔ _
  exact SimpleGraph.pathGraph_adj

/-- Canonical orientation of an edge. -/
def ttCanon {m : ℕ} (v w : Fin 2 ⊕ Fin m) : Prop :=
  (v = Sum.inl 0 ∧ w = Sum.inl 1) ∨ (∃ a b, v = Sum.inl a ∧ w = Sum.inr b) ∨
    (∃ b b' : Fin m, v = Sum.inr b ∧ w = Sum.inr b' ∧ b'.val = b.val + 1)

theorem tt_canon_of_adj {m : ℕ} (v w : Fin 2 ⊕ Fin m)
    (h : (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      v w) : ttCanon v w ∨ ttCanon w v := by
  rcases v with a | b <;> rcases w with a' | b'
  · rw [tt_join_adj_ll] at h
    fin_cases a <;> fin_cases a'
    · exact absurd rfl h
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd rfl h
  · exact Or.inl (Or.inr (Or.inl ⟨a, b', rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a', b, rfl, rfl⟩))
  · rw [tt_join_adj_rr] at h
    rcases h with h | h
    · exact Or.inl (Or.inr (Or.inr ⟨b, b', rfl, rfl, h.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b', b, rfl, rfl, h.symm⟩))

theorem tt_pt_rev {m : ℕ} (v w : Fin 2 ⊕ Fin m) (s : ℝ) :
    ttP w + s • (ttP v - ttP w) = ttP v + (1 - s) • (ttP w - ttP v) := by
  ext <;> simp <;> ring

theorem tt_sigma (a : Fin 2) : (1 - 2 * ((a : ℕ) : ℝ) = 1 ∧ a = 0) ∨
    (1 - 2 * ((a : ℕ) : ℝ) = -1 ∧ a = 1) := by
  fin_cases a
  · left; norm_num
  · right; norm_num

/-- An interior point of a canonical edge is not a vertex. -/
theorem tt_A_canon {m : ℕ} (v w z : Fin 2 ⊕ Fin m) (hc : ttCanon v w) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) : ttP v + s • (ttP w - ttP v) ≠ ttP z := by
  intro heq
  have hX := congrArg Prod.fst heq
  have hY := congrArg Prod.snd heq
  rcases hc with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ | ⟨b, b', rfl, rfl, hb⟩
  · rcases z with c | d
    · simp [ttP] at hY
      rcases tt_sigma c with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] at hY <;> nlinarith
    · simp [ttP] at hX
      have : (0:ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
      linarith
  · rcases z with c | d
    · simp [ttP] at hX
      have : (0:ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
      rcases hX with h | h
      · linarith
      · linarith
    · simp [ttP] at hY
      rcases tt_sigma a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] at hY <;> nlinarith
  · rcases z with c | d
    · simp [ttP] at hY
      rcases tt_sigma c with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] at hY <;> linarith
    · simp [ttP] at hX
      have hb' : ((b' : ℕ) : ℝ) = (b : ℕ) + 1 := by rw [hb]; push_cast; ring
      rw [hb'] at hX
      have h1 : ((b : ℕ) : ℝ) < (d : ℕ) := by linarith
      have h2 : ((d : ℕ) : ℝ) < (b : ℕ) + 1 := by linarith
      have h1' : (b : ℕ) < (d : ℕ) := by exact_mod_cast h1
      have h2' : (d : ℕ) < (b : ℕ) + 1 := by exact_mod_cast h2
      omega

/-- Two interior points of canonical edges coincide only on the same edge. -/
theorem tt_B_canon {m : ℕ} (v w x y : Fin 2 ⊕ Fin m) (hc : ttCanon v w) (hc' : ttCanon x y)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (heq : ttP v + s • (ttP w - ttP v) = ttP x + t • (ttP y - ttP x)) : v = x ∧ w = y := by
  have hX := congrArg Prod.fst heq
  have hY := congrArg Prod.snd heq
  rcases hc with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ | ⟨b, b', rfl, rfl, hb⟩ <;>
    rcases hc' with ⟨rfl, rfl⟩ | ⟨c, d, rfl, rfl⟩ | ⟨d, d', rfl, rfl, hd⟩
  · exact ⟨rfl, rfl⟩
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
    rcases hX with h | h <;> linarith
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ (d' : ℕ) := Nat.cast_nonneg _
    nlinarith
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
    rcases hX with h | h <;> linarith
  · simp [ttP] at hX hY
    have hb0 : (0:ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
    have hd0 : (0:ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
    fin_cases a <;> fin_cases c <;> norm_num at hY
    all_goals first
      | (exfalso; linarith)
      | (have hst : s = t := by linarith
         subst hst
         have h1 : ((b : ℕ) : ℝ) = (d : ℕ) := by
           have := mul_left_cancel₀ hs0.ne' hX
           linarith
         have h2 : (b : ℕ) = (d : ℕ) := by exact_mod_cast h1
         exact ⟨rfl, by rw [Fin.ext h2]⟩)
  · simp [ttP] at hY
    exfalso
    rcases tt_sigma a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] at hY <;> nlinarith
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ (b' : ℕ) := Nat.cast_nonneg _
    nlinarith
  · simp [ttP] at hY
    exfalso
    rcases tt_sigma c with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] at hY <;> nlinarith
  · simp [ttP] at hX
    have hb' : ((b' : ℕ) : ℝ) = (b : ℕ) + 1 := by rw [hb]; push_cast; ring
    have hd' : ((d' : ℕ) : ℝ) = (d : ℕ) + 1 := by rw [hd]; push_cast; ring
    rw [hb', hd'] at hX
    have h1 : ((b : ℕ) : ℝ) < (d : ℕ) + 1 := by linarith
    have h2 : ((d : ℕ) : ℝ) < (b : ℕ) + 1 := by linarith
    have h1' : (b : ℕ) < (d : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (d : ℕ) < (b : ℕ) + 1 := by exact_mod_cast h2
    have hbd : (b : ℕ) = (d : ℕ) := by omega
    refine ⟨by rw [Fin.ext hbd], ?_⟩
    congr 1
    exact Fin.ext (by omega)

theorem tt_A {m : ℕ} (v w z : Fin 2 ⊕ Fin m)
    (h : (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      v w) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : ttP v + s • (ttP w - ttP v) ≠ ttP z := by
  rcases tt_canon_of_adj v w h with hc | hc
  · exact tt_A_canon v w z hc s hs0 hs1
  · have r := tt_pt_rev v w (1 - s)
    rw [sub_sub_cancel] at r
    rw [← r]
    exact tt_A_canon w v z hc (1 - s) (by linarith) (by linarith)

theorem tt_B {m : ℕ} (v w x y : Fin 2 ⊕ Fin m)
    (h : (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      v w)
    (k : (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph m)).Adj
      x y)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (heq : ttP v + s • (ttP w - ttP v) = ttP x + t • (ttP y - ttP x)) :
    (v = x ∧ w = y) ∨ (v = y ∧ w = x) := by
  have r1 := tt_pt_rev v w (1 - s)
  have r2 := tt_pt_rev x y (1 - t)
  rw [sub_sub_cancel] at r1 r2
  rcases tt_canon_of_adj v w h with hc | hc <;> rcases tt_canon_of_adj x y k with hc' | hc'
  · exact Or.inl (tt_B_canon v w x y hc hc' s t hs0 hs1 ht0 ht1 heq)
  · obtain ⟨h1, h2⟩ := tt_B_canon v w y x hc hc' s (1 - t) hs0 hs1 (by linarith) (by linarith)
      (by rw [heq, r2])
    exact Or.inr ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := tt_B_canon w v x y hc hc' (1 - s) t (by linarith) (by linarith) ht0 ht1
      (by rw [r1, heq])
    exact Or.inr ⟨h2, h1⟩
  · obtain ⟨h1, h2⟩ := tt_B_canon w v y x hc hc' (1 - s) (1 - t) (by linarith) (by linarith)
      (by linarith) (by linarith) (by rw [r1, heq, r2])
    exact Or.inl ⟨h2, h1⟩

theorem tt_ttP_injective {m : ℕ} : Function.Injective (ttP (m := m)) := by
  intro v w hvw
  have hX := congrArg Prod.fst hvw
  have hY := congrArg Prod.snd hvw
  rcases v with a | b <;> rcases w with c | d
  · simp [ttP] at hY
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hY))
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
    linarith
  · simp [ttP] at hX
    have : (0:ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
    linarith
  · simp [ttP] at hX
    exact congrArg Sum.inr (Fin.ext (by exact_mod_cast hX))

theorem tt_unit_cases (s : unitInterval) : s = 0 ∨ s = 1 ∨ (0 < (s : ℝ) ∧ (s : ℝ) < 1) := by
  rcases eq_or_lt_of_le s.2.1 with h | h
  · left; exact Subtype.ext h.symm
  rcases eq_or_lt_of_le s.2.2 with h' | h'
  · right; left; exact Subtype.ext h'
  · right; right; exact ⟨h, h'⟩

theorem tt_bookPath_planar (m : ℕ) :
    IsPlanar (TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2))
      (SimpleGraph.pathGraph m)) := by
  refine ⟨{
    vertex := ttP
    vertex_injective := tt_ttP_injective
    arc := fun {v w} _ => ttSeg (ttP v) (ttP w)
    arc_injective := ?_
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro v w h s t hst
    have hne : ttP v ≠ ttP w := fun e => (SimpleGraph.ne_of_adj _ h) (tt_ttP_injective e)
    simp only [ttSeg_apply, add_right_inj] at hst
    exact Subtype.ext (smul_left_injective ℝ (sub_ne_zero.2 hne.symm) hst)
  · intro v w h
    apply Path.ext
    funext t
    show ttSeg (ttP w) (ttP v) t = ttSeg (ttP v) (ttP w) (unitInterval.symm t)
    rw [ttSeg_apply, ttSeg_apply, unitInterval.coe_symm_eq, tt_pt_rev]
  · intro v w h t z hz
    simp only [ttSeg_apply] at hz
    rcases tt_unit_cases t with rfl | rfl | ⟨h0, h1⟩
    · simp at hz
      exact Or.inl (tt_ttP_injective hz).symm
    · simp at hz
      exact Or.inr (tt_ttP_injective hz).symm
    · exact absurd hz (tt_A v w z h t h0 h1)
  · intro v w x y h k s t hst
    simp only [ttSeg_apply] at hst
    rcases tt_unit_cases s with hs | hs | ⟨hs0, hs1⟩ <;>
      rcases tt_unit_cases t with ht | ht | ⟨ht0, ht1⟩
    all_goals first
      | exact Or.inr (Or.inr ⟨by tauto, by tauto⟩)
      | skip
    · subst hs; simp at hst
      exact absurd hst.symm (tt_A x y v k t ht0 ht1)
    · subst hs; simp at hst
      exact absurd hst.symm (tt_A x y w k t ht0 ht1)
    · subst ht; simp at hst
      exact absurd hst (tt_A v w x h s hs0 hs1)
    · subst ht; simp at hst
      exact absurd hst (tt_A v w y h s hs0 hs1)
    · exact (tt_B v w x y h k s t hs0 hs1 ht0 ht1 hst).elim (fun e => Or.inl e)
        (fun e => Or.inr (Or.inl e))

end TTBook

section TTGlue

open WangKangXue.SpectralTuran Matrix RobertsonSeymour1986.GM5 TaitTobin.Planar

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

theorem tt_book_adj_lr (n : ℕ) (a : Fin 2) (b : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inl a) (Sum.inr b) := trivial

theorem tt_book_adj_rl (n : ℕ) (a : Fin 2) (b : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inr b) (Sum.inl a) := trivial

theorem tt_book_planar (n : ℕ) : IsPlanar (bookPath n) := tt_bookPath_planar (n - 2)

-- The spectral radius of `K₂ + P_{n-2}` grows.
open Classical in
theorem tt_book_lower (n : ℕ) (K : ℝ) (hK : 0 < K) (hn : 16 * K ^ 2 + 3 ≤ (n : ℝ)) :
    K < specRad (bookPath n) := by
  have hn2 : 2 ≤ n := by
    have : (2:ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hm : (((n - 2 : ℕ)) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub hn2]; norm_num
  have hV : 0 < Fintype.card (Fin 2 ⊕ Fin (n - 2)) := by simp
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 4 * K := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  obtain ⟨y, hy⟩ : ∃ y : Fin 2 ⊕ Fin (n - 2) → ℝ,
      y = Sum.elim (fun a => if a = 0 then M else 0) (fun _ => 1) := ⟨_, rfl⟩
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i; rw [hy]; rcases i with a | b
    · simp only [Sum.elim_inl]; split_ifs <;> linarith
    · simp
  have hF0 : ∀ i j, 0 ≤ (if (bookPath n).Adj i j then y i * y j else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hy0 i) (hy0 j)
    · exact le_rfl
  have hR0 : ∀ i, 0 ≤ ∑ j, (if (bookPath n).Adj i j then y i * y j else 0) := fun i =>
    Finset.sum_nonneg (fun j _ => hF0 i j)
  have hyl0 : y (Sum.inl 0) = M := by rw [hy]; simp
  have hyr : ∀ b, y (Sum.inr b) = 1 := by intro b; rw [hy]; simp
  have hQlow : 2 * (((n - 2 : ℕ) : ℝ) * M) ≤
      ∑ i, ∑ j, (if (bookPath n).Adj i j then y i * y j else 0) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_two]
    have e1 : ((n - 2 : ℕ) : ℝ) * M ≤
        ∑ j, (if (bookPath n).Adj (Sum.inl 0) j then y (Sum.inl 0) * y j else 0) := by
      rw [Fintype.sum_sum_type]
      have h1 : (∑ b : Fin (n - 2), (if (bookPath n).Adj (Sum.inl 0) (Sum.inr b) then
          y (Sum.inl 0) * y (Sum.inr b) else 0)) = ((n - 2 : ℕ) : ℝ) * M := by
        simp only [if_pos (tt_book_adj_lr n 0 _), hyl0, hyr, mul_one, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2 : 0 ≤ ∑ a : Fin 2, (if (bookPath n).Adj (Sum.inl 0) (Sum.inl a) then
          y (Sum.inl 0) * y (Sum.inl a) else 0) :=
        Finset.sum_nonneg (fun a _ => hF0 _ _)
      linarith
    have e2 := hR0 (Sum.inl 1)
    have e3 : ((n - 2 : ℕ) : ℝ) * M ≤ ∑ b : Fin (n - 2),
        ∑ j, (if (bookPath n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0) := by
      have hb : ∀ b : Fin (n - 2), M ≤
          ∑ j, (if (bookPath n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0) := by
        intro b
        have := Finset.single_le_sum (f := fun j =>
          if (bookPath n).Adj (Sum.inr b) j then y (Sum.inr b) * y j else 0)
          (fun j _ => hF0 _ _) (Finset.mem_univ (Sum.inl 0))
        simp only [if_pos (tt_book_adj_rl n 0 b), hyl0, hyr, one_mul] at this ⊢
        exact this
      calc ((n - 2 : ℕ) : ℝ) * M = ∑ b : Fin (n - 2), M := by simp
        _ ≤ _ := Finset.sum_le_sum (fun b _ => hb b)
    linarith
  have hyy : ∑ i, y i * y i = M * M + ((n - 2 : ℕ) : ℝ) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, hy]
    simp
  have hQ := tt_Q_le (bookPath n) hV y
  rw [hyy] at hQ
  have hpos : 0 < M * M + ((n - 2 : ℕ) : ℝ) := by positivity
  by_contra hcon
  push Not at hcon
  have h1 : specRad (bookPath n) * (M * M + ((n - 2 : ℕ) : ℝ)) ≤
      K * (M * M + ((n - 2 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hcon hpos.le
  rw [hm] at h1 hQlow hQ
  rw [hM] at h1 hQlow hQ
  have h4 : K * (16 * K ^ 2 + 3) ≤ K * n := mul_le_mul_of_nonneg_left hn hK.le
  nlinarith [h4, pow_pos hK 3, hQ, hQlow, h1]

-- `λ(K₂ + P_{n-2}) ≤ λ(G)` for every planar maximiser.
open Classical in
theorem tt_book_le_max {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G) : specRad (bookPath n) ≤ specRad G := by
  have hc : Fintype.card (Fin n) = Fintype.card (Fin 2 ⊕ Fin (n - 2)) := by simp; omega
  obtain ⟨e, -⟩ : ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)), True := ⟨Fintype.equivOfCardEq hc, trivial⟩
  have hB : IsPlanar ((bookPath n).comap e) :=
    tt_planar_pull _ (bookPath n) e Set.univ e.injective.injOn (fun _ _ _ => trivial)
      (fun _ _ h => h) (tt_book_planar n)
  have iso : (bookPath n).comap e ≃g bookPath n := { toEquiv := e, map_rel_iff' := Iff.rfl }
  rw [← wkx_specRad_eq_of_iso iso]
  exact hG.2 _ hB

-- Strict growth of `λ(K₂ + P_{m-2})` in `m`.
open Classical in
theorem tt_book_lt (k n : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    specRad (bookPath k) < specRad (bookPath n) := by
  have hV : 0 < Fintype.card (Fin 2 ⊕ Fin (k - 2)) := by simp
  obtain ⟨u, hu0, huu, hurow⟩ := tt_nonneg_eig (bookPath k) hV
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
      · fin_cases a
        · exact h.symm
        · have := hz (Sum.inl 1) (Finset.mem_univ _)
          rwa [if_pos (show (bookPath k).Adj (Sum.inl 0) (Sum.inl 1) from by
            show (⊤ : SimpleGraph (Fin 2)).Adj 0 1; simp)] at this
      · have := hz (Sum.inr b) (Finset.mem_univ _)
        rwa [if_pos (tt_book_adj_lr k 0 b)] at this
    simp [hall] at huu
  have hle2 : k - 2 ≤ n - 2 := by omega
  let f : (Fin 2 ⊕ Fin (k - 2)) ↪ (Fin 2 ⊕ Fin (n - 2)) :=
    Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hle2)
  obtain ⟨h1, h2, -, hrow⟩ := tt_ext f (bookPath k) u (specRad (bookPath k)) hurow
  have hmap : (bookPath k).map f ≤ bookPath n := by
    intro p q hpq
    rw [SimpleGraph.map_adj] at hpq
    obtain ⟨a, b, hab, rfl, rfl⟩ := hpq
    rcases a with a | a <;> rcases b with b | b
    · exact hab
    · exact trivial
    · exact trivial
    · show (SimpleGraph.pathGraph (n - 2)).Adj _ _
      have hab' : (SimpleGraph.pathGraph (k - 2)).Adj a b := hab
      rw [SimpleGraph.pathGraph_adj] at hab' ⊢
      simpa [f] using hab'
  have hlt : k - 2 < n - 2 := by omega
  refine tt_strict ((bookPath k).map f) (bookPath n) hmap (Function.extend f u 0) ?_ _ hrow
    (Sum.inl 0) (Sum.inr ⟨k - 2, hlt⟩) (tt_book_adj_lr n 0 _) ?_ ?_
  · intro i
    by_cases hi : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := hi; rw [h1]; exact hu0 a
    · rw [h2 i hi]
  · have := h1 (Sum.inl 0)
    simp only [f] at this ⊢
    rw [show (Function.Embedding.sumMap (Function.Embedding.refl (Fin 2)) (Fin.castLEEmb hle2))
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
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (x : Fin n) (hx : v x = 1)
    (hrow : ∀ i, (∑ j, if G.Adj i j then v j else 0) = specRad G * v i) :
    ∃ k : ℕ, ∃ H : SimpleGraph (Fin k), ∃ u : Fin k → ℝ,
      TaitTobin.Outerplanar.IsSpecMax IsPlanar H ∧ specRad H = specRad G ∧
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
  have hHplanar : IsPlanar H :=
    tt_planar_pull H G σ Set.univ σ.injective.injOn (fun _ _ _ => trivial) (fun _ _ h => h) hG.1
  -- padding: every planar graph on `Fin k` has `λ ≤ λ(G)`
  have hpad : ∀ H' : SimpleGraph (Fin k), IsPlanar H' → specRad H' ≤ specRad G := by
    intro H' hH'
    let σe : Fin k ↪ Fin n := σ.toEmbedding
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    let g : Fin n → Fin k := Function.invFun σe
    have hg : ∀ a, g (σe a) = a := Function.leftInverse_invFun σe.injective
    have hP : IsPlanar (H'.map σe) := by
      refine tt_planar_pull (H'.map σe) H' g (Set.range σe) ?_ ?_ ?_ hH'
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
  have hHG : specRad H ≤ specRad G := hpad H hHplanar
  have heq : specRad H = specRad G := le_antisymm hHG hGH
  refine ⟨k, H, u, ⟨hHplanar, fun H' hH' => (hpad H' hH').trans hGH⟩, heq, hupos,
    fun a => hv1 _, ⟨a0, by simp only [u]; rw [ha0, hx]⟩, ?_, rfl⟩
  intro a
  rw [heq]
  exact hrowH a

-- The positive case: two universal vertices, then compare with `K₂ + P_{n-2}`.
open Classical in
theorem tt_core {n : ℕ}
    (hsub : ∀ (G : SimpleGraph (Fin n)), IsPlanar G → ∀ x w : Fin n, x ≠ w →
      (∀ y : Fin n, y ≠ x → G.Adj x y) → (∀ y : Fin n, y ≠ w → G.Adj w y) →
      ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)),
        ∀ a b : Fin n, G.Adj a b → (bookPath n).Adj (e a) (e b))
    (G : SimpleGraph (Fin n)) (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hpos : ∀ i, 0 < v i)
    (hrow : ∀ i, (∑ j, if G.Adj i j then v j else 0) = specRad G * v i)
    (x w : Fin n) (hxw : G.Adj x w)
    (huw : ∀ u, u ≠ x → u ≠ w → G.Adj u x ∧ G.Adj u w) :
    Nonempty (G ≃g bookPath n) := by
  have hxw' : x ≠ w := G.ne_of_adj hxw
  have hxu : ∀ y : Fin n, y ≠ x → G.Adj x y := by
    intro y hy
    by_cases hyw : y = w
    · rw [hyw]; exact hxw
    · exact (huw y hy hyw).1.symm
  have hwu : ∀ y : Fin n, y ≠ w → G.Adj w y := by
    intro y hy
    by_cases hyx : y = x
    · rw [hyx]; exact hxw.symm
    · exact (huw y hyx hy).2.symm
  obtain ⟨e, he⟩ := hsub G hG.1 x w hxw' hxu hwu
  have hB : IsPlanar ((bookPath n).comap e) :=
    tt_planar_pull _ (bookPath n) e Set.univ e.injective.injOn (fun _ _ _ => trivial)
      (fun _ _ h => h) (tt_book_planar n)
  have hle : G ≤ (bookPath n).comap e := fun a b h => he a b h
  have hlam := hG.2 _ hB
  have hnc : 0 < Fintype.card (Fin n) := by simpa using (Fin.pos x)
  have hGB : G = (bookPath n).comap e := by
    by_contra hne
    obtain ⟨a, b, hab, hab'⟩ : ∃ a b, ((bookPath n).comap e).Adj a b ∧ ¬ G.Adj a b := by
      by_contra hc
      push Not at hc
      exact hne (le_antisymm hle (fun a b h => hc a b h))
    have hg := tt_gain G ((bookPath n).comap e) hle v (fun i => (hpos i).le) a b hab hab'
    have hQ := tt_Q_le ((bookPath n).comap e) hnc v
    rw [tt_Q_of_row G v _ hrow] at hg
    have hvv : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have h3 : specRad ((bookPath n).comap e) * ∑ i, v i * v i ≤ specRad G * ∑ i, v i * v i :=
      mul_le_mul_of_nonneg_right hlam hvv
    nlinarith [mul_pos (hpos a) (hpos b)]
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro a b
  rw [hGB]
  exact Iff.rfl

-- Forward direction from the positive case.
open Classical in
theorem tt_forward (N1 : ℕ) (hN1 : 3 ≤ N1)
    (good : ∀ m ≥ N1, ∀ H : SimpleGraph (Fin m), TaitTobin.Outerplanar.IsSpecMax IsPlanar H →
      ∀ u : Fin m → ℝ, (∀ i, 0 < u i) → (∀ i, u i ≤ 1) → (∃ x, u x = 1) →
      (∀ i, (∑ j, if H.Adj i j then u j else 0) = specRad H * u i) →
      Nonempty (H ≃g bookPath m))
    (n : ℕ) (hn : 16 * (N1 : ℝ) ^ 2 + 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G) : Nonempty (G ≃g bookPath n) := by
  have hN1r : (3:ℝ) ≤ N1 := by exact_mod_cast hN1
  have hNn : N1 < n := by
    have : (N1 : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hn0 : 0 < n := by omega
  obtain ⟨v, hv0, hv1, ⟨x, hx⟩, hrow⟩ := tt_normalized G hn0
  have hB : (N1 : ℝ) < specRad G := by
    have h1 := tt_book_lower n N1 (by positivity) hn
    have h2 := tt_book_le_max (by omega) G hG
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
      have e1 : specRad H = specRad (bookPath k) := wkx_specRad_eq_of_iso φ
      have e2 := tt_book_lt k n (by omega) hkn
      have e3 := tt_book_le_max (by omega) G hG
      linarith
    · have : (k : ℝ) < N1 := by exact_mod_cast (by omega : k < N1)
      linarith

end TTGlue

section TTMain

open WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

-- Assembly: Theorem 15 from Lemmas 11, 13, 14 and the structure lemma for two universal vertices.
open Classical in
theorem tt_main
    (h11 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
        ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
          (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
            ∃ w : Fin n, IsSecondHub G ε v x w)
    (h13 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
        ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
          (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
            ∀ w : Fin n, IsSecondHub G ε v x w → G.Adj x w)
    (h14 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
        ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
          (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
            ∀ w : Fin n, IsSecondHub G ε v x w →
              ∀ u : Fin n, u ≠ x → u ≠ w → G.Adj u x ∧ G.Adj u w)
    (hsub : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsPlanar G → ∀ (x w : Fin n), x ≠ w →
      (∀ y : Fin n, y ≠ x → G.Adj x y) → (∀ y : Fin n, y ≠ w → G.Adj w y) →
      ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)),
        ∀ a b : Fin n, G.Adj a b → (bookPath n).Adj (e a) (e b)) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ G : SimpleGraph (Fin n),
      TaitTobin.Outerplanar.IsSpecMax IsPlanar G ↔ Nonempty (G ≃g bookPath n) := by
  obtain ⟨e11, he11, h11'⟩ := h11
  obtain ⟨e13, he13, h13'⟩ := h13
  obtain ⟨e14, he14, h14'⟩ := h14
  have hmin : 0 < min e11 (min e13 e14) := lt_min he11 (lt_min he13 he14)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min e11 (min e13 e14) / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεm : ε < min e11 (min e13 e14) := by rw [hε]; linarith
  have hε11 : ε < e11 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hε13 : ε < e13 := lt_of_lt_of_le hεm ((min_le_right _ _).trans (min_le_left _ _))
  have hε14 : ε < e14 := lt_of_lt_of_le hεm ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N11, hN11⟩ := h11' ε hε0 hε11
  obtain ⟨N13, hN13⟩ := h13' ε hε0 hε13
  obtain ⟨N14, hN14⟩ := h14' ε hε0 hε14
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, N1 = max (max N11 N13) (max N14 3) := ⟨_, rfl⟩
  have good : ∀ m ≥ N1, ∀ H : SimpleGraph (Fin m),
      TaitTobin.Outerplanar.IsSpecMax IsPlanar H →
      ∀ u : Fin m → ℝ, (∀ i, 0 < u i) → (∀ i, u i ≤ 1) → (∃ x, u x = 1) →
      (∀ i, (∑ j, if H.Adj i j then u j else 0) = specRad H * u i) →
      Nonempty (H ≃g bookPath m) := by
    intro m hm H hH u hpos hle1 hux hrow
    obtain ⟨x, hx⟩ := hux
    have hmv := tt_mulVec_of_row H u hrow
    obtain ⟨w, hw⟩ := hN11 m (by omega) H hH u hmv hpos hle1 x hx
    have h13x := hN13 m (by omega) H hH u hmv hpos hle1 x hx w hw
    have h14x := hN14 m (by omega) H hH u hmv hpos hle1 x hx w hw
    exact tt_core (fun G hG x w hxw hx hw => hsub G hG x w hxw hx hw) H hH u hpos hrow x w
      h13x h14x
  have hN3 : 3 ≤ N1 := by omega
  refine ⟨16 * N1 ^ 2 + 3, fun n hn G => ?_⟩
  have hnr : 16 * (N1 : ℝ) ^ 2 + 3 ≤ n := by exact_mod_cast hn
  constructor
  · exact tt_forward N1 hN3 good n hnr G
  · rintro ⟨φ⟩
    have hGpl : IsPlanar G :=
      tt_planar_pull G (bookPath n) φ Set.univ φ.injective.injOn (fun _ _ _ => trivial)
        (fun _ _ h => φ.map_adj_iff.2 h) (tt_book_planar n)
    obtain ⟨Gs, hGs_mem, hGs_max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun H : SimpleGraph (Fin n) => IsPlanar H)) specRad
      ⟨G, Finset.mem_filter.2 ⟨Finset.mem_univ _, hGpl⟩⟩
    have hGs : TaitTobin.Outerplanar.IsSpecMax IsPlanar Gs :=
      ⟨(Finset.mem_filter.1 hGs_mem).2,
        fun H hH => hGs_max H (Finset.mem_filter.2 ⟨Finset.mem_univ _, hH⟩)⟩
    obtain ⟨ψ⟩ := tt_forward N1 hN3 good n hnr Gs hGs
    have χ : G ≃g Gs := φ.trans ψ.symm
    exact ⟨hGpl, fun H hH => (hGs.2 H hH).trans (le_of_eq (wkx_specRad_eq_of_iso χ).symm)⟩

end TTMain

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G ↔ Nonempty (G ≃g bookPath n) :=
  tt_main TaitTobin.Planar.lemma_11 TaitTobin.Planar.lemma_13 TaitTobin.Planar.lemma_14
    TaitTobin.Planar.subgraph_bookPath_of_universal
