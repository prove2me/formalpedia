-- Prove2me | solution 1 for TaitTobin.Planar.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:49:46.888979+00:00
-- url     : https://prove2.me/submissions/c445ae0a-5697-4878-8685-c6bc9a75db82

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_planar_facts

set_option autoImplicit false

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


theorem tt_book_adj_lr (n : ℕ) (a : Fin 2) (b : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inl a) (Sum.inr b) := trivial

theorem tt_book_adj_rl (n : ℕ) (a : Fin 2) (b : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inr b) (Sum.inl a) := trivial

theorem tt_book_planar (n : ℕ) : IsPlanar (bookPath n) := tt_bookPath_planar (n - 2)

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

end TTGlue

section TTL8

open WangKangXue.SpectralTuran Matrix RobertsonSeymour1986.GM5 TaitTobin.Planar

open Classical in
theorem l8_book_lower (n : ℕ) (hn : 3 ≤ n) :
    Real.sqrt (2 * (n : ℝ) - 4) < specRad (bookPath n) := by
  have hm : 0 < n - 2 := by omega
  have hmR : (((n - 2 : ℕ)) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
  have hV : 0 < Fintype.card (Fin 2 ⊕ Fin (n - 2)) := by simp <;> omega
  let x : Fin 2 ⊕ Fin (n - 2) → ℝ := fun v => match v with
    | Sum.inl _ => Real.sqrt ((n : ℝ) - 2)
    | Sum.inr _ => Real.sqrt 2
  have hpos : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsq1 : Real.sqrt ((n : ℝ) - 2) * Real.sqrt ((n : ℝ) - 2) = (n : ℝ) - 2 :=
    Real.mul_self_sqrt hpos.le
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hN : ∑ i, x i * x i = 4 * ((n : ℝ) - 2) := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, x, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsq1, hsq2, hmR]
    ring
  have hQ : 2 * ((n : ℝ) - 2) + 4 * ((n : ℝ) - 2) * (Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2) ≤
      ∑ i, ∑ j, (if (bookPath n).Adj i j then x i * x j else 0) := by
    have hs : 0 ≤ Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2 := by positivity
    have hx : ∀ i, 0 ≤ x i := by
      intro i; cases i <;> simp [x] <;> positivity
    let g : Fin 2 ⊕ Fin (n - 2) → Fin 2 ⊕ Fin (n - 2) → ℝ := fun i j => match i, j with
      | Sum.inl a, Sum.inl b => if a ≠ b then (n : ℝ) - 2 else 0
      | Sum.inl _, Sum.inr _ => Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2
      | Sum.inr _, Sum.inl _ => Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2
      | Sum.inr _, Sum.inr _ => 0
    have hg : ∑ i, ∑ j, g i j =
        2 * ((n : ℝ) - 2) + 4 * ((n : ℝ) - 2) * (Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2) := by
      simp [Fintype.sum_sum_type, Fin.sum_univ_two, g, hmR]
      ring
    calc 2 * ((n : ℝ) - 2) + 4 * ((n : ℝ) - 2) * (Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2)
        = ∑ i, ∑ j, g i j := hg.symm
      _ ≤ ∑ i, ∑ j, (if (bookPath n).Adj i j then x i * x j else 0) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          rcases i with a | a <;> rcases j with b | b
          · by_cases hab : a ≠ b
            · have hadj : (bookPath n).Adj (Sum.inl a) (Sum.inl b) := hab
              rw [if_pos hadj]
              change (if a ≠ b then (n : ℝ) - 2 else 0) ≤ Real.sqrt ((n : ℝ) - 2) * Real.sqrt ((n : ℝ) - 2)
              rw [if_pos hab, hsq1]
            · change (if a ≠ b then (n : ℝ) - 2 else 0) ≤ _
              rw [if_neg hab]
              split_ifs
              · exact mul_nonneg (hx (Sum.inl a)) (hx (Sum.inl b))
              · exact le_refl _
          · rw [if_pos (tt_book_adj_lr n a b)]
          · rw [if_pos (tt_book_adj_rl n b a)]
            change _ ≤ Real.sqrt 2 * Real.sqrt ((n : ℝ) - 2)
            rw [mul_comm]
          · change (0 : ℝ) ≤ _
            split_ifs
            · exact mul_nonneg (hx (Sum.inr a)) (hx (Sum.inr b))
            · exact le_refl _
  have h := tt_Q_le (bookPath n) hV x
  rw [hN] at h
  have hs2 : Real.sqrt ((n : ℝ) - 2) * Real.sqrt 2 = Real.sqrt (2 * (n : ℝ) - 4) := by
    rw [← Real.sqrt_mul hpos.le]; congr 1; ring
  rw [hs2] at hQ
  nlinarith [hQ, h]

open Classical in
theorem l8_upper {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    specRad G ^ 2 ≤ 2 * (G.edgeFinset.card : ℝ) := by
  have hV : 0 < Fintype.card (Fin n) := by simpa using hn
  obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) hV
  have hl : specRad G = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hV⟩ := by
    unfold specRad; rw [dif_pos hV]
  rw [hl]
  set lam := (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hV⟩ with hlam
  have hrow : ∀ i, lam * v i = ∑ j, (if G.Adj i j then v j else 0) := by
    intro i
    have := congrFun hv i
    rw [wk9_row] at this
    simpa using this.symm
  have hCS : ∀ i, (lam * v i) ^ 2 ≤ (G.degree i : ℝ) := by
    intro i
    rw [hrow i]
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => if G.Adj i j then (1 : ℝ) else 0) v
    have e1 : ∑ j, (if G.Adj i j then (1 : ℝ) else 0) * v j = ∑ j, (if G.Adj i j then v j else 0) := by
      refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> simp
    have e2 : ∑ j, (if G.Adj i j then (1 : ℝ) else 0) ^ 2 = (G.degree i : ℝ) := by
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.sum_boole]
    have e3 : ∑ j, v j ^ 2 = 1 := by
      have : v ⬝ᵥ v = ∑ j, v j ^ 2 := by simp [dotProduct, sq]
      rw [← this]; exact hvv
    rw [e1, e2, e3] at h1
    simpa using h1
  have hsum : ∑ i, (lam * v i) ^ 2 = lam ^ 2 := by
    have : ∑ i, (lam * v i) ^ 2 = lam ^ 2 * ∑ i, v i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    have e3 : ∑ j, v j ^ 2 = 1 := by
      have : v ⬝ᵥ v = ∑ j, v j ^ 2 := by simp [dotProduct, sq]
      rw [← this]; exact hvv
    rw [e3, mul_one]
  have hdeg : ∑ i, (G.degree i : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  rw [← hsum, ← hdeg]
  exact Finset.sum_le_sum (fun i _ => hCS i)

end TTL8

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 in
theorem solution {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G) :
    Real.sqrt (2 * (n : ℝ) - 4) < specRad G ∧ specRad G < Real.sqrt (6 * (n : ℝ)) := by
  constructor
  · exact lt_of_lt_of_le (l8_book_lower n hn) (tt_book_le_max (by omega) G hG)
  · have hf := (TaitTobin.Planar.planar_facts hn G hG.1).2.1
    have h2 := l8_upper (by omega) G
    have hc : (G.edgeFinset.card : ℝ) ≤ 3 * (n : ℝ) - 6 := by
      have : (G.edgeFinset.card : ℝ) ≤ ((3 * n - 6 : ℕ) : ℝ) := by exact_mod_cast hf
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    have h3 : specRad G ^ 2 < 6 * (n : ℝ) := by linarith
    calc specRad G ≤ |specRad G| := le_abs_self _
      _ = Real.sqrt (specRad G ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (6 * (n : ℝ)) := Real.sqrt_lt_sqrt (sq_nonneg _) h3
