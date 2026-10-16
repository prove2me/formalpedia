-- Prove2me | solution 1 for TaitTobin.Planar.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:39:20.722979+00:00
-- url     : https://prove2.me/submissions/bc39c68a-1b08-4988-8e85-8bfc5695e4a6

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_8
import Theorems.Thm_TaitTobin_Planar_planar_pendant

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
section L10

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-- Delete every edge at `u`. -/
def ttDel {V : Type} (G : SimpleGraph V) (u : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ u ∧ b ≠ u
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

/-- Delete every edge at `u`, then join `u` to `a`. -/
def ttSw1 {V : Type} (G : SimpleGraph V) (u a : V) (h : u ≠ a) : SimpleGraph V where
  Adj p q := (ttDel G u).Adj p q ∨ (p = u ∧ q = a) ∨ (q = u ∧ p = a)
  symm := ⟨fun p q hpq => by
    rcases hpq with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
  loopless := ⟨fun p hp => by
    rcases hp with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (ttDel G u).loopless.irrefl p h1
    · exact h (h1.symm.trans h2)
    · exact h (h1.symm.trans h2)⟩

/-- Rayleigh comparison: if the rewired graph (star of `u` deleted, `u` joined to `a`) is planar,
then `v a ≤` the neighbour sum of `u`. -/
theorem l10_contra {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hn : 0 < n)
    (u a : Fin n) (hua : u ≠ a)
    (hpl : IsPlanar (ttSw1 G u a hua)) :
    v a ≤ ∑ j, (if G.Adj u j then v j else 0) := by
  have hQ : (∑ i, ∑ j, (if G.Adj i j then v i * v j else 0)) =
      specRad G * ∑ i, v i * v i := by
    rw [← wk9_quad G v, hmv, dotProduct_smul, smul_eq_mul]
    rfl
  have hle1 : specRad (ttSw1 G u a hua) ≤ specRad G := hG.2 _ hpl
  have hQ1 := tt_Q_le (ttSw1 G u a hua) (by simpa using hn) v
  have hss : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have h0 : ∀ a b, 0 ≤ v a * v b := fun a b => mul_nonneg (hpos a).le (hpos b).le
  have hle01 : ttDel G u ≤ ttSw1 G u a hua := fun p q h => Or.inl h
  have hA1 : (ttSw1 G u a hua).Adj u a := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hN1 : ¬ (ttDel G u).Adj u a := fun h => h.2.1 rfl
  have hg1 := tt_gain (ttDel G u) (ttSw1 G u a hua) hle01 v (fun i => (hpos i).le) u a hA1 hN1
  have key : ∀ i j, (if G.Adj i j then v i * v j else 0) ≤
      (if (ttDel G u).Adj i j then v i * v j else 0) +
      (if i = u then (if G.Adj u j then v u * v j else 0) else 0) +
      (if j = u then (if G.Adj i u then v i * v u else 0) else 0) := by
    intro i j
    by_cases hi : i = u
    · rw [hi]
      have hnd : ¬ (ttDel G u).Adj u j := fun h => h.2.1 rfl
      simp only [hnd, if_false, if_true, zero_add]
      split_ifs <;> nlinarith [h0 u j, h0 j u]
    · by_cases hj : j = u
      · rw [hj]
        have hnd : ¬ (ttDel G u).Adj i u := fun h => h.2.2 rfl
        simp only [hnd, hi, if_false, if_true, zero_add]
        split_ifs <;> nlinarith [h0 i u]
      · have hiff : (ttDel G u).Adj i j ↔ G.Adj i j := ⟨fun h => h.1, fun h => ⟨h, hi, hj⟩⟩
        simp only [hiff, hi, hj, if_false, add_zero]
        exact le_refl _
  have hsum : (∑ i, ∑ j, (if G.Adj i j then v i * v j else 0)) ≤
      (∑ i, ∑ j, (if (ttDel G u).Adj i j then v i * v j else 0)) +
      (∑ j, (if G.Adj u j then v u * v j else 0)) +
      (∑ i, (if G.Adj i u then v i * v u else 0)) := by
    have e1 : ∑ i, ∑ j, (if i = u then (if G.Adj u j then v u * v j else 0) else 0) =
        ∑ j, (if G.Adj u j then v u * v j else 0) := by
      rw [Finset.sum_comm]; simp
    have e2 : ∑ i, ∑ j, (if j = u then (if G.Adj i u then v i * v u else 0) else 0) =
        ∑ i, (if G.Adj i u then v i * v u else 0) := by simp
    rw [← e1, ← e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => key i j)
  have hf : (∑ j, (if G.Adj u j then v u * v j else 0)) =
      v u * ∑ j, (if G.Adj u j then v j else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : G.Adj u j <;> simp [h]
  have hg : (∑ i, (if G.Adj i u then v i * v u else 0)) =
      v u * ∑ j, (if G.Adj u j then v j else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : G.Adj u i
    · have h' : G.Adj i u := h.symm
      simp [h, h']; ring
    · have h' : ¬ G.Adj i u := fun h'' => h h''.symm
      simp [h, h']
  have hspec : specRad (ttSw1 G u a hua) * ∑ i, v i * v i ≤ specRad G * ∑ i, v i * v i :=
    mul_le_mul_of_nonneg_right hle1 hss
  by_contra hcon
  have hlt : ∑ j, (if G.Adj u j then v j else 0) < v a := not_le.1 hcon
  have hpr : 0 < v u * (v a - ∑ j, (if G.Adj u j then v j else 0)) :=
    mul_pos (hpos u) (sub_pos.2 hlt)
  have hpr' : v u * (v a - ∑ j, (if G.Adj u j then v j else 0)) =
      v u * v a - v u * ∑ j, (if G.Adj u j then v j else 0) := by ring
  linarith [hQ, hQ1, hg1, hsum, hf, hg, hspec, hpr, hpr']

/-- The rewired graph is planar: delete the star of `u` (a subgraph), then add the pendant edge. -/
theorem l10_planar {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (u a : Fin n) (hua : u ≠ a) : IsPlanar (ttSw1 G u a hua) := by
  have hdel : IsPlanar (ttDel G u) :=
    tt_planar_pull (ttDel G u) G id Set.univ (Set.injOn_id _) (fun _ _ _ => Set.mem_univ _)
      (fun x y h => h.1) hG
  exact TaitTobin.Planar.planar_pendant (ttDel G u) hdel u a hua (fun q h => h.2.1 rfl)
    (ttSw1 G u a hua) (fun p q => Iff.rfl)

theorem l10_core {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (x : Fin n) (hx : v x = 1) (z : Fin n) :
    1 / Real.sqrt (6 * (n : ℝ)) < v z := by
  have hn0 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h8 := TaitTobin.Planar.lemma_8 hn G hG
  have hlam : 0 < specRad G := lt_of_le_of_lt (Real.sqrt_nonneg _) h8.1
  have hs6 : 0 < Real.sqrt (6 * (n : ℝ)) := Real.sqrt_pos.2 (by linarith)
  by_cases hzx : z = x
  · rw [hzx, hx]
    have h1 : (1 : ℝ) < Real.sqrt (6 * (n : ℝ)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    rw [div_lt_one hs6]
    exact h1
  · have hpl := l10_planar G hG.1 z x hzx
    have hc := l10_contra G hG v hmv hpos (by omega) z x hzx hpl
    have hrow : (G.adjMatrix ℝ).mulVec v z = ∑ j, (if G.Adj z j then v j else 0) :=
      wk9_row G v z
    rw [hmv] at hrow
    simp only [Pi.smul_apply, smul_eq_mul] at hrow
    rw [hx] at hc
    rw [← hrow] at hc
    have h1 : 1 / specRad G ≤ v z := by
      rw [div_le_iff₀ hlam]; linarith
    have h2 : 1 / Real.sqrt (6 * (n : ℝ)) < 1 / specRad G :=
      one_div_lt_one_div_of_lt hlam h8.2
    exact lt_of_lt_of_le h2 h1

end L10

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ z : Fin n, 1 / Real.sqrt (6 * (n : ℝ)) < v z := by
  refine ⟨3, fun n hn G hG v hv hpos _ x hx z => ?_⟩
  exact l10_core hn G hG v hv hpos x hx z
