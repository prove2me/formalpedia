-- Prove2me | solution 1 for TaitTobin.Planar.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:10:32.951706+00:00
-- url     : https://prove2.me/submissions/76bf511b-df17-4fc8-8271-37701c934cd8

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_12
import Theorems.Thm_TaitTobin_Planar_lemma_13
import Theorems.Thm_TaitTobin_Planar_planar_facts
import Theorems.Thm_TaitTobin_Planar_planar_attach_to_edge

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

section L14

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

/-- Delete every edge at `u`, then join `u` to `a` and to `b`. -/
def ttSw {V : Type} (G : SimpleGraph V) (u a b : V) (ha : u ≠ a) (hb : u ≠ b) : SimpleGraph V where
  Adj p q := (ttDel G u).Adj p q ∨ (p = u ∧ (q = a ∨ q = b)) ∨ (q = u ∧ (p = a ∨ p = b))
  symm := ⟨fun p q hpq => by
    rcases hpq with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
  loopless := ⟨fun p hp => by
    rcases hp with h1 | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · exact (ttDel G u).loopless.irrefl p h1
    · exact ha (h1.symm.trans h2)
    · exact hb (h1.symm.trans h2)
    · exact ha (h1.symm.trans h2)
    · exact hb (h1.symm.trans h2)⟩

/-- Rayleigh comparison: if the switched graph is planar, then `v_a + v_b ≤` the neighbour sum
of `u`. -/
theorem l14_contra {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hn : 0 < n)
    (u x w : Fin n) (hux : u ≠ x) (huw : u ≠ w) (hxw : x ≠ w)
    (hpl : IsPlanar (ttSw G u x w hux huw)) :
    v x + v w ≤ ∑ j, (if G.Adj u j then v j else 0) := by
  have hQ : (∑ i, ∑ j, (if G.Adj i j then v i * v j else 0)) =
      specRad G * ∑ i, v i * v i := by
    rw [← wk9_quad G v, hmv, dotProduct_smul, smul_eq_mul]
    rfl
  have hle1 : specRad (ttSw G u x w hux huw) ≤ specRad G := hG.2 _ hpl
  have hQ1 := tt_Q_le (ttSw G u x w hux huw) (by simpa using hn) v
  have hss : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have h0 : ∀ a b, 0 ≤ v a * v b := fun a b => mul_nonneg (hpos a).le (hpos b).le
  -- G0 ≤ G1 ≤ G'
  have hle01 : ttDel G u ≤ ttSw1 G u x hux := fun a b h => Or.inl h
  have hle12 : ttSw1 G u x hux ≤ ttSw G u x w hux huw := by
    intro a b h
    rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
    · exact Or.inr (Or.inr ⟨h1, Or.inl h2⟩)
  have hA1 : (ttSw1 G u x hux).Adj u x := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hN1 : ¬ (ttDel G u).Adj u x := fun h => h.2.1 rfl
  have hA2 : (ttSw G u x w hux huw).Adj u w := Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
  have hN2 : ¬ (ttSw1 G u x hux).Adj u w := by
    rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
    · exact h.2.1 rfl
    · exact hxw h2.symm
    · exact huw h1.symm
  have hg1 := tt_gain (ttDel G u) (ttSw1 G u x hux) hle01 v (fun i => (hpos i).le) u x hA1 hN1
  have hg2 := tt_gain (ttSw1 G u x hux) (ttSw G u x w hux huw) hle12 v (fun i => (hpos i).le) u w hA2 hN2
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
  have hspec : specRad (ttSw G u x w hux huw) * ∑ i, v i * v i ≤ specRad G * ∑ i, v i * v i :=
    mul_le_mul_of_nonneg_right hle1 hss
  by_contra hcon
  have hlt : ∑ j, (if G.Adj u j then v j else 0) < v x + v w := not_le.1 hcon
  have hpr : 0 < v u * (v x + v w - ∑ j, (if G.Adj u j then v j else 0)) :=
    mul_pos (hpos u) (sub_pos.2 hlt)
  have hpr' : v u * (v x + v w - ∑ j, (if G.Adj u j then v j else 0)) =
      v u * v x + v u * v w - v u * ∑ j, (if G.Adj u j then v j else 0) := by ring
  linarith [hQ, hQ1, hg1, hg2, hsum, hf, hg, hspec, hpr, hpr']

/-- A planar graph on `Fin n` has, in any nonempty vertex set `A`, a vertex with at most five
neighbours in `A`. -/
theorem l14_mindeg {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G) (A : Finset (Fin n))
    (hA : A.Nonempty) : ∃ u ∈ A, (A.filter (fun y => G.Adj u y)).card ≤ 5 := by
  by_cases hsmall : A.card ≤ 6
  · obtain ⟨u, hu⟩ := hA
    refine ⟨u, hu, ?_⟩
    have hsub : A.filter (fun y => G.Adj u y) ⊆ A.erase u := by
      intro y hy
      rw [Finset.mem_filter] at hy
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hy.2).symm, hy.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hu] at this
    omega
  · have hbig : 7 ≤ A.card := by omega
    let g : Fin A.card → Fin n := fun i => (A.equivFin.symm i).1
    have hginj : Function.Injective g := fun i j h => A.equivFin.symm.injective (Subtype.ext h)
    let H : SimpleGraph (Fin A.card) := SimpleGraph.comap g G
    have hH : IsPlanar H :=
      tt_planar_pull H G g Set.univ hginj.injOn (fun _ _ _ => Set.mem_univ _) (fun _ _ h => h) hG
    have hm3 : 3 ≤ A.card := by omega
    have hfacts : H.edgeFinset.card ≤ 3 * A.card - 6 :=
      (TaitTobin.Planar.planar_facts hm3 H hH).2.1
    have hhand : ∑ i, H.degree i = 2 * H.edgeFinset.card := by
      convert SimpleGraph.sum_degrees_eq_twice_card_edges H
    have hex : ∃ i, H.degree i ≤ 5 := by
      by_contra hcon
      have hall : ∀ i, 6 ≤ H.degree i := fun i => by
        by_contra h; exact hcon ⟨i, by omega⟩
      have h6 : ∑ _i : Fin A.card, 6 ≤ ∑ i, H.degree i :=
        Finset.sum_le_sum (fun i _ => hall i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h6
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨g i, (A.equivFin.symm i).2, ?_⟩
    have himg : A.filter (fun y => G.Adj (g i) y) = (H.neighborFinset i).image g := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_neighborFinset,
        SimpleGraph.comap_adj, H]
      constructor
      · rintro ⟨hy, hadj⟩
        refine ⟨A.equivFin ⟨y, hy⟩, ?_, ?_⟩
        · simpa [g] using hadj
        · simp [g]
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(A.equivFin.symm j).2, hj⟩
    rw [himg, Finset.card_image_of_injective _ hginj]
    exact hi

end L14

section L14b

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-- At most two neighbours of `u` are adjacent to both ends `x`, `w` of an edge (`K₃,₃`-freeness). -/
theorem l14_k33 {n : ℕ} (hn3 : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (u x w : Fin n) (hux : u ≠ x) (huw : u ≠ w) (hxw : x ≠ w) :
    ((Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w)).card) ≤ 2 := by
  by_contra hcon
  have h3 : 2 < (Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w)).card :=
    not_le.1 hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h3
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hfree := (TaitTobin.Planar.planar_facts hn3 G hG).1
  apply hfree
  let f : Fin 3 ⊕ Fin 3 → Fin n := Sum.elim ![u, x, w] ![a, b, c]
  have hadj : ∀ (i : Fin 3) (j : Fin 3), G.Adj (![u, x, w] i) (![a, b, c] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ha.1, hb.1, hc.1, ha.2.1.symm, hb.2.1.symm, hc.2.1.symm,
      ha.2.2.symm, hb.2.2.symm, hc.2.2.symm]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (i | i) (j | j) h
    · simp [completeBipartiteGraph_adj] at h
    · exact hadj i j
    · exact (hadj j i).symm
    · simp [completeBipartiteGraph_adj] at h
  · have hne : ∀ (i : Fin 3) (j : Fin 3), ![u, x, w] i ≠ ![a, b, c] j := fun i j =>
      (hadj i j).ne
    rintro (i | i) (j | j) h
    · congr 1
      fin_cases i <;> fin_cases j <;> simp_all [f]
    · exact absurd h (by simpa [f] using hne i j)
    · exact absurd h.symm (by simpa [f] using hne j i)
    · congr 1
      fin_cases i <;> fin_cases j <;> simp_all [f]

end L14b

section L14c

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

theorem l14_core {n : ℕ} (ε : ℝ) (hε1 : ε < 1/80)
    (G : SimpleGraph (Fin n)) (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) (x : Fin n) (hx : v x = 1)
    (w : Fin n) (hw : IsSecondHub G ε v x w) (hn3 : 3 ≤ n) (hxw : G.Adj x w)
    (h12 : ∀ u : Fin n, u ≠ x → u ≠ w → v u < 1 / 10) :
    ∀ u : Fin n, u ≠ x → u ≠ w → G.Adj u x ∧ G.Adj u w := by
  intro u0 hu0x hu0w
  by_contra hcon
  have hxw' : x ≠ w := hxw.ne
  set A : Finset (Fin n) :=
    Finset.univ.filter (fun y => y ≠ x ∧ y ≠ w ∧ ¬ (G.Adj y x ∧ G.Adj y w)) with hAdef
  have hA : A.Nonempty := ⟨u0, by simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hu0x, hu0w, hcon⟩⟩
  obtain ⟨u, huA, hdeg⟩ := l14_mindeg G hG.1 A hA
  simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at huA
  obtain ⟨hux, huw, hunot⟩ := huA
  have hux' : u ≠ x := hux
  have huw' : u ≠ w := huw
  -- neighbour sum bound
  have hT : ∑ j, (if G.Adj u j then v j else 0) ≤ 17 / 10 := by
    set N : Finset (Fin n) := Finset.univ.filter (fun j => G.Adj u j) with hN
    have hsumN : ∑ j, (if G.Adj u j then v j else 0) = ∑ j ∈ N, v j := by
      rw [hN, Finset.sum_filter]
    rw [hsumN]
    set N1 : Finset (Fin n) := N.filter (fun j => j = x ∨ j = w) with hN1
    set N2 : Finset (Fin n) := N.filter (fun j => ¬ (j = x ∨ j = w)) with hN2
    have hsplit : ∑ j ∈ N, v j = ∑ j ∈ N1, v j + ∑ j ∈ N2, v j :=
      (Finset.sum_filter_add_sum_filter_not N (fun j => j = x ∨ j = w) v).symm
    have hc1 : N1.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [hN1, hN, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rcases ha with ⟨ha1, ha2 | ha2⟩ <;> rcases hb with ⟨hb1, hb2 | hb2⟩
      · rw [ha2, hb2]
      · exfalso; apply hunot; rw [ha2] at ha1; rw [hb2] at hb1
        exact ⟨ha1, hb1⟩
      · exfalso; apply hunot; rw [ha2] at ha1; rw [hb2] at hb1
        exact ⟨hb1, ha1⟩
      · rw [ha2, hb2]
    have hs1 : ∑ j ∈ N1, v j ≤ 1 := by
      calc ∑ j ∈ N1, v j ≤ ∑ _j ∈ N1, (1:ℝ) := Finset.sum_le_sum (fun j _ => hle j)
        _ = N1.card := by simp
        _ ≤ 1 := by exact_mod_cast hc1
    set B2 : Finset (Fin n) := N2.filter (fun j => G.Adj j x ∧ G.Adj j w) with hB2
    set A2 : Finset (Fin n) := N2.filter (fun j => ¬ (G.Adj j x ∧ G.Adj j w)) with hA2
    have hsplit2 : ∑ j ∈ N2, v j = ∑ j ∈ B2, v j + ∑ j ∈ A2, v j :=
      (Finset.sum_filter_add_sum_filter_not N2 (fun j => G.Adj j x ∧ G.Adj j w) v).symm
    have hv2 : ∀ j ∈ N2, v j ≤ 1 / 10 := by
      intro j hj
      simp only [hN2, Finset.mem_filter, not_or] at hj
      exact (h12 j hj.2.1 hj.2.2).le
    have hB2c : B2.card ≤ 2 := by
      have hsub : B2 ⊆ Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w) := by
        intro j hj
        simp only [hB2, hN2, hN, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨hj.1.1, hj.2⟩
      exact (Finset.card_le_card hsub).trans (l14_k33 hn3 G hG.1 u x w hux' huw' hxw')
    have hA2c : A2.card ≤ 5 := by
      have hsub : A2 ⊆ A.filter (fun y => G.Adj u y) := by
        intro j hj
        simp only [hA2, hN2, hN, hAdef, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hj ⊢
        exact ⟨⟨hj.1.2.1, hj.1.2.2, hj.2⟩, hj.1.1⟩
      exact (Finset.card_le_card hsub).trans hdeg
    have hsB : ∑ j ∈ B2, v j ≤ 2 / 10 := by
      calc ∑ j ∈ B2, v j ≤ ∑ _j ∈ B2, (1/10 : ℝ) :=
            Finset.sum_le_sum (fun j hj => hv2 j (Finset.mem_filter.1 hj).1)
        _ = B2.card * (1/10) := by simp
        _ ≤ 2 * (1/10) := by
            have : (B2.card : ℝ) ≤ 2 := by exact_mod_cast hB2c
            linarith
        _ = 2 / 10 := by norm_num
    have hsA : ∑ j ∈ A2, v j ≤ 5 / 10 := by
      calc ∑ j ∈ A2, v j ≤ ∑ _j ∈ A2, (1/10 : ℝ) :=
            Finset.sum_le_sum (fun j hj => hv2 j (Finset.mem_filter.1 hj).1)
        _ = A2.card * (1/10) := by simp
        _ ≤ 5 * (1/10) := by
            have : (A2.card : ℝ) ≤ 5 := by exact_mod_cast hA2c
            linarith
        _ = 5 / 10 := by norm_num
    linarith
  -- planarity of the switched graph
  have hG0 : IsPlanar (ttDel G u) :=
    tt_planar_pull (ttDel G u) G id Set.univ Function.injective_id.injOn
      (fun _ _ _ => Set.mem_univ _) (fun a b h => h.1) hG.1
  have hxw0 : (ttDel G u).Adj x w := ⟨hxw, fun h => hux' h.symm, fun h => huw' h.symm⟩
  have hiso : ∀ q, ¬ (ttDel G u).Adj u q := fun q h => h.2.1 rfl
  have hpl : IsPlanar (ttSw G u x w hux' huw') :=
    TaitTobin.Planar.planar_attach_to_edge (ttDel G u) hG0 x w u hxw0 hiso
      (ttSw G u x w hux' huw') (fun p q => Iff.rfl)
  have hfin := l14_contra G hG v hmv hpos (by omega) u x w hux' huw' hxw' hpl
  have hvw := hw.2.2.1
  rw [hx] at hfin
  nlinarith

end L14c

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w →
          ∀ u : Fin n, u ≠ x → u ≠ w → G.Adj u x ∧ G.Adj u w := by
  obtain ⟨e12, he12, h12⟩ := TaitTobin.Planar.lemma_12
  obtain ⟨e13, he13, h13⟩ := TaitTobin.Planar.lemma_13
  refine ⟨min (min e12 e13) (1/80), lt_min (lt_min he12 he13) (by norm_num), fun ε hε0 hε1 => ?_⟩
  have hε12 : ε < e12 := lt_of_lt_of_le hε1 ((min_le_left _ _).trans (min_le_left _ _))
  have hε13 : ε < e13 := lt_of_lt_of_le hε1 ((min_le_left _ _).trans (min_le_right _ _))
  have hε80 : ε < 1/80 := lt_of_lt_of_le hε1 (min_le_right _ _)
  obtain ⟨N12, hN12⟩ := h12 ε hε0 hε12
  obtain ⟨N13, hN13⟩ := h13 ε hε0 hε13
  refine ⟨max (max N12 N13) 3, fun n hn G hG v hv hpos hle x hx w hw => ?_⟩
  have hn' := hn
  simp only [ge_iff_le, max_le_iff] at hn'
  obtain ⟨⟨hn12, hn13⟩, hn3⟩ := hn'
  exact l14_core ε hε80 G hG v hv hpos hle x hx w hw hn3
    (hN13 n hn13 G hG v hv hpos hle x hx w hw)
    (fun u hux huw => hN12 n hn12 G hG v hv hpos hle x hx w hw u hux huw)
