-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:40:50.016846+00:00
-- url     : https://prove2.me/submissions/2fef89e8-e515-41c0-a258-93fbd0fab015

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

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
theorem wk9_key {V : Type*} [Fintype V] [DecidableEq V] (G G' : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hG : G.Connected) (hle : G' ≤ G) (hne : G' ≠ G) (h : 0 < Fintype.card V) :
    (G'.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, h⟩ <
      (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, h⟩ := by
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (G'.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, h⟩ := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, h⟩ := ⟨_, rfl⟩
  have hLe := wk9_le (G.isHermitian_adjMatrix ℝ) h
  obtain ⟨v, hvv, hv⟩ := wk9_exists (G'.isHermitian_adjMatrix ℝ) h
  rw [← hμ, ← hL]
  rw [← hμ] at hv
  rw [← hL] at hLe
  obtain ⟨x, hxd⟩ : ∃ x : V → ℝ, x = fun i => |v i| := ⟨_, rfl⟩
  have hx0 : ∀ i, 0 ≤ x i := by intro i; rw [hxd]; exact abs_nonneg _
  have hxx : x ⬝ᵥ x = 1 := by
    rw [← hvv, hxd]
    simp only [dotProduct, abs_mul_abs_self]
  have hq' : μ ≤ x ⬝ᵥ (G'.adjMatrix ℝ *ᵥ x) := by
    have : v ⬝ᵥ (G'.adjMatrix ℝ *ᵥ v) = μ := by
      rw [hv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    rw [← this, wk9_quad, wk9_quad]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs
    · rw [hxd]; simp only [← abs_mul]; exact le_abs_self _
    · exact le_rfl
  have hD : ∀ i j, 0 ≤ (if G.Adj i j then x i * x j else 0) -
      (if G'.Adj i j then x i * x j else 0) := by
    intro i j
    by_cases h1 : G'.Adj i j
    · rw [if_pos (hle h1), if_pos h1]; simp
    · rw [if_neg h1]
      split_ifs
      · simpa using mul_nonneg (hx0 i) (hx0 j)
      · simp
  have hqq : x ⬝ᵥ (G'.adjMatrix ℝ *ᵥ x) ≤ x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
    rw [wk9_quad, wk9_quad]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    linarith [hD i j]
  by_contra hcon
  push Not at hcon
  have hupper := hLe x
  rw [hxx, mul_one] at hupper
  have heq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = L * (x ⬝ᵥ x) := by
    rw [hxx, mul_one]; linarith
  have hev := wk9_eq _ (wk9_transpose (G.isHermitian_adjMatrix ℝ)) L hLe x heq
  -- missing edge
  obtain ⟨a, b, hab, hab'⟩ : ∃ a b, G.Adj a b ∧ ¬ G'.Adj a b := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hle (fun a b h => hc a b h))
  have hsame : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) - x ⬝ᵥ (G'.adjMatrix ℝ *ᵥ x) = 0 := by linarith
  rw [wk9_quad, wk9_quad, ← Finset.sum_sub_distrib] at hsame
  simp only [← Finset.sum_sub_distrib] at hsame
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hD i j))).mp hsame a (Finset.mem_univ _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hD a j)).mp hrow b
    (Finset.mem_univ _)
  rw [if_pos hab, if_neg hab', sub_zero] at hterm
  -- zero propagation
  have hprop : ∀ i j, x i = 0 → G.Adj i j → x j = 0 := by
    intro i j hi hij
    have hr := congrFun hev i
    rw [wk9_row, Pi.smul_apply, hi, smul_eq_mul, mul_zero] at hr
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ (if G.Adj i k then x k else 0) := by
      intro k _; split_ifs
      · exact hx0 k
      · exact le_rfl
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hr j (Finset.mem_univ _)
    rwa [if_pos hij] at this
  have hwalk : ∀ (u w : V) (p : G.Walk u w), x u = 0 → x w = 0 := by
    intro u w p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hu => ih (hprop _ _ hu hadj)
  obtain ⟨c, hc⟩ : ∃ c, x c = 0 := by
    rcases mul_eq_zero.mp hterm with h1 | h1
    · exact ⟨a, h1⟩
    · exact ⟨b, h1⟩
  have hall : ∀ i, x i = 0 := fun i => hwalk c i (hG.preconnected c i).some hc
  have : x ⬝ᵥ x = 0 := by simp [dotProduct, hall]
  rw [hxx] at this
  exact one_ne_zero this

/- Lemma 2.3 (Wang–Kang–Xue): a proper spanning subgraph of a connected graph has smaller λ. -/
open WangKangXue.SpectralTuran Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G G' : SimpleGraph V)
    (hG : G.Connected) (hle : G' ≤ G) (hne : G' ≠ G) :
    specRad G' < specRad G := by
  have h : 0 < Fintype.card V := by
    have := hG.nonempty
    exact Fintype.card_pos
  unfold WangKangXue.SpectralTuran.specRad
  rw [dif_pos h, dif_pos h]
  exact wk9_key G G' hG hle hne h
