-- Prove2me | solution 1 for TinyCoreset.DimRed.theorem22_dimensionality_reduction
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:11:07.033735+00:00
-- url     : https://prove2.me/submissions/305a3182-c958-481d-a4ce-632fbed41436

import Theorems.Thm_TinyCoreset_DimRed_corollary16_subspace_coreset_bound
import Theorems.Thm_TinyCoreset_DimRed_corollary20_projected_truncation_error
import Theorems.Thm_TinyCoreset_DimRed_corollary21_weak_triangle
import Theorems.Thm_TinyCoreset_DimRed_eq9_pythagoras_for_shapes
import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

set_option autoImplicit false

open TinyCoreset
open TinyCoreset.DimRed

open scoped Matrix

open scoped InnerProductSpace
open ProjLikeRetr.FixedRank

private theorem basis_pair {d j : ℕ} (L : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hL : Module.finrank ℝ L = j) :
    ∃ (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ),
      Xᵀ * X = 1 ∧ Yᵀ * Y = 1 ∧ Xᵀ * Y = 0 ∧ L ≤ LinearMap.range (Matrix.toEuclideanLin X) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hdim : Module.finrank ℝ Lᗮ = d - j := by
    have h := L.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hL] at h
    omega
  let x := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  let y := (stdOrthonormalBasis ℝ Lᗮ).reindex (finCongr hdim)
  let X : Matrix (Fin d) (Fin j) ℝ := Matrix.of fun i a => (x a : E) i
  let Y : Matrix (Fin d) (Fin (d - j)) ℝ := Matrix.of fun i b => (y b : E) i
  have gram {s : ℕ} {K : Submodule ℝ E} (b : OrthonormalBasis (Fin s) ℝ K) :
      let M : Matrix (Fin d) (Fin s) ℝ := Matrix.of fun i a => (b a : E) i
      Mᵀ * M = 1 := by
    intro M
    ext i l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := orthonormal_iff_ite.mp b.orthonormal i l
    change ⟪(b i : E), (b l : E)⟫_ℝ = _ at h
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ a, M a i * M a l) = _
    simpa [M, dotProduct, mul_comm] using h
  refine ⟨X, Y, gram x, gram y, ?_, ?_⟩
  · ext i l
    have h := L.inner_right_of_mem_orthogonal (x i).property (y l).property
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.zero_apply]
    change (∑ a, X a i * Y a l) = 0
    simpa [X, Y, dotProduct, mul_comm] using h
  · intro v hv
    let vL : L := ⟨v, hv⟩
    refine ⟨x.repr vL, ?_⟩
    have expand (c : EuclideanSpace ℝ (Fin j)) : Matrix.toEuclideanLin X c = ∑ a, c a • (x a : E) := by
      ext i
      change (X *ᵥ WithLp.ofLp c) i = WithLp.ofLp (∑ a, c a • (x a : E)) i
      simp [Matrix.mulVec, dotProduct, X, WithLp.ofLp_sum, Finset.sum_apply, mul_comm]
    rw [expand]
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun b : L => (b : E)) (x.sum_repr vL)

theorem solution {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j m : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hm : ⌈8 * (j : ℝ) / ε ^ 2⌉₊ ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCL : ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
      Module.finrank ℝ L = j ∧ C ⊆ L) :
    |(distSq (ProjLikeRetr.FixedRank.truncSVD m U S V) C +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - distSq A C| ≤
      ε * distSq A C := by
  obtain ⟨L, hL, hLC⟩ := hCL
  obtain ⟨X, Y, hX, hY, hXY, hspan⟩ := basis_pair L hL
  have hCX : C ⊆ LinearMap.range (Matrix.toEuclideanLin X) := fun _ hx => hspan (hLC hx)
  let η : ℝ := ε ^ 2 / 4
  let δ : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjle : j ≤ m + 1 := by
    have hεsq : ε ^ 2 ≤ 1 := by nlinarith [mul_nonneg hε0.le (sub_nonneg.mpr hε1)]
    have h₁ : j ≤ 8 * (j : ℝ) / ε ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < ε ^ 2)).2
      nlinarith [mul_le_mul_of_nonneg_left hεsq hjpos.le]
    have h₂ : 8 * (j : ℝ) / ε ^ 2 ≤ ((m + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    exact_mod_cast h₁.trans h₂
  have hcut : ⌈(j : ℝ) / η⌉₊ + j ≤ m + 1 := by
    suffices h : ⌈(j : ℝ) / η⌉₊ ≤ m + 1 - j by omega
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub hjle]
    have hraw : 8 * (j : ℝ) / ε ^ 2 ≤ ((m + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    have aux : (j : ℝ) ≤ 4 * (j : ℝ) / ε ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < ε ^ 2)).2
      nlinarith [mul_le_mul_of_nonneg_left (show ε ^ 2 ≤ 1 by nlinarith [mul_nonneg hε0.le (sub_nonneg.mpr hε1)]) hjpos.le]
    have heq : (j : ℝ) / η = 4 * (j : ℝ) / ε ^ 2 := by
      dsimp [η]
      field_simp [hε0.ne']
    rw [heq]
    linarith [show 8 * (j : ℝ) / ε ^ 2 = 2 * (4 * (j : ℝ) / ε ^ 2) by ring]
  let B := truncSVD m U S V
  let F := frobSq (A * Y)
  let G := distSq (A * X * Xᵀ) C
  let D := frobSq (A - B)
  have err1 := corollary16_subspace_coreset_bound A U S V hA j hj1 hjd η hη m hcut hmnd Y hY
  have err2 := (corollary20_projected_truncation_error A U S V hA j hj1 hjd η hη m hcut hmnd X Y hX hY hXY).2
  have hA_split : distSq A C = F + G := eq9_pythagoras_for_shapes (by omega) X Y hX hY hXY A C hC hCX
  have hB_split : distSq B C = frobSq (B * Y) + distSq (B * X * Xᵀ) C :=
    eq9_pythagoras_for_shapes (by omega) X Y hX hY hXY B C hC hCX
  have weak := corollary21_weak_triangle δ hδ (A * X * Xᵀ) (B * X * Xᵀ) C hC
  change |G - distSq (B * X * Xᵀ) C| ≤ δ * G +
    (1 + 1 / δ) * frobSq (A * X * Xᵀ - B * X * Xᵀ) at weak
  have hweak := weak.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left err2 (by positivity : 0 ≤ 1 + 1 / δ)))
  rw [abs_sub_comm] at hweak
  have hone : |(frobSq (B * Y) + D) - F| ≤ η * F := by
    change F ≤ frobSq (B * Y) + D ∧ frobSq (B * Y) + D ≤ (1 + η) * F at err1
    rw [abs_of_nonneg (sub_nonneg.mpr err1.1)]
    linarith [err1.2]
  have coefficient : (2 + 1 / δ) * η ≤ ε := by
    have heq : (2 + 1 / δ) * η = (ε ^ 2 + ε) / 2 := by
      dsimp [δ, η]
      field_simp [hε0.ne']
      ring
    rw [heq]
    nlinarith [mul_nonneg hε0.le (sub_nonneg.mpr hε1)]
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change |(distSq B C + D) - distSq A C| ≤ _
  rw [hA_split, hB_split]
  calc
    _ = |((frobSq (B * Y) + D) - F) + (distSq (B * X * Xᵀ) C - G)| := by congr 1; ring
    _ ≤ |(frobSq (B * Y) + D) - F| + |distSq (B * X * Xᵀ) C - G| := abs_add_le _ _
    _ ≤ η * F + (δ * G + (1 + 1 / δ) * (η * F)) := add_le_add hone hweak
    _ = (2 + 1 / δ) * η * F + δ * G := by ring
    _ ≤ ε * F + ε * G := add_le_add (mul_le_mul_of_nonneg_right coefficient hF)
      (mul_le_mul_of_nonneg_right (by dsimp [δ]; linarith) hG)
    _ = ε * (F + G) := by ring
