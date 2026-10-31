-- Prove2me | solution 1 for WainwrightHDS.NucNorm.cone_constraint_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:33:04.388028+00:00
-- url     : https://prove2.me/submissions/751f7835-54c9-4d0f-8d5b-444209bf03e2

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_projMperp
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
import Theorems.Thm_WainwrightHDS_NucNorm_isLUB_traceInner_nucNorm_le_one
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_le
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_smul

open WainwrightHDS.NucNorm

lemma toEuclideanLin_mul {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

lemma toEuclideanLin_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Matrix.toEuclideanLin A.transpose = (Matrix.toEuclideanLin A).adjoint := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma starProjection_toLinearMap_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Submodule ℝ E) :
    ((U.starProjection : E →L[ℝ] E).toLinearMap).adjoint = (U.starProjection : E →L[ℝ] E).toLinearMap := by
  rw [ContinuousLinearMap.adjoint_toLinearMap]
  congr 1
  have h : star U.starProjection = U.starProjection := (isSelfAdjoint_starProjection U).star_eq
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

lemma toEuclideanLin_projMat {d : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix.toEuclideanLin (projMat U) = (U.starProjection : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).toLinearMap := by
  dsimp [projMat]
  exact Matrix.toEuclideanLin.apply_symm_apply _

lemma projMat_transpose {d : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    (projMat U).transpose = projMat U := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_transpose, toEuclideanLin_projMat]
  exact starProjection_toLinearMap_adjoint U

lemma projM_mem_Mspace {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projM U V Θ ∈ Mspace U V := by
  dsimp [Mspace, projM]
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, projMat_transpose, projMat_transpose]
    rw [toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection V).le
  · rw [Matrix.mul_assoc, toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection U).le

lemma projMbarPerp_mem_MbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projMbarPerp U V Δ ∈ MbarPerp U V := by
  dsimp [MbarPerp, projMbarPerp]
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, projMat_transpose, projMat_transpose]
    rw [toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection Vᗮ).le
  · rw [Matrix.mul_assoc, toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection Uᗮ).le

lemma traceInner_comm {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = traceInner B A := by
  unfold traceInner
  simp_rw [mul_comm]

lemma traceInner_smul_left {d₁ d₂ : ℕ} (c : ℝ) (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (c • A) B = c * traceInner A B := by
  unfold traceInner
  simp_rw [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma traceInner_neg_left {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (-A) B = - traceInner A B := by
  unfold traceInner
  simp_rw [Matrix.neg_apply, neg_mul, ← Finset.sum_neg_distrib]

lemma traceInner_add_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  unfold traceInner
  simp_rw [Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

lemma opNorm2_neg {d₁ d₂ : ℕ} (G : Matrix (Fin d₁) (Fin d₂) ℝ) :
    opNorm2 (-G) = opNorm2 G := by
  dsimp [opNorm2]
  rw [map_neg Matrix.toEuclideanLin, map_neg LinearMap.toContinuousLinearMap, norm_neg]

lemma nucNorm_neg {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (-M) = nucNorm M := by
  have h := nucNorm_smul (-1 : ℝ) M
  have h_neg_one : (-1 : ℝ) • M = -M := by
    ext i j
    simp [Matrix.smul_apply]
  rw [h_neg_one] at h
  have h_abs : |(-1 : ℝ)| = 1 := by norm_num
  rw [h_abs, one_mul] at h
  exact h

lemma traceInner_le_opNorm2_mul_nucNorm {d₁ d₂ : ℕ} (M N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner M N ≤ opNorm2 N * nucNorm M := by
  have hlub := isLUB_traceInner_nucNorm_le_one N
  have hub := hlub.1
  by_cases hpos : 0 < nucNorm M
  · have h_le_one : nucNorm ((nucNorm M)⁻¹ • M) ≤ 1 := by
      rw [nucNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    have h_mem : traceInner ((nucNorm M)⁻¹ • M) N ∈ {t : ℝ | ∃ M' : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M' ≤ 1 ∧ t = traceInner M' N} :=
      ⟨(nucNorm M)⁻¹ • M, h_le_one, rfl⟩
    have h_bound := hub h_mem
    rw [traceInner_smul_left] at h_bound
    have h_mul := mul_le_mul_of_nonneg_right h_bound (le_of_lt hpos)
    have h_cancel : (nucNorm M)⁻¹ * traceInner M N * nucNorm M = traceInner M N := by
      calc (nucNorm M)⁻¹ * traceInner M N * nucNorm M
        _ = traceInner M N * ((nucNorm M)⁻¹ * nucNorm M) := by ring
        _ = traceInner M N * 1 := by rw [inv_mul_cancel₀ (ne_of_gt hpos)]
        _ = traceInner M N := mul_one _
    rwa [h_cancel] at h_mul
  · have hzero : nucNorm M = 0 := by
      have : 0 ≤ nucNorm M := by
        dsimp [nucNorm, singVal]
        exact Finset.sum_nonneg (fun j _ => LinearMap.singularValues_nonneg _ _)
      linarith
    rw [hzero, mul_zero]
    by_contra! h_gt
    let c := (opNorm2 N + 1) / traceInner M N
    have hc_pos : 0 < c := div_pos (by
      have : 0 ≤ opNorm2 N := norm_nonneg _
      linarith) h_gt
    have hc_bound : nucNorm (c • M) ≤ 1 := by
      rw [nucNorm_smul, abs_of_pos hc_pos, hzero, mul_zero]
      linarith
    have h_mem : traceInner (c • M) N ∈ {t : ℝ | ∃ M' : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M' ≤ 1 ∧ t = traceInner M' N} :=
      ⟨c • M, hc_bound, rfl⟩
    have h_ub := hub h_mem
    rw [traceInner_smul_left] at h_ub
    dsimp [c] at h_ub
    rw [div_mul_cancel₀ (opNorm2 N + 1) (ne_of_gt h_gt)] at h_ub
    linarith

lemma projMbar_add_projMbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projMbar U V Δ + projMbarPerp U V Δ = Δ := by
  dsimp [projMbar]
  abel

lemma projM_add_projMperp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projM U V Θ + projMperp U V Θ = Θ := by
  dsimp [projMperp]
  abel

theorem solution {d₁ d₂ : ℕ}
    (L : Matrix (Fin d₁) (Fin d₂) ℝ → ℝ) (Θstar G : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hG : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, L Θstar + traceInner G Δ ≤ L (Θstar + Δ))
    (lam : ℝ) (hlam : 0 < lam) (hlamG : 2 * opNorm2 G ≤ lam)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, L Θhat + lam * nucNorm Θhat ≤ L Θ + lam * nucNorm Θ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) :
    nucNorm (projMbarPerp U V (Θhat - Θstar)) ≤
      3 * nucNorm (projMbar U V (Θhat - Θstar)) + 4 * nucNorm (projMperp U V Θstar) := by
  let Δ := Θhat - Θstar
  let M := projM U V Θstar
  let Mperp := projMperp U V Θstar
  let ΔMbar := projMbar U V Δ
  let ΔMbarPerp := projMbarPerp U V Δ

  have h_decomp_M : Θstar = M + Mperp := (projM_add_projMperp U V Θstar).symm
  have h_decomp_Δ : Δ = ΔMbar + ΔMbarPerp := (projMbar_add_projMbarPerp U V Δ).symm

  have h_M_mem : M ∈ Mspace U V := projM_mem_Mspace U V Θstar
  have h_ΔMbarPerp_mem : ΔMbarPerp ∈ MbarPerp U V := projMbarPerp_mem_MbarPerp U V Δ

  have h_sum_nuc : nucNorm (M + ΔMbarPerp) = nucNorm M + nucNorm ΔMbarPerp :=
    nucNorm_add_of_mem_Mspace_of_mem_MbarPerp U V M ΔMbarPerp h_M_mem h_ΔMbarPerp_mem

  have h_Θhat_eq : Θhat = (M + ΔMbarPerp) + (Mperp + ΔMbar) := by
    have h_sum : Θhat = Θstar + Δ := by
      dsimp [Δ]
      abel
    calc Θhat = Θstar + Δ := h_sum
      _ = (M + Mperp) + (ΔMbar + ΔMbarPerp) := by rw [h_decomp_M, h_decomp_Δ]
      _ = (M + ΔMbarPerp) + (Mperp + ΔMbar) := by abel

  have h_M_plus_perp : M + ΔMbarPerp = Θhat + (-(Mperp + ΔMbar)) := by
    rw [h_Θhat_eq]
    abel

  have h_le_Θhat : nucNorm (M + ΔMbarPerp) ≤ nucNorm Θhat + nucNorm (Mperp + ΔMbar) := by
    have h_tri := nucNorm_add_le Θhat (-(Mperp + ΔMbar))
    rw [← h_M_plus_perp] at h_tri
    rw [nucNorm_neg] at h_tri
    exact h_tri

  have h_le_perp_Δ : nucNorm (Mperp + ΔMbar) ≤ nucNorm Mperp + nucNorm ΔMbar :=
    nucNorm_add_le Mperp ΔMbar

  have h_bound1 : nucNorm M + nucNorm ΔMbarPerp ≤ nucNorm Θhat + nucNorm Mperp + nucNorm ΔMbar := by
    rw [← h_sum_nuc]
    linarith

  have h_bound_star : nucNorm Θstar ≤ nucNorm M + nucNorm Mperp := by
    rw [h_decomp_M]
    exact nucNorm_add_le M Mperp

  have h_lower : nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp ≤ nucNorm Θhat - nucNorm Θstar := by
    linarith

  have h_lam_lower : lam * (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) ≤
      lam * (nucNorm Θhat - nucNorm Θstar) := by
    nlinarith

  have h_min_star := hmin Θstar
  have h_Δ_add : Θstar + Δ = Θhat := by
    dsimp [Δ]
    abel
  have h_G_Δ := hG Δ
  rw [h_Δ_add] at h_G_Δ

  have h_opt_bound : lam * (nucNorm Θhat - nucNorm Θstar) ≤ - traceInner G Δ := by
    linarith

  have h_trace_decomp : - traceInner G Δ = traceInner (-G) ΔMbar + traceInner (-G) ΔMbarPerp := by
    rw [← traceInner_neg_left, h_decomp_Δ, traceInner_add_right]

  have h_dual_ΔMbar : traceInner (-G) ΔMbar ≤ opNorm2 G * nucNorm ΔMbar := by
    rw [traceInner_comm]
    have h := traceInner_le_opNorm2_mul_nucNorm ΔMbar (-G)
    rwa [opNorm2_neg] at h

  have h_dual_ΔMbarPerp : traceInner (-G) ΔMbarPerp ≤ opNorm2 G * nucNorm ΔMbarPerp := by
    rw [traceInner_comm]
    have h := traceInner_le_opNorm2_mul_nucNorm ΔMbarPerp (-G)
    rwa [opNorm2_neg] at h

  have h_dual_sum : - traceInner G Δ ≤ opNorm2 G * (nucNorm ΔMbar + nucNorm ΔMbarPerp) := by
    rw [h_trace_decomp]
    linarith

  have h_nonneg_Mbar : 0 ≤ nucNorm ΔMbar := by
    dsimp [nucNorm, singVal]
    exact Finset.sum_nonneg (fun j _ => LinearMap.singularValues_nonneg _ _)

  have h_nonneg_MbarPerp : 0 ≤ nucNorm ΔMbarPerp := by
    dsimp [nucNorm, singVal]
    exact Finset.sum_nonneg (fun j _ => LinearMap.singularValues_nonneg _ _)

  have h_dual_lam : opNorm2 G * (nucNorm ΔMbar + nucNorm ΔMbarPerp) ≤
      (lam / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) := by
    have : opNorm2 G ≤ lam / 2 := by linarith
    have h_sum_nonneg : 0 ≤ nucNorm ΔMbar + nucNorm ΔMbarPerp := by linarith
    nlinarith

  have h_comb : lam * (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) ≤
      (lam / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) := by
    linarith

  have h_final : 2 * (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) ≤
      nucNorm ΔMbar + nucNorm ΔMbarPerp := by
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_mul := mul_le_mul_of_nonneg_right h_comb (le_of_lt (inv_pos.mpr hlam))
    have h_cancel1 : lam * (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) * lam⁻¹ =
        nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp := by
      calc lam * (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) * lam⁻¹
        _ = (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) * (lam * lam⁻¹) := by ring
        _ = (nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp) * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hlam)]
        _ = nucNorm ΔMbarPerp - nucNorm ΔMbar - 2 * nucNorm Mperp := mul_one _
    have h_cancel2 : (lam / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) * lam⁻¹ =
        (1 / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) := by
      calc (lam / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) * lam⁻¹
        _ = (nucNorm ΔMbar + nucNorm ΔMbarPerp) * ((lam * (1 / 2)) * lam⁻¹) := by ring
        _ = (nucNorm ΔMbar + nucNorm ΔMbarPerp) * ((1 / 2) * (lam * lam⁻¹)) := by ring
        _ = (nucNorm ΔMbar + nucNorm ΔMbarPerp) * ((1 / 2) * 1) := by rw [mul_inv_cancel₀ (ne_of_gt hlam)]
        _ = (1 / 2) * (nucNorm ΔMbar + nucNorm ΔMbarPerp) := by ring
    rw [h_cancel1, h_cancel2] at h_mul
    linarith

  linarith
