-- Prove2me | solution 1 for SNumbers.prod_approximationNumber_le_detNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:40:36.123252+00:00
-- url     : https://prove2.me/submissions/6aad3fc8-24e0-4382-9142-0569a26690af

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_norm_det_le_detNumber
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_LinearMap_det_eq_prod_of_apply_eq_smul
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_norm_padFin_clm_le
public import Theorems.Thm_SNumbers_norm_projFin_clm_le
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SVD_IsCompactOperator_diagonalFactorisation
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X}
    {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := by
  classical
  have : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  set T := B.comp (S.comp A) with hTdef
  have hTc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_rng T
  obtain ⟨A₁, B₁, hA₁, hB₁, hdiag⟩ := SVD.IsCompactOperator.diagonalFactorisation hTc n
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hcast : ∀ i : Fin n, Fin.castLE hle i = Fin.castSucc i := fun i => rfl
  -- The compressed admissible pair.
  set A₂ : EuclideanSpace 𝕜 (Fin n) →L[𝕜] X :=
    (A.comp A₁).comp (padFin (p := 2)) with hA₂def
  set B₂ : Y →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    (projFin (p := 2) hle).comp (B₁.comp B) with hB₂def
  have hA₂n : ‖A₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_padFin_clm_le hle))
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans hA₁)
  have hB₂n : ‖B₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (norm_projFin_clm_le hle)).trans ?_)
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hB₁).trans hB)
  -- `padFin`/`projFin` act on standard basis vectors as expected.
  have hpad_single : ∀ j : Fin n,
      padFin (p := 2) (EuclideanSpace.single j (1 : 𝕜))
        = EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜) := by
    intro j
    ext i
    rw [padFin_apply, PiLp.single_apply]
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi, PiLp.single_apply]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_castSucc]
    · rw [dif_neg hi, if_neg fun h => hi (by rw [h, Fin.val_castSucc]; exact j.isLt)]
  have hproj_single : ∀ j : Fin n,
      projFin (p := 2) hle (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, hcast i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  -- The compressed operator is diagonal with entries `a₀(T), …, a_{n-1}(T)`.
  have hD : ∀ j : Fin n, (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
      = (approximationNumber T (j : ℕ) : 𝕜) • EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    have h1 : (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
        = projFin (p := 2) hle
            (B₁ (T (A₁ (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))))) := by
      rw [hA₂def, hB₂def, hTdef]
      simp only [ContinuousLinearMap.comp_apply, hpad_single j]
    rw [h1, hdiag (Fin.castSucc j), map_smul, hproj_single j, Fin.val_castSucc]
  -- Its determinant is the product of the diagonal entries (it is diagonal in the
  -- standard basis, by `hD`), via the general `det_eq_prod_of_apply_eq_smul`.
  have hdet : LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ∏ j : Fin n, (approximationNumber T (j : ℕ) : 𝕜) :=
    LinearMap.det_eq_prod_of_apply_eq_smul
      (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
      (B₂.comp (S.comp A₂) : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      (fun j => (approximationNumber T (j : ℕ) : 𝕜))
      (fun j => by
        simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hD j)
  -- Conclude.
  have hnorm : ‖LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖
      = ∏ i ∈ Finset.range n, approximationNumber T i := by
    rw [hdet, norm_prod, ← Fin.prod_univ_eq_prod_range (fun i => approximationNumber T i) n]
    exact Finset.prod_congr rfl fun j _ => by
      rw [RCLike.norm_ofReal, abs_of_nonneg (approximationNumber_nonneg _ _)]
  calc ∏ i ∈ Finset.range n, approximationNumber T i
      = ‖LinearMap.det (B₂.comp (S.comp A₂) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖ := hnorm.symm
    _ ≤ detNumber S n := norm_det_le_detNumber S hA₂n hB₂n
end SNumbers
