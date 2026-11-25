-- Prove2me | solution 1 for SNumbers.norm_det_le_pow_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:34.210349+00:00
-- url     : https://prove2.me/submissions/62cf3e37-431f-41b5-8f6c-718de7e80f7b

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_approximationNumber_le_norm
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_prod_approximationNumber_eq_norm_det

section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
omit [RCLike 𝕜] in
/-- The trivial space `ℓ₂⁰` has only one element. -/
private lemma subsingleton_euclidean_zero :
    Subsingleton (EuclideanSpace 𝕜 (Fin 0)) :=
  ⟨fun _ _ => PiLp.ext fun i => i.elim0⟩
section Border
variable {k : ℕ}
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
end Border
end SNumbers
end
end

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
theorem _root_.solution {k : ℕ}
    (T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
      ≤ ‖T‖ ^ k := by
  cases k with
  | zero =>
    have := subsingleton_euclidean_zero (𝕜 := 𝕜)
    rw [LinearMap.det_eq_one_of_subsingleton, norm_one, pow_zero]
  | succ m =>
    have : Nontrivial (EuclideanSpace 𝕜 (Fin (m + 1))) :=
      Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
    have h := prod_approximationNumber_eq_norm_det T
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    calc ∏ i ∈ Finset.range (m + 1), approximationNumber T i
        ≤ ∏ _i ∈ Finset.range (m + 1), ‖T‖ :=
          Finset.prod_le_prod (fun i _ => approximationNumber_nonneg T i)
            (fun i _ => approximationNumber_le_norm T i)
      _ = ‖T‖ ^ (m + 1) := by rw [Finset.prod_const, Finset.card_range]
end SNumbers
