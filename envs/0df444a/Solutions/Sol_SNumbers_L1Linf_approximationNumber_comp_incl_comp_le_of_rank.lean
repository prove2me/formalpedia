-- Prove2me | solution 1 for SNumbers.L1Linf.approximationNumber_comp_incl_comp_le_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:47:22.685799+00:00
-- url     : https://prove2.me/submissions/0d65dc3c-569b-433f-9d94-9be67e7b5fe8

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_T1_le
public import Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_adjoint_T2_le
public import Theorems.Thm_SNumbers_L1Linf_isCompactOperator_comp_incl_comp
public import Theorems.Thm_SNumbers_L1Linf_comp_incl_comp_eq
public import Theorems.Thm_SVD_mul_approximationNumber_le_of_factorization


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution {m : ℕ}
    (hrank : A.rank ≤ (m : Cardinal)) (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  have key := SVD.mul_approximationNumber_le_of_factorization
    (isCompactOperator_comp_incl_comp A B hrank) (comp_incl_comp_eq A B)
    (fun u hu s => sum_norm_sq_T1_le A hu s)
    (fun v hv s => sum_norm_sq_adjoint_T2_le B hv s)
    (norm_nonneg A) (norm_nonneg B) n
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [key]
end SNumbers.L1Linf
