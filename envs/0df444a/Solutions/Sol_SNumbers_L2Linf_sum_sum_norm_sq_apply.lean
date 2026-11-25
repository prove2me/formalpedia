-- Prove2me | solution 1 for SNumbers.L2Linf.sum_sum_norm_sq_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:59:38.873089+00:00
-- url     : https://prove2.me/submissions/f168bb67-a0b7-4f13-a696-3b514c4af3aa

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
variable {N : ℕ} {ι : Type*} [Fintype ι] {M : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜))}
namespace SNumbers.L2Linf
theorem _root_.solution (b : OrthonormalBasis ι 𝕜 M) :
    ∑ k, ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 = Fintype.card ι := by
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ k, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 = 1 := fun i => by
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => 𝕜) (b i : PiLp 2 (fun _ : Fin N => 𝕜)),
      Submodule.norm_coe, b.orthonormal.1 i, one_pow]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
end SNumbers.L2Linf
