-- Prove2me | solution 1 for SNumbers.L2Linf.exists_mem_apply_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:59:30.280707+00:00
-- url     : https://prove2.me/submissions/7da372e6-2fe3-4a77-b909-a18d6b5f27d3

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
theorem _root_.solution (b : OrthonormalBasis ι 𝕜 M) (k : Fin N) :
    ∃ x ∈ M, x k = ((∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 : ℝ) : 𝕜) ∧
      ‖x‖ ^ 2 = ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := by
  set a : EuclideanSpace 𝕜 ι :=
    WithLp.toLp 2 (fun i => conj ((b i : PiLp 2 (fun _ : Fin N => 𝕜)) k)) with ha
  refine ⟨(b.repr.symm a : PiLp 2 (fun _ : Fin N => 𝕜)), (b.repr.symm a).2, ?_, ?_⟩
  · rw [← b.sum_repr_symm a, Submodule.coe_sum]
    simp [ha, RCLike.conj_mul]
  · rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
    simp [ha]
end SNumbers.L2Linf
