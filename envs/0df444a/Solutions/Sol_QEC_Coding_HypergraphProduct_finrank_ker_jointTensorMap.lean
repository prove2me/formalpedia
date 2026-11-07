-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:00.511209+00:00
-- url     : https://prove2.me/submissions/ddf0cffa-e963-4873-a0cf-5e19f9aa594f

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Coordinates
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_jointTensorMap_of_surjective


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M] [Module.Free F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Free F M'] [Module.Finite F M']
    [AddCommGroup N] [Module F N] [Module.Free F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Free F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N') :
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
      Module.finrank F (LinearMap.ker f) *
        Module.finrank F (LinearMap.ker g) := by
  let fRange : M →ₗ[F] LinearMap.range f := f.rangeRestrict
  let gRange : N →ₗ[F] LinearMap.range g := g.rangeRestrict
  have hfPostInjective :
      Function.Injective ((LinearMap.range f).subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (LinearMap.range f).subtype (LinearMap.range f).injective_subtype
  have hgPostInjective :
      Function.Injective ((LinearMap.range g).subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (LinearMap.range g).subtype (LinearMap.range g).injective_subtype
  have hfFactor :
      f.rTensor N =
        ((LinearMap.range f).subtype.rTensor N).comp (fRange.rTensor N) := by
    rw [← LinearMap.rTensor_comp]
    rfl
  have hgFactor :
      g.lTensor M =
        ((LinearMap.range g).subtype.lTensor M).comp (gRange.lTensor M) := by
    rw [← LinearMap.lTensor_comp]
    rfl
  have hfKer : LinearMap.ker (f.rTensor N) = LinearMap.ker (fRange.rTensor N) := by
    rw [hfFactor]
    exact LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr hfPostInjective)
  have hgKer : LinearMap.ker (g.lTensor M) = LinearMap.ker (gRange.lTensor M) := by
    rw [hgFactor]
    exact LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr hgPostInjective)
  have hJointKer :
      LinearMap.ker (jointTensorMap f g) =
        LinearMap.ker (jointTensorMap fRange gRange) := by
    rw [jointTensorMap, LinearMap.ker_prod, jointTensorMap,
      LinearMap.ker_prod, hfKer, hgKer]
  calc
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
        Module.finrank F (LinearMap.ker (jointTensorMap fRange gRange)) := by
      rw [hJointKer]
    _ = Module.finrank F (LinearMap.ker fRange) *
          Module.finrank F (LinearMap.ker gRange) :=
      finrank_ker_jointTensorMap_of_surjective fRange gRange
        f.surjective_rangeRestrict g.surjective_rangeRestrict
    _ = Module.finrank F (LinearMap.ker f) *
          Module.finrank F (LinearMap.ker g) := by
      rw [LinearMap.ker_rangeRestrict, LinearMap.ker_rangeRestrict]
end QEC.Coding.HypergraphProduct
