-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.scalarOperatorKernel_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/79cab290-3766-4f29-b7a8-5eb1c38af471

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution {I : Type u}
    (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (scalarOperatorKernel K).PosSemidef := by
  apply ((RKHS.posSemidef_tfae
    (K := scalarOperatorKernel K)).out 2 0).mp
  constructor
  · apply Matrix.IsHermitian.ext
    intro g h
    change star (ContinuousLinearMap.toSpanSingleton ℂ (K h g)) =
      ContinuousLinearMap.toSpanSingleton ℂ (K g h)
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_toSpanSingleton]
    apply ContinuousLinearMap.ext
    intro z
    calc
      (innerSL ℂ (K h g)) z = star (K h g) * z := by
        simp only [innerSL_apply_apply, RCLike.inner_apply',
          RCLike.star_def]
      _ = K g h * z := by rw [hK.isHermitian.apply g h]
      _ = z * K g h := mul_comm _ _
      _ = (ContinuousLinearMap.toSpanSingleton ℂ (K g h)) z := by
        simp only [ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul]
  · intro c
    have hc := hK.2 c
    have hreal :
        0 ≤ RCLike.re (c.sum fun g z =>
          c.sum fun h w => star z * K g h * w) :=
      (RCLike.nonneg_iff.mp hc).1
    simp only [scalarOperatorKernel,
      ContinuousLinearMap.toSpanSingleton_apply,
      RCLike.inner_apply', smul_eq_mul, map_mul]
    simpa only [← RCLike.star_def, hK.isHermitian.apply,
      mul_assoc, mul_left_comm, mul_comm] using hreal
end SoficGroups.KunRootedIndicatorCrossing
