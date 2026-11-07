-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_quotientProjection_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:36.26226+00:00
-- url     : https://prove2.me/submissions/84fbdac6-a52e-4d22-afd7-f357fdf1b828

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    IsOpenMap (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℍ → MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  let : ContinuousConstSMul (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
    ⟨fun g => continuous_const_smul g.val⟩
  exact isOpenMap_quotient_mk'_mul
end QEC.Coding.TannerLiftedProduct
