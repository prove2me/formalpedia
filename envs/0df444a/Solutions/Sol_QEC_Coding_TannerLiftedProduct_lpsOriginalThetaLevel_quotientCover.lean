-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_quotientCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:10.783992+00:00
-- url     : https://prove2.me/submissions/55603441-5bd1-4b4a-86cf-a7a0b3619224

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : q≠0) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) ℍ))
      (lpsGamma0Projective ((4*q)^2)) := by
  have : NeZero ((4*q)^2) := ⟨by positivity⟩
  apply lpsGamma0_quotientCover
  exact dvd_pow (dvd_mul_right 4 q) (by decide)
end QEC.Coding.TannerLiftedProduct
