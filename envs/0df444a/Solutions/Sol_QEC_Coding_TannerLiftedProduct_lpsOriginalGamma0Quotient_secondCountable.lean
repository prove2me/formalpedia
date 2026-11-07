-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Quotient_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:41.530849+00:00
-- url     : https://prove2.me/submissions/5aa8e61d-02e0-4491-9588-18605e381210

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0_quotientProjection_open

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    SecondCountableTopology (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  TopologicalSpace.Quotient.secondCountableTopology (lpsOriginalGamma0_quotientProjection_open N)
end QEC.Coding.TannerLiftedProduct
