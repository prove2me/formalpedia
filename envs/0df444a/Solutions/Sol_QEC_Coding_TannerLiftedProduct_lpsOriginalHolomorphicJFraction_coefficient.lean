-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicJFraction_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:32:43.299427+00:00
-- url     : https://prove2.me/submissions/1f4de5e5-7a76-4102-9944-b5872d46c46a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom =
      Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic) := by
  apply RingHom.ext
  intro p
  change algebraMap R H (p.eval₂ (algebraMap ℂ R) lpsOriginalJHolomorphic) = _
  exact Polynomial.hom_eval₂ p (algebraMap ℂ R) (algebraMap R H)
    lpsOriginalJHolomorphic
end QEC.Coding.TannerLiftedProduct
