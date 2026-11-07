-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_functionTimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:56:40.488901+00:00
-- url     : https://prove2.me/submissions/708f4028-67b9-47c1-8a3b-5dedda506852

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_629
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_630
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : R) (sectionForm : V) :
    lpsOriginalCompactMeromorphicCovectorRatioMap N hN
      (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F sectionForm) =
        lpsOriginalCompactMeromorphicGermAlgHom N hN F *
          lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm := by
  let := lpsOriginalFilledTopology N
  apply Subtype.ext
  change ((fun y => (F.val y * sectionForm.val y (1 : ℂ)) /
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ)) :
      Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) =
    (F.val : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) *
      ((fun y => sectionForm.val y (1 : ℂ) /
        lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ)) :
          Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ)
  rw [←Filter.Germ.coe_mul]
  congr 1
  funext y
  exact mul_div_assoc _ _ _
end QEC.Coding.TannerLiftedProduct
