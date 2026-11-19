-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:15.801203+00:00
-- url     : https://prove2.me/submissions/af0d2a5a-de2a-4598-aa65-87494f0d91e9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : (∑ a : Fin 5,lpsThetaEisensteinTwoWeight a)=0 := by
  norm_num [lpsThetaEisensteinTwoWeight,Fin.sum_univ_succ]
end QEC.Coding.TannerLiftedProduct
