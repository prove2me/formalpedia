-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinChi4Weight_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:31.954772+00:00
-- url     : https://prove2.me/submissions/d5517f89-776d-4fbd-83cc-417a5c82b18b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (b : Fin 3) :
    lpsThetaEisensteinChi4Weight q b/((q^b.val:ℕ):ℂ)^2=
      -lpsThetaEisensteinPrimeWeight q b/((q^b.val:ℕ):ℂ) := by
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  fin_cases b <;> norm_num [lpsThetaEisensteinChi4Weight,lpsThetaEisensteinPrimeWeight]
  all_goals field_simp [hq]
  all_goals ring
end QEC.Coding.TannerLiftedProduct
