-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0SectionPetersson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:51.796621+00:00
-- url     : https://prove2.me/submissions/fef061df-b4d3-48c6-b409-93e9a191953c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) =
      lpsCuspCosetPetersson N f g τ ((lpsEffectiveGamma0CosetEquiv N).symm c) := by
  rw [←Quotient.out_eq' ((lpsEffectiveGamma0CosetEquiv N).symm c),
    lpsCuspCosetPetersson_apply]
  rfl
end QEC.Coding.TannerLiftedProduct
