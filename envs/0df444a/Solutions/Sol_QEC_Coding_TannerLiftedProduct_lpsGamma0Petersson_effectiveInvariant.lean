-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_effectiveInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:03.044046+00:00
-- url     : https://prove2.me/submissions/87989433-db9e-4d26-83e4-523cf59e08ef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g (h • τ) = petersson 2 f g τ := by
  rcases Subgroup.mem_map.mp h.property with ⟨γ,hγ,he⟩
  change petersson 2 f g (((h : lpsEffectiveModularGroup) : Equiv.Perm ℍ) τ) = _
  rw [←he]
  exact lpsCuspPetersson_smul N f g γ hγ τ
end QEC.Coding.TannerLiftedProduct
