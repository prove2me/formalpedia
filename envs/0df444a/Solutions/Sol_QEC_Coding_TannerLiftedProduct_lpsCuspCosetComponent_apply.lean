-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:56.888437+00:00
-- url     : https://prove2.me/submissions/6f3e0cf6-74fc-4fc4-824f-874c731731b6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) : lpsCuspCosetComponent N f ⟦h⟧=(f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹ := rfl
end QEC.Coding.TannerLiftedProduct
