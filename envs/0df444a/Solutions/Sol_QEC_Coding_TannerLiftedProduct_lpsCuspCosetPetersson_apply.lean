-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:34.461385+00:00
-- url     : https://prove2.me/submissions/76cd9159-1979-423b-b111-1aec407f3bf8

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
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) :
    lpsCuspCosetPetersson N f g τ ⟦h⟧=petersson 2 f g (h⁻¹ • τ) := rfl
end QEC.Coding.TannerLiftedProduct
