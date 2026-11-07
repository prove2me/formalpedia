-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:46.565028+00:00
-- url     : https://prove2.me/submissions/331f6c33-8720-4f34-b0a3-dd845fee18e8

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
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N g f τ γ=conj (lpsCuspCosetPetersson N f g τ γ) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  exact petersson_symm 2 f g (h⁻¹ • τ)
end QEC.Coding.TannerLiftedProduct
