-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_petersson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:16.531752+00:00
-- url     : https://prove2.me/submissions/17fb207b-106f-4721-ae78-69badd5c0537

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
    lpsCuspCosetPetersson N f g τ γ=
      petersson 2 (lpsCuspCosetComponent N f γ) (lpsCuspCosetComponent N g γ) τ := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  exact (petersson_slash_SL 2 f g h⁻¹ τ).symm
end QEC.Coding.TannerLiftedProduct
