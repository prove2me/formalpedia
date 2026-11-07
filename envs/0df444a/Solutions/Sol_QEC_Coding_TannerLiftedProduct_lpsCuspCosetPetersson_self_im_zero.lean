-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_self_im_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:14.860786+00:00
-- url     : https://prove2.me/submissions/ba72bf38-ccc5-44fa-96ee-0ab3ef873063

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_slash_self

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (lpsCuspCosetPetersson N f f τ γ).im=0 := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  rw [lpsCuspCosetPetersson_slash_self]
  exact Complex.ofReal_im _
end QEC.Coding.TannerLiftedProduct
