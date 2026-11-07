-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_slash_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:21:52.118198+00:00
-- url     : https://prove2.me/submissions/0a1a7007-9725-483e-aa9e-4cbcd155bb8d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_self
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) :
    lpsCuspCosetPetersson N f f τ ⟦h⟧=
      ((‖((f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) τ‖^2*τ.im^2:ℝ):ℂ) := by
  rw [lpsCuspCosetPetersson_apply, ← petersson_slash_SL,lpsWeightTwoPetersson_self]
end QEC.Coding.TannerLiftedProduct
