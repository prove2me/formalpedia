-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:37.943296+00:00
-- url     : https://prove2.me/submissions/2bfb73ce-f0f4-4adb-a7c5-2e05f4b163ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_continuous

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Continuous (lpsCuspPeterssonTrace N f g) := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact continuous_finsetSum _ (fun γ _ => lpsCuspCosetPetersson_continuous N f g γ)
end QEC.Coding.TannerLiftedProduct
