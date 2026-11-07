-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:33.167849+00:00
-- url     : https://prove2.me/submissions/6000acfa-c5df-4a53-9b77-cac6532f1a70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_add_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (g+h)=
      lpsCuspPeterssonPairing N f g+lpsCuspPeterssonPairing N f h := by
  simp only [lpsCuspPeterssonPairing,lpsCuspPeterssonTrace_add_right]
  exact integral_add (lpsCuspPeterssonTrace_integrable N f g) (lpsCuspPeterssonTrace_integrable N f h)
end QEC.Coding.TannerLiftedProduct
