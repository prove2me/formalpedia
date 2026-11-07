-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:05.949752+00:00
-- url     : https://prove2.me/submissions/05b7b3cd-44e8-47f2-9bed-9c458b825fc5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_smul_right

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) : lpsCuspPeterssonPairing N (c • f) g=conj c*lpsCuspPeterssonPairing N f g := by
  calc
    _ = conj (lpsCuspPeterssonPairing N g (c • f)) := lpsCuspPeterssonPairing_conj N g (c • f)
    _ = conj (c*lpsCuspPeterssonPairing N g f) := by rw [lpsCuspPeterssonPairing_smul_right]
    _ = _ := by rw [map_mul,← lpsCuspPeterssonPairing_conj]
end QEC.Coding.TannerLiftedProduct
