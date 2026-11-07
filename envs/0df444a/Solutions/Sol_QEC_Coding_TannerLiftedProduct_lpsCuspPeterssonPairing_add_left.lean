-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:28.18101+00:00
-- url     : https://prove2.me/submissions/c4b61d37-8140-49eb-be10-5691832f54fb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_add_right

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (f+g) h=
      lpsCuspPeterssonPairing N f h+lpsCuspPeterssonPairing N g h := by
  calc
    _ = conj (lpsCuspPeterssonPairing N h (f+g)) := lpsCuspPeterssonPairing_conj N h (f+g)
    _ = conj (lpsCuspPeterssonPairing N h f+lpsCuspPeterssonPairing N h g) := by
      rw [lpsCuspPeterssonPairing_add_right]
    _ = _ := by rw [map_add,← lpsCuspPeterssonPairing_conj,← lpsCuspPeterssonPairing_conj]
end QEC.Coding.TannerLiftedProduct
