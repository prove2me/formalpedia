-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:36.189908+00:00
-- url     : https://prove2.me/submissions/3b8108c8-666e-40af-a978-13959ce97e39

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0≤(lpsCuspPeterssonPairing N f f).re := by
  rw [lpsCuspPeterssonPairing_self_eq,Complex.ofReal_re]
  exact integral_nonneg (lpsCuspPeterssonDensity_nonneg N f)
end QEC.Coding.TannerLiftedProduct
