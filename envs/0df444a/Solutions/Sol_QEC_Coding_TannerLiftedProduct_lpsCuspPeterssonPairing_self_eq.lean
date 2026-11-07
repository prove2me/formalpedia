-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:35.690446+00:00
-- url     : https://prove2.me/submissions/39714d9e-5e49-4406-8557-3391cf6164b1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_ofReal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f f=(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ : ℝ) := by
  unfold lpsCuspPeterssonPairing
  simp_rw [← lpsCuspPeterssonDensity_ofReal]
  exact integral_ofReal
end QEC.Coding.TannerLiftedProduct
