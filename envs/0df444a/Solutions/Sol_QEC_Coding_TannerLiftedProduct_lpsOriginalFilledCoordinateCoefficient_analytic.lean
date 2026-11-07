-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:56.88064+00:00
-- url     : https://prove2.me/submissions/c3037d01-a4ba-4461-aad6-57a6058529fa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForm_ofComplex_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    AnalyticAt ℂ (lpsOriginalFilledCoordinateCoefficient N f x) z := by
  cases x with
  | inl y =>
    have hp := lpsOriginalFilledInteriorChart_target_pos N hN y z hz
    exact lpsOriginalCuspForm_ofComplex_analytic N f ⟨z,hp⟩
  | inr c =>
    let r := lpsOriginalCuspRepresentative N c
    have hw : 0<(lpsOriginalCuspGroup N r).strictWidthInfty :=
      lpsOriginalCuspGroup_width_positive N r
    have he : Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N r).strictWidthInfty)<1 := by
      rw [Real.exp_lt_one_iff]
      exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hw
    change ‖z‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N r).strictWidthInfty) at hz
    exact lpsOriginalCuspQCoefficient_analytic N f r z (hz.trans he)
end QEC.Coding.TannerLiftedProduct
