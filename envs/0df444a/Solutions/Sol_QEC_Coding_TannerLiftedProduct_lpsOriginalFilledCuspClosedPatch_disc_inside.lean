-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_disc_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:23.941427+00:00
-- url     : https://prove2.me/submissions/7ab36aa8-90cf-492e-8a41-6b1e72949a0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Metric.closedBall (0:ℂ) (Real.exp
      (-2*Real.pi*2/(lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty))⊆
        (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target := by
  intro q hq
  rw [mem_closedBall_zero_iff] at hq
  change ‖q‖<_
  apply hq.trans_lt
  apply Real.exp_lt_exp.mpr
  have hw := lpsOriginalCuspGroup_width_positive N (lpsOriginalCuspRepresentative N c)
  apply (div_lt_div_iff_of_pos_right hw).mpr
  nlinarith [Real.pi_pos]
end QEC.Coding.TannerLiftedProduct
