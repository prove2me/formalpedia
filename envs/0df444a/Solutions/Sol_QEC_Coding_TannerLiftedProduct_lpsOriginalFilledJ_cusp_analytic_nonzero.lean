-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_analytic_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:37.552298+00:00
-- url     : https://prove2.me/submissions/62f91fec-cf0f-44ea-a617-19ccb56dee5c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_interior_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by
  let := lpsOriginalFilledTopology N
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c ⟨z,hz⟩ hz0
  let y := lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ
  let a := lpsOriginalFilledCuspChart N c
  let b := lpsOriginalFilledInteriorChart N hN y
  let e := a.symm.trans b
  have hp : a.symm z=Sum.inl y := hτ
  have hs : z∈e.source := by
    refine ⟨hz,?_⟩
    change a.symm z∈b.source
    rw [hp]
    exact lpsOriginalFilledInteriorChart_mem N hN y
  have he := lpsOriginalFilled_cusp_interior_analytic N hN y c z hs
  have hb := lpsOriginalFilledJ_interior_analytic N hN y (e z) (e.map_source hs).1
  have hf := hb.comp he
  apply hf.congr
  filter_upwards [e.open_source.mem_nhds hs] with w hw
  change lpsOriginalFilledJ N (b.symm (b (a.symm w)))=
    lpsOriginalFilledJ N (a.symm w)
  have hi := hw.2
  change a.symm w∈b.source at hi
  rw [b.left_inv hi]
end QEC.Coding.TannerLiftedProduct
