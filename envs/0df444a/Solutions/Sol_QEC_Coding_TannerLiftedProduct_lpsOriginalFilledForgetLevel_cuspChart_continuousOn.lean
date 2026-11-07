-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspChart_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:18:34.797579+00:00
-- url     : https://prove2.me/submissions/6e04137c-9628-448f-9960-ca3a3b64de38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_preferredCuspCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    ContinuousOn
      (fun q : ℂ => lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q))
      (lpsOriginalFilledCuspChart M c).target := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let ρ := lpsOriginalCuspRepresentative M c
  let d := lpsOriginalCuspForgetLevel N M hNM c
  let e := lpsOriginalCuspLevelDegree N M ρ
  obtain ⟨α,hα,hαnorm,h⟩ := lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
  have hp : Continuous (fun q : ℂ => α * q ^ e) :=
    continuous_const.mul (continuous_id.pow e)
  have hc : ContinuousOn
      (fun q : ℂ => (lpsOriginalFilledCuspChart N d).symm (α * q ^ e))
      (lpsOriginalFilledCuspChart M c).target :=
    (lpsOriginalFilledCuspChart N d).continuousOn_invFun.comp hp.continuousOn
      (fun q hq => (h q hq).1)
  apply hc.congr
  intro q hq
  exact (h q hq).2.1
end QEC.Coding.TannerLiftedProduct
