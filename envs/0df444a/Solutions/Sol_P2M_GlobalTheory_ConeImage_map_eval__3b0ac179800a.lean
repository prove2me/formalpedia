-- Prove2me | solution 1 for P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:49.232627+00:00
-- url     : https://prove2.me/submissions/8dbde538-c218-4167-9cdc-20833738066e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (r : MvPolynomial σ ℂ) :
    φ (j r) = MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i))) r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [← MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end GlobalTheory.ConeImage
