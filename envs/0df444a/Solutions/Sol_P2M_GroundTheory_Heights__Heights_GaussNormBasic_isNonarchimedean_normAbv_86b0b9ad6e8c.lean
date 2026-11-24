-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:47.543617+00:00
-- url     : https://prove2.me/submissions/d8c94e7f-6fd5-4064-b2de-80c7de7a8359

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution : IsNonarchimedean (normAbv L) :=
  fun x y ↦ IsUltrametricDist.isNonarchimedean_norm x y
end GroundTheory.Heights₂.Heights.GaussNormBasic
