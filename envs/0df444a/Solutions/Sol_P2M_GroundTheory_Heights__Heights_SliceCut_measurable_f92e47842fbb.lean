-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:24.185977+00:00
-- url     : https://prove2.me/submissions/7f30d860-063e-43f2-a061-b60e5f8d9144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)
namespace GroundTheory.Heights₂.Heights.SliceCut
theorem _root_.solution (k : ℕ) : Measurable (sliceCut h k) :=
  (contDiff h k).continuous.measurable
end GroundTheory.Heights₂.Heights.SliceCut
