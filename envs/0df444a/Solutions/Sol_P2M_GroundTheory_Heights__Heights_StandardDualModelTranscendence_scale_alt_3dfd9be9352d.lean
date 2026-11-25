-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:24.458711+00:00
-- url     : https://prove2.me/submissions/b8a87c58-0b72-49b7-a67c-da9b54310d1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
variable {L : Type} [Field L]
variable {K : Type} [Field K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
theorem _root_.solution {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelT K i) = dualStdModelEmb K i a⁻¹ * dualStdModelT K i := by
  simp only [dualStdModelT, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_alt, map_mul]
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
