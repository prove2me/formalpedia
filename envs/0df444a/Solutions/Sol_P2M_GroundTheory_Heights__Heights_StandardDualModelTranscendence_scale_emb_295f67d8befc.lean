-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.980793+00:00
-- url     : https://prove2.me/submissions/7c29d07c-c78b-4d59-a496-cc995370ef6f

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
theorem _root_.solution {a : ProjField K i} (ha : a ≠ 0) (x : ProjField K i) :
    scale ha (dualStdModelEmb K i x) = dualStdModelEmb K i x := by
  simp only [dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_CC]
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
