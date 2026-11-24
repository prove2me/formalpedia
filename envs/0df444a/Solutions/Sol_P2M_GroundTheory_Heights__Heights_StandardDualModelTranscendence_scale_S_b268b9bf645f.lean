-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.951802+00:00
-- url     : https://prove2.me/submissions/7b985667-c522-4550-800e-7f02790c7848

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
    scale ha (dualStdModelS K i) = dualStdModelEmb K i a * dualStdModelS K i := by
  simp only [dualStdModelS, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_S, map_mul]
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
