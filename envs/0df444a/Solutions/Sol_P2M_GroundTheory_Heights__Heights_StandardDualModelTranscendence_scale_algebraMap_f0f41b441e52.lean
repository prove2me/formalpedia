-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:30.390998+00:00
-- url     : https://prove2.me/submissions/6d750e5d-a063-4f70-84a1-23b1a458920e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc

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
namespace GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
theorem _root_.solution {a : L} (ha : a ≠ 0) (p : MvPolynomial Unit (MvPolynomial Unit L)) :
    scale ha (algebraMap _ _ p) = algebraMap _ _ (scaleHom a p) :=
  IsFractionRing.lift_algebraMap _ p
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
