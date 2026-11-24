-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:36.253353+00:00
-- url     : https://prove2.me/submissions/9d49934c-8d45-434a-a2b8-c2dcced529b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ det (gram ℂ w) :=
  (posSemidef_gram ℂ w).det_nonneg
end GroundTheory.Heights₂.Heights
