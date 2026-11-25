-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexTrans_toAddSubgroup_span_3783b3369c55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:39.683696+00:00
-- url     : https://prove2.me/submissions/2f270a4a-43d6-4ecf-8b6d-432bcb12a482

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexTrans

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
open GroundTheory.Heights₂.Heights.KLinesGenIndexTrans
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexTrans
theorem _root_.solution {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s
end GroundTheory.Heights₂.Heights.KLinesGenIndexTrans
