-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_proof_fcd8b7eacf3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:19.191861+00:00
-- url     : https://prove2.me/submissions/18940e6d-d3ed-41f2-b675-092ac1943228

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalLatticeIndex
theorem _root_.solution : LocalLatticeIndex.Statement := by
  intro K _ _ V _ _ _ _ v A B g hA hB hBA
  exact LocalLatticeIndex.index_eq_det A B g hA.1 hA.2 hB hBA
end LocalLatticeIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
