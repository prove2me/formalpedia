-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_proof_df941c76f478
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:01.616675+00:00
-- url     : https://prove2.me/submissions/df52fb9a-2960-4fdb-b458-81adc57ac549

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechTop
theorem _root_.solution : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)
end CechTop
end GroundTheory.Heights₂.Heights.Kleiman
