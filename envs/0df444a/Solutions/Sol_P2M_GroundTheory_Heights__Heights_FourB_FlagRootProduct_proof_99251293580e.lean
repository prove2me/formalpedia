-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_proof_99251293580e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:30.740808+00:00
-- url     : https://prove2.me/submissions/995f4b27-7935-4540-ba26-12e94af164a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagRootProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
namespace GroundTheory.Heights₂.Heights.FourB
namespace FlagRootProduct
theorem _root_.solution : FlagRootProduct.Statement := by
  intro N p lam hd
  have h := fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q
  exact ⟨h, Finset.prod_congr rfl fun q _ => h q⟩
end FlagRootProduct
end GroundTheory.Heights₂.Heights.FourB
