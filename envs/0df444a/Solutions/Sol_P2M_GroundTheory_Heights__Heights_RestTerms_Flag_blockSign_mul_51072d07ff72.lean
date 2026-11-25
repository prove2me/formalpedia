-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:06.235012+00:00
-- url     : https://prove2.me/submissions/5149f43d-37c9-4222-9238-195c2aea52a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N (v * w) = blockSign f N v * blockSign f N w := by
  simp only [blockSign, ← Finset.prod_mul_distrib, Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
