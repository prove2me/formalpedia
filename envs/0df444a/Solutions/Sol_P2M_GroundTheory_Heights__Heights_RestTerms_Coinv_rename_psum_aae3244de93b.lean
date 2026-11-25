-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:35.105043+00:00
-- url     : https://prove2.me/submissions/b34e6a23-c3ec-4104-9068-4e1172973f5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution (b : Fin f) (m : ℕ) :
    rename (fun i : Fin n => (b, i)) (psum (Fin n) K m) = bps K f n m b := by
  simp [psum, bps]
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
