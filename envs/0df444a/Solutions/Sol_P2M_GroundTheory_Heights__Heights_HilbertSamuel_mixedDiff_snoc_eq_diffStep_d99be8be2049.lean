-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:53.069914+00:00
-- url     : https://prove2.me/submissions/2a3e4d99-cb17-41da-9c45-7108eb449c74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {n : ℕ} (bs : Fin n → K → ℤ) (b : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc bs b : Fin (n + 1) → K → ℤ) f = mixedDiff bs (diffStep b f) := by
  unfold mixedDiff
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, List.foldr_append]
end GroundTheory.Heights₂.Heights.HilbertSamuel
