-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:58.471781+00:00
-- url     : https://prove2.me/submissions/8a01df3a-b83b-40bd-b9ce-205ac33d5dd8

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (g : (K → ℤ) → ℤ) (m : K → ℕ) (k : K) :
    diffStep (Pi.single k 1) g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) =
      g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) - g (fun j => (m j : ℤ)) := by
  unfold diffStep
  congr 2
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]
end GroundTheory.Heights₂.Heights.HilbertSamuel
