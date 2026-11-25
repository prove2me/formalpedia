-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:43.780881+00:00
-- url     : https://prove2.me/submissions/7f75679d-e932-4086-950f-dd7f944aff47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_snoc_eq_diffStep_d99be8be2049

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
theorem _root_.solution {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1)) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b : Fin (n + 1) → K → ℤ)
  rwa [mixedDiff_snoc_eq_diffStep] at h
end GroundTheory.Heights₂.Heights.HilbertSamuel
