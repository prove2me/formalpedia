-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_contDiff_factor_240d0b9df1f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:38.849479+00:00
-- url     : https://prove2.me/submissions/50962c6f-21d3-4d55-9603-247fdee34e0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi

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
open ReciprocityTheory.AnForm
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {f N : ℕ} (τ : Fin f) :
    ContDiff ℝ 2 fun z : (Σ _ : Fin f, LowerPair N) → ℂ => fun q : LowerPair N => z ⟨τ, q⟩ := by
  fun_prop
end GroundTheory.Heights₂.Heights.FourB
