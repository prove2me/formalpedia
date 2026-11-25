-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:46.824155+00:00
-- url     : https://prove2.me/submissions/3b8207e9-4241-4865-abc8-edcb1b98840d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  apply Real.log_nonneg
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
end GroundTheory.Heights₂.Heights.NineStatements
