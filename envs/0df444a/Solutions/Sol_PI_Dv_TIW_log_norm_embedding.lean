-- Prove2me | solution 1 for PI.Dv.TIW.log_norm_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:53.533093+00:00
-- url     : https://prove2.me/submissions/ad15719a-7d5b-43ff-b9c4-01d5569d8aca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_PI_Dv_TIW_norm_embedding_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((vAdd v x : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) := by
  rw [norm_embedding_eq v x hx, Real.log_zpow]
  push_cast
  ring
end PI.Dv.TIW
