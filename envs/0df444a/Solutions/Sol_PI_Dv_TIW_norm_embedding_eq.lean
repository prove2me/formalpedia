-- Prove2me | solution 1 for PI.Dv.TIW.norm_embedding_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:20.912937+00:00
-- url     : https://prove2.me/submissions/1bed294c-9a37-4504-ab4d-fcee5aa78634

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_PI_Dv_TIW_unzero_toAdd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  have he : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
    first
    | exact v.valuedAdicCompletion_eq_valuation' x
    | exact v.valuedAdicCompletion_eq_valuation x
    | rfl
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ hv, unzero_toAdd _ hv]
  simp [vAdd]
end PI.Dv.TIW
