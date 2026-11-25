-- Prove2me | solution 1 for PI.Dv.TIW.mem_pow_of_vAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:11.933579+00:00
-- url     : https://prove2.me/submissions/0cebcd3a-3032-41e0-b7c8-b7712a743462

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_volume_nonneg
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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.TIW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    a ∈ w.asIdeal ^ (vAdd w (algebraMap (𝓞 K) K a)).toNat := by
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
  have h0 : w.valuation K (algebraMap (𝓞 K) K a) ≠ 0 := by simpa using ha
  have hnn := volume_nonneg K w a
  rw [Int.toNat_of_nonneg hnn]
  unfold vAdd
  rw [neg_neg, WithZero.exp_log h0]
end PI.Dv.TIW
