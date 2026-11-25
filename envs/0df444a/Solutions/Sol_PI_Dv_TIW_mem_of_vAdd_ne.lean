-- Prove2me | solution 1 for PI.Dv.TIW.mem_of_vAdd_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:44.035524+00:00
-- url     : https://prove2.me/submissions/ac41ef15-7beb-4005-bbe7-1c3a57617ff1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (h : vAdd w (algebraMap (𝓞 K) K x) ≠ 0) : x ∈ w.asIdeal := by
  by_contra hx
  apply h
  have h1 : w.valuation K (algebraMap (𝓞 K) K x) = 1 :=
    le_antisymm (w.valuation_le_one x) (not_lt.mp fun hlt => hx ((w.valuation_lt_one_iff_mem x).mp hlt))
  unfold vAdd
  rw [h1, WithZero.log_one, neg_zero]
end PI.Dv.TIW
