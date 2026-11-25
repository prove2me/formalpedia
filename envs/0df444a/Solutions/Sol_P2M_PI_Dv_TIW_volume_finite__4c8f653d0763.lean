-- Prove2me | solution 1 for P2M_PI_Dv_TIW_volume_finite__4c8f653d0763
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:49.820327+00:00
-- url     : https://prove2.me/submissions/9406bbe6-ddd0-4673-a63e-7e2cc596b396

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_PI_Dv_TIW_mem_of_vAdd_ne

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
theorem _root_.solution : VFin := by
  intro K _ _ x hx
  have hI : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  exact Ideal.dvd_span_singleton.mpr (mem_of_vAdd_ne w x hw)
end PI.Dv.TIW
