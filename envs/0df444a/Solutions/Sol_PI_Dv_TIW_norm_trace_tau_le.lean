-- Prove2me | solution 1 for PI.Dv.TIW.norm_trace_tau_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:01.479874+00:00
-- url     : https://prove2.me/submissions/9155a00c-e16a-4808-b279-b33c4ff036a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_trace_end_finite_order


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
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W (τ g))‖ ≤ Module.finrank K W :=
  (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1
end PI.Dv.TIW
