-- Prove2me | solution 1 for PI.Dv.TIW.trace_tau_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:23.742454+00:00
-- url     : https://prove2.me/submissions/549d5755-724f-4cbc-b25c-d274fa3f9b59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_mem_O_of_isIntegral
import Theorems.Thm_PI_Dv_TIW_exists_embedding
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
    (τ : Representation K G W) (g : G) : LinearMap.trace K W (τ g) ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨σ⟩ := exists_embedding (K := K)
  have h := (trace_end_finite_order (τ g) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  exact mem_O_of_isIntegral _ h
end PI.Dv.TIW
