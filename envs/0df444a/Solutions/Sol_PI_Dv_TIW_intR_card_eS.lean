-- Prove2me | solution 1 for PI.Dv.TIW.intR_card_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:47.646009+00:00
-- url     : https://prove2.me/submissions/07486bd2-6046-44ca-abb6-099f4f60a101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_intR_of
import Theorems.Thm_PI_Dv_TIW_intR_sum
import Theorems.Thm_PI_Dv_TIW_intR_smul
import Theorems.Thm_PI_Dv_TIW_trace_tau_mem

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) : IntR (((Fintype.card G : ℕ) : K) • eS T s) := by
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eS, Finset.smul_sum]
  refine intR_sum _ _ fun x _ => ?_
  rw [smul_smul]
  refine intR_smul _ ?_ (intR_of x)
  have : ((Fintype.card G : ℕ) : K) * (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s x⁻¹)) =
      ((Module.finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
    field_simp
  rw [this]
  obtain ⟨u, hu⟩ := trace_tau_mem (T.tau s) x⁻¹
  exact ⟨(Module.finrank K (T.W s) : 𝓞 K) * u, by rw [map_mul, hu, map_natCast]⟩
end PI.Dv.TIW
