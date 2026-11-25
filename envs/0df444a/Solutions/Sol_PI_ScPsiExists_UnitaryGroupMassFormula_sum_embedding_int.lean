-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:32.046749+00:00
-- url     : https://prove2.me/submissions/a3e089ca-11ff-4823-b141-cde9044d67fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_sum_embedding_eq_trace
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
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : 𝓞 F) :
    ∃ n : ℤ, ∑ v : InfinitePlace F, v.embedding (algebraMap (𝓞 F) F c) = (n : ℂ) := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F c)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe c)
  obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hi
  refine ⟨n, ?_⟩
  rw [sum_embedding_eq_trace, ← hn]
  simp
end PI.ScPsiExists.UnitaryGroupMassFormula
