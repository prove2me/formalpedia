-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.int_of_alg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:02.070812+00:00
-- url     : https://prove2.me/submissions/04d47564-82f8-4aca-aad6-1e687dded1d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (F : Type) [Field F] [NumberField F] (y : F)
    (h : algebraMap F (Af F) y ∈ Formalism.UG.intAd F) : ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = y := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact RingHom.mem_range.1 (HeightOneSpectrum.mem_integers_of_valuation_le_one F y hv)
end PI.ScPsiExists.UnitaryGroupMassFormula
