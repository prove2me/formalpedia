-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:16.496367+00:00
-- url     : https://prove2.me/submissions/6da4261d-ce63-48d5-906c-57cbe18732a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution : ∃ π : 𝓞 F, (algebraMap (𝓞 F) F π) ≠ 0 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F π)) < 1 := by
  obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨z, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hz0
  · rw [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem v z).2 hzI
end PI.SplitIntLoc.Proof
