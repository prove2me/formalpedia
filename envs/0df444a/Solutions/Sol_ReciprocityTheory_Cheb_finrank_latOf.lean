-- Prove2me | solution 1 for ReciprocityTheory.Cheb.finrank_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:27.930656+00:00
-- url     : https://prove2.me/submissions/be9a8d14-382c-48d6-b003-d5bd289b0eed

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : Module.finrank ℤ (latOf I) = Module.finrank ℚ E := by
  have e : (I.restrictScalars ℤ) ≃ₗ[ℤ] latOf I := Submodule.equivMapOfInjective _ embZ_injective _
  rw [← e.finrank_eq, Ideal.finrank_eq_finrank (RingOfIntegers.basis E) I hI, RingOfIntegers.rank]
end ReciprocityTheory.Cheb
