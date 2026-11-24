-- Prove2me | solution 1 for PI.IntAdCpctOpenWork.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:48.428234+00:00
-- url     : https://prove2.me/submissions/517e92e1-6d10-46d2-b9a5-08be27829df8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.IntAdCpctOpenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.IntAdCpctOpenWork
theorem _root_.solution : Formalism.L2.Props.IntAdelesCompactOpen := by
  intro F _ _
  have hO : ∀ w : HeightOneSpectrum (𝓞 F),
      IsOpen ((w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    fun w => Valued.isOpen_valuationSubring _
  refine ⟨RestrictedProduct.isOpen_forall_mem hO, ?_⟩
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap hO).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h
end PI.IntAdCpctOpenWork
