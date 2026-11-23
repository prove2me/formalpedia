-- Prove2me | solution 1 for PI.SelfDualLoc.W.one_tmul_mem_Oloc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:27.324813+00:00
-- url     : https://prove2.me/submissions/1db2f300-88fb-4306-8c67-873eac7d05ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]
namespace PI.SelfDualLoc.W
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {b : v.adicCompletion F}
    (hb : b ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] b ∈ Oloc F E v := by
  exact Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)
end PI.SelfDualLoc.W
