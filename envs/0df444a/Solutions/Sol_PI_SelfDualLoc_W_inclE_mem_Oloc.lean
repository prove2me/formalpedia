-- Prove2me | solution 1 for PI.SelfDualLoc.W.inclE_mem_Oloc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:16.585205+00:00
-- url     : https://prove2.me/submissions/de1291be-c4c2-4b94-a4ee-79c6ce7d6f14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Theorems.Thm_PI_SelfDualLoc_W_inclE_apply

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {e : E} (he : e ∈ intOE E) :
    inclE (F := F) (v.adicCompletion F) e ∈ Oloc F E v := by
  rw [inclE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)
end PI.SelfDualLoc.W
