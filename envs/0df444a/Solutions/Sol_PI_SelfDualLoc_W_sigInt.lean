-- Prove2me | solution 1 for PI.SelfDualLoc.W.sigInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:26.479981+00:00
-- url     : https://prove2.me/submissions/5463c273-28f0-4814-8cd3-e52696b17c6b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Theorems.Thm_PI_SelfDualLoc_W_sigR_tmul
import Theorems.Thm_PI_SelfDualLoc_W_inclE_apply
import Theorems.Thm_PI_SelfDualLoc_W_intOE_map
import Theorems.Thm_PI_SelfDualLoc_W_inclE_mem_Oloc
import Theorems.Thm_PI_SelfDualLoc_W_one_tmul_mem_Oloc

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
theorem _root_.solution : SigInt := by
  intro F E _ _ _ _ _ σ v c hc
  have key : Oloc F E v ≤ (Oloc F E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ _ (x ⊗ₜ[F] 1) ∈ Oloc F E v
      rw [sigR_tmul, ← inclE_apply]
      exact inclE_mem_Oloc v (intOE_map σ hx)
    · show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ Oloc F E v
      rw [sigR_tmul, map_one]
      exact one_tmul_mem_Oloc v hy
  exact key hc
end PI.SelfDualLoc.W
