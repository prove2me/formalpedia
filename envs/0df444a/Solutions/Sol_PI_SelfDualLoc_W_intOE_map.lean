-- Prove2me | solution 1 for PI.SelfDualLoc.W.intOE_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:26.836211+00:00
-- url     : https://prove2.me/submissions/52647786-56bf-401c-a82d-2f4a8479191b

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
theorem _root_.solution (σ : E →ₐ[F] E) {e : E} (he : e ∈ intOE E) : σ e ∈ intOE E := by
  obtain ⟨x, rfl⟩ := he
  refine ⟨⟨σ x, ?_⟩, rfl⟩
  have hx : IsIntegral ℤ (x : E) := NumberField.RingOfIntegers.isIntegral_coe x
  exact (mem_integralClosure_iff ℤ E).2 (hx.map (σ : E →+* E).toIntAlgHom)
end PI.SelfDualLoc.W
