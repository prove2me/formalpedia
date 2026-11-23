-- Prove2me | solution 1 for PI.TrDualLocW.mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:49.5758+00:00
-- url     : https://prove2.me/submissions/9c1e86dc-e183-4d9a-be11-48ed1ca9c8f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
variable {K ℓ}
variable (K ℓ)
variable {K ℓ}
namespace PI.TrDualLocW
theorem _root_.solution {x : ℚ_[ℓ] ⊗[ℚ] K} : x ∈ S K ℓ ↔ ∀ i, (BA K ℓ).repr x i ∈ PadicInt.subring ℓ := Iff.rfl
end PI.TrDualLocW
