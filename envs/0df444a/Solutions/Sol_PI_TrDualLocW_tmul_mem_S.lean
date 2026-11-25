-- Prove2me | solution 1 for PI.TrDualLocW.tmul_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:47.334128+00:00
-- url     : https://prove2.me/submissions/aebad878-8f8f-4b90-b52b-67b0202d3924

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
import Theorems.Thm_PI_TrDualLocW_mem_S

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
theorem _root_.solution (x : K) (hx : IsIntegral ℤ x) : (1 ⊗ₜ x : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ := by
  rw [mem_S]
  intro i
  rw [BA_repr_tmul]
  obtain ⟨z, hz⟩ := coord_int x hx i
  rw [hz, Rat.cast_intCast]
  exact intCast_mem _ z
end PI.TrDualLocW
