-- Prove2me | solution 1 for PI.TrDualLocW.BA_repr_natPow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:40.695766+00:00
-- url     : https://prove2.me/submissions/9f8bd89a-1e6a-404e-9e7d-e6272d202adc

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
namespace PI.TrDualLocW
theorem _root_.solution (D : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (BA K ℓ).repr ((ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * x) i = (ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr x i := by
  rw [show ((ℓ : ℚ_[ℓ] ⊗[ℚ] K)) ^ D * x = ((ℓ : ℚ_[ℓ]) ^ D) • x by
    rw [Algebra.smul_def, map_pow, map_natCast]]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
end PI.TrDualLocW
