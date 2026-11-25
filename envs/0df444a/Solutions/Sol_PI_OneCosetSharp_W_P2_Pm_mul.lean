-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.Pm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:05.440577+00:00
-- url     : https://prove2.me/submissions/c4e8e555-61fe-443e-98de-2c4d64671d83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.P2
variable {k : Type} [Field k]
variable {k₀ m t b : ℕ}
namespace PI.OneCosetSharp.W.P2
theorem _root_.solution {c n : ℕ} (hk : k₀ ≤ n) (κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Pm k₀ hk (κ₁ * κ₂) = Pm k₀ hk κ₁ * Pm k₀ hk κ₂ := by
  have e : (κ₁ * κ₂).toLinearMap = κ₁.toLinearMap ∘ₗ κ₂.toLinearMap := LinearMap.ext fun _ => rfl
  rw [Pm, Pm, Pm, e, LinearMap.toMatrix'_comp, Matrix.submatrix_mul_equiv]
end PI.OneCosetSharp.W.P2
