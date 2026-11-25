-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.Pm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:10.243355+00:00
-- url     : https://prove2.me/submissions/d75cf3b9-31ce-45f9-a4e5-14656001c420

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
theorem _root_.solution {c n : ℕ} (hk : k₀ ≤ n) : Pm (k := k) (c := c) (n := n) k₀ hk 1 = 1 := by
  have e : (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)).toLinearMap = LinearMap.id := LinearMap.ext fun _ => rfl
  rw [Pm, e, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv]
end PI.OneCosetSharp.W.P2
