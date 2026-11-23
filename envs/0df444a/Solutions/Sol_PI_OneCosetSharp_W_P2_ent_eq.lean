-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.ent_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:17.169203+00:00
-- url     : https://prove2.me/submissions/d7f6eec5-0f89-4cd5-9640-21fbe6fb51b1

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
theorem _root_.solution {c n : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (p q : Fin (n + c)) :
    ent k₀ c n c n κ.toLinearMap p.1 q.1 = Pm k₀ hk κ p q := by
  have e : eN k (n + c) (fIdx k₀ c n q.1) = Pi.single (fe k₀ c n hk q) (1 : k) := by
    funext j'
    simp only [eN, Pi.single_apply, fe, Equiv.ofBijective_apply, Fin.ext_iff]
  simp only [Pm, Matrix.submatrix_apply, LinearMap.toMatrix'_apply, ent, atN, dif_pos (fIdx_lt hk p.2), e]
  rfl
end PI.OneCosetSharp.W.P2
