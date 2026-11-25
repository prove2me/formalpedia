-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.alg_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:06.26695+00:00
-- url     : https://prove2.me/submissions/0c073132-13a6-4bfe-b8d6-fbe577777165

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
import Theorems.Thm_PI_OneCosetSharp_W_P2_S_antisymm

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
theorem _root_.solution {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b)
    (p : Fin b) (hp : p.1 < k₀ + m - 1) : (A * B) p p = A p p * B p p := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · intro s _ hs
    by_contra h
    exact hs (Fin.ext (S_antisymm hp (hA p s (left_ne_zero_of_mul h)) (hB s p (right_ne_zero_of_mul h)))).symm
  · intro h
    exact absurd (Finset.mem_univ p) h
end PI.OneCosetSharp.W.P2
