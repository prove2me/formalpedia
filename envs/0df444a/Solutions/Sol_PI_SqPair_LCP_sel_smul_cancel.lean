-- Prove2me | solution 1 for PI.SqPair.LCP.sel_smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:45.158244+00:00
-- url     : https://prove2.me/submissions/8e056a96-bfb1-4f23-afa1-24fafc4b0b56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_left_cancel₀ hc h'
end PI.SqPair.LCP
