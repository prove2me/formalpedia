-- Prove2me | solution 1 for PI.Tr.dualZ_eq_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:20:55.856775+00:00
-- url     : https://prove2.me/submissions/c793a3f4-d1e2-456f-a002-23b69cafc81c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Module
noncomputable section
open PI PI.Tr
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace PI.Tr
theorem _root_.solution {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) :
    PI.dualZ M = dualLat M := by
  ext x
  show (∀ y ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) ↔ (∀ y ∈ M, ∃ n : ℤ, inner ℝ y x = (n : ℝ))
  simp only [real_inner_comm]
end PI.Tr
