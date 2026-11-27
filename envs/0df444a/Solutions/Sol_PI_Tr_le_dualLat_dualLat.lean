-- Prove2me | solution 1 for PI.Tr.le_dualLat_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:17:44.191793+00:00
-- url     : https://prove2.me/submissions/e9bf2896-306c-4580-a36a-11e910718a2a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open PI PI.Tr
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace PI.Tr
theorem _root_.solution (Λ : Submodule ℤ E) : Λ ≤ dualLat (dualLat Λ) := by
  intro x hx
  show ∀ y ∈ dualLat Λ, ∃ n : ℤ, inner ℝ y x = (n : ℝ)
  intro y hy
  have hy' : ∀ z ∈ Λ, ∃ n : ℤ, inner ℝ z y = (n : ℝ) := hy
  obtain ⟨n, hn⟩ := hy' x hx
  exact ⟨n, by rw [real_inner_comm]; exact hn⟩
end PI.Tr
