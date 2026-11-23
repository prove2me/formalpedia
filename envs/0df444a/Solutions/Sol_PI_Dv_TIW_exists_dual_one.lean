-- Prove2me | solution 1 for PI.Dv.TIW.exists_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:23.165808+00:00
-- url     : https://prove2.me/submissions/2401ec66-7f9e-49d1-8382-533f3c4a9ab9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
namespace PI.Dv.TIW
theorem _root_.solution (w : W) (hw : w ≠ 0) : ∃ φ : Module.Dual K W, φ w = 1 := by
  by_contra h
  push_neg at h
  apply hw
  rw [← Module.forall_dual_apply_eq_zero_iff K w]
  intro φ
  by_contra hφ
  exact h ((φ w)⁻¹ • φ) (by simp [inv_mul_cancel₀ hφ])
end PI.Dv.TIW
