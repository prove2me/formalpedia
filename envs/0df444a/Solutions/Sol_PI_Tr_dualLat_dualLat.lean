-- Prove2me | solution 1 for PI.Tr.dualLat_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:20:51.02867+00:00
-- url     : https://prove2.me/submissions/9a841187-376e-41d9-bf7f-15af470e59c4

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
variable [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
namespace PI.Tr
theorem _root_.solution : dualLat (dualLat Λ) = Λ := by
  classical
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b) = Λ := Module.Basis.ofZLatticeBasis_span ℝ Λ _
  have hnd : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h0 := congrArg (fun f => f m) hm
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at h0
    exact inner_self_eq_zero.1 h0
  have hsym : LinearMap.BilinForm.IsSymm (innerₗ E) :=
    LinearMap.BilinForm.isSymm_def.2 fun x y => by simp [innerₗ_apply_apply, real_inner_comm]
  rw [dualLat_eq, dualLat_eq, ← hspan,
    LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hnd hsym]
end PI.Tr
