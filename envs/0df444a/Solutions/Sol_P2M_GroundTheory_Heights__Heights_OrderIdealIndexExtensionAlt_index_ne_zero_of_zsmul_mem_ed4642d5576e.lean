-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:36.535711+00:00
-- url     : https://prove2.me/submissions/2c36b1b4-add0-4cb4-ad9d-a328723b7194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
namespace GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (H : AddSubgroup M)
    {N : ℤ} (hN : N ≠ 0) (h : ∀ x : M, N • x ∈ H) : H.index ≠ 0 := by
  have htor : Module.IsTorsion ℤ (M ⧸ H.toIntSubmodule) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨⟨N, mem_nonZeroDivisors_of_ne_zero hN⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact h x
  have : Finite (M ⧸ H.toIntSubmodule) := Module.finite_of_fg_torsion _ htor
  have : Finite (M ⧸ H) := this
  exact AddSubgroup.index_ne_zero_of_finite
end GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
