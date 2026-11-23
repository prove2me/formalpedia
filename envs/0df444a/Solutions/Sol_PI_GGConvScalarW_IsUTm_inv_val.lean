-- Prove2me | solution 1 for PI.GGConvScalarW.IsUTm.inv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:41.044719+00:00
-- url     : https://prove2.me/submissions/32b5630d-539b-4361-b20d-80aa3f24910c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGConvScalarW
namespace IsUTm
theorem _root_.solution (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by
  have h2 : ∀ i j, j < i → ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) i j = 0 := by
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
      (fun a b hab => h.2 a b hab) hij
  refine ⟨fun i => ?_, h2⟩
  have hm : ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) * (u : Matrix (Fin k) (Fin k) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he := congrFun (congrFun hm i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, h.1, mul_one, Matrix.one_apply_eq] at he
  · exact he
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hh | hh
    · rw [h2 i l hh, zero_mul]
    · rw [h.2 l i hh, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ i) hh
end IsUTm
end PI.GGConvScalarW
