-- Prove2me | solution 1 for PI.GGConvScalarW.cardU_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:40.932922+00:00
-- url     : https://prove2.me/submissions/4a72036e-710a-480a-90bc-0e61c8689428

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGConvScalarW
theorem _root_.solution (F : Type) [Field F] [Fintype F] (k : ℕ) : (cardU F k : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold cardU
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  first
    | (simp [IsUni]; intro i j h; simp [Matrix.one_apply, ne_of_gt h])
    | simp [IsUni]
    | (unfold IsUni; simp)
    | (unfold IsUni; intro i j h; simp [Matrix.one_apply, ne_of_gt h])
    | decide
end PI.GGConvScalarW
