-- Prove2me | solution 1 for PI.GGConvScalarW.IsUTm.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:04.702589+00:00
-- url     : https://prove2.me/submissions/f26b8ced-cd60-4e0d-8b60-f6ffe02d2805

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
theorem _root_.solution {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.1, hB.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.2 i l h, zero_mul]
      · rw [hB.2 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA.2 i l h, zero_mul]
    · rw [hB.2 l j (lt_of_lt_of_le hij h), mul_zero]
end IsUTm
end PI.GGConvScalarW
