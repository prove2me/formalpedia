-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ChebyshevThetaBound_intersectionNumber_baseChange_1e58a3fff588
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:08.331728+00:00
-- url     : https://prove2.me/submissions/7bb8ed86-0354-44ea-b0b9-f2000a907d63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

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
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace ChebyshevThetaBound
theorem _root_.solution : ChebyshevThetaBound.Statement := by
  intro x hx
  set n := ⌊x⌋₊
  have hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial n) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    exact_mod_cast this.ne'
  rw [hprod]
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log hpos
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le hx)
        exact Real.log_nonneg (by norm_num)
end ChebyshevThetaBound
end GroundTheory.Heights₂.Heights.RestTerms
