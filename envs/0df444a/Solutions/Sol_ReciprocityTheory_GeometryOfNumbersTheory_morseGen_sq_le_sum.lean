-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morseGen_sq_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:05.218849+00:00
-- url     : https://prove2.me/submissions/38a8a299-e8da-4e5e-ab9a-19ac7955aa2f

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory Complex
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  have hs : 0 ≤ ∑ j, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have h : ‖z‖ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs
end ReciprocityTheory.GeometryOfNumbersTheory
