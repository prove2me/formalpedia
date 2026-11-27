-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.rank_mul_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:01.017917+00:00
-- url     : https://prove2.me/submissions/e3eb911b-9d2d-403b-82b4-f64b80b3d1df

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) (r : ℕ → ℝ) (δ t : ℝ)
    (hr : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / (D.factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ D) :
    (fun n : ℕ => (n : ℝ) * r n * t -
        ((D + 1 : ℝ) * δ * t) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left t).mul_isLittleO hr
  refine h.congr (fun n => ?_) (fun n => by ring)
  have hD : (0 : ℝ) < (D.factorial : ℝ) := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
