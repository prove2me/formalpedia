-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_pow_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:29.264323+00:00
-- url     : https://prove2.me/submissions/4dc93d52-d95c-4dca-b7c3-43fdaad949ec

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
theorem _root_.solution (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto ht
  have h2 : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have h3 := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO (h1.trans_isBigO h2)
  exact h3.congr (fun n => rfl) (fun n => by ring)
end ReciprocityTheory.GeometryOfNumbersTheory
