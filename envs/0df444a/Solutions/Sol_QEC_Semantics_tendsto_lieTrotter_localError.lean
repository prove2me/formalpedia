-- Prove2me | solution 1 for QEC.Semantics.tendsto_lieTrotter_localError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:49.313034+00:00
-- url     : https://prove2.me/submissions/874e4278-4c42-4baa-829d-06bbce4d18bb

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Theorems.Thm_QEC_Semantics_hasDerivAt_lieTrotterStep_zero

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x y : A) :
    Tendsto
      (fun n : Nat => (n : Real) *
        ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
          lieTrotterStep x y ((n : Complex)⁻¹)‖)
      atTop (nhds 0) := by
  let reference : Complex → A := fun z => NormedSpace.exp (z • (x + y))
  have href : HasDerivAt reference (x + y) (0 : Complex) := by
    simpa [reference] using
      hasDerivAt_exp_smul_const (x + y) (0 : Complex)
  have hdefect := href.sub (hasDerivAt_lieTrotterStep_zero x y)
  have hquotient := (hasDerivAt_iff_tendsto.mp hdefect).comp
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Complex))
  refine hquotient.congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [reference, lieTrotterStep, norm_inv]
end QEC.Semantics
