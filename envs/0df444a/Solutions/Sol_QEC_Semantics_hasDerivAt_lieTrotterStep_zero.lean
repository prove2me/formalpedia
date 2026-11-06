-- Prove2me | solution 1 for QEC.Semantics.hasDerivAt_lieTrotterStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:39:22.03114+00:00
-- url     : https://prove2.me/submissions/ffdefa5f-c78a-420a-abdd-4f07db595cb1

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x y : A) :
    HasDerivAt (lieTrotterStep x y) (x + y) (0 : Complex) := by
  change HasDerivAt
    ((fun z : Complex => NormedSpace.exp (z • x)) *
      (fun z : Complex => NormedSpace.exp (z • y))) (x + y) (0 : Complex)
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one, one_mul] using
    (hasDerivAt_exp_smul_const x (0 : Complex)).mul
      (hasDerivAt_exp_smul_const y (0 : Complex))
end QEC.Semantics
