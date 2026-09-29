-- Prove2me | solution 1 for Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3b9b4074-82c9-5507-82e3-18bb8c9a8b01

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero

set_option autoImplicit false

open Filter Topology

theorem solution
    (R D : ℕ) (N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
    Polynomial.aeval (N 0) q = 0 := by

  let S : ℝ → Matrix (Fin R) (Fin R) ℂ := fun y => ∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro a _
    exact ((Complex.continuous_ofReal.pow _).smul continuous_const)
  let f : ℝ → Matrix (Fin R) (Fin R) ℂ := fun y => Polynomial.aeval (S y) q
  have hf : Continuous f := (Polynomial.continuous_aeval q).comp hS
  have hS0 : S 0 = N 0 := by
    show ∑ a : Fin (D + 1), (((0 : ℝ) : ℂ) ^ (a : ℕ)) • N a = N 0
    rw [Fin.sum_univ_succ]
    simp
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).symm
  have h3 : f 0 = 0 := tendsto_nhds_unique h1 h2
  have : f 0 = Polynomial.aeval (N 0) q := by show Polynomial.aeval (S 0) q = _; rw [hS0]
  rw [← this, h3]

end S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
end P2MW
export P2MW.S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero (solution)
