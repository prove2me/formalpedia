-- Prove2me | solution 1 for PermanentRollout.criticalGradientIdeal_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/a07c06ca-b32c-4720-a309-1ac8dac2fce7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_eval_zero_of_pos
import Theorems.Thm_PermanentRollout_zeroLocus_gradientIdeal_eq_criticalLocus

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d) :
    homogeneousMapIdeal
      (fun i : Fin m => MvPolynomial.pderiv i P) ≠ ⊤ := by
  intro htop
  have horigin : (0 : Fin m → ℂ) ∈ criticalLocus P := by
    rw [mem_criticalLocus_iff]
    intro i
    exact homogeneous_eval_zero_of_pos (by omega) (hP.pderiv (i := i))
  have hzero : (0 : Fin m → ℂ) ∈
      MvPolynomial.zeroLocus ℂ
        (homogeneousMapIdeal
          (fun i : Fin m => MvPolynomial.pderiv i P)) := by
    rw [zeroLocus_gradientIdeal_eq_criticalLocus]
    exact horigin
  rw [htop, MvPolynomial.zeroLocus_top] at hzero
  exact hzero
end PermanentRollout
