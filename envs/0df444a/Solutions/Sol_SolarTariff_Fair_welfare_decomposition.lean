-- Prove2me | solution 1 for SolarTariff.Fair.welfare_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:41:11.562766+00:00
-- url     : https://prove2.me/submissions/5a6aa6fa-2b4d-432d-8530-0e2680ea4ef4

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (B : Bills ι) (A : Finset ι) (ps : ℝ)
    (hU : utilityChange M B A = M.dU)
    (hS : (ps - M.cs (DeltaE M A)) * DeltaE M A = M.dS) :
    (∑ i, M.h i * (-outflowChange M B A ps i)) = dC M A := by
  have key : ∑ i, M.h i * (-outflowChange M B A ps i) =
      M.pr0 * E0 M - ∑ i, M.h i * (if i ∈ A then B.adopt i else B.nonAdopt i)
        - ps * DeltaE M A := by
    unfold outflowChange DeltaE E0
    rw [Finset.mul_sum, Finset.mul_sum]
    have h1 : ∑ i ∈ A, ps * (M.h i * M.g i) =
        ∑ i, if i ∈ A then ps * (M.h i * M.g i) else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [key]
  unfold utilityChange at hU
  unfold dC dWF
  linarith
