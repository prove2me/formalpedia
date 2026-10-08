-- Prove2me | solution 1 for SolomonRWRE.DiffEq.proof_4_4_regroup
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:51:48.167979+00:00
-- url     : https://prove2.me/submissions/04688e11-5d68-40e4-bdb0-780cedf17fe6

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology


namespace SolomonRWRE.DiffEq

theorem Z_eq_sum_core {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Z, ih, Finset.Icc_self, Finset.prod_singleton, Finset.mul_sum, mul_add, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [Finset.prod_Icc_succ_top (by omega), mul_comm]

theorem regroup_core {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.Icc 1 n, Z σ m ω = ∑ k ∈ Finset.Icc 1 n, Y σ k n ω := by
  simp_rw [Z_eq_sum_core, Y]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.1 - p.2 + 1, p.2⟩) (fun p => ⟨p.2 + p.1 - 1, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    omega
  · rintro ⟨m, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 1
    omega
  · rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 1
    omega
  · rintro ⟨m, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 2
    omega

end SolomonRWRE.DiffEq

open SolomonRWRE.DiffEq


theorem solution {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.Icc 1 n, Z σ m ω = ∑ k ∈ Finset.Icc 1 n, Y σ k n ω := by
  exact regroup_core σ n ω
