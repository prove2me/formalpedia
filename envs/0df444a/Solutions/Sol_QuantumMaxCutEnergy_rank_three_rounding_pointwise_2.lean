-- Prove2me | solution 2 for QuantumMaxCutEnergy.rank_three_rounding_pointwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:53:57.327626+00:00
-- url     : https://prove2.me/submissions/15ba46f2-bac8-44d9-971c-1cd01d3f6cd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
open scoped BigOperators

namespace QMCRank3

variable {n : ℕ}

/-- Double sum of a symmetric kernel with vanishing diagonal equals twice its upper half. -/
lemma two_mul_sum_edges (b : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0) :
    (∑ i, ∑ j, b i j) = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, b e.val.1 e.val.2 := by
  classical
  set A : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2) with hA
  set B : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => ¬ p.1 < p.2) with hB
  set C : Finset (Fin n × Fin n) := B.filter (fun p => p.2 < p.1) with hC
  set D : Finset (Fin n × Fin n) := B.filter (fun p => ¬ p.2 < p.1) with hD
  have hCD : ∑ p ∈ C, b p.1 p.2 + ∑ p ∈ D, b p.1 p.2 = ∑ p ∈ B, b p.1 p.2 :=
    Finset.sum_filter_add_sum_filter_not B (fun p : Fin n × Fin n => p.2 < p.1) (fun p => b p.1 p.2)
  have hAB : ∑ p ∈ A, b p.1 p.2 + ∑ p ∈ B, b p.1 p.2 = ∑ p : Fin n × Fin n, b p.1 p.2 :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 < p.2) (fun p => b p.1 p.2)
  have hD0 : ∑ p ∈ D, b p.1 p.2 = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    simp only [hD, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hEq : p.1 = p.2 := le_antisymm (not_lt.mp hp.2) (not_lt.mp hp.1)
    rw [hEq, hdiag]
  have hCA : ∑ p ∈ C, b p.1 p.2 = ∑ p ∈ A, b p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hC, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.2
    · intro p1 _ p2 _ h
      have h1 : p1.2 = p2.2 := by simpa using congrArg Prod.fst h
      have h2 : p1.1 = p2.1 := by simpa using congrArg Prod.snd h
      exact Prod.ext h2 h1
    · intro q hq
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [hC, hB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨not_lt.mpr (le_of_lt hq), hq⟩
    · intro p _
      exact hsym p.1 p.2
  have hedge : ∑ e : QuantumMaxCutEnergy.Edge n, b e.val.1 e.val.2 = ∑ p ∈ A, b p.1 p.2 := by
    rw [← Finset.sum_subtype A (fun x => by simp [hA]) (fun p : Fin n × Fin n => b p.1 p.2)]
  have hprod : (∑ i, ∑ j, b i j) = ∑ p : Fin n × Fin n, b p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : Fin n × Fin n => b p.1 p.2)).symm
  rw [hprod, hedge]
  linarith [hAB, hCD, hD0, hCA]

/-- The weighted adjacency matrix of the campaign: `w` at `i < j`, mirrored, zero diagonal. -/
abbrev wAdj (w : QuantumMaxCutEnergy.Weights n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if h : i < j then (w ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (w ⟨(j, i), h⟩ : ℝ) else 0

lemma wAdj_symm (w : QuantumMaxCutEnergy.Weights n) (i j : Fin n) :
    wAdj w i j = wAdj w j i := by
  simp only [wAdj, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_neg (not_lt.mpr (le_of_lt h)), dif_pos h]
  · subst h; rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
  · rw [dif_neg (not_lt.mpr (le_of_lt h)), dif_pos h, dif_pos h]

lemma wAdj_diag (w : QuantumMaxCutEnergy.Weights n) (i : Fin n) : wAdj w i i = 0 := by
  simp [wAdj]

lemma wAdj_edge (w : QuantumMaxCutEnergy.Weights n) (e : QuantumMaxCutEnergy.Edge n) :
    wAdj w e.val.1 e.val.2 = (w e : ℝ) := by
  obtain ⟨⟨i, j⟩, hij⟩ := e
  simp only [wAdj, Matrix.of_apply]
  rw [dif_pos hij]

end QMCRank3

open scoped BigOperators
open QMCRank3


/-- **Pointwise form of the rank-three rank gap.**

For every weighted graph `G` and every feasible matrix `X` of its classical Max-Cut SDP,
the Quantum Max-Cut optimum is at least `0.954` times the relaxation objective of `X`.
The rounding step is the imported rank-three Gaussian (Bloch) rounding inequality; the
energy bound is the imported proved bound `unit_bloch_assignment_energy_lower_bound`. -/
theorem solution (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
      ≤ QuantumMaxCutEnergy.optimum G := by
  classical
  obtain ⟨r, hr, hround⟩ :=
    QuantumMaxCutEnergy.agm_rank3_gaussian_rounding G.n G.weights X hX.1 hX.2
  have henergy := QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound G r hr
  have hXsym : ∀ i j : Fin G.n, X i j = X j i := by
    intro i j
    have h1 := (Matrix.PosSemidef.isHermitian hX.1).apply i j
    simpa using h1.symm
  have hpair : (∑ i, ∑ j, wAdj G.weights i j * (1 - X i j))
      = 2 * ∑ e : QuantumMaxCutEnergy.Edge G.n,
          (G.weights e : ℝ) * (1 - X e.val.1 e.val.2) := by
    rw [two_mul_sum_edges (fun i j => wAdj G.weights i j * (1 - X i j)) ?_ ?_]
    · congr 1
      exact Finset.sum_congr rfl (fun e _ => by rw [wAdj_edge])
    · intro i j
      rw [wAdj_symm G.weights i j, hXsym i j]
    · intro i
      rw [wAdj_diag G.weights i]
      ring
  have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective (wAdj G.weights) X
      = ((∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
          - ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2) / 2 := by
    have hsplit : (∑ e : QuantumMaxCutEnergy.Edge G.n,
          (G.weights e : ℝ) * (1 - X e.val.1 e.val.2))
        = (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
          - ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    simp only [ModernConvex.Relaxations.maxcutRelaxationObjective]
    rw [hpair, hsplit]
    ring
  have henEq : (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)
      = ((∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
          - ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
              (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) / 2 := by
    have h1 : (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)
        = (∑ e : QuantumMaxCutEnergy.Edge G.n, ((G.weights e : ℝ) - (G.weights e : ℝ) *
            (∑ a : Fin 3, r e.val.1 a * r e.val.2 a))) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [h1, Finset.sum_sub_distrib]
  calc (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective (wAdj G.weights) X
      = 0.954 * (((∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
          - ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2) / 2) := by
        rw [hobj]
    _ ≤ ((∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
          - ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
              (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) / 2 := by
        linarith [hround]
    _ = ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2 := henEq.symm
    _ ≤ QuantumMaxCutEnergy.optimum G := henergy
