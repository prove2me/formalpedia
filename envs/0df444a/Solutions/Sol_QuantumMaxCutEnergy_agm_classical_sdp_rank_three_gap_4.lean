-- Prove2me | solution 4 for QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T18:59:20.624193+00:00
-- url     : https://prove2.me/submissions/0ee6d2cf-5a60-4360-b445-c1ea6418c6fa

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound

open scoped BigOperators

namespace QMCGlue

/-- The symmetric weight matrix attached to a `Weights n`. -/
private def wMat {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then (w ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (w ⟨(j, i), h⟩ : ℝ) else 0

private lemma wMat_apply {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (i j : Fin n) :
    wMat w i j = (if h : i < j then (w ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (w ⟨(j, i), h⟩ : ℝ) else 0) := rfl

private lemma wMat_symm {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (i j : Fin n) :
    wMat w i j = wMat w j i := by
  rw [wMat_apply, wMat_apply]
  rcases lt_trichotomy i j with h | h | h
  · have h' : ¬ j < i := not_lt.mpr (le_of_lt h)
    simp [h, h']
  · subst h
    simp
  · have h' : ¬ i < j := not_lt.mpr (le_of_lt h)
    simp [h, h']

private lemma wMat_diag {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (i : Fin n) :
    wMat w i i = 0 := by
  rw [wMat_apply]
  simp

private lemma wMat_lt {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (i j : Fin n) (h : i < j) :
    wMat w i j = (w ⟨(i, j), h⟩ : ℝ) := by
  rw [wMat_apply]
  simp [h]

/-- Doubly stochastic bookkeeping: for a symmetric matrix with zero diagonal the full double
sum is twice the sum over the ordered pairs with `i < j`. -/
private lemma two_mul_edge_sum {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, g i j = g j i) (hdiag : ∀ i, g i i = 0) :
    (∑ i : Fin n, ∑ j : Fin n, g i j)
      = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, g e.val.1 e.val.2 := by
  classical
  have hprod : (∑ i : Fin n, ∑ j : Fin n, g i j) = ∑ p : Fin n × Fin n, g p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : Fin n × Fin n => g p.1 p.2)).symm
  have key : ∀ p : Fin n × Fin n, g p.1 p.2 =
      (if p.1 < p.2 then g p.1 p.2 else 0) + (if p.2 < p.1 then g p.1 p.2 else 0) := by
    rintro ⟨i, j⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr (le_of_lt h)), add_zero]
    · subst h
      simp [hdiag]
    · rw [if_neg (not_lt.mpr (le_of_lt h)), if_pos h, zero_add]
  have hstep : (∑ p : Fin n × Fin n, g p.1 p.2)
      = (∑ p : Fin n × Fin n, if p.1 < p.2 then g p.1 p.2 else 0)
        + ∑ p : Fin n × Fin n, if p.2 < p.1 then g p.1 p.2 else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => key p)
  have hlt : (∑ p : Fin n × Fin n, if p.1 < p.2 then g p.1 p.2 else 0)
      = ∑ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)), g p.1 p.2 :=
    (Finset.sum_filter (fun p : Fin n × Fin n => p.1 < p.2) (fun p => g p.1 p.2)).symm
  have hgtFilter : (∑ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)), g p.1 p.2)
      = ∑ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)), g p.1 p.2 := by
    refine Finset.sum_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p hp
      simp
    · intro p hp
      simp
    · intro p hp
      simpa using hsym p.1 p.2
  have hgt : (∑ p : Fin n × Fin n, if p.2 < p.1 then g p.1 p.2 else 0)
      = ∑ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)), g p.1 p.2 := by
    rw [← Finset.sum_filter (fun p : Fin n × Fin n => p.2 < p.1) (fun p => g p.1 p.2)]
    exact hgtFilter
  have hedge : (∑ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)), g p.1 p.2)
      = ∑ e : QuantumMaxCutEnergy.Edge n, g e.val.1 e.val.2 :=
    Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (fun x => by simp) (fun p => g p.1 p.2)
  rw [hprod, hstep, hlt, hgt, ← hedge]
  ring

/-- The `MAXCUT` SDP objective of the weight matrix is the averaged edge objective. -/
private lemma maxcut_objective_eq {n : ℕ} (w : QuantumMaxCutEnergy.Weights n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hXsym : ∀ i j, X i j = X j i) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (wMat w) X
      = (1 / 2) * ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * (1 - X e.val.1 e.val.2) := by
  have hsym : ∀ i j, wMat w i j * (1 - X i j) = wMat w j i * (1 - X j i) := by
    intro i j
    rw [wMat_symm w i j, hXsym i j]
  have hdiag : ∀ i, wMat w i i * (1 - X i i) = 0 := by
    intro i
    rw [wMat_diag w i]
    ring
  have h2 := two_mul_edge_sum (fun i j => wMat w i j * (1 - X i j)) hsym hdiag
  have hedge : ∀ e : QuantumMaxCutEnergy.Edge n,
      wMat w e.val.1 e.val.2 * (1 - X e.val.1 e.val.2)
        = (w e : ℝ) * (1 - X e.val.1 e.val.2) := by
    rintro ⟨⟨i, j⟩, hij⟩
    rw [wMat_lt w i j hij]
  rw [ModernConvex.Relaxations.maxcutRelaxationObjective, h2,
    Finset.sum_congr rfl (fun e _ => hedge e)]
  ring

/-- Per-feasible-point bound: the rounding lemma plus the Bloch-vector energy bound. -/
private lemma per_X_bound (G : QuantumMaxCutEnergy.Input)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective (wMat G.weights) X
      ≤ QuantumMaxCutEnergy.optimum G := by
  classical
  obtain ⟨hXpsd, hXdiag⟩ := hX
  obtain ⟨r, hrnorm, hrbound⟩ :=
    QuantumMaxCutEnergy.agm_rank3_gaussian_rounding G.n G.weights X hXpsd hXdiag
  have hbloch := QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound G r hrnorm
  have hXsym : ∀ i j, X i j = X j i := by
    intro i j
    have h := hXpsd.isHermitian.apply j i
    simpa using h
  have hobj := maxcut_objective_eq G.weights X hXsym
  -- the three sums
  have hid1 : (∑ e : QuantumMaxCutEnergy.Edge G.n,
        (G.weights e : ℝ) * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a))
      = (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
        - (∑ e : QuantumMaxCutEnergy.Edge G.n,
            (G.weights e : ℝ) * (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hid2 : (∑ e : QuantumMaxCutEnergy.Edge G.n,
        (G.weights e : ℝ) * (1 - X e.val.1 e.val.2))
      = (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ))
        - (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hid3 : (∑ e : QuantumMaxCutEnergy.Edge G.n,
        (G.weights e : ℝ) * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)
      = ((∑ e : QuantumMaxCutEnergy.Edge G.n,
            (G.weights e : ℝ) * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) / 2) :=
    (Finset.sum_div _ _ _).symm
  rw [hobj]
  linarith [hrbound, hbloch, hid1, hid2, hid3]

end QMCGlue

open scoped BigOperators

theorem solution (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G := by
  have hbound : ∀ y ∈ (ModernConvex.Relaxations.maxcutRelaxationObjective (QMCGlue.wMat G.weights) ''
      {X | ModernConvex.Relaxations.IsUnitDiagPSD X}),
      y ≤ QuantumMaxCutEnergy.optimum G / 0.954 := by
    rintro y ⟨X, hX, rfl⟩
    have h := QMCGlue.per_X_bound G X hX
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.954)]
    linarith [h]
  have hSle : S ≤ QuantumMaxCutEnergy.optimum G / 0.954 := (isLUB_le_iff hS).mpr hbound
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.954)] at hSle
  linarith [hSle]
