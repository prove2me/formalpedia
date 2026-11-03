-- Prove2me | solution 4 for QuantumMaxCutEnergy.rank_three_rounding_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:08:20.562212+00:00
-- url     : https://prove2.me/submissions/e4bb7ab5-594a-43e3-9555-d08fef123bbc

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound

open scoped BigOperators

namespace QMCPointwise

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

end QMCPointwise

open scoped BigOperators

theorem solution
    (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
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
  -- the double sum is twice the edge sum
  have hsym : ∀ i j,
      (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j * (1 - X i j)
        = (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) j i * (1 - X j i) := by
    intro i j
    rw [hXsym i j]
    congr 1
    rw [Matrix.of_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · have h' : ¬ j < i := not_lt.mpr (le_of_lt h)
      simp [h, h']
    · subst h
      simp
    · have h' : ¬ i < j := not_lt.mpr (le_of_lt h)
      simp [h, h']
  have hdiag : ∀ i,
      (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i i * (1 - X i i) = 0 := by
    intro i
    rw [hXdiag i, Matrix.of_apply]
    simp
  have h2 := QMCPointwise.two_mul_edge_sum
    (fun i j => (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j * (1 - X i j)) hsym hdiag
  have hedge : ∀ e : QuantumMaxCutEnergy.Edge G.n,
      (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) e.val.1 e.val.2
        * (1 - X e.val.1 e.val.2)
      = (G.weights e : ℝ) * (1 - X e.val.1 e.val.2) := by
    rintro ⟨⟨i, j⟩, hij⟩
    rw [Matrix.of_apply]
    simp [hij]
  have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
      = (1 / 2) * ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * (1 - X e.val.1 e.val.2) := by
    rw [ModernConvex.Relaxations.maxcutRelaxationObjective, h2,
      Finset.sum_congr rfl (fun e _ => hedge e)]
    ring
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
