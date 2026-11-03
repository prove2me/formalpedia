-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank_three_rounding_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:41:40.183021+00:00
-- url     : https://prove2.me/submissions/07ef29d1-8b3b-405a-b3dc-c55f515c28e4

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
import Mathlib
open scoped BigOperators

namespace QMCGlue

lemma sum_symm_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (h0 : ∀ i, f i i = 0) (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by
  classical
  have htri : ∀ p : Fin n × Fin n, f p.1 p.2 =
      (if p.1 < p.2 then f p.1 p.2 else 0) + (if p.2 < p.1 then f p.1 p.2 else 0)
        + (if p.1 = p.2 then f p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg h.ne]; ring
    · rw [if_neg (by omega : ¬ p.1 < p.2), if_neg (by omega : ¬ p.2 < p.1), if_pos h,
        show f p.1 p.2 = 0 by rw [h, h0]]; ring
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg h.ne']; ring
  have hswap : (∑ p : Fin n × Fin n, if p.2 < p.1 then f p.1 p.2 else 0)
      = ∑ p : Fin n × Fin n, if p.1 < p.2 then f p.1 p.2 else 0 := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n))
      (fun p : Fin n × Fin n => if p.2 < p.1 then f p.1 p.2 else 0)
      (fun p : Fin n × Fin n => if p.1 < p.2 then f p.1 p.2 else 0) (fun p => ?_)
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hsym p.2 p.1]
    rfl
  have hdiag : (∑ p : Fin n × Fin n, if p.1 = p.2 then f p.1 p.2 else 0) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    by_cases h : p.1 = p.2
    · simp [h, h0]
    · simp [h]
  have hP1 : (∑ p : Fin n × Fin n, if p.1 < p.2 then f p.1 p.2 else 0)
      = ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by
    rw [← Finset.sum_filter (s := Finset.univ)
      (p := fun p : Fin n × Fin n => p.1 < p.2) (f := fun p => f p.1 p.2)]
    exact Finset.sum_subtype _ (by intro x; simp) _
  calc (∑ i, ∑ j, f i j) = ∑ p : Fin n × Fin n, f p.1 p.2 := by
        rw [Fintype.sum_prod_type]
  _ = (∑ p : Fin n × Fin n, if p.1 < p.2 then f p.1 p.2 else 0)
        + (∑ p : Fin n × Fin n, if p.2 < p.1 then f p.1 p.2 else 0)
        + (∑ p : Fin n × Fin n, if p.1 = p.2 then f p.1 p.2 else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun p _ => htri p)
  _ = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by
        rw [hswap, hdiag, hP1]; ring

end QMCGlue

open scoped BigOperators

theorem solution (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
      ≤ QuantumMaxCutEnergy.optimum G := by
  classical
  obtain ⟨hpsd, hdiag⟩ := hX
  obtain ⟨r, hr, hround⟩ :=
    QuantumMaxCutEnergy.agm_rank3_gaussian_rounding G.n G.weights X hpsd hdiag
  have hunit := QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound G r hr
  have hXsym : ∀ i j, X i j = X j i := fun i j => by
    have h := hpsd.isHermitian.apply i j
    simpa using h.symm
  -- the symmetric weight matrix
  set a : Matrix (Fin G.n) (Fin G.n) ℝ := Matrix.of fun i j =>
      if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0 with ha
  have haval : ∀ i j : Fin G.n, a i j =
      if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0 := by
    intro i j; simp only [ha, Matrix.of_apply]
  have hasym : ∀ i j, a i j = a j i := by
    intro i j
    rw [haval i j, haval j i]
    by_cases h1 : i < j
    · have h2 : ¬ (j < i) := not_lt.mpr h1.le
      simp only [dif_pos h1, dif_neg h2]
    · by_cases h2 : j < i
      · simp only [dif_neg h1, dif_pos h2]
      · simp only [dif_neg h1, dif_neg h2]
  have h0 : ∀ i : Fin G.n, a i i * (1 - X i i) = 0 := by
    intro i
    have : a i i = 0 := by rw [haval i i, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
    rw [this]; ring
  have hsymf : ∀ i j : Fin G.n, a i j * (1 - X i j) = a j i * (1 - X j i) := by
    intro i j; rw [hasym i j, hXsym i j]
  have hkey := QMCGlue.sum_symm_pairs (n := G.n) (f := fun i j => a i j * (1 - X i j)) h0 hsymf
  have hedge : ∀ e : QuantumMaxCutEnergy.Edge G.n,
      a e.val.1 e.val.2 * (1 - X e.val.1 e.val.2)
        = (G.weights e : ℝ) * (1 - X e.val.1 e.val.2) := by
    intro e
    have hlt : (e.val.1 : Fin G.n) < e.val.2 := e.2
    have hw : a e.val.1 e.val.2 = (G.weights e : ℝ) := by
      rw [haval, dif_pos hlt]
    rw [hw]
  have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective a X
      = (1 / 4) * (∑ i, ∑ j, a i j * (1 - X i j)) := rfl
  set W : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) with hW
  set C : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n,
    (G.weights e : ℝ) * (∑ b : Fin 3, r e.val.1 b * r e.val.2 b) with hC
  set Z : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2 with hZ
  set S2 : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * (1 - X e.val.1 e.val.2)
    with hS2
  have hA : S2 = W - Z := by
    rw [hS2, hW, hZ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hB : (∑ e : QuantumMaxCutEnergy.Edge G.n,
      (G.weights e : ℝ) * (1 - ∑ b : Fin 3, r e.val.1 b * r e.val.2 b) / 2) = (W - C) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [hW, hC, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hC' : C ≤ 0.046 * W + 0.954 * Z := hround
  have hedge2 : (∑ e : QuantumMaxCutEnergy.Edge G.n,
      a e.val.1 e.val.2 * (1 - X e.val.1 e.val.2)) = S2 := by
    rw [hS2]
    exact Finset.sum_congr rfl (fun e _ => hedge e)
  have hobj2 : ModernConvex.Relaxations.maxcutRelaxationObjective a X = S2 / 2 := by
    rw [hobj, hkey, hedge2]
    ring
  rw [hobj2]
  rw [hB] at hunit
  nlinarith [hunit, hC', hA]
