-- Prove2me | solution 2 for QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:01:11.560357+00:00
-- url     : https://prove2.me/submissions/f74ed07b-8f23-47c4-9fb4-073ffac156c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Mathlib
open scoped BigOperators

namespace QMCGap053

open QuantumMaxCutEnergy

/-- The symmetric zero-diagonal weight function of a campaign input. -/
def wt (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) : Fin n → Fin n → ℝ :=
  fun i j =>
    if h : i < j then (w ⟨(i, j), h⟩ : ℝ) else if h : j < i then (w ⟨(j, i), h⟩ : ℝ) else 0

lemma wt_self (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (i : Fin n) : wt n w i i = 0 := by
  simp [wt]

lemma wt_symm (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (i j : Fin n) :
    wt n w i j = wt n w j i := by
  simp only [wt]
  by_cases h : i < j
  · rw [dif_pos h, dif_neg (not_lt.mpr h.le), dif_pos h]
  · by_cases h2 : j < i
    · rw [dif_neg h, dif_pos h2, dif_pos h2]
    · rw [dif_neg h, dif_neg h2]
      have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h)
      subst hij
      simp

lemma wt_edge (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (e : QuantumMaxCutEnergy.Edge n) :
    wt n w e.val.1 e.val.2 = (w e : ℝ) := by
  obtain ⟨⟨i, j⟩, hij⟩ := e
  simp only [wt, dif_pos hij]

/-- Double sums of a symmetric matrix against the weight function are twice the edge sums. -/
lemma sum_sum_eq_two_mul_edge_sum {n : ℕ} (w : QuantumMaxCutEnergy.Weights n)
    (g : Fin n → Fin n → ℝ) (hsym : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, wt n w i j * g i j)
      = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * g e.val.1 e.val.2 := by
  classical
  set A : Fin n → Fin n → ℝ := fun i j => wt n w i j * g i j with hA
  have hAii : ∀ i, A i i = 0 := by
    intro i; simp [hA, wt_self]
  have hAsym : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA, wt_symm n w i j, hsym i j]
  -- split each row into its upper and lower halves
  have hsplit : (∑ i, ∑ j, A i j) =
      (∑ i, ∑ j, if i < j then A i j else 0) + (∑ i, ∑ j, if j < i then A i j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases h1 : i < j
    · have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [h1, h2]
    · by_cases h2 : j < i
      · simp [h1, h2]
      · have hij : j = i := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
        subst hij
        simp [hAii]
  -- the two halves agree by symmetry
  have hhalves : (∑ i, ∑ j, if j < i then A i j else 0) =
      (∑ i, ∑ j, if i < j then A i j else 0) := by
    have h1 : (∑ i, ∑ j, if j < i then A i j else 0) =
        (∑ i, ∑ j, (fun aa bb => if aa < bb then A aa bb else 0) j i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      show (if j < i then A i j else 0) = (if j < i then A j i else 0)
      by_cases h : j < i
      · rw [if_pos h, if_pos h]; exact hAsym i j
      · rw [if_neg h, if_neg h]
    have h2 : (∑ i, ∑ j, (fun aa bb => if aa < bb then A aa bb else 0) j i) =
        (∑ i, ∑ j, if i < j then A i j else 0) := by
      rw [Finset.sum_comm]
    rw [h1, h2]
  -- identify the upper half with the sum over edges
  have hedge : (∑ i, ∑ j, if i < j then A i j else 0) =
      ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * g e.val.1 e.val.2 := by
    rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
      if p.1 < p.2 then A p.1 p.2 else 0)]
    rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin n × Fin n)))
      (p := fun p : Fin n × Fin n => p.1 < p.2) (f := fun p => A p.1 p.2)]
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p : Fin n × Fin n => p.1 < p.2)) (p := fun p : Fin n × Fin n => p.1 < p.2)
      (by intro x; simp) (f := fun p => A p.1 p.2)]
    refine Finset.sum_congr rfl ?_
    intro e _
    simp only [hA, wt_edge]
  rw [hsplit, hhalves, hedge]
  ring

end QMCGap053

theorem solution (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G := by
  classical
  set a : Matrix (Fin G.n) (Fin G.n) ℝ := Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0 with ha
  have haij : ∀ i j, a i j = QMCGap053.wt G.n G.weights i j := by
    intro i j
    simp only [ha, Matrix.of_apply, QMCGap053.wt]
  have key : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X →
      0.954 * ModernConvex.Relaxations.maxcutRelaxationObjective a X
        ≤ QuantumMaxCutEnergy.optimum G := by
    intro X hX
    obtain ⟨r, hr, hround⟩ :=
      QuantumMaxCutEnergy.agm_rank3_gaussian_rounding G.n G.weights X hX.1 hX.2
    have hbloch := QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound G r hr
    -- the SDP objective as twice an edge sum
    have hsymX : ∀ i j, X i j = X j i := by
      intro i j
      have h := hX.1.isHermitian.apply i j
      simpa using h.symm
    have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective a X =
        (1 / 4) * (2 * (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ)) -
          2 * (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2)) := by
      have h1 : (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j * (1 - X i j)) =
          (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j) -
            (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j * X i j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      have h2 : ModernConvex.Relaxations.maxcutRelaxationObjective a X =
          (1 / 4) * (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j * (1 - X i j)) := by
        unfold ModernConvex.Relaxations.maxcutRelaxationObjective
        simp only [haij]
      have hW : (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j) =
          2 * ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
        have h := QMCGap053.sum_sum_eq_two_mul_edge_sum G.weights (fun _ _ => (1 : ℝ))
          (fun _ _ => rfl)
        simpa using h
      have hXT : (∑ i, ∑ j, QMCGap053.wt G.n G.weights i j * X i j) =
          2 * ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2 :=
        QMCGap053.sum_sum_eq_two_mul_edge_sum G.weights X hsymX
      rw [h2, h1, hW, hXT]
    -- the Bloch energy as half the slack
    have hsum : (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (1 - ∑ c : Fin 3, r e.val.1 c * r e.val.2 c) / 2) =
        ((∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ)) -
          (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
            (∑ c : Fin 3, r e.val.1 c * r e.val.2 c))) / 2 := by
      have hpt : ∀ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (1 - ∑ c : Fin 3, r e.val.1 c * r e.val.2 c) / 2
          = ((G.weights e : ℝ) -
            (G.weights e : ℝ) * (∑ c : Fin 3, r e.val.1 c * r e.val.2 c)) / 2 := by
        intro e; ring
      simp only [hpt, div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    rw [hsum] at hbloch
    rw [hobj]
    linarith [hround, hbloch]
  have hupper : ∀ y ∈ (ModernConvex.Relaxations.maxcutRelaxationObjective a ''
      {X | ModernConvex.Relaxations.IsUnitDiagPSD X}), y ≤ QuantumMaxCutEnergy.optimum G / 0.954 := by
    rintro y ⟨X, hX, rfl⟩
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.954)]
    linarith [key X hX]
  have hSle : S ≤ QuantumMaxCutEnergy.optimum G / 0.954 := hS.2 hupper
  have hcancel : (0.954 : ℝ) * (QuantumMaxCutEnergy.optimum G / 0.954) =
      QuantumMaxCutEnergy.optimum G := by
    field_simp
  linarith [mul_le_mul_of_nonneg_left hSle (by norm_num : (0 : ℝ) ≤ 0.954)]
