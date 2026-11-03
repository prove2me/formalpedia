-- Prove2me | solution 3 for QuantumMaxCutEnergy.rank_three_rounding_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:07:40.513431+00:00
-- url     : https://prove2.me/submissions/f52ae035-524f-450f-a27b-a0a98fe8e306

import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding
import Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib

open scoped BigOperators

/-- For a symmetric matrix vanishing on the diagonal, the double sum over all ordered pairs
is twice the sum over the unordered pairs `i < j`. -/
theorem qmc_sum_univ_prod_eq_two_mul_sum_edges {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by
  classical
  set h : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then f p.1 p.2 else 0 with hh
  have hpt : ∀ p : Fin n × Fin n, f p.1 p.2 = h p + h p.swap := by
    rintro ⟨i, j⟩
    by_cases hij : i < j
    · have hji : ¬ j < i := not_lt.mpr hij.le
      simp [hh, hij, hji]
    · by_cases hji : j < i
      · simp [hh, hij, hji, hsym i j]
      · have hne : i = j := by omega
        rw [hne]
        simp [hh, hdiag]
  have hswap : (∑ p : Fin n × Fin n, h p.swap) = ∑ p : Fin n × Fin n, h p := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n))
      (fun p : Fin n × Fin n => h p.swap) (fun p : Fin n × Fin n => h p) ?_
    intro p
    rfl
  have hfilter : (∑ p : Fin n × Fin n, h p)
      = Finset.sum (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
          (fun p => f p.1 p.2) := by
    have hsf := (Finset.sum_filter (s := (Finset.univ : Finset (Fin n × Fin n)))
      (p := fun p : Fin n × Fin n => p.1 < p.2) (f := fun p => f p.1 p.2)).symm
    simpa [hh] using hsf
  have hsub : Finset.sum (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
        (fun p => f p.1 p.2)
      = ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by
    exact Finset.sum_subtype (M := ℝ) (p := fun q : Fin n × Fin n => q.1 < q.2)
      (F := Subtype.fintype _) (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
      (fun x => by simp) (f := fun q => f q.1 q.2)
  calc (∑ i, ∑ j, f i j) = ∑ p : Fin n × Fin n, f p.1 p.2 := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin n × Fin n, (h p + h p.swap) := Finset.sum_congr rfl (fun p _ => hpt p)
    _ = (∑ p : Fin n × Fin n, h p) + (∑ p : Fin n × Fin n, h p.swap) := Finset.sum_add_distrib
    _ = 2 * (∑ p : Fin n × Fin n, h p) := by rw [hswap]; ring
    _ = 2 * ∑ e : QuantumMaxCutEnergy.Edge n, f e.val.1 e.val.2 := by rw [hfilter, hsub]

theorem solution (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
      ≤ QuantumMaxCutEnergy.optimum G := by
  classical
  set A : Matrix (Fin G.n) (Fin G.n) ℝ := Matrix.of (fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) with hA
  obtain ⟨r, hr, hround⟩ :=
    QuantumMaxCutEnergy.agm_rank3_gaussian_rounding G.n G.weights X hX.1 hX.2
  have hbloch := QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound G r hr
  set W : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) with hW
  set T : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) * X e.val.1 e.val.2 with hT
  set R : ℝ := ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
      (∑ a : Fin 3, r e.val.1 a * r e.val.2 a) with hR
  have henergy : (W - R) / 2 ≤ QuantumMaxCutEnergy.optimum G := by
    have h1 : (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
          (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) = (1 / 2) * (W - R) := by
      have hp : ∀ e : QuantumMaxCutEnergy.Edge G.n,
          (G.weights e : ℝ) * (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2
            = (1 / 2) * ((G.weights e : ℝ) -
                (G.weights e : ℝ) * (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) := by
        intro e; ring
      rw [Finset.sum_congr rfl (fun e _ => hp e), ← Finset.mul_sum, Finset.sum_sub_distrib,
        ← hW, ← hR]
    rw [h1] at hbloch
    linarith [hbloch]
  have hAsym : ∀ i j, A i j = A j i := by
    intro i j
    by_cases hij : i < j
    · have hji : ¬ j < i := not_lt.mpr hij.le
      simp [hA, hij, hji]
    · by_cases hji : j < i
      · simp [hA, hij, hji]
      · have hne : i = j := by omega
        rw [hne]
  have hXsym : ∀ i j, X i j = X j i := by
    intro i j
    have h1 : Matrix.conjTranspose X i j = X i j := by rw [hX.1.1]
    rw [Matrix.conjTranspose_apply] at h1
    simpa using h1.symm
  have hAdiag : ∀ i, A i i = 0 := by
    intro i; simp [hA]
  have hAe : ∀ e : QuantumMaxCutEnergy.Edge G.n, A e.val.1 e.val.2 = (G.weights e : ℝ) := by
    intro e; simp [hA, e.property]
  have hkey := qmc_sum_univ_prod_eq_two_mul_sum_edges (n := G.n)
    (f := fun i j => A i j * (1 - X i j))
    (fun i j => by rw [hAsym i j, hXsym i j]) (fun i => by simp [hAdiag])
  have hedge : (∑ e : QuantumMaxCutEnergy.Edge G.n,
        A e.val.1 e.val.2 * (1 - X e.val.1 e.val.2)) = W - T := by
    have h1 : ∀ e : QuantumMaxCutEnergy.Edge G.n,
        A e.val.1 e.val.2 * (1 - X e.val.1 e.val.2)
          = (G.weights e : ℝ) - (G.weights e : ℝ) * X e.val.1 e.val.2 := by
      intro e; rw [hAe e]; ring
    rw [Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_sub_distrib, ← hW, ← hT]
  have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective A X = (W - T) / 2 := by
    rw [ModernConvex.Relaxations.maxcutRelaxationObjective, hkey, hedge]
    ring
  have hmain : (0.954 : ℝ) * ((W - T) / 2) ≤ (W - R) / 2 := by
    linarith [hround]
  have hfin : (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective A X
      ≤ QuantumMaxCutEnergy.optimum G := by
    rw [hobj]; linarith [hmain, henergy]
  simpa [hA] using hfin
