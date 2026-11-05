-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-04T18:57:13.190376+00:00
-- url     : https://prove2.me/submissions/37c95cee-f65f-4f48-8f2f-1306ab781794
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_certificate_tm2
import Mathlib
open scoped BigOperators

namespace QMCSDPCertificate

open Matrix ModernConvex.Relaxations

/-- `tr(PZ) ≥ 0` for real positive semidefinite `P, Z` (diagonalize `Z`). -/
theorem trace_mul_nonneg {n : ℕ} (P Z : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (hZ : Z.PosSemidef) : 0 ≤ (P * Z).trace := by
  have hspec := hZ.1.spectral_theorem
  rw [hspec]
  simp only [Unitary.conjStarAlgAut_apply]
  set U : Matrix (Fin n) (Fin n) ℝ := (hZ.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hQ : (star U * P * U).PosSemidef := by
    simpa [Matrix.star_eq_conjTranspose] using hP.conjTranspose_mul_mul_same U
  rw [Matrix.trace]
  refine Finset.sum_nonneg fun k _ => ?_
  simp only [Matrix.diag, Matrix.mul_diagonal, Function.comp_apply]
  have hk : 0 ≤ (star U * P * U) k k := hQ.diag_nonneg
  rw [Matrix.mul_assoc] at hk
  exact mul_nonneg hk (by simpa using hZ.eigenvalues_nonneg k)

/-- Weak duality for the Max-Cut SDP: a dual-feasible `y` bounds every feasible objective. -/
theorem objective_le_dual {n : ℕ} (a Z : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hy : (diagonal y + (1 / 4 : ℝ) • a).PosSemidef) (hZ : IsUnitDiagPSD Z) :
    maxcutRelaxationObjective a Z ≤ (1 / 4 : ℝ) * ∑ i, ∑ j, a i j + ∑ i, y i := by
  have h0 := trace_mul_nonneg _ _ hy hZ.1
  have hsym : ∀ i j, Z j i = Z i j := fun i j => by simpa using hZ.1.1.apply i j
  have h1 : (diagonal y * Z).trace = ∑ i, y i := by
    simp [Matrix.trace, Matrix.diagonal_mul, hZ.2]
  have h2 : (a * Z).trace = ∑ i, ∑ j, a i j * Z i j := by
    simp [Matrix.trace, Matrix.mul_apply, hsym]
  rw [add_mul, trace_add, Matrix.smul_mul, trace_smul, h1, h2, smul_eq_mul] at h0
  have h3 : ∑ i, ∑ j, a i j * (1 - Z i j) = ∑ i, ∑ j, a i j - ∑ i, ∑ j, a i j * Z i j := by
    simp [mul_sub, Finset.sum_sub_distrib]
  unfold maxcutRelaxationObjective
  rw [h3]
  linarith

/-- A primal-feasible `X` and a dual-feasible `y` sandwich the exact SDP value. -/
theorem sandwich {n : ℕ} (a X : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hX : IsUnitDiagPSD X) (hy : (diagonal y + (1 / 4 : ℝ) • a).PosSemidef) :
    ∃ S, IsMaxcutSDPValue a S ∧ maxcutRelaxationObjective a X ≤ S ∧
      S ≤ (1 / 4 : ℝ) * ∑ i, ∑ j, a i j + ∑ i, y i := by
  have hne : (maxcutRelaxationObjective a '' {Z | IsUnitDiagPSD Z}).Nonempty := ⟨_, X, hX, rfl⟩
  have hbdd : BddAbove (maxcutRelaxationObjective a '' {Z | IsUnitDiagPSD Z}) := by
    refine ⟨(1 / 4 : ℝ) * ∑ i, ∑ j, a i j + ∑ i, y i, ?_⟩
    rintro _ ⟨Z, hZ, rfl⟩
    exact objective_le_dual a Z y hy hZ
  refine ⟨sSup _, isLUB_csSup hne hbdd, le_csSup hbdd ⟨X, hX, rfl⟩, csSup_le hne ?_⟩
  rintro _ ⟨Z, hZ, rfl⟩
  exact objective_le_dual a Z y hy hZ

end QMCSDPCertificate

open scoped BigOperators

theorem solution :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨L, hTM, hcert⟩ := QuantumMaxCutEnergy.agm_classical_sdp_certificate_tm2
  refine ⟨L, hTM, fun G => ?_⟩
  obtain ⟨X, y, hX, hy, hL, hgap⟩ := hcert G
  obtain ⟨S, hS, hlo, hhi⟩ := QMCSDPCertificate.sandwich _ _ _ hX hy
  refine ⟨S, hS, ?_, ?_⟩
  · rw [hL]; exact hlo
  · linarith
