-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.distance_contractivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:47:08.899507+00:00
-- url     : https://prove2.me/submissions/85c0f369-9cfe-491b-b4a3-167ce33c1144

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.3, (6): contractivity under every CPTP map implies (C2a). -/
theorem gk_kraus_density {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) : IsDensityMatrix (krausApply K rho) := by
  refine ⟨?_, ?_⟩
  · unfold krausApply
    exact Matrix.posSemidef_sum _ (fun i _ => hrho.1.mul_mul_conjTranspose_same (K i))
  · unfold krausApply
    rw [Matrix.trace_sum]
    have : ∀ i, (K i * rho * (K i)ᴴ).trace = ((K i)ᴴ * K i * rho).trace := by
      intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]
    exact hrho.2

theorem gk_kraus_diag {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∀ i, PreservesDiagonalBranch (K i)) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.PosSemidef) (hd : BasisDiagonal X) : BasisDiagonal (krausApply K X) := by
  intro i j hij
  unfold krausApply
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun k _ => hK k X hX hd i j hij)

theorem solution (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hcontract : DistanceContractive D) :
    CoherenceMonotone (fun d => distanceCandidate (D d)) := by
  intro d e hd he a K hK rho hrho
  obtain ⟨delta, hdelta, hmin⟩ := hattain d hd rho hrho
  have hKd := gk_kraus_density K hK.1 delta hdelta.1
  have hKr := gk_kraus_density K hK.1 rho hrho
  have hinc : IncoherentState (krausApply K delta) :=
    ⟨hKd, gk_kraus_diag K hK.2 delta hdelta.1.1 hdelta.2⟩
  have hch : IsChannel (krausApply K) := ⟨a, K, hK.1, fun _ => rfl⟩
  have h1 : distanceCandidate (D e) (krausApply K rho) ≤
      D e (krausApply K rho) (krausApply K delta) := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro v ⟨s, hs, rfl⟩
      exact hD e he _ _ hKr hs.1
    · exact ⟨_, hinc, rfl⟩
  have h2 : D d rho delta ≤ distanceCandidate (D d) rho := by
    unfold distanceCandidate
    refine le_csInf ⟨D d rho delta, delta, hdelta, rfl⟩ ?_
    rintro v ⟨s, hs, rfl⟩
    exact hmin s hs
  have h3 := hcontract d e hd he _ hch rho delta hrho hdelta.1
  show distanceCandidate (D e) (krausApply K rho) ≤ distanceCandidate (D d) rho
  linarith

