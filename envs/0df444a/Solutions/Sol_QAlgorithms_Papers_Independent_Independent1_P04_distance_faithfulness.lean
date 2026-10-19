-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.distance_faithfulness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:48:53.54663+00:00
-- url     : https://prove2.me/submissions/8a95bdd2-545c-4a3d-93a8-c96f1563052b

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

/-- PDF p.3, (5), (C1'): separating nonnegative distances with attained incoherent minima. -/
theorem gk_cand_eq {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hmin : ∀ sigma, IncoherentState sigma → D rho delta ≤ D rho sigma) :
    distanceCandidate D rho = D rho delta := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨D rho delta, ?_⟩
      rintro v ⟨s, hs, rfl⟩
      exact hmin s hs
    · exact ⟨_, hdelta, rfl⟩
  · refine le_csInf ⟨D rho delta, delta, hdelta, rfl⟩ ?_
    rintro v ⟨s, hs, rfl⟩
    exact hmin s hs

theorem solution (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hsep : ∀ d, 0 < d → ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
      (D d rho sigma = 0 ↔ rho = sigma)) :
    CoherenceNonnegative (fun d => distanceCandidate (D d)) ∧
    CoherenceFaithful (fun d => distanceCandidate (D d)) ∧
    ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho → AttainedCandidateSpec (D d) rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := hattain d hd rho hrho
    show 0 ≤ distanceCandidate (D d) rho
    rw [gk_cand_eq _ rho delta hdelta hmin]
    exact hD d hd _ _ hrho hdelta.1
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := hattain d hd rho hrho
    show distanceCandidate (D d) rho = 0 ↔ _
    rw [gk_cand_eq _ rho delta hdelta hmin]
    constructor
    · intro h
      rw [(hsep d hd rho delta hrho hdelta.1).1 h]
      exact hdelta
    · intro h
      apply le_antisymm
      · have := hmin rho h
        rw [(hsep d hd rho rho hrho hrho).2 rfl] at this
        exact this
      · exact hD d hd _ _ hrho hdelta.1
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := hattain d hd rho hrho
    have he := gk_cand_eq _ rho delta hdelta hmin
    refine ⟨delta, hdelta, he, fun s hs => ?_⟩
    rw [he]; exact hmin s hs

