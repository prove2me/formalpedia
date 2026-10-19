-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.distance_joint_convexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:50:14.275969+00:00
-- url     : https://prove2.me/submissions/5d9bfab6-2762-48cd-877c-474349f4d777

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

/-- PDF p.3, (7): joint convexity implies (C3), without a contractivity hypothesis. -/
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

theorem gk_cand_le {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hb : ∀ sigma, IncoherentState sigma → 0 ≤ D rho sigma) :
    distanceCandidate D rho ≤ D rho delta := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨s, hs, rfl⟩
    exact hb s hs
  · exact ⟨_, hdelta, rfl⟩

theorem gk_mix_density {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IsDensityMatrix (rho i)) :
    IsDensityMatrix (ensembleMixture p rho) := by
  refine ⟨?_, ?_⟩
  · unfold ensembleMixture
    exact Matrix.posSemidef_sum _ (fun i _ =>
      (hr i).1.smul (by exact_mod_cast hp.1 i))
  · unfold ensembleMixture
    rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, (hr _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp.2

theorem gk_mix_inc {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IncoherentState (rho i)) :
    IncoherentState (ensembleMixture p rho) := by
  refine ⟨gk_mix_density p rho hp (fun i => (hr i).1), ?_⟩
  intro i j hij
  unfold ensembleMixture
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun k _ => by simp [(hr k).2 i j hij])

theorem solution (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hconvex : DistanceJointConvex D) :
    CoherenceConvex (fun d => distanceCandidate (D d)) ∧
    ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
      Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      ∃ sigma : Fin a → CoherenceMatrix d,
        (∀ i, IncoherentState (sigma i) ∧
          distanceCandidate (D d) (rho i) = D d (rho i) (sigma i)) ∧
        distanceCandidate (D d) (ensembleMixture p rho) ≤
          D d (ensembleMixture p rho) (ensembleMixture p sigma) ∧
        D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤
          (∑ i, p i * D d (rho i) (sigma i)) ∧
        (∑ i, p i * D d (rho i) (sigma i)) =
          ∑ i, p i * distanceCandidate (D d) (rho i) := by
  have key : ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
      Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      ∃ sigma : Fin a → CoherenceMatrix d,
        (∀ i, IncoherentState (sigma i) ∧
          distanceCandidate (D d) (rho i) = D d (rho i) (sigma i)) ∧
        distanceCandidate (D d) (ensembleMixture p rho) ≤
          D d (ensembleMixture p rho) (ensembleMixture p sigma) ∧
        D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤
          (∑ i, p i * D d (rho i) (sigma i)) ∧
        (∑ i, p i * D d (rho i) (sigma i)) =
          ∑ i, p i * distanceCandidate (D d) (rho i) := by
    intro d hd a p rho hp hr
    have := fun i => hattain d hd (rho i) (hr i)
    choose sigma hs hmin using this
    have heq : ∀ i, distanceCandidate (D d) (rho i) = D d (rho i) (sigma i) :=
      fun i => gk_cand_eq _ _ _ (hs i) (hmin i)
    have hmr := gk_mix_density p rho hp hr
    refine ⟨sigma, fun i => ⟨hs i, heq i⟩, ?_, ?_, ?_⟩
    · exact gk_cand_le _ _ _ (gk_mix_inc p sigma hp hs)
        (fun s hs' => hD d hd _ _ hmr hs'.1)
    · exact hconvex d hd a p rho sigma hp hr (fun i => (hs i).1)
    · simp_rw [heq]
  refine ⟨?_, key⟩
  intro d hd a p rho hp hr
  obtain ⟨sigma, h1, h2, h3, h4⟩ := key d hd a p rho hp hr
  show distanceCandidate (D d) (ensembleMixture p rho) ≤
    ∑ i, p i * distanceCandidate (D d) (rho i)
  linarith

