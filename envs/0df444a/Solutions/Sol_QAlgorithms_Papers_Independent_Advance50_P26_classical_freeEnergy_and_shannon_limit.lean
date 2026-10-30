-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P26.classical_freeEnergy_and_shannon_limit
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:46:04.698011+00:00
-- url     : https://prove2.me/submissions/e512d521-1def-4d87-84bf-3743428dabc6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26
noncomputable section
open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Advance50.P26
open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)
open QAlgorithms.ZeroSum (classicalGibbs)
open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

theorem solution {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1)
    (T0 : ℝ) (hT0 : 0 < T0) :
    (∀ T : ℝ, 0 < T → T ≠ T0 →
      classicalFreeEnergy (referenceEnergies p T0) T =
        -(T - T0) * classicalRenyiNats p (T0 / T)) ∧
    Tendsto (fun T : ℝ => classicalRenyiNats p (T0 / T))
      (nhdsWithin T0 {T : ℝ | 0 < T ∧ T ≠ T0}) (𝓝 (shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)))) ∧
    Tendsto (fun T : ℝ => -classicalFreeEnergy (referenceEnergies p T0) T / (T - T0))
      (nhdsWithin T0 {T : ℝ | 0 < T ∧ T ≠ T0}) (𝓝 (shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)))) := by
  have hpart : ∀ T : ℝ, 0 < T →
      classicalPartition (referenceEnergies p T0) T = ∑ i, p i ^ (T0 / T) := by
    intro T hT
    unfold classicalPartition referenceEnergies
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.rpow_def_of_pos (hp i)]
    congr 1
    field_simp
  have h1 : ∀ T : ℝ, 0 < T → T ≠ T0 →
      classicalFreeEnergy (referenceEnergies p T0) T =
        -(T - T0) * classicalRenyiNats p (T0 / T) := by
    intro T hT hne
    have hq1 : T0 / T ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hT.ne'] at h
      exact hne h.symm
    unfold classicalFreeEnergy classicalRenyiNats
    rw [if_neg hq1, hpart T hT]
    have h2 : (1 - T0 / T) = (T - T0) / T := by field_simp
    have h3 : T - T0 ≠ 0 := sub_ne_zero.mpr hne
    rw [h2]
    field_simp
  -- limit of Renyi entropy
  set φ : ℝ → ℝ := fun q => Real.log (∑ i, p i ^ q) with hφ
  have hS1 : ∑ i, p i ^ (1 : ℝ) = 1 := by simpa using hnorm
  have hderS : HasDerivAt (fun q : ℝ => ∑ i, p i ^ q) (∑ i, p i * Real.log (p i)) 1 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (x := (1:ℝ))
      (fun i _ => (Real.hasStrictDerivAt_const_rpow (hp i) 1).hasDerivAt)
    simpa using this
  have hderφ : HasDerivAt φ (∑ i, p i * Real.log (p i)) 1 := by
    have := hderS.log (by rw [hS1]; norm_num)
    rw [hS1, div_one] at this
    exact this
  have hφ1 : φ 1 = 0 := by simp only [hφ]; rw [hS1, Real.log_one]
  have hslope : Tendsto (fun q : ℝ => (φ q) / (q - 1)) (nhdsWithin 1 {1}ᶜ)
      (𝓝 (∑ i, p i * Real.log (p i))) := by
    have := hasDerivAt_iff_tendsto_slope.mp hderφ
    refine this.congr (fun q => ?_)
    rw [slope_def_field, hφ1, sub_zero]
  have hshan : shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)) =
      -∑ i, p i * Real.log (p i) := by
    unfold shannonEntropyNats
    congr 1
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun i => p i * Real.log (p i)))
  have hR : Tendsto (fun q : ℝ => classicalRenyiNats p q) (nhdsWithin 1 {1}ᶜ)
      (𝓝 (shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i)))) := by
    rw [hshan]
    have := hslope.neg
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq1 : q ≠ 1 := hq
    unfold classicalRenyiNats
    rw [if_neg hq1]
    have : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
    have : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
    simp only [hφ]
    field_simp
    ring
  have hqT : Tendsto (fun T : ℝ => T0 / T) (nhdsWithin T0 {T : ℝ | 0 < T ∧ T ≠ T0})
      (nhdsWithin 1 {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun T : ℝ => T0 / T) T0 :=
        continuousAt_const.div continuousAt_id hT0.ne'
      have := hc.tendsto
      rw [div_self hT0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with T hT
      obtain ⟨hT1, hT2⟩ := hT
      intro h
      have h' : T0 / T = 1 := h
      rw [div_eq_one_iff_eq hT1.ne'] at h'
      exact hT2 h'.symm
  have h2 := hR.comp hqT
  refine ⟨h1, h2, ?_⟩
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with T hT
  obtain ⟨hT1, hT2⟩ := hT
  rw [h1 T hT1 hT2]
  have : T - T0 ≠ 0 := sub_ne_zero.mpr hT2
  simp only [Function.comp]
  field_simp
