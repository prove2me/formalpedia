-- Prove2me | solution 1 for QuantumMC.MeanEst.lemma_4_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:28:05.81014+00:00
-- url     : https://prove2.me/submissions/5e884a99-b04e-4e9a-bdfb-c8d137dd9c15

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false

open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 k,
        Real.sqrt ((2 : ℝ) ^ ℓ) *
          Real.sqrt (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ≤
      Real.sqrt (k : ℝ) *
        Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ *
          (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ∧
    Real.sqrt (k : ℝ) *
        Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ *
          (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ≤
      Real.sqrt (2 * (k : ℝ)) * l2norm P X := by
  let T : ℕ → Ω → ℝ := fun ℓ => truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X
  let E : ℕ → ℝ := fun ℓ => ∫ ω, T ℓ ω ∂P
  let S : ℝ := ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * E ℓ
  have hTdef : ∀ ℓ ω, T ℓ ω = truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω :=
    fun _ _ => rfl
  have hEdef : ∀ ℓ, E ℓ = ∫ ω, T ℓ ω ∂P := fun _ => rfl
  have hSdef : S = ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * E ℓ := rfl
  show (∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (E ℓ)) ≤
      Real.sqrt (k : ℝ) * Real.sqrt S ∧
    Real.sqrt (k : ℝ) * Real.sqrt S ≤ Real.sqrt (2 * (k : ℝ)) * l2norm P X
  have hTnn : ∀ ℓ ω, 0 ≤ T ℓ ω := by
    intro ℓ ω
    rw [hTdef ℓ ω]
    simp only [truncIco]; split
    · exact hpos ω
    · exact le_refl 0
  have hEnn : ∀ ℓ, 0 ≤ E ℓ := by
    intro ℓ
    rw [hEdef ℓ]
    exact integral_nonneg (fun ω => hTnn ℓ ω)
  have haesm : ∀ c d : ℝ, AEStronglyMeasurable (truncIco c d X) P := by
    intro c d
    have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
    refine (show AEMeasurable (truncIco c d X) P from
      ⟨truncIco c d (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncIco
      exact Measurable.ite
        ((measurableSet_le measurable_const hXa.measurable_mk).inter
          (measurableSet_lt hXa.measurable_mk measurable_const))
        hXa.measurable_mk measurable_const
    · filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncIco, hω]
  have hTint : ∀ ℓ, Integrable (fun ω => (2 : ℝ) ^ ℓ * T ℓ ω) P := by
    intro ℓ
    have hbd : ∀ ω, (2 : ℝ) ^ ℓ * T ℓ ω ≤ 2 * X ω ^ 2 := by
      intro ω
      rw [hTdef ℓ ω]
      simp only [truncIco]
      by_cases h : (2 : ℝ) ^ (ℓ - 1) ≤ X ω ∧ X ω < (2 : ℝ) ^ ℓ
      · rw [if_pos h]
        have hℓ1 : 1 ≤ ℓ := by
          by_contra hc
          have h0 : ℓ = 0 := by omega
          subst h0
          norm_num at h
          linarith [h.1, h.2]
        have hjp : (2 : ℝ) ^ ℓ = 2 * (2 : ℝ) ^ (ℓ - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hℓ1]
          rw [pow_succ]; ring
        have hxnn : 0 ≤ X ω := le_trans (by positivity) h.1
        calc (2 : ℝ) ^ ℓ * X ω = (2 * (2 : ℝ) ^ (ℓ - 1)) * X ω := by rw [hjp]
          _ ≤ (2 * X ω) * X ω := by
              apply mul_le_mul_of_nonneg_right _ hxnn
              linarith
          _ = 2 * X ω ^ 2 := by ring
      · rw [if_neg h, mul_zero]
        positivity
    refine Integrable.mono' (hX.integrable_sq.const_mul 2) ?_
      (Eventually.of_forall (fun ω => ?_))
    · have hfun : (fun ω => (2 : ℝ) ^ ℓ * T ℓ ω) =
          fun ω => (2 : ℝ) ^ ℓ * truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω := by
        funext ω; rw [hTdef ℓ ω]
      rw [hfun]
      exact (haesm _ _).const_mul _
    · rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hTnn ℓ ω))]
      exact hbd ω
  have hpt : ∀ ω, ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω ≤ 2 * X ω ^ 2 := by
    intro ω
    by_cases hex : ∃ j ∈ Finset.Icc 1 k, (2 : ℝ) ^ (j - 1) ≤ X ω ∧ X ω < (2 : ℝ) ^ j
    · obtain ⟨j, hjmem, hjl, hju⟩ := hex
      have hsingle : (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω) = (2 : ℝ) ^ j * T j ω := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro i himem hij
          have hTi : T i ω = 0 := by
            rw [hTdef i ω]
            simp only [truncIco]
            rw [if_neg]
            rintro ⟨hil, hiu⟩
            have huniq : i = j := by
              rcases lt_trichotomy i j with hlt | heq | hgt
              · exfalso
                have hile : i ≤ j - 1 := by omega
                have hp : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (j - 1) :=
                  pow_le_pow_right₀ (by norm_num) hile
                linarith [hiu, hp, hjl]
              · exact heq
              · exfalso
                have hile : j ≤ i - 1 := by omega
                have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (i - 1) :=
                  pow_le_pow_right₀ (by norm_num) hile
                linarith [hju, hp, hil]
            exact hij huniq
          rw [hTi, mul_zero]
        · intro hjnot
          exact absurd hjmem hjnot
      rw [hsingle]
      have hTj : T j ω = X ω := by
        rw [hTdef j ω]
        simp only [truncIco]
        rw [if_pos ⟨hjl, hju⟩]
      rw [hTj]
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
      have hjp : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj1]
        rw [pow_succ]; ring
      have hxnn : 0 ≤ X ω := le_trans (by positivity) hjl
      calc (2 : ℝ) ^ j * X ω = (2 * (2 : ℝ) ^ (j - 1)) * X ω := by rw [hjp]
        _ ≤ (2 * X ω) * X ω := by
            apply mul_le_mul_of_nonneg_right _ hxnn
            linarith
        _ = 2 * X ω ^ 2 := by ring
    · have hzero : ∀ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω = 0 := by
        intro ℓ hℓ
        have hTz : T ℓ ω = 0 := by
          rw [hTdef ℓ ω]
          simp only [truncIco]
          rw [if_neg]
          rintro ⟨hl, hu⟩
          exact hex ⟨ℓ, hℓ, hl, hu⟩
        rw [hTz, mul_zero]
      rw [Finset.sum_eq_zero hzero]
      positivity
  have hSeq : S = ∫ ω, ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω ∂P := by
    rw [hSdef]
    rw [integral_finsetSum _ (fun ℓ _ => hTint ℓ)]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [hEdef ℓ, integral_const_mul]
  have hl2 : l2norm P X ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
    rw [l2norm, Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (X ω)))]
  have hl2nn : 0 ≤ l2norm P X := Real.sqrt_nonneg _
  constructor
  · have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.Icc 1 k)
      (f := fun _ : ℕ => (1 : ℝ)) (g := fun ℓ => (2 : ℝ) ^ ℓ * E ℓ)
      (fun _ => zero_le_one) (fun ℓ => mul_nonneg (by positivity) (hEnn ℓ))
    have hcard : (∑ ℓ ∈ Finset.Icc 1 k, (1 : ℝ)) = (k : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp
    have hstep : (∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (E ℓ))
        = ∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((1 : ℝ)) * Real.sqrt ((2 : ℝ) ^ ℓ * E ℓ) := by
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Real.sqrt_one, one_mul, Real.sqrt_mul (by positivity)]
    rw [hstep]
    calc (∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((1 : ℝ)) * Real.sqrt ((2 : ℝ) ^ ℓ * E ℓ))
        ≤ Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (1 : ℝ)) *
            Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * E ℓ) := hcs
      _ = Real.sqrt (k : ℝ) * Real.sqrt S := by rw [hcard, hSdef]
  · have hS_le : S ≤ 2 * l2norm P X ^ 2 := by
      rw [hSeq]
      have h2X2 : Integrable (fun ω => 2 * X ω ^ 2) P := hX.integrable_sq.const_mul 2
      have hsum_int : Integrable (fun ω => ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω) P :=
        integrable_finsetSum _ (fun ℓ _ => hTint ℓ)
      calc ∫ ω, ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * T ℓ ω ∂P
          ≤ ∫ ω, 2 * X ω ^ 2 ∂P :=
            integral_mono hsum_int h2X2 hpt
        _ = 2 * ∫ ω, X ω ^ 2 ∂P := integral_const_mul _ _
        _ = 2 * l2norm P X ^ 2 := by rw [hl2]
    calc Real.sqrt (k : ℝ) * Real.sqrt S
        ≤ Real.sqrt (k : ℝ) * Real.sqrt (2 * l2norm P X ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS_le) (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * (k : ℝ)) * l2norm P X := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hl2nn,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (k : ℝ)]
          ring
