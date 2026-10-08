-- Prove2me | solution 1 for WassersteinDRO.Duality.robust_lower_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:02:31.491173+00:00
-- url     : https://prove2.me/submissions/8c9ef834-c9d0-4115-8a0e-03ba2190e5ea

import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2

-- Complete local proof: Solutions.DualityReplay_SignedExpectation
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma erealExpectation_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    erealExpectation Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold erealExpectation
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]

lemma nominalRisk_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    nominalRisk Q l = (∫ x, l x ∂Q : ℝ) :=
  erealExpectation_eq_integral Q l hl

#print axioms erealExpectation_eq_integral
#print axioms nominalRisk_eq_integral
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_Empirical
set_option autoImplicit false
namespace DualityReplayCodex
open MeasureTheory
open scoped BigOperators
open WassersteinDRO.Duality

lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma empirical_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    Integrable l (empiricalDistribution X) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')

lemma empirical_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (l : Z → ℝ) :
    (∫ z, l z ∂empiricalDistribution X) = (n : ℝ)⁻¹ * ∑ i, l (X i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro i hi
    exact integrable_dirac (by simp)

lemma empirical_nominalRisk {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    nominalRisk (empiricalDistribution X) l = ((n : ℝ)⁻¹ * ∑ i, l (X i) : ℝ) := by
  rw [nominalRisk_eq_integral _ _ (empirical_integrable hn X l), empirical_integral]

#print axioms empirical_probability
#print axioms empirical_map
#print axioms empirical_lintegral
#print axioms empirical_coupling
#print axioms empirical_integrable
#print axioms empirical_integral
#print axioms empirical_nominalRisk
end DualityReplayCodex

-- Complete local proof: Solutions.Duality_EmpiricalPerturbation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DualityCodex
open WassersteinDRO.Duality

lemma empirical_supported {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (X : Fin N → E) (Ξ : Set E) (hX : ∀ i, X i ∈ Ξ) :
    empiricalDistribution X Ξᶜ = 0 := by
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply,
    hX]

lemma empirical_cost {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (X Y : Fin N → E)
    (p : ℝ) :
    (∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ p)
      ∂empiricalDistribution (fun i => (X i,Y i))) =
      ENNReal.ofReal ((∑ i, ‖X i - Y i‖ ^ p) / (N : ℝ)) := by
  rw [DualityReplayCodex.empirical_lintegral]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro i hi; exact Real.rpow_nonneg (norm_nonneg _) _)]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Finset.sum_nonneg (by intro i hi; exact Real.rpow_nonneg (norm_nonneg _) _))]
  simp [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN : (0 : ℝ) < N), mul_comm]

lemma empirical_perturbed_in_ambiguity {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {N : ℕ} (hN : 0 < N)
    (X θ : Fin N → E) (Ξ : Set E) (hθ : ∀ i, X i + θ i ∈ Ξ)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p)
    (hcost : (∑ i, ‖θ i‖ ^ p) / (N : ℝ) ≤ ε ^ p) :
    empiricalDistribution (fun i => X i + θ i) ∈
      ambiguitySet ε p Ξ (empiricalDistribution X) := by
  have hprob := DualityReplayCodex.empirical_probability hN (fun i => X i + θ i)
  have hcouple := DualityReplayCodex.empirical_coupling hN (fun i => X i + θ i) X
  refine ⟨hprob.measure_univ, empirical_supported _ Ξ hθ, ?_⟩
  unfold wassersteinDistance
  apply le_trans (ENNReal.rpow_le_rpow
    (iInf_le_of_le (empiricalDistribution (fun i => (X i + θ i, X i)))
      (iInf_le_of_le ⟨hcouple.2.1,hcouple.2.2⟩ le_rfl)) (by positivity))
  rw [empirical_cost hN]
  simp only [add_sub_cancel_left]
  apply le_trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hcost) (by positivity))
  rw [← ENNReal.ofReal_rpow_of_nonneg hε (by positivity), ← ENNReal.rpow_mul]
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  simp [hp0]

#print axioms empirical_supported
#print axioms empirical_cost
#print axioms empirical_perturbed_in_ambiguity
end DualityCodex

-- Complete local proof: Solutions.Sol_WassersteinDRO_Duality_robust_lower_bound_v2
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    (⨆ (θ : Fin N → E)
        (_ : ∀ i, ξhat i + θ i ∈ Ξ)
        (_ : (∑ i, ‖θ i‖ ^ p) / (N : ℝ) ≤ ε ^ p),
        (((∑ i, ℓ (ξhat i + θ i)) / (N : ℝ) : ℝ) : EReal))
      ≤ worstCaseRisk ε p Ξ (empiricalDistribution ξhat) ℓ := by
  apply iSup_le
  intro θ
  apply iSup_le
  intro hθ
  apply iSup_le
  intro hcost
  have hmem := DualityCodex.empirical_perturbed_in_ambiguity hN ξhat θ Ξ hθ ε p hε hp hcost
  have hrisk := DualityReplayCodex.empirical_nominalRisk hN (fun i => ξhat i + θ i) ℓ
  rw [div_eq_mul_inv, mul_comm, ← hrisk]
  exact le_iSup_of_le (empiricalDistribution (fun i => ξhat i + θ i))
    (le_iSup_of_le hmem le_rfl)

#print axioms solution
