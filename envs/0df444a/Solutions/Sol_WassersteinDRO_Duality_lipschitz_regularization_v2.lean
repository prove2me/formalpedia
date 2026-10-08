-- Prove2me | solution 1 for WassersteinDRO.Duality.lipschitz_regularization_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:09:41.843545+00:00
-- url     : https://prove2.me/submissions/a44a497a-b065-4dad-9cfb-3e0463a0fab4

import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
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

-- Complete local proof: Solutions.DualityReplay_Diagonal
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma wasserstein_one_eq {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) :
    wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π := by
  simp [wassersteinDistance]

lemma wasserstein_one_le_coupling {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) (π : Measure (E × E))
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = P) :
    wassersteinDistance 1 Q P ≤ ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π := by
  rw [wasserstein_one_eq]
  exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

lemma empirical_wasserstein_self {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E) :
    wassersteinDistance 1 (empiricalDistribution X) (empiricalDistribution X) = 0 := by
  apply le_antisymm _ bot_le
  have hc := empirical_coupling hN X X
  apply (wasserstein_one_le_coupling _ _ _ ⟨hc.2.1, hc.2.2⟩).trans
  rw [empirical_lintegral]
  simp

lemma empirical_in_ambiguity {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E) (ε : ℝ) :
    empiricalDistribution X ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution X) := by
  have := empirical_probability hN X
  exact ⟨measure_univ, by simp, by rw [empirical_wasserstein_self hN X]; exact bot_le⟩

lemma nominalRisk_le_worstCaseRisk {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] {N : ℕ}
    (hN : 0 < N) (X : Fin N → E) (ε : ℝ) (l : E → ℝ) :
    nominalRisk (empiricalDistribution X) l ≤
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  exact le_iSup_of_le (empiricalDistribution X)
    (le_iSup_of_le (empirical_in_ambiguity hN X ε) le_rfl)

#print axioms wasserstein_one_eq
#print axioms wasserstein_one_le_coupling
#print axioms empirical_wasserstein_self
#print axioms empirical_in_ambiguity
#print axioms nominalRisk_le_worstCaseRisk
end DualityReplayCodex

-- Complete local proof: Solutions.Duality_TransportExponent
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma coupling_cost_one_le_power_root {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (π : Measure (E × E)) [IsProbabilityMeasure π] (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ z : E × E, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ≤
      (∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1/p) := by
  have hf : AEStronglyMeasurable (fun z : E × E => z.1 - z.2) π :=
    (measurable_fst.sub measurable_snd).aestronglyMeasurable
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le zero_lt_one hp π hf
  simpa only [eLpNorm', ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
    (by linarith : 0 ≤ p), ENNReal.rpow_one, div_one] using h

lemma ennreal_rpow_iInf {I : Sort*} (f : I → ENNReal) (r : ℝ) (hr : 0 < r) :
    (⨅ i, f i) ^ r = ⨅ i, (f i) ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iInf f

lemma wasserstein_one_le_power {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) [IsProbabilityMeasure P] (p : ℝ) (hp : 1 ≤ p) :
    wassersteinDistance 1 Q P ≤ wassersteinDistance p Q P := by
  conv_rhs => unfold wassersteinDistance
  rw [ennreal_rpow_iInf _ _ (by positivity)]
  apply le_iInf
  intro π
  rw [ennreal_rpow_iInf _ _ (by positivity)]
  apply le_iInf
  intro hπ
  have hmass : π Set.univ = 1 := by
    have := congrArg (fun μ : Measure E => μ Set.univ) hπ.2
    simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using this
  have : IsProbabilityMeasure π := ⟨hmass⟩
  exact (DualityReplayCodex.wasserstein_one_le_coupling Q P π hπ).trans
    (coupling_cost_one_le_power_root π p hp)

#print axioms ennreal_rpow_iInf
#print axioms coupling_cost_one_le_power_root
#print axioms wasserstein_one_le_power
end DualityCodex

-- Complete local proof: Solutions.DualityReplay_FiniteModulus
set_option autoImplicit false
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma abs_sub_le_modulus_mul_dist {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hfinite : lipschitzModulus l ≠ ⊤) (x y : E) :
    |l x - l y| ≤ (lipschitzModulus l).toReal * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    simp
  have hm : ENNReal.ofReal (|l x - l y| / ‖x - y‖) ≤ lipschitzModulus l :=
    le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [← ENNReal.ofReal_toReal hfinite] at hm
  have hr : |l x - l y| / ‖x - y‖ ≤ (lipschitzModulus l).toReal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hm
  exact (div_le_iff₀ hn).mp hr

lemma modulus_zero_constant {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hzero : lipschitzModulus l = 0) (x y : E) : l x = l y := by
  have hf : lipschitzModulus l ≠ ⊤ := by simp [hzero]
  have h := abs_sub_le_modulus_mul_dist l hf x y
  simp only [hzero, ENNReal.toReal_zero, zero_mul, abs_nonpos_iff] at h
  exact sub_eq_zero.mp h

#print axioms abs_sub_le_modulus_mul_dist
#print axioms modulus_zero_constant
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_SignedCoupling
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma finite_modulus_lipschitz {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hfinite : lipschitzModulus l ≠ ⊤) :
    LipschitzWith ⟨(lipschitzModulus l).toReal, ENNReal.toReal_nonneg⟩ l := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change |l x - l y| ≤ (lipschitzModulus l).toReal * ‖x - y‖
  exact abs_sub_le_modulus_mul_dist l hfinite x y

lemma signed_coupling_upper {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (π : Measure (E × E)) (l : E → ℝ) (L : ℝ)
    (hl : Measurable l) (_hL : 0 ≤ L)
    (hbound : ∀ x y, |l x - l y| ≤ L * ‖x - y‖)
    (hP : Integrable l P) (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = P)
    (hcost : (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ≠ ⊤) :
    Integrable l Q ∧ (∫ x, l x ∂Q) ≤
      (∫ x, l x ∂P) + L * (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π).toReal := by
  have hm : Measurable (fun z : E × E => ‖z.1 - z.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hi : Integrable (fun z : E × E => ‖z.1 - z.2‖) π :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => norm_nonneg (z.1 - z.2))).mp hcost
  have hPs : Integrable l (π.map Prod.snd) := by rwa [hπ.2]
  have hs : Integrable (fun z : E × E => l z.2) π := hPs.comp_measurable measurable_snd
  have hb : Integrable (fun z : E × E => ‖l z.2‖ + L * ‖z.1 - z.2‖) π :=
    hs.norm.add (hi.const_mul L)
  have hf : Integrable (fun z : E × E => l z.1) π := by
    apply hb.mono' (hl.comp measurable_fst).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    have h := hbound z.1 z.2
    have ha := abs_add_le (l z.1 - l z.2) (l z.2)
    simp only [sub_add_cancel] at ha
    simp only [Real.norm_eq_abs, Function.comp_apply]
    linarith
  have hQ : Integrable l Q := by
    rw [← hπ.1]
    exact (integrable_map_measure hl.aestronglyMeasurable measurable_fst.aemeasurable).mpr hf
  refine ⟨hQ, ?_⟩
  have hfst : (∫ x, l x ∂Q) = ∫ z, l z.1 ∂π := by
    rw [← hπ.1]
    exact integral_map_of_stronglyMeasurable measurable_fst hl.stronglyMeasurable
  have hsnd : (∫ x, l x ∂P) = ∫ z, l z.2 ∂π := by
    rw [← hπ.2]
    exact integral_map_of_stronglyMeasurable measurable_snd hl.stronglyMeasurable
  rw [hfst, hsnd]
  calc
    (∫ z, l z.1 ∂π) ≤ ∫ z, l z.2 + L * ‖z.1 - z.2‖ ∂π := by
      apply integral_mono hf (hs.add (hi.const_mul L))
      intro z
      simp only [Pi.add_apply]
      have h := (le_abs_self (l z.1 - l z.2)).trans (hbound z.1 z.2)
      linarith
    _ = (∫ z, l z.2 ∂π) + L * (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π).toReal := by
      rw [integral_add hs (hi.const_mul L), integral_const_mul,
        integral_eq_lintegral_of_nonneg_ae (f := fun z : E × E => ‖z.1 - z.2‖)
          (Filter.Eventually.of_forall fun z => norm_nonneg (z.1 - z.2)) hm.aestronglyMeasurable]

#print axioms finite_modulus_lipschitz
#print axioms signed_coupling_upper
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_TransportUpper
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma exists_coupling_lt_budget_add {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (hbudget : wassersteinDistance 1 Q P ≤ ENNReal.ofReal ε) :
    ∃ π : Measure (E × E), (π.map Prod.fst = Q ∧ π.map Prod.snd = P) ∧
      (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) < ENNReal.ofReal (ε + η) := by
  have hlt : wassersteinDistance 1 Q P < ENNReal.ofReal (ε + η) :=
    lt_of_le_of_lt hbudget ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε).mpr (by linarith))
  rw [wasserstein_one_eq, iInf_lt_iff] at hlt
  obtain ⟨π, hπ⟩ := hlt
  rw [iInf_lt_iff] at hπ
  obtain ⟨hmap, hcost⟩ := hπ
  exact ⟨π, hmap, hcost⟩

lemma integrable_and_integral_upper_of_wasserstein_budget {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (l : E → ℝ) (L ε : ℝ) (hl : Measurable l) (hL : 0 ≤ L)
    (hbound : ∀ x y, |l x - l y| ≤ L * ‖x - y‖) (hP : Integrable l P) (hε : 0 ≤ ε)
    (hbudget : wassersteinDistance 1 Q P ≤ ENNReal.ofReal ε) :
    Integrable l Q ∧ (∫ x, l x ∂Q) ≤ (∫ x, l x ∂P) + L * ε := by
  obtain ⟨π, hπ, hc⟩ := exists_coupling_lt_budget_add Q P ε 1 hε zero_lt_one hbudget
  have hcfin : (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ≠ ⊤ :=
    (lt_of_lt_of_le hc le_top).ne
  have hQ := (signed_coupling_upper Q P π l L hl hL hbound hP hπ hcfin).1
  refine ⟨hQ, ?_⟩
  apply le_of_forall_pos_le_add
  intro ζ hζ
  let η := ζ / (L + 1)
  have hL1 : 0 < L + 1 := by linarith
  have hη : 0 < η := div_pos hζ hL1
  obtain ⟨ρ, hρ, hρc⟩ := exists_coupling_lt_budget_add Q P ε η hε hη hbudget
  have hρfin : (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂ρ) ≠ ⊤ :=
    (lt_of_lt_of_le hρc le_top).ne
  have hr := (signed_coupling_upper Q P ρ l L hl hL hbound hP hρ hρfin).2
  have hcost := ENNReal.toReal_lt_of_lt_ofReal hρc
  have he : η * (L + 1) = ζ := div_mul_cancel₀ ζ hL1.ne'
  have heL : L * η ≤ ζ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hcost.le hL
  nlinarith

#print axioms exists_coupling_lt_budget_add
#print axioms integrable_and_integral_upper_of_wasserstein_budget
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_ZeroDistance
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma zero_budget_integral_eq_of_lipschitz {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (l : E → ℝ) (K : NNReal) (hl : LipschitzWith K l)
    (hP : Integrable l P) (hzero : wassersteinDistance 1 Q P ≤ 0) :
    (∫ x, l x ∂Q) = ∫ x, l x ∂P := by
  have hbudget : wassersteinDistance 1 Q P ≤ ENNReal.ofReal 0 := by simpa using hzero
  have hb : ∀ x y, |l x - l y| ≤ (K : ℝ) * ‖x - y‖ := by
    intro x y
    simpa [dist_eq_norm, Real.norm_eq_abs] using hl.dist_le_mul x y
  have hbn : ∀ x y, |(-l x) - (-l y)| ≤ (K : ℝ) * ‖x - y‖ := by
    intro x y
    simpa only [neg_sub_neg, abs_sub_comm] using hb x y
  have hln : Measurable (fun x => -l x) := hl.continuous.measurable.neg
  have hu := (integrable_and_integral_upper_of_wasserstein_budget Q P l K 0
    hl.continuous.measurable K.coe_nonneg hb hP le_rfl hbudget).2
  have hn := (integrable_and_integral_upper_of_wasserstein_budget Q P (fun x => -l x) K 0
    hln K.coe_nonneg hbn hP.neg le_rfl hbudget).2
  simp only [mul_zero, add_zero, integral_neg] at hu hn
  exact le_antisymm hu (by linarith)

lemma zero_budget_measure_eq {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (hzero : wassersteinDistance 1 Q P ≤ 0) : Q = P := by
  have hclosed : ∀ F : Set E, IsClosed F → Q F = P F := by
    intro F hF
    have heq : ∀ n : ℕ,
        (∫⁻ x, (thickenedIndicator (δ := 1 / (n + 1)) Nat.one_div_pos_of_nat F x : ENNReal) ∂Q) =
        ∫⁻ x, (thickenedIndicator (δ := 1 / (n + 1)) Nat.one_div_pos_of_nat F x : ENNReal) ∂P := by
      intro n
      let δ := (1 : ℝ) / (n + 1)
      have hδ : 0 < δ := Nat.one_div_pos_of_nat
      let f := thickenedIndicator hδ F
      have hl : LipschitzWith δ.toNNReal⁻¹ (fun x => (f x : ℝ)) := by
        have h := NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator hδ F)
        change LipschitzWith δ.toNNReal⁻¹ (NNReal.toReal ∘ ⇑f)
        simpa only [one_mul] using h
      have hiP : Integrable (fun x => (f x : ℝ)) P := integrable_thickenedIndicator F hδ
      have hiQ : Integrable (fun x => (f x : ℝ)) Q := integrable_thickenedIndicator F hδ
      have he := zero_budget_integral_eq_of_lipschitz Q P (fun x => (f x : ℝ)) _ hl hiP hzero
      rw [lintegral_coe_eq_integral _ hiQ, lintegral_coe_eq_integral _ hiP]
      exact congrArg ENNReal.ofReal he
    have hQ := tendsto_lintegral_thickenedIndicator_of_isClosed Q hF
      (fun _ => Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat
    have hP := tendsto_lintegral_thickenedIndicator_of_isClosed P hF
      (fun _ => Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [heq] at hQ
    exact tendsto_nhds_unique hQ hP
  apply ext_of_generate_finite {F : Set E | IsClosed F} ?_ isPiSystem_isClosed
  · exact hclosed
  · exact hclosed Set.univ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := E), borel_eq_generateFrom_isClosed]

lemma zero_radius_worstCaseRisk_eq {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ) :
    worstCaseRisk 0 1 Set.univ (empiricalDistribution X) l =
      nominalRisk (empiricalDistribution X) l := by
  apply le_antisymm _ (nominalRisk_le_worstCaseRisk hN X 0 l)
  unfold worstCaseRisk
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  have : IsProbabilityMeasure Q := ⟨hQ.1⟩
  have := empirical_probability hN X
  have hzero : wassersteinDistance 1 Q (empiricalDistribution X) ≤ 0 := by
    simpa using hQ.2.2
  rw [zero_budget_measure_eq Q (empiricalDistribution X) hzero]

#print axioms zero_budget_integral_eq_of_lipschitz
#print axioms zero_budget_measure_eq
#print axioms zero_radius_worstCaseRisk_eq
end DualityReplayCodex

-- Complete local proof: Solutions.Sol_WassersteinDRO_Duality_lipschitz_regularization_v2
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN]
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ) (hℓ : Integrable ℓ PN) :
    worstCaseRisk ε p Ξ PN ℓ ≤
      nominalRisk PN ℓ + ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal)  := by
  by_cases hzero : ε = 0
  · subst ε
    simp only [ENNReal.ofReal_zero, zero_mul, EReal.coe_ennreal_zero, add_zero]
    unfold worstCaseRisk
    apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    have : IsProbabilityMeasure Q := ⟨hQ.1⟩
    have hw : wassersteinDistance 1 Q PN ≤ 0 :=
      (DualityCodex.wasserstein_one_le_power Q PN p hp).trans (by simpa using hQ.2.2)
    rw [DualityReplayCodex.zero_budget_measure_eq Q PN hw]
  · by_cases htop : lipschitzModulus ℓ = ⊤
    · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hzero)
      have hεenn : ENNReal.ofReal ε ≠ 0 := by
        exact (ENNReal.ofReal_pos.mpr hεpos).ne'
      rw [htop, ENNReal.mul_top hεenn,
        DualityReplayCodex.nominalRisk_eq_integral PN ℓ hℓ, EReal.coe_ennreal_top,
        EReal.coe_add_top]
      exact le_top
    · have hl := (DualityReplayCodex.finite_modulus_lipschitz ℓ htop).continuous.measurable
      have hpen : ENNReal.ofReal ε * lipschitzModulus ℓ ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
      unfold worstCaseRisk
      apply iSup_le
      intro Q
      apply iSup_le
      intro hQ
      have : IsProbabilityMeasure Q := ⟨hQ.1⟩
      have hw := (DualityCodex.wasserstein_one_le_power Q PN p hp).trans hQ.2.2
      obtain ⟨hQi, hu⟩ := DualityReplayCodex.integrable_and_integral_upper_of_wasserstein_budget
        Q PN ℓ (lipschitzModulus ℓ).toReal ε hl ENNReal.toReal_nonneg
        (DualityReplayCodex.abs_sub_le_modulus_mul_dist ℓ htop) hℓ hε hw
      rw [DualityReplayCodex.nominalRisk_eq_integral Q ℓ hQi,
        DualityReplayCodex.nominalRisk_eq_integral PN ℓ hℓ,
        ← EReal.coe_ennreal_toReal hpen, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε,
        ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)

#print axioms solution
