-- Prove2me | solution 1 for WassersteinDRO.Regularization.convex_loss_p1_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T10:41:11.862198+00:00
-- url     : https://prove2.me/submissions/d6e01567-2cf7-4b8c-a0ec-9c8907d7d438

import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk_v2
import Mathlib

-- Solutions.DRO_FiniteModulus
set_option autoImplicit false
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_SignedExpectation
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_Empirical
set_option autoImplicit false
namespace DROCodex
open MeasureTheory
open scoped BigOperators
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_Diagonal
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_SignedCoupling
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_TransportUpper
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.DRO_RareMixture
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DROCodex
open WassersteinDRO.Regularization

lemma probability_mixture {Z : Type*} [MeasurableSpace Z]
    (P Q : Measure Z) (hP : IsProbabilityMeasure P) (hQ : IsProbabilityMeasure Q)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • P + ENNReal.ofReal b • Q) := by
  let := hP
  let := hQ
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, hab]
  norm_num

lemma mixture_integrable {Z : Type*} [MeasurableSpace Z]
    (P Q : Measure Z) (l : Z → ℝ) (hP : Integrable l P) (hQ : Integrable l Q)
    (a b : ℝ) : Integrable l (ENNReal.ofReal a • P + ENNReal.ofReal b • Q) :=
  (hP.smul_measure ENNReal.ofReal_ne_top).add_measure (hQ.smul_measure ENNReal.ofReal_ne_top)

lemma mixture_nominalRisk {Z : Type*} [MeasurableSpace Z]
    (P Q : Measure Z) (l : Z → ℝ) (hP : Integrable l P) (hQ : Integrable l Q)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    nominalRisk (ENNReal.ofReal a • P + ENNReal.ofReal b • Q) l =
      (a * (∫ x, l x ∂P) + b * (∫ x, l x ∂Q) : ℝ) := by
  rw [nominalRisk_eq_integral _ _ (mixture_integrable P Q l hP hQ a b),
    integral_add_measure (hP.smul_measure ENNReal.ofReal_ne_top)
      (hQ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul]

noncomputable def rareMixture {E : Type*} [MeasurableSpace E] {N : ℕ}
    (X : Fin N → E) (j : Fin N) (z : E) (w : ℝ) : Measure E :=
  ENNReal.ofReal (1 - w) • empiricalDistribution X +
    ENNReal.ofReal w • empiricalDistribution (Function.update X j z)

noncomputable def rareCoupling {E : Type*} [MeasurableSpace E] {N : ℕ}
    (X : Fin N → E) (j : Fin N) (z : E) (w : ℝ) : Measure (E × E) :=
  ENNReal.ofReal (1 - w) • empiricalDistribution (fun i => (X i, X i)) +
    ENNReal.ofReal w • empiricalDistribution (fun i => (Function.update X j z i, X i))

lemma rareMixture_probability {E : Type*} [MeasurableSpace E] {N : ℕ}
    (hN : 0 < N) (X : Fin N → E) (j : Fin N) (z : E) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : IsProbabilityMeasure (rareMixture X j z w) := by
  exact probability_mixture _ _ (empirical_probability hN _) (empirical_probability hN _)
    (1 - w) w (sub_nonneg.mpr hw1) hw (by ring)

lemma rareCoupling_marginals {E : Type*} [MeasurableSpace E] {N : ℕ}
    (X : Fin N → E) (j : Fin N) (z : E) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (rareCoupling X j z w).map Prod.fst = rareMixture X j z w ∧
    (rareCoupling X j z w).map Prod.snd = empiricalDistribution X := by
  constructor
  · unfold rareCoupling rareMixture
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      empirical_map _ Prod.fst measurable_fst, empirical_map _ Prod.fst measurable_fst]
  · unfold rareCoupling
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      empirical_map _ Prod.snd measurable_snd, empirical_map _ Prod.snd measurable_snd,
      ← add_smul, ← ENNReal.ofReal_add (sub_nonneg.mpr hw1) hw]
    simp

lemma updated_empirical_cost {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (X : Fin N → E) (j : Fin N) (z : E) :
    (∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖
      ∂empiricalDistribution (fun i => (Function.update X j z i, X i))) =
      (N : ENNReal)⁻¹ * ENNReal.ofReal ‖z - X j‖ := by
  rw [empirical_lintegral]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Function.update_of_ne hij]
  · simp

lemma rareCoupling_cost {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (X : Fin N → E) (j : Fin N) (z : E) (w : ℝ) :
    (∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂rareCoupling X j z w) =
      ENNReal.ofReal w * ((N : ENNReal)⁻¹ * ENNReal.ofReal ‖z - X j‖) := by
  unfold rareCoupling
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    updated_empirical_cost, empirical_lintegral]
  simp [smul_eq_mul]

lemma updated_empirical_loss_sum {E : Type*} {N : ℕ}
    (X : Fin N → E) (j : Fin N) (z : E) (l : E → ℝ) :
    (∑ i, l (Function.update X j z i)) = (∑ i, l (X i)) + (l z - l (X j)) := by
  have he : (fun i => l (Function.update X j z i)) =
      (fun i => l (X i) + if i = j then l z - l (X j) else 0) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  rw [he, Finset.sum_add_distrib]
  simp

lemma rareMixture_nominalRisk {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (j : Fin N) (z : E)
    (l : E → ℝ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    nominalRisk (rareMixture X j z w) l =
      ((N : ℝ)⁻¹ * ∑ i, l (X i) + w * (N : ℝ)⁻¹ * (l z - l (X j)) : ℝ) := by
  unfold rareMixture
  rw [mixture_nominalRisk _ _ l (empirical_integrable hN X l)
      (empirical_integrable hN _ l) (1 - w) w (sub_nonneg.mpr hw1) hw,
    empirical_integral, empirical_integral, updated_empirical_loss_sum]
  congr 1
  ring

#print axioms updated_empirical_loss_sum
#print axioms rareMixture_nominalRisk
#print axioms probability_mixture
#print axioms mixture_integrable
#print axioms mixture_nominalRisk
#print axioms rareMixture_probability
#print axioms rareCoupling_marginals
#print axioms updated_empirical_cost
#print axioms rareCoupling_cost
end DROCodex

-- Solutions.DRO_RareBudget
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DROCodex
open WassersteinDRO.Regularization

lemma rareCoupling_cost_ofReal {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E)
    (j : Fin N) (z : E) (w : ℝ) (hw : 0 ≤ w) :
    (∫⁻ p, ENNReal.ofReal ‖p.1 - p.2‖ ∂rareCoupling X j z w) =
      ENNReal.ofReal (w * (N : ℝ)⁻¹ * ‖z - X j‖) := by
  rw [rareCoupling_cost, ENNReal.ofReal_mul (by positivity : 0 ≤ w * (N : ℝ)⁻¹),
    ENNReal.ofReal_mul hw, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN),
    ENNReal.ofReal_natCast, mul_assoc]

lemma rareMixture_in_ambiguity {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E)
    (j : Fin N) (z : E) (w ε : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hbudget : w * (N : ℝ)⁻¹ * ‖z - X j‖ ≤ ε) :
    rareMixture X j z w ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution X) := by
  have := rareMixture_probability hN X j z w hw hw1
  refine ⟨measure_univ, by simp, ?_⟩
  apply (wasserstein_one_le_coupling _ _ (rareCoupling X j z w)
    (rareCoupling_marginals X j z w hw hw1)).trans
  rw [rareCoupling_cost_ofReal hN X j z w hw]
  exact ENNReal.ofReal_le_ofReal hbudget

lemma worstCaseRisk_ge_rareMixture {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E)
    (j : Fin N) (z : E) (l : E → ℝ) (w ε : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hbudget : w * (N : ℝ)⁻¹ * ‖z - X j‖ ≤ ε) :
    ((N : ℝ)⁻¹ * ∑ i, l (X i) + w * (N : ℝ)⁻¹ * (l z - l (X j)) : ℝ) ≤
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  rw [← rareMixture_nominalRisk hN X j z l w hw hw1]
  exact le_iSup_of_le (rareMixture X j z w)
    (le_iSup_of_le (rareMixture_in_ambiguity hN X j z w ε hw hw1 hbudget) le_rfl)

#print axioms rareCoupling_cost_ofReal
#print axioms rareMixture_in_ambiguity
#print axioms worstCaseRisk_ge_rareMixture
end DROCodex

-- Solutions.DRO_ConvexRay
set_option autoImplicit false
namespace DROCodex

lemma convex_ray_lower {E : Type*} [AddCommGroup E] [Module ℝ E]
    (l : E → ℝ) (hl : ConvexOn ℝ Set.univ l) (a b : E) (t : ℝ) (ht : 1 ≤ t) :
    l a + t * (l b - l a) ≤ l ((1 - t) • a + t • b) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
  have hinv1 : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr ht
  let z := (1 - t) • a + t • b
  have he : (1 - t⁻¹) • a + t⁻¹ • z = b := by
    dsimp [z]
    rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
    have hzero : 1 - t⁻¹ + t⁻¹ * (1 - t) = 0 := by
      field_simp [htpos.ne']
      ring
    rw [hzero, inv_mul_cancel₀ htpos.ne', zero_smul, one_smul, zero_add]
  have hc := hl.2 (Set.mem_univ a) (Set.mem_univ z) (sub_nonneg.mpr hinv1) hinv
    (by ring : 1 - t⁻¹ + t⁻¹ = 1)
  rw [he] at hc
  simp only [smul_eq_mul] at hc
  have hm : t * l b ≤ (t - 1) * l a + l z := by
    calc
      t * l b ≤ t * ((1 - t⁻¹) * l a + t⁻¹ * l z) :=
        mul_le_mul_of_nonneg_left hc htpos.le
      _ = (t - 1) * l a + l z := by field_simp [htpos.ne']
  change l a + t * (l b - l a) ≤ l z
  linarith

lemma convex_ray_distance_upper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b x : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖(1 - t) • a + t • b - x‖ ≤ ‖a - x‖ + t * ‖b - a‖ := by
  have he : (1 - t) • a + t • b - x = (a - x) + t • (b - a) := by module
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

lemma penalized_convex_ray_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E → ℝ) (hl : ConvexOn ℝ Set.univ l) (a b x : E) (γ t : ℝ)
    (hγ : 0 ≤ γ) (ht : 1 ≤ t) :
    l a - γ * ‖a - x‖ + t * (l b - l a - γ * ‖b - a‖) ≤
      l ((1 - t) • a + t • b) - γ * ‖(1 - t) • a + t • b - x‖ := by
  have hLoss := convex_ray_lower l hl a b t ht
  have hNorm := convex_ray_distance_upper a b x t ((by linarith : 0 ≤ t))
  have hScaled := mul_le_mul_of_nonneg_left hNorm hγ
  nlinarith

#print axioms convex_ray_lower
#print axioms convex_ray_distance_upper
#print axioms penalized_convex_ray_lower
end DROCodex

-- Solutions.DRO_AnchoredSlope
set_option autoImplicit false
namespace DROCodex

lemma convex_ray_distance_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b x : E) (t : ℝ) (ht : 0 ≤ t) :
    t * ‖b - a‖ - ‖a - x‖ ≤ ‖(1 - t) • a + t • b - x‖ := by
  have he : t • (b - a) = ((1 - t) • a + t • b - x) - (a - x) := by module
  have hn := norm_sub_le ((1 - t) • a + t • b - x) (a - x)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hn
  linarith

/-- A positive global uphill chord gives arbitrarily distant uphill points from any base. -/
lemma exists_distant_uphill_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E → ℝ) (hl : ConvexOn ℝ Set.univ l) (a b x : E) (k R : ℝ)
    (hk : 0 ≤ k) (hab : a ≠ b) (hchord : k * ‖b - a‖ < l b - l a) :
    ∃ z : E, R < ‖z - x‖ ∧ k * ‖z - x‖ < l z - l x := by
  have hd : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  let σ := l b - l a - k * ‖b - a‖
  have hσ : 0 < σ := sub_pos.mpr hchord
  let C := l a - l x - k * ‖a - x‖
  let t := max 1 (max ((1 - C) / σ) ((R + ‖a - x‖ + 1) / ‖b - a‖))
  have ht : 1 ≤ t := le_max_left _ _
  have htσ : (1 - C) / σ ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htd : (R + ‖a - x‖ + 1) / ‖b - a‖ ≤ t :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hσbound : 1 - C ≤ t * σ := (div_le_iff₀ hσ).mp htσ
  have hdbound : R + ‖a - x‖ + 1 ≤ t * ‖b - a‖ := (div_le_iff₀ hd).mp htd
  refine ⟨(1 - t) • a + t • b, ?_, ?_⟩
  · have hn := convex_ray_distance_lower a b x t (by linarith)
    linarith
  · have hp := penalized_convex_ray_lower l hl a b x k t hk ht
    dsimp [C, σ] at hσbound
    linarith

#print axioms convex_ray_distance_lower
#print axioms exists_distant_uphill_point
end DROCodex

-- Solutions.DRO_ModulusChord
set_option autoImplicit false
namespace DROCodex
open WassersteinDRO.Regularization

lemma exists_uphill_chord {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (k : ℝ) (hk : 0 ≤ k) (hmod : ENNReal.ofReal k < lipschitzModulus l) :
    ∃ a b : E, a ≠ b ∧ k * ‖b - a‖ < l b - l a := by
  rw [lipschitzModulus, lt_iSup_iff] at hmod
  obtain ⟨x, hx⟩ := hmod
  rw [lt_iSup_iff] at hx
  obtain ⟨y, hy⟩ := hx
  rw [lt_iSup_iff] at hy
  obtain ⟨hxy, hxySlope⟩ := hy
  have hs : k < |l x - l y| / ‖x - y‖ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hk).mp hxySlope
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hm : k * ‖x - y‖ < |l x - l y| := (lt_div_iff₀ hn).mp hs
  by_cases hsign : 0 ≤ l x - l y
  · rw [abs_of_nonneg hsign] at hm
    exact ⟨y, x, Ne.symm hxy, hm⟩
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hm
    refine ⟨x, y, hxy, ?_⟩
    rw [norm_sub_rev]
    linarith

lemma exists_distant_modulus_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E → ℝ) (hl : ConvexOn ℝ Set.univ l) (x : E) (k R : ℝ)
    (hk : 0 ≤ k) (hmod : ENNReal.ofReal k < lipschitzModulus l) :
    ∃ z : E, R < ‖z - x‖ ∧ k * ‖z - x‖ < l z - l x := by
  obtain ⟨a, b, hab, hchord⟩ := exists_uphill_chord l k hk hmod
  exact exists_distant_uphill_point l hl a b x k R hk hab hchord

#print axioms exists_uphill_chord
#print axioms exists_distant_modulus_slope
end DROCodex

-- Solutions.DRO_LowerSlope
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DROCodex
open WassersteinDRO.Regularization

lemma worstCaseRisk_gt_submodulus {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε k : ℝ) (hε : 0 < ε) (hk : 0 ≤ k)
    (hmod : ENNReal.ofReal k < lipschitzModulus l) :
    ((N : ℝ)⁻¹ * ∑ i, l (X i) + ε * k : ℝ) <
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  let j : Fin N := ⟨0, hN⟩
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨z, hz, hs⟩ := exists_distant_modulus_slope l hl (X j) k ((N : ℝ) * ε) hk hmod
  have hD : 0 < ‖z - X j‖ := lt_trans (mul_pos hNr hε) hz
  let w := (N : ℝ) * ε / ‖z - X j‖
  have hw : 0 ≤ w := (div_pos (mul_pos hNr hε) hD).le
  have hw1 : w ≤ 1 := (div_le_one hD).mpr hz.le
  have hwN : w * (N : ℝ)⁻¹ = ε / ‖z - X j‖ := by
    dsimp [w]
    field_simp [hNr.ne', hD.ne']
  have hbudget : w * (N : ℝ)⁻¹ * ‖z - X j‖ = ε := by
    rw [hwN]
    exact div_mul_cancel₀ ε hD.ne'
  have hgain : ε * k < w * (N : ℝ)⁻¹ * (l z - l (X j)) := by
    rw [hwN]
    have hm := mul_lt_mul_of_pos_left hs (div_pos hε hD)
    have he : ε / ‖z - X j‖ * (k * ‖z - X j‖) = ε * k := by
      field_simp [hNr.ne', hD.ne']
    rwa [he] at hm
  have hc := worstCaseRisk_ge_rareMixture hN X j z l w ε hw hw1 hbudget.le
  apply lt_of_lt_of_le _ hc
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

#print axioms worstCaseRisk_gt_submodulus
end DROCodex

-- Solutions.DRO_LowerLimits
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DROCodex
open WassersteinDRO.Regularization

lemma worstCaseRisk_eq_top_of_modulus_top {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 < ε)
    (hmod : lipschitzModulus l = ⊤) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  let A := (N : ℝ)⁻¹ * ∑ i, l (X i)
  let k := max 0 ((r - A) / ε)
  have hk : 0 ≤ k := le_max_left _ _
  have hkr : (r - A) / ε ≤ k := le_max_right _ _
  have hr : r ≤ A + ε * k := by
    have h := (div_le_iff₀ hε).mp hkr
    linarith
  have hm : ENNReal.ofReal k < lipschitzModulus l := by simp [hmod]
  exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hr)
    (worstCaseRisk_gt_submodulus hN X l hl ε k hε hk hm)

lemma worstCaseRisk_ge_finite_modulus {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 ≤ ε)
    (hfinite : lipschitzModulus l ≠ ⊤) :
    ((N : ℝ)⁻¹ * ∑ i, l (X i) + ε * (lipschitzModulus l).toReal : ℝ) ≤
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  have hbase := nominalRisk_le_worstCaseRisk hN X ε l
  rw [empirical_nominalRisk hN X l] at hbase
  by_cases hε0 : ε = 0
  · simpa [hε0] using hbase
  have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
  by_cases hL0 : (lipschitzModulus l).toReal = 0
  · simpa [hL0] using hbase
  have hL : 0 < (lipschitzModulus l).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hL0)
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  obtain ⟨r, hWr, hrT⟩ := EReal.exists_between_coe_real hlt
  have hAr : (N : ℝ)⁻¹ * ∑ i, l (X i) < r :=
    EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt hbase hWr)
  have hrT' := EReal.coe_lt_coe_iff.mp hrT
  let A := (N : ℝ)⁻¹ * ∑ i, l (X i)
  let q := (r - A) / ε
  have hq : 0 < q := div_pos (by exact sub_pos.mpr hAr) hεpos
  have hqL : q < (lipschitzModulus l).toReal := (div_lt_iff₀ hεpos).mpr (by linarith)
  let k := (q + (lipschitzModulus l).toReal) / 2
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hkL : k < (lipschitzModulus l).toReal := by dsimp [k]; linarith
  have hqk : q < k := by dsimp [k]; linarith
  have hmod : ENNReal.ofReal k < lipschitzModulus l := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hk).mpr hkL
  have hs := worstCaseRisk_gt_submodulus hN X l hl ε k hεpos hk hmod
  have hrk : r < A + ε * k := by
    have h := (div_lt_iff₀ hεpos).mp hqk
    linarith
  have he : (r : EReal) < worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l :=
    lt_trans (EReal.coe_lt_coe_iff.mpr hrk) hs
  exact (lt_asymm hWr he)

#print axioms worstCaseRisk_eq_top_of_modulus_top
#print axioms worstCaseRisk_ge_finite_modulus
end DROCodex

-- Solutions.DRO_LowerBound
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

lemma regularized_nominalRisk_le_worstCaseRisk {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 ≤ ε) :
    nominalRisk (empiricalDistribution X) l +
      ((ENNReal.ofReal ε * lipschitzModulus l : ENNReal) : EReal) ≤
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  by_cases hε0 : ε = 0
  · simpa [hε0] using nominalRisk_le_worstCaseRisk hN X ε l
  have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
  by_cases htop : lipschitzModulus l = ⊤
  · rw [worstCaseRisk_eq_top_of_modulus_top hN X l hl ε hεpos htop]
    exact le_top
  have hpfinite : ENNReal.ofReal ε * lipschitzModulus l ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
  rw [empirical_nominalRisk hN X l, ← EReal.coe_ennreal_toReal hpfinite,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, ← EReal.coe_add]
  exact worstCaseRisk_ge_finite_modulus hN X l hl ε hε htop

lemma convex_loss_identity_of_modulus_top {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 < ε)
    (htop : lipschitzModulus l = ⊤) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l =
      nominalRisk (empiricalDistribution X) l +
        ((ENNReal.ofReal ε * lipschitzModulus l : ENNReal) : EReal) := by
  rw [worstCaseRisk_eq_top_of_modulus_top hN X l hl ε hε htop,
    empirical_nominalRisk hN X l, htop]
  rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hε)),
    EReal.coe_ennreal_top, EReal.coe_add_top]

#print axioms regularized_nominalRisk_le_worstCaseRisk
#print axioms convex_loss_identity_of_modulus_top
end DROCodex

-- Solutions.DRO_FiniteIdentity
set_option autoImplicit false
open MeasureTheory
namespace DROCodex
open WassersteinDRO.Regularization

lemma worstCaseRisk_le_finite_modulus {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hfinite : lipschitzModulus l ≠ ⊤) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l ≤
      nominalRisk (empiricalDistribution X) l +
        ((ENNReal.ofReal ε * lipschitzModulus l : ENNReal) : EReal) := by
  have hl : Measurable l := (finite_modulus_lipschitz l hfinite).continuous.measurable
  have hp := empirical_integrable hN X l
  have hpen : ENNReal.ofReal ε * lipschitzModulus l ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  unfold worstCaseRisk
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  obtain ⟨hQi, hu⟩ := integrable_and_integral_upper_of_wasserstein_budget Q
    (empiricalDistribution X) l (lipschitzModulus l).toReal ε hl ENNReal.toReal_nonneg
    (abs_sub_le_modulus_mul_dist l hfinite) hp hε hQ.2.2
  rw [nominalRisk_eq_integral Q l hQi, nominalRisk_eq_integral _ l hp,
    ← EReal.coe_ennreal_toReal hpen, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε,
    ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

lemma convex_loss_identity_of_modulus_finite {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 ≤ ε)
    (hfinite : lipschitzModulus l ≠ ⊤) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l =
      nominalRisk (empiricalDistribution X) l +
        ((ENNReal.ofReal ε * lipschitzModulus l : ENNReal) : EReal) := by
  exact le_antisymm (worstCaseRisk_le_finite_modulus hN X l ε hε hfinite)
    (regularized_nominalRisk_le_worstCaseRisk hN X l hl ε hε)

lemma convex_loss_identity_of_radius_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (X : Fin N → E) (l : E → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (ε : ℝ) (hε : 0 < ε) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l =
      nominalRisk (empiricalDistribution X) l +
        ((ENNReal.ofReal ε * lipschitzModulus l : ENNReal) : EReal) := by
  by_cases htop : lipschitzModulus l = ⊤
  · exact convex_loss_identity_of_modulus_top hN X l hl ε hε htop
  · exact convex_loss_identity_of_modulus_finite hN X l hl ε hε.le htop

#print axioms worstCaseRisk_le_finite_modulus
#print axioms convex_loss_identity_of_modulus_finite
#print axioms convex_loss_identity_of_radius_positive
end DROCodex

-- Solutions.DRO_ZeroDistance
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace DROCodex
open WassersteinDRO.Regularization

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
end DROCodex

-- Solutions.Sol_WassersteinDRO_Regularization_convex_loss_p1_v2
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Regularization

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution ξhat) ℓ =
      nominalRisk (empiricalDistribution ξhat) ℓ +
        ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by
  have := hℓ
  by_cases hzero : ε = 0
  · subst ε
    simpa using DROCodex.zero_radius_worstCaseRisk_eq hN ξhat ℓ
  · exact DROCodex.convex_loss_identity_of_radius_positive hN ξhat ℓ hconv ε
      (lt_of_le_of_ne hε (Ne.symm hzero))

#print axioms solution
