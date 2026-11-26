-- Prove2me | solution 1 for PalomarClarkOcone.generated_clark_ocone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:01.324731+00:00
-- url     : https://prove2.me/submissions/30b66ef4-6b37-4875-b9fa-193106a7dc80

import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Definitions.Def_ClarkOconeSolution
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryPredictable_coeFn
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_naturalClarkOcone_condExp_of_generated
import Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_of_generated
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace
noncomputable section
open PalomarClarkOcone
universe u
set_option maxHeartbeats 800000
namespace PalomarClarkOcone
theorem _root_.solution
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P)
    (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    ∃ (timeDerivative : Lp (CameronMartin.Space P) 2 P →ₗᵢ[ℝ] TimeProcessL2 P)
        (itoIntegral : PredictableProcessL2 filtration P →L[ℝ] RandomL2 P),
      (∀ h : CameronMartin.Space P,
        (∀ t, ⟪h, CameronMartin.ofDual P (coordinate t)⟫_ℝ = 0) → h = 0) ∧
      (∀ t (G : RandomL2 P),
        (timeDerivative (smulLp (CameronMartin.ofDual P (coordinate t)) G) :
            ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
          fun p ↦ (Set.Ioc 0 t).indicator (1 : ℝ≥0 → ℝ) p.1 * G p.2) ∧
      (∀ U, ‖itoIntegral U‖ = ‖U‖) ∧
      (∀ U, ∫ w, itoIntegral U w ∂P = 0) ∧
      (∀ {a b : ℝ≥0} (_hab : a ≤ b)
          (Z : lpMeas ℝ ℝ (filtration a) 2 P),
        ∃ U : PredictableProcessL2 filtration P,
          (U : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
            (fun p ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 *
              (Z : W → ℝ) p.2) ∧
          (itoIntegral U : W → ℝ) =ᵐ[P]
            fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) ∧
      (∀ G : RandomL2 P, ∃ U : PredictableProcessL2 filtration P,
        G = expectationL2 G + itoIntegral U) ∧
      ∀ {F : RandomL2 P} {η : Lp (CameronMartin.Space P) 2 P},
        InGraphClosure P F η →
          ∃ G : ℝ≥0 × W → ℝ,
            StronglyMeasurable[filtration.predictable] G ∧
            (predictableProjection filtration (timeDerivative η) :
                ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
            (∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
              (fun w ↦ G (t, w)) =ᵐ[P]
                P[(fun w ↦ (timeDerivative η : ℝ≥0 × W → ℝ) (t, w)) |
                  filtration t]) ∧
            F = expectationL2 F +
              itoIntegral (predictableProjection filtration (timeDerivative η)) := by
  have hgenerated : Malliavin.IsWienerGenerated B := by
    simpa [IsWienerGenerated, processMeasurableSpace,
      Malliavin.IsWienerGenerated, Malliavin.processMeasurableSpace] using generated
  let T : Lp (CameronMartin.Space P) 2 P →ₗᵢ[ℝ] TimeProcessL2 P :=
    Malliavin.timeDerivative hB coordinate coordinate_apply hgenerated
  let I : PredictableProcessL2 filtration P →L[ℝ] RandomL2 P :=
    Malliavin.naturalItoIntegral hB hsm hnat
  refine ⟨T, I, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h horth
    apply Subtype.ext
    exact Malliavin.eq_zero_of_mem_space_of_orthogonal
      hB coordinate coordinate_apply hgenerated h.property fun t ↦ by
        rw [Malliavin.brownianLp_eq_ofDual hB coordinate coordinate_apply]
        exact horth t
  · intro t G
    change (Malliavin.timeDerivative hB coordinate coordinate_apply hgenerated
        (Malliavin.smulLp (Malliavin.CameronMartin.ofDual P (coordinate t)) G) :
          ℝ≥0 × W → ℝ) =ᵐ[Malliavin.nonnegativeLebesgueMeasure.prod P] _
    rw [Malliavin.timeDerivative_smulLp hB coordinate coordinate_apply hgenerated,
      Malliavin.wienerIntegralEquiv_symm_ofDual
        hB coordinate coordinate_apply hgenerated]
    have hi : ∀ᵐ p : ℝ≥0 × W ∂Malliavin.nonnegativeLebesgueMeasure.prod P,
        (Malliavin.intervalIndicator t : ℝ≥0 → ℝ) p.1 =
          (Set.Ioc 0 t).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := Malliavin.nonnegativeLebesgueMeasure_Ioc_ne_top 0 t) (c := (1 : ℝ)))
    filter_upwards [Malliavin.coeFn_tensor (Malliavin.intervalIndicator t) G, hi]
      with p hp hi'
    rw [hp, hi']
  · intro U
    exact Malliavin.norm_naturalItoIntegral hB hsm hnat U
  · intro U
    exact Malliavin.integral_naturalItoIntegral hB hsm hnat U
  · intro a b hab Z
    let U : PredictableProcessL2 filtration P :=
      Malliavin.elementaryPredictable filtration a b Z
    refine ⟨U, ?_, ?_⟩
    · simpa [U, nonnegativeLebesgueMeasure,
        Malliavin.nonnegativeLebesgueMeasure, Set.indicator] using
        (Malliavin.elementaryPredictable_coeFn filtration a b Z)
    · change (Malliavin.naturalItoIntegral hB hsm hnat
          (Malliavin.elementaryPredictable filtration a b Z) : W → ℝ) =ᵐ[P] _
      rw [Malliavin.naturalItoIntegral_elementaryPredictable hB hsm hnat hab Z]
      exact Malliavin.coeFn_elementaryBrownianValue hB hsm hnat hab Z
  · intro G
    obtain ⟨U, hU⟩ := Malliavin.naturalMartingaleRepresentation_of_generated
      hB coordinate coordinate_apply hgenerated hsm hnat G
    refine ⟨U, ?_⟩
    change G = Malliavin.expectationL2 G +
      Malliavin.naturalItoIntegral hB hsm hnat U
    exact hU
  · intro F η hgraph
    have hgraph' : Malliavin.InGraphClosure P F η := by
      rcases hgraph with ⟨Fk, hFk, hDk⟩
      let Fk' : ℕ → {f : W → ℝ // Malliavin.IsSmoothBounded f} := fun k ↦
        ⟨(Fk k).1, ⟨(Fk k).2.contDiff, (Fk k).2.bounded,
          (Fk k).2.bounded_fderiv⟩⟩
      refine ⟨Fk', ?_, ?_⟩
      · exact hFk
      · exact hDk
    let F' : Malliavin.D12 P := ⟨F, ⟨η, hgraph'⟩⟩
    have hderiv : Malliavin.mderivD12 P F' = η :=
      Malliavin.mderivClosure_eq P hgraph'
    obtain ⟨G, hG, hGae, hsection, hformula⟩ :=
      Malliavin.naturalClarkOcone_condExp_of_generated
        hB coordinate coordinate_apply hgenerated hsm hnat F'
    rw [hderiv] at hGae hsection hformula
    exact ⟨G, hG, hGae, hsection, hformula⟩
end PalomarClarkOcone
