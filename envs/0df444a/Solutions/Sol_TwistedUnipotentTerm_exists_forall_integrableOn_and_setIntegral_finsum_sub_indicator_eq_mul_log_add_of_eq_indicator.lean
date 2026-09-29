-- Prove2me | solution 1 for TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ba748b95-9e4b-51f0-8261-0f1ddbaffd44

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
import Theorems.Thm_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_integrable_zetaIntegrand
import Theorems.Thm_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace TwistedUnipotentTerm

section LogShellMass

open scoped Pointwise

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal NNReal

namespace ShellMass

variable (L : Type) [Field L] [NumberField L]

private noncomputable abbrev principalRange : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
  (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range

private def shell (a b : ℝ) : Set (AdeleRing (𝓞 L) L)ˣ := {z | ideleNorm L z ∈ Set.Ioc a b}

private noncomputable def logNorm (z : (AdeleRing (𝓞 L) L)ˣ) : ℝ := Real.log (ideleNorm L z)

private theorem countable_principalRange : Countable (principalRange L) := by
  haveI : Countable L := Countable.of_equiv _ (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.symm
  haveI : Countable Lˣ := Units.val_injective.countable
  exact (Set.countable_range _).to_subtype

variable {L}

private theorem preimage_shell_eq (hn : ∀ γ : principalRange L, ideleNorm L (γ : (AdeleRing (𝓞 L) L)ˣ) = 1)
    (γ : principalRange L) (a b : ℝ) : (fun z => γ • z) ⁻¹' shell L a b = shell L a b := by
  ext z
  show ideleNorm L ((γ : (AdeleRing (𝓞 L) L)ˣ) * z) ∈ Set.Ioc a b ↔ ideleNorm L z ∈ Set.Ioc a b
  rw [ideleNorm_mul, hn γ, one_mul]

private theorem preimage_logNorm_Ioc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    logNorm L ⁻¹' Set.Ioc (Real.log a) (Real.log b) = shell L a b := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Ioc, logNorm, shell, Set.mem_setOf_eq]
  rw [Real.log_lt_log_iff ha (ideleNorm_pos z), Real.log_le_log_iff (ideleNorm_pos z) (ha.trans hab)]

variable (L)

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]

private theorem measurable_logNorm : Measurable (logNorm L) :=
  Real.measurable_log.comp (continuous_ideleNorm L).measurable

private theorem measurableSet_shell (a b : ℝ) : MeasurableSet (shell L a b) :=
  (continuous_ideleNorm L).measurable measurableSet_Ioc

variable {L}

private theorem exists_forall_measure_inter_shell_eq (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsHaarMeasure]
    (hn : ∀ γ : principalRange L, ideleNorm L (γ : (AdeleRing (𝓞 L) L)ˣ) = 1) :
    ∃ c : ℝ≥0, ∀ D : Set (AdeleRing (𝓞 L) L)ˣ, IsFundamentalDomain (principalRange L) D ν →
      ∀ a b : ℝ, 0 < a → a < b →
        ν (D ∩ shell L a b) = (c : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a) := by
  haveI := countable_principalRange L
  haveI : MeasurableConstSMul (principalRange L) (AdeleRing (𝓞 L) L)ˣ :=
    ⟨fun γ => (continuous_const_mul (γ : (AdeleRing (𝓞 L) L)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure (principalRange L) (AdeleRing (𝓞 L) L)ˣ ν :=
    ⟨fun γ s hs => measure_preimage_mul ν (γ : (AdeleRing (𝓞 L) L)ˣ) s⟩
  haveI : MeasurableConstSMul (AdeleRing (𝓞 L) L)ˣ (AdeleRing (𝓞 L) L)ˣ :=
    ⟨fun g => (continuous_const_mul g).measurable⟩
  haveI : SMulInvariantMeasure (AdeleRing (𝓞 L) L)ˣ (AdeleRing (𝓞 L) L)ˣ ν :=
    ⟨fun g s hs => measure_preimage_mul ν g s⟩
  haveI : SMulCommClass (AdeleRing (𝓞 L) L)ˣ (principalRange L) (AdeleRing (𝓞 L) L)ˣ :=
    ⟨fun g γ x => mul_left_comm g (γ : (AdeleRing (𝓞 L) L)ˣ) x⟩

  obtain ⟨D₀, hD₀m, hD₀F, hint⟩ :=
    exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow L ν
  have hD₀ : IsFundamentalDomain (principalRange L) D₀ ν := hD₀F
  obtain ⟨s, -, hs, -⟩ := exists_continuous_monoidHom_ideleNorm_apply_eq L

  set μ' : Measure ℝ := Measure.map (logNorm L) (ν.restrict D₀) with hμ'
  have hμ'_apply : ∀ {A : Set ℝ}, MeasurableSet A → μ' A = ν (logNorm L ⁻¹' A ∩ D₀) := by
    intro A hA
    rw [hμ', Measure.map_apply (measurable_logNorm L) hA,
      Measure.restrict_apply ((measurable_logNorm L) hA)]

  haveI : μ'.IsAddLeftInvariant := by
    refine (MeasureTheory.forall_measure_preimage_add_iff μ').mp fun r A hA => ?_
    set ρ : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp r))
      (by simp [Real.toNNReal_eq_zero, not_le, Real.exp_pos])
    set g : (AdeleRing (𝓞 L) L)ˣ := s ρ with hg
    have hgn : ideleNorm L g = Real.exp r := by
      rw [hg, hs ρ]
      simp [ρ, Real.coe_toNNReal _ (Real.exp_pos r).le]
    have hpre : logNorm L ⁻¹' ((fun x => r + x) ⁻¹' A) = (fun z => g • z) ⁻¹' (logNorm L ⁻¹' A) := by
      ext z
      simp only [Set.mem_preimage, logNorm, smul_eq_mul, ideleNorm_mul, hgn,
        Real.log_mul (Real.exp_pos r).ne' (ideleNorm_pos z).ne', Real.log_exp]
    have hD₀g : IsFundamentalDomain (principalRange L) (g • D₀) ν := hD₀.smul_of_comm g
    have hlog : MeasurableSet (logNorm L ⁻¹' A) := measurable_logNorm L hA
    have hA' : MeasurableSet ((fun x : ℝ => r + x) ⁻¹' A) := (measurable_const.add measurable_id) hA
    rw [hμ'_apply hA', hμ'_apply hA, hpre]
    calc ν ((fun z => g • z) ⁻¹' (logNorm L ⁻¹' A) ∩ D₀)
        = ν ((fun z => g • z) ⁻¹' (logNorm L ⁻¹' A ∩ g • D₀)) := by
          rw [Set.preimage_inter, Set.preimage_smul g (g • D₀), inv_smul_smul]
      _ = ν (logNorm L ⁻¹' A ∩ g • D₀) :=
          SMulInvariantMeasure.measure_preimage_smul g (hlog.inter (hD₀m.const_smul g))
      _ = ν (logNorm L ⁻¹' A ∩ D₀) :=
          hD₀g.measure_set_eq hD₀ hlog fun γ => by
            ext z
            simp only [Set.mem_preimage, logNorm]
            show Real.log (ideleNorm L ((γ : (AdeleRing (𝓞 L) L)ˣ) * z)) ∈ A ↔ _
            rw [ideleNorm_mul, hn γ, one_mul]

  haveI : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    obtain ⟨k, hk⟩ := hint 0
    have hε : (0 : ℝ) < Real.exp (-R) ^ k := pow_pos (Real.exp_pos _) _
    refine (measure_mono hR).trans_lt ?_
    rw [hμ', Measure.map_apply (measurable_logNorm L) measurableSet_closedBall]
    refine (measure_mono ?_).trans_lt (Integrable.measure_norm_ge_lt_top hk hε)
    intro z hz
    simp only [Set.mem_preimage, Real.closedBall_eq_Icc, zero_sub, zero_add, Set.mem_Icc,
      logNorm] at hz
    have hpos := ideleNorm_pos z
    have h₁ : Real.exp (-R) ≤ ideleNorm L z := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hz.1
    have h₂ : Real.exp (-R) ≤ (ideleNorm L z)⁻¹ := by
      rw [Real.exp_neg]
      refine inv_anti₀ hpos ?_
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hz.2
    have hmin : Real.exp (-R) ^ k ≤ min (ideleNorm L z) (ideleNorm L z)⁻¹ ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le (le_min h₁ h₂) k
    show Real.exp (-R) ^ k ≤ ‖min (ideleNorm L z) (ideleNorm L z)⁻¹ ^ k * ideleNorm L z ^ (0 : ℝ)‖
    rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (pow_nonneg (le_min hpos.le (inv_pos.mpr hpos).le) k)]
    exact hmin

  refine ⟨Measure.addHaarScalarFactor μ' volume, fun D hD a b ha hab => ?_⟩
  have hshell : ν (D ∩ shell L a b) = ν (shell L a b ∩ D₀) := by
    rw [Set.inter_comm]
    exact hD.measure_set_eq hD₀ (measurableSet_shell L a b) fun γ => preimage_shell_eq hn γ a b
  have hval : μ' (Set.Ioc (Real.log a) (Real.log b)) = ν (shell L a b ∩ D₀) := by
    rw [hμ'_apply measurableSet_Ioc, preimage_logNorm_Ioc ha hab]
  rw [hshell, ← hval]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ' volume]
  rw [Measure.smul_apply, Real.volume_Ioc, ENNReal.smul_def, smul_eq_mul]

end Measure

end ShellMass

end LogShellMass

section RankOneFurniture

open NumberField.AdelicFourier NumberField.TateGlobal NumberField.StandardAddChar
open scoped ENNReal NNReal Pointwise

private theorem integrable_tsum_of_tsum_lintegral_ne_top {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {ν : Measure α} {g : ι → α → ℂ} (hg : ∀ i, AEStronglyMeasurable (g i) ν)
    (hfin : ∑' i, ∫⁻ a, ‖g i a‖ₑ ∂ν ≠ ∞) : Integrable (fun a => ∑' i, g i a) ν := by
  have hg' : ∀ i, AEMeasurable (fun a => ‖g i a‖ₑ) ν := fun i => (hg i).enorm
  have htot : ∫⁻ a, ∑' i, ‖g i a‖ₑ ∂ν ≠ ∞ := by rwa [lintegral_tsum hg']
  have hsum : ∀ᵐ a ∂ν, Summable fun i => (‖g i a‖₊ : ℝ) := by
    have hT : AEMeasurable (fun a => ∑' i, ‖g i a‖ₑ) ν := by
      simp_rw [ENNReal.tsum_eq_iSup_sum]
      exact .iSup fun s => Finset.aemeasurable_fun_sum s fun i _ => hg' i
    refine (ae_lt_top' hT htot).mono fun a ha => ?_
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact ha.ne
  refine ⟨?_, ?_⟩
  · haveI := Encodable.ofCountable ι
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (fun s => s.aestronglyMeasurable_fun_sum fun i _ => hg i) ?_
    filter_upwards [hsum] with a ha
    have ha' : Summable fun i => ‖g i a‖ := by simpa only [coe_nnnorm] using ha
    exact (Summable.of_norm ha').hasSum
  · rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ a, ‖∑' i, g i a‖ₑ ∂ν ≤ ∫⁻ a, ∑' i, ‖g i a‖ₑ ∂ν :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ < ∞ := htot.lt_top

variable (F : Type) [Field F] [NumberField F]

private theorem countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm

open scoped Classical in

private theorem continuous_of_mem_schwartzBruhat {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    Continuous f := by
  refine schwartzBruhat_induction (p := fun f _ => Continuous f) ?_ continuous_zero ?_ ?_ hf
  · intro f hf
    obtain ⟨g, h, hlc, -, rfl⟩ := hf
    exact (g.continuous.comp ((NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst)).mul
      (hlc.continuous.comp continuous_snd)
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro c f _ hf
    exact hf.const_smul c

private theorem ideleNorm_one' : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 F) F)ˣ)).ne' (h.symm.trans (mul_one _).symm)

private theorem ideleNorm_inv' (y : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F y⁻¹ = (ideleNorm F y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← ideleNorm_mul, inv_mul_cancel, ideleNorm_one']

private theorem ideleNorm_unitsMap (η : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) η) = 1 := by
  have hdet : Matrix.det (Matrix.diagonal ![(η : F), 1]) ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]
  have hγ : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) = η :=
    Units.ext (by
      show Matrix.det (Matrix.diagonal ![(η : F), 1]) = (η : F)
      simp [Matrix.det_diagonal, Fin.prod_univ_two])
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)
  rw [show AutomorphicForm.globalPoints (𝓞 F) F =
      Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F)) from rfl,
    Matrix.GeneralLinearGroup.map_det, hγ] at h
  exact h

private theorem ideleNorm_coe_eq_one (γ : ShellMass.principalRange F) :
    ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨η, hη⟩ := γ.2
  rw [← hη]
  exact ideleNorm_unitsMap F η

private theorem unitsMap_injective :
    Function.Injective (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

private noncomputable def principalEquiv : {ξ : F // ξ ≠ 0} ≃ ShellMass.principalRange F :=
  Equiv.ofBijective
    (fun ξ => ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 ξ.1 ξ.2),
      Units.mk0 ξ.1 ξ.2, rfl⟩)
    ⟨fun ξ ξ' h => by
        have h' : algebraMap F (AdeleRing (𝓞 F) F) ξ.1 = algebraMap F (AdeleRing (𝓞 F) F) ξ'.1 :=
          congr_arg (fun γ : ShellMass.principalRange F => ((γ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) h
        exact Subtype.ext (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F) h'),
      fun γ => by
        obtain ⟨η, hη⟩ := γ.2
        refine ⟨⟨(η : F), η.ne_zero⟩, Subtype.ext ?_⟩
        show Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 (η : F) η.ne_zero) = γ
        rw [Units.mk0_val, hη]⟩

private theorem coe_principalEquiv (ξ : {ξ : F // ξ ≠ 0}) :
    (((principalEquiv F ξ : ShellMass.principalRange F) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
      algebraMap F (AdeleRing (𝓞 F) F) ξ := rfl

section Adelic

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]

include μ in

private theorem finite_setOf_apply_mul_ne_zero {Ψ : AdeleRing (𝓞 F) F → ℂ} (hΨc : HasCompactSupport Ψ)
    (y : (AdeleRing (𝓞 F) F)ˣ) :
    {ξ : F | Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≠ 0}.Finite := by
  haveI := countable_numberField F
  obtain ⟨U, hUo, hUne, hUbox⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox F
  obtain ⟨Kb, hKb, hboxKb⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset F
  refine Set.not_infinite.mp fun hinf => ?_
  haveI : Infinite {ξ : F // Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≠ 0} := Set.infinite_coe_iff.mpr hinf

  have hTm : ∀ ξ : F, MeasurableSet ((fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ + z) ⁻¹' U) := fun ξ =>
    (hUo.preimage (continuous_const.add continuous_id)).measurableSet
  have hTμ : ∀ ξ : F, μ ((fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ + z) ⁻¹' U) = μ U := fun ξ =>
    measure_preimage_add μ _ U
  have hdisj : Pairwise (Function.onFun Disjoint fun ξ : {ξ : F // Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≠ 0} =>
        (fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ.1 + z) ⁻¹' U) := by
    intro ξ ξ' hne
    show Disjoint ((fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ.1 + z) ⁻¹' U)
      ((fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ'.1 + z) ⁻¹' U)
    refine Set.disjoint_left.mpr fun z hz hz' => hne (Subtype.ext (neg_injective ?_))
    have h1 : algebraMap F (AdeleRing (𝓞 F) F) (-ξ.1) + z ∈ NumberField.AdelicBox.adelicBox F := by
      rw [map_neg]; exact hUbox hz
    have h2 : algebraMap F (AdeleRing (𝓞 F) F) (-ξ'.1) + z ∈ NumberField.AdelicBox.adelicBox F := by
      rw [map_neg]; exact hUbox hz'
    exact (NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F z).unique h1 h2
  have hKc : IsCompact (tsupport Ψ * {((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)} + Kb) :=
    (hΨc.isCompact.mul isCompact_singleton).add hKb
  have hsub : (⋃ ξ : {ξ : F // Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≠ 0},
        (fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ.1 + z) ⁻¹' U) ⊆
      tsupport Ψ * {((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)} + Kb := by
    refine Set.iUnion_subset fun ξ z hz => ?_
    have hξ : algebraMap F (AdeleRing (𝓞 F) F) ξ.1 ∈
        tsupport Ψ * {((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)} := by
      have hm := Set.mul_mem_mul (subset_tsupport Ψ ξ.2)
        (Set.mem_singleton ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      rwa [mul_assoc, Units.inv_mul, mul_one] at hm
    rw [← add_neg_cancel_left (algebraMap F (AdeleRing (𝓞 F) F) ξ.1) z]
    exact Set.add_mem_add hξ (hboxKb (hUbox hz))
  have hU0 : μ U ≠ 0 := (hUo.measure_pos μ hUne).ne'
  have h1 : μ (⋃ ξ : {ξ : F // Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≠ 0},
        (fun z => -algebraMap F (AdeleRing (𝓞 F) F) ξ.1 + z) ⁻¹' U) = ∞ := by
    rw [measure_iUnion hdisj fun ξ => hTm ξ.1]
    simp only [hTμ]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hU0
  have h2 := measure_mono (μ := μ) hsub
  rw [h1, top_le_iff] at h2
  exact hKc.measure_lt_top.ne h2

private theorem exists_forall_apply_eq_zero_of_lt_ideleNorm (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    {Ψ : AdeleRing (𝓞 F) F → ℂ} (hΨc : HasCompactSupport Ψ) :
    ∃ U₀ : ℝ, ∀ z : (AdeleRing (𝓞 F) F)ˣ, U₀ < ideleNorm F z → Ψ z = 0 := by
  obtain ⟨U, hUo, hUne, hUbox⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox F
  obtain ⟨Kb, hKb, hboxKb⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset F
  have hKc : IsCompact (tsupport Ψ * Kb) := hΨc.isCompact.mul hKb
  have hU0 : μ U ≠ 0 := (hUo.measure_pos μ hUne).ne'
  have hUfin : μ U ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hUbox)
    rw [hμ1]
    exact ENNReal.one_ne_top
  refine ⟨(μ (tsupport Ψ * Kb) / μ U).toReal, fun z hz => ?_⟩
  by_contra hne
  have hmem : ((z : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ tsupport Ψ := subset_tsupport _ hne
  have hsub : z • U ⊆ tsupport Ψ * Kb := by
    rintro _ ⟨b, hb, rfl⟩
    exact Set.mul_mem_mul hmem (hboxKb (hUbox hb))

  have hscal : μ (z • U) = ((distribHaarChar (AdeleRing (𝓞 F) F) z : ℝ≥0) : ℝ≥0∞) * μ U := by
    have h := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (DomMulAct.mk z • μ) μ hUo
    simpa only [Measure.domSMul_apply, Equiv.symm_apply_apply, addHaarScalarFactor_smul_eq_distribHaarChar,
      ENNReal.smul_def, smul_eq_mul] using h
  have h1 : ((distribHaarChar (AdeleRing (𝓞 F) F) z : ℝ≥0) : ℝ≥0∞) ≤ μ (tsupport Ψ * Kb) / μ U := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hU0) (Or.inl hUfin), ← hscal]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono (ENNReal.div_lt_top hKc.measure_lt_top.ne hU0).ne h1
  rw [ENNReal.coe_toReal] at h2
  exact absurd hz (not_lt.mpr h2)

private noncomputable def tailSum (Ψ : AdeleRing (𝓞 F) F → ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ∑' ξ : {ξ : F // ξ ≠ 0},
    fourierIntegral (stdAddChar F) μ Ψ
      (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))

omit [BorelSpace (AdeleRing (𝓞 F) F)] [μ.IsAddHaarMeasure] in
private theorem fourierIntegral_zero_eq (f : AdeleRing (𝓞 F) F → ℂ) :
    fourierIntegral (stdAddChar F) μ f 0 = ∫ u, f u ∂μ := by
  simp only [fourierIntegral, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
private theorem coeff_eq (y : (AdeleRing (𝓞 F) F)ˣ) :
    ((((distribHaarChar (AdeleRing (𝓞 F) F) y⁻¹ : ℝ≥0) : ℝ)) : ℂ)⁻¹ = ((ideleNorm F y : ℝ) : ℂ) := by
  show ((ideleNorm F y⁻¹ : ℝ) : ℂ)⁻¹ = ((ideleNorm F y : ℝ) : ℂ)
  rw [ideleNorm_inv', Complex.ofReal_inv, inv_inv]

private theorem finsum_eq_of_poisson (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    {Ψ : AdeleRing (𝓞 F) F → ℂ} (hΨ : Ψ ∈ schwartzBruhat F) (hΨc : HasCompactSupport Ψ)
    (y : (AdeleRing (𝓞 F) F)ˣ) :
    (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) =
      ((ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ + ((ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y - Ψ 0 := by
  classical
  have hgSB : (fun v => Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * v)) ∈ schwartzBruhat F :=
    comp_mul_mem_schwartzBruhat F y⁻¹ hΨ
  have hP := tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero F μ
    (isGlobalAddChar_stdAddChar F) hgSB
  rw [hμ1, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul, one_mul, sub_eq_iff_eq_add] at hP

  have hint : ∫ v, Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * v) ∂μ =
      ((ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ := by
    have h := fourierIntegral_comp_mul_left F μ (stdAddChar F) Ψ y⁻¹ 0
    rw [fourierIntegral_zero_eq, mul_zero, fourierIntegral_zero_eq, coeff_eq] at h
    exact h
  have hF : ∀ ξ : {ξ : F // ξ ≠ 0},
      fourierIntegral (stdAddChar F) μ (fun v => Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * v))
          (algebraMap F (AdeleRing (𝓞 F) F) ξ) =
        ((ideleNorm F y : ℝ) : ℂ) * fourierIntegral (stdAddChar F) μ Ψ
          (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    intro ξ
    rw [fourierIntegral_comp_mul_left F μ (stdAddChar F) Ψ y⁻¹, inv_inv, coeff_eq, mul_comm (_ : AdeleRing (𝓞 F) F)]
  have htail : (∑' ξ : {ξ : F // ξ ≠ 0},
      fourierIntegral (stdAddChar F) μ (fun v => Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * v))
        (algebraMap F (AdeleRing (𝓞 F) F) ξ)) = ((ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y := by
    rw [tailSum, ← tsum_mul_left]
    exact tsum_congr hF
  rw [hint, htail] at hP

  have hfin := finite_setOf_apply_mul_ne_zero F μ hΨc y
  have hsupp : Function.support (fun ξ : F => Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) *
      algebraMap F (AdeleRing (𝓞 F) F) ξ)) ⊆ ↑hfin.toFinset := by
    intro ξ hξ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mul_comm]
    exact hξ
  have hsum : (∑' ξ : F, Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ξ)) =
      ∑ ξ ∈ hfin.toFinset,
        Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
    tsum_eq_sum fun ξ hξ => of_not_not fun h => hξ (hsupp h)
  have hunits : (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
      ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) =
      ∑ ξ ∈ hfin.toFinset.erase 0,
        Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    rw [← Finset.sum_preimage (fun η : Fˣ => (η : F)) (hfin.toFinset.erase 0) (Units.val_injective.injOn) _
      (fun ξ hξ hξ' => (hξ' ⟨Units.mk0 ξ (Finset.ne_of_mem_erase hξ), rfl⟩).elim)]
    refine (finsum_eq_sum_of_support_subset _ fun η hη => ?_).trans (Finset.sum_congr rfl fun η _ => ?_)
    · rw [Finset.mem_coe, Finset.mem_preimage, Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨η.ne_zero, hη⟩
    · rw [mul_comm]
  have hzero : Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) (0 : F)) =
      Ψ 0 := by
    rw [map_zero, mul_zero]
  have hsplit : (∑ ξ ∈ hfin.toFinset,
        Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ξ)) =
      Ψ 0 + ∑ ξ ∈ hfin.toFinset.erase 0,
        Ψ (((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    by_cases h0 : (0 : F) ∈ hfin.toFinset
    · rw [← Finset.add_sum_erase _ _ h0, hzero]
    · rw [Finset.erase_eq_of_notMem h0]
      have : Ψ 0 = 0 := by
        rw [← hzero]
        by_contra hne
        exact h0 (by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, mul_comm]; exact hne)
      rw [this, zero_add]
  rw [hunits]
  rw [hsum, hsplit] at hP
  linear_combination hP

private theorem integrand_eq (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    {Ψ : AdeleRing (𝓞 F) F → ℂ} (hΨ : Ψ ∈ schwartzBruhat F) (hΨc : HasCompactSupport Ψ) (X : ℝ)
    (y : (AdeleRing (𝓞 F) F)ˣ) :
    ((ideleNorm F y : ℝ) : ℂ)⁻¹ *
        ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
            ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) -
          (if X < ideleNorm F y then ((ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) =
      tailSum F μ Ψ y + (if X < ideleNorm F y then 0 else ∫ u, Ψ u ∂μ) - ((ideleNorm F y : ℝ) : ℂ)⁻¹ * Ψ 0 := by
  have hy : ((ideleNorm F y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos y).ne'
  have h : ((ideleNorm F y : ℝ) : ℂ)⁻¹ * ((ideleNorm F y : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hy
  rw [finsum_eq_of_poisson F μ hμ1 hΨ hΨc y]
  split_ifs
  · linear_combination (tailSum F μ Ψ y) * h
  · linear_combination ((∫ u, Ψ u ∂μ) + tailSum F μ Ψ y) * h

section Idelic

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
private theorem measurableSet_lt_ideleNorm (c : ℝ) : MeasurableSet {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y} :=
  measurableSet_lt measurable_const (continuous_ideleNorm F).measurable

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
private theorem measurableSet_ideleNorm_le (b : ℝ) : MeasurableSet {y : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F y ≤ b} :=
  measurableSet_le (continuous_ideleNorm F).measurable measurable_const

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
  [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
private theorem ideleNorm_smul (γ : ShellMass.principalRange F) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (γ • y) = ideleNorm F y := by
  show ideleNorm F ((γ : (AdeleRing (𝓞 F) F)ˣ) * y) = ideleNorm F y
  rw [ideleNorm_mul, ideleNorm_coe_eq_one, one_mul]

variable {ν}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

private theorem exists_shell_constant {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) :
    ∃ c₀ : ℝ≥0,
      (∀ a b : ℝ, 0 < a → a < b →
        ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a)) ∧
      ν (Ω ∩ {y | 1 ≤ ideleNorm F y ∧ ideleNorm F y ≤ Real.exp 1}) = c₀ := by
  obtain ⟨c₀, hc₀⟩ := ShellMass.exists_forall_measure_inter_shell_eq ν (ideleNorm_coe_eq_one F)
  have hshell : ∀ a b : ℝ, 0 < a → a < b →
      ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a) :=
    fun a b ha hab => hc₀ Ω hΩ a b ha hab
  refine ⟨c₀, hshell, ?_⟩

  have hnull : ν (Ω ∩ {y | ideleNorm F y = 1}) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    have hlim : Filter.Tendsto (fun n : ℕ => (c₀ : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul (a := (c₀ : ℝ≥0∞))
        (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) (Or.inr ENNReal.coe_ne_top)
      rwa [ENNReal.ofReal_zero, mul_zero] at h
    refine ge_of_tendsto' hlim fun n => ?_
    · have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      calc ν (Ω ∩ {y | ideleNorm F y = 1})
          ≤ ν (Ω ∩ {y | Real.exp (-(1 / ((n : ℝ) + 1))) < ideleNorm F y ∧ ideleNorm F y ≤ 1}) := by
            refine measure_mono (Set.inter_subset_inter_right _ fun y hy => ?_)
            rw [Set.mem_setOf_eq] at hy
            rw [Set.mem_setOf_eq, hy]
            exact ⟨Real.exp_lt_one_iff.mpr (neg_neg_of_pos hn), le_rfl⟩
        _ = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log 1 - Real.log (Real.exp (-(1 / ((n : ℝ) + 1))))) :=
            hshell _ _ (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hn))
        _ = (c₀ : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
            rw [Real.log_one, Real.log_exp, zero_sub, neg_neg]
  have hopen : ν (Ω ∩ {y | 1 < ideleNorm F y ∧ ideleNorm F y ≤ Real.exp 1}) = c₀ := by
    rw [hshell 1 (Real.exp 1) one_pos (Real.one_lt_exp_iff.mpr one_pos), Real.log_exp,
      Real.log_one, sub_zero, ENNReal.ofReal_one, mul_one]
  refine le_antisymm ?_ ?_
  · calc ν (Ω ∩ {y | 1 ≤ ideleNorm F y ∧ ideleNorm F y ≤ Real.exp 1})
        ≤ ν ((Ω ∩ {y | ideleNorm F y = 1}) ∪ (Ω ∩ {y | 1 < ideleNorm F y ∧ ideleNorm F y ≤ Real.exp 1})) := by
          refine measure_mono fun y ⟨hyΩ, hy1, hye⟩ => ?_
          rcases hy1.eq_or_lt with h | h
          · exact Or.inl ⟨hyΩ, h.symm⟩
          · exact Or.inr ⟨hyΩ, h, hye⟩
      _ ≤ ν (Ω ∩ {y | ideleNorm F y = 1}) + ν (Ω ∩ {y | 1 < ideleNorm F y ∧ ideleNorm F y ≤ Real.exp 1}) :=
          measure_union_le _ _
      _ = c₀ := by rw [hnull, hopen, zero_add]
  · rw [← hopen]
    exact measure_mono (Set.inter_subset_inter_right _ fun y hy => ⟨hy.1.le, hy.2⟩)

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
private theorem measure_inter_shell_ne_top {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) ≠ ∞ := by
  obtain ⟨c₀, hshell, -⟩ := exists_shell_constant F hΩ
  by_cases hab : a < b
  · rw [hshell a b ha hab]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  · have : Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y ⟨_, h1, h2⟩ => hab ?_
      exact lt_of_lt_of_le h1 h2
    rw [this, measure_empty]
    exact ENNReal.zero_ne_top

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [ν.IsHaarMeasure] in

private theorem integrableOn_indicator_const {t s : Set (AdeleRing (𝓞 F) F)ˣ} (ht : MeasurableSet t)
    (hfin : ν (t ∩ s) ≠ ∞) (I : ℂ) : IntegrableOn (t.indicator fun _ => I) s ν := by
  refine (integrable_indicator_iff ht).mpr ?_
  rw [IntegrableOn, Measure.restrict_restrict ht]
  haveI : IsFiniteMeasure (ν.restrict (t ∩ s)) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  exact integrable_const I

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

private theorem integrableOn_inv_ideleNorm {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y => (ideleNorm F y)⁻¹) (Ω ∩ {y | c < ideleNorm F y}) ν := by
  obtain ⟨c₀, hshell, -⟩ := exists_shell_constant F hΩ
  refine ⟨((continuous_ideleNorm F).measurable.inv).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => inv_nonneg.mpr (ideleNorm_pos y).le)]

  set sh : ℕ → Set (AdeleRing (𝓞 F) F)ˣ := fun k =>
    Ω ∩ {y | c * Real.exp ((k : ℝ) - 1) < ideleNorm F y ∧ ideleNorm F y ≤ c * Real.exp ((k : ℝ) + 1)} with hsh
  have hcover : Ω ∩ {y | c < ideleNorm F y} ⊆ ⋃ k, sh k := by
    rintro y ⟨hyΩ, hy⟩
    rw [Set.mem_setOf_eq] at hy
    have hpos := ideleNorm_pos y
    have ht : 0 < Real.log (ideleNorm F y / c) := Real.log_pos (by rw [one_lt_div hc]; exact hy)
    refine Set.mem_iUnion.mpr ⟨⌊Real.log (ideleNorm F y / c)⌋₊, hyΩ, ?_, ?_⟩
    · have h1 : (⌊Real.log (ideleNorm F y / c)⌋₊ : ℝ) - 1 < Real.log (ideleNorm F y / c) := by
        linarith [Nat.floor_le ht.le]
      calc c * Real.exp ((⌊Real.log (ideleNorm F y / c)⌋₊ : ℝ) - 1)
          < c * Real.exp (Real.log (ideleNorm F y / c)) := by
            exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h1) hc
        _ = ideleNorm F y := by rw [Real.exp_log (div_pos hpos hc), mul_div_cancel₀ _ hc.ne']
    · have h2 : Real.log (ideleNorm F y / c) ≤ (⌊Real.log (ideleNorm F y / c)⌋₊ : ℝ) + 1 :=
        (Nat.lt_floor_add_one _).le
      calc ideleNorm F y = c * Real.exp (Real.log (ideleNorm F y / c)) := by
            rw [Real.exp_log (div_pos hpos hc), mul_div_cancel₀ _ hc.ne']
        _ ≤ c * Real.exp ((⌊Real.log (ideleNorm F y / c)⌋₊ : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hc.le

  have hmass : ∀ k : ℕ, ν (sh k) = (c₀ : ℝ≥0∞) * ENNReal.ofReal 2 := by
    intro k
    have hk : c * Real.exp ((k : ℝ) - 1) < c * Real.exp ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hc
    rw [hsh]
    show ν (Ω ∩ _) = _
    rw [hshell _ _ (mul_pos hc (Real.exp_pos _)) hk, Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    congr 2
    ring
  have hbound : ∀ k : ℕ, ∫⁻ y in sh k, ENNReal.ofReal (ideleNorm F y)⁻¹ ∂ν ≤
      ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k * ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2) := by
    intro k
    calc ∫⁻ y in sh k, ENNReal.ofReal (ideleNorm F y)⁻¹ ∂ν
        ≤ ∫⁻ _ in sh k, ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k ∂ν := by
          refine setLIntegral_mono measurable_const fun y hy => ?_
          obtain ⟨-, hy1, -⟩ := hy
          have hek : 0 < c * Real.exp ((k : ℝ) - 1) := mul_pos hc (Real.exp_pos _)
          rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc (ideleNorm F y)⁻¹ ≤ (c * Real.exp ((k : ℝ) - 1))⁻¹ := inv_anti₀ hek hy1.le
            _ = Real.exp 1 / c * Real.exp (-1) ^ k := by
                rw [← Real.exp_nat_mul, Real.exp_sub, mul_comm (k : ℝ) (-1), neg_one_mul, Real.exp_neg]
                simp only [div_eq_mul_inv, mul_inv, inv_inv]
                ring
      _ = ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k * ν (sh k) := setLIntegral_const _ _
      _ = ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k * ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2) := by
          rw [hmass k]

  have hr : ENNReal.ofReal (Real.exp (-1)) < 1 :=
    ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hgeom : (∑' k : ℕ, ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k *
      ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2)) ≠ ∞ := by
    have hre : (∑' k : ℕ, ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k *
        ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2)) =
        ENNReal.ofReal (Real.exp 1 / c) * ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2) *
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ k := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun k => by ring
    rw [hre, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
      (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr).ne')
  calc ∫⁻ y in Ω ∩ {y | c < ideleNorm F y}, ENNReal.ofReal (ideleNorm F y)⁻¹ ∂ν
      ≤ ∫⁻ y in ⋃ k, sh k, ENNReal.ofReal (ideleNorm F y)⁻¹ ∂ν := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ y in sh k, ENNReal.ofReal (ideleNorm F y)⁻¹ ∂ν := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp 1 / c) * ENNReal.ofReal (Real.exp (-1)) ^ k *
          ((c₀ : ℝ≥0∞) * ENNReal.ofReal 2) := ENNReal.tsum_le_tsum hbound
    _ < ∞ := hgeom.lt_top

private theorem integrableOn_tailSum {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) {Ψ : AdeleRing (𝓞 F) F → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat F) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (tailSum F μ Ψ) (Ω ∩ {y | c < ideleNorm F y}) ν := by
  haveI := countable_numberField F
  haveI := ShellMass.countable_principalRange F
  haveI : MeasurableConstSMul (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun γ => (continuous_const_mul (γ : (AdeleRing (𝓞 F) F)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun γ s _ => measure_preimage_mul ν (γ : (AdeleRing (𝓞 F) F)ˣ) s⟩
  have hΦSB : fourierIntegral (stdAddChar F) μ Ψ ∈ schwartzBruhat F :=
    fourierIntegral_mem_schwartzBruhat F μ (isGlobalAddChar_stdAddChar F) hΨ
  have hΦc : Continuous (fourierIntegral (stdAddChar F) μ Ψ) := continuous_of_mem_schwartzBruhat F hΦSB
  have hSm := measurableSet_lt_ideleNorm F c

  have h1c : Continuous (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := by
    rw [show ⇑(1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) = fun _ => 1 from rfl]
    exact continuous_const
  have h1u : AutomorphicForm.IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
  have hZ := (integrable_zetaIntegrand F ν hΦSB h1c h1u (s := ((2 : ℕ) : ℂ)) (by norm_num)).norm
  have hZ' : Integrable (fun y : (AdeleRing (𝓞 F) F)ˣ =>
      ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ 2) ν := by
    refine hZ.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [Real.norm_of_nonneg (ideleNorm_pos y).le]
  have hZfin : ∫⁻ y, ‖(‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ 2)‖ₑ ∂ν ≠ ∞ :=
    (hasFiniteIntegral_iff_enorm.mp hZ'.2).ne
  show Integrable (fun y : (AdeleRing (𝓞 F) F)ˣ => ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral (stdAddChar F) μ Ψ
    (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)))
    (ν.restrict (Ω ∩ {y | c < ideleNorm F y}))
  refine integrable_tsum_of_tsum_lintegral_ne_top (fun ξ => ?_) ?_
  · exact (hΦc.comp (continuous_const.mul Units.continuous_val)).aestronglyMeasurable

  have hpt : ∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
      {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator
          (fun y : (AdeleRing (𝓞 F) F)ˣ => ‖fourierIntegral (stdAddChar F) μ Ψ y‖ₑ) (principalEquiv F ξ • y) =
        {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator (fun y : (AdeleRing (𝓞 F) F)ˣ =>
          ‖fourierIntegral (stdAddChar F) μ Ψ
            (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))‖ₑ) y := by
    intro ξ y
    unfold Set.indicator
    simp only [Set.mem_setOf_eq, ideleNorm_smul]
    rfl
  have key : (∑' ξ : {ξ : F // ξ ≠ 0}, ∫⁻ y in Ω ∩ {y | c < ideleNorm F y},
        ‖fourierIntegral (stdAddChar F) μ Ψ
          (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))‖ₑ ∂ν) =
      ∫⁻ y, {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator
        (fun y : (AdeleRing (𝓞 F) F)ˣ => ‖fourierIntegral (stdAddChar F) μ Ψ y‖ₑ) y ∂ν := by
    rw [hΩ.lintegral_eq_tsum', ← ((principalEquiv F).trans (Equiv.inv (ShellMass.principalRange F))).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, inv_inv, hpt]
    rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]
  rw [key]

  have hcc : c⁻¹ ^ 2 * c ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal (c⁻¹ ^ 2) ≠ ⊤) hZfin) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}
  · rw [Set.indicator_of_mem hy]
    rw [Set.mem_setOf_eq] at hy
    have hc2 : c ^ 2 ≤ ideleNorm F y ^ 2 := pow_le_pow_left₀ hc.le hy.le 2
    rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖fourierIntegral (stdAddChar F) μ Ψ y‖
        = c⁻¹ ^ 2 * (‖fourierIntegral (stdAddChar F) μ Ψ y‖ * c ^ 2) := by
          rw [← mul_assoc, mul_comm (c⁻¹ ^ 2), mul_assoc, hcc, mul_one]
      _ ≤ c⁻¹ ^ 2 * (‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc2 (norm_nonneg _)) (by positivity)
  · rw [Set.indicator_of_notMem hy]
    exact zero_le

end Idelic

end Adelic

end RankOneFurniture

section RankOneRegularisation

open NumberField.AdelicFourier NumberField.TateGlobal NumberField.StandardAddChar
open scoped ENNReal NNReal Pointwise

variable (F : Type) [Field F] [NumberField F]
variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
variable {ν : Measure (AdeleRing (𝓞 F) F)ˣ}

private theorem measurable_log_ideleNorm :
    Measurable fun y : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F y) :=
  Real.measurable_log.comp (NumberField.TateGlobal.continuous_ideleNorm F).measurable

variable {F}

private theorem smul_volume_eq_map_log_ideleNorm {Ω : Set (AdeleRing (𝓞 F) F)ˣ} {c₀ : ℝ≥0}
    (hshell : ∀ a b : ℝ, 0 < a → a < b →
      ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a)) :
    (c₀ • (volume : Measure ℝ)) =
      Measure.map (fun y : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F y)) (ν.restrict Ω) := by
  refine Measure.ext_of_Ioc _ _ ?_
  intro a b hab
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Real.volume_Ioc,
    Measure.map_apply (measurable_log_ideleNorm F) measurableSet_Ioc, Measure.restrict_apply
    ((measurable_log_ideleNorm F) measurableSet_Ioc), Set.inter_comm]
  have hset : (fun y : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F y)) ⁻¹' Set.Ioc a b =
      {y | Real.exp a < ideleNorm F y ∧ ideleNorm F y ≤ Real.exp b} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_setOf_eq]
    rw [Real.lt_log_iff_exp_lt (ideleNorm_pos y), Real.log_le_iff_le_exp (ideleNorm_pos y)]
  rw [hset, hshell _ _ (Real.exp_pos a) (Real.exp_lt_exp.mpr hab), Real.log_exp, Real.log_exp]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

private theorem indicator_cpow_eq (w : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ({y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y}).indicator (fun y => ((ideleNorm F y : ℝ) : ℂ) ^ w) y =
      (Set.Ioi (0 : ℝ)).indicator (fun u : ℝ => Complex.exp (w * (u : ℂ))) (Real.log (ideleNorm F y)) := by
  have hmem : Real.log (ideleNorm F y) ∈ Set.Ioi (0 : ℝ) ↔ y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y} := by
    rw [Set.mem_Ioi, Set.mem_setOf_eq, Real.log_pos_iff (ideleNorm_pos y).le]
  by_cases hy : y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmem.mpr hy)]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ideleNorm_pos y).ne'),
      ← Complex.ofReal_log (ideleNorm_pos y).le, mul_comm]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hmem.mp h))]

private theorem measurable_indicator_exp (w : ℂ) :
    Measurable ((Set.Ioi (0 : ℝ)).indicator fun u : ℝ => Complex.exp (w * (u : ℂ))) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.indicator
    measurableSet_Ioi

private theorem integrableOn_cpow_large_half {Ω : Set (AdeleRing (𝓞 F) F)ˣ} {c₀ : ℝ≥0}
    (hshell : ∀ a b : ℝ, 0 < a → a < b →
      ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a))
    {w : ℂ} (hw : w.re < 0) :
    IntegrableOn (fun y => ((ideleNorm F y : ℝ) : ℂ) ^ w) (Ω ∩ {y | 1 < ideleNorm F y}) ν := by
  have hG : Integrable ((Set.Ioi (0 : ℝ)).indicator fun u : ℝ => Complex.exp (w * (u : ℂ))) (c₀ • volume) := by
    rw [ENNReal.smul_def]
    exact ((integrableOn_exp_mul_complex_Ioi hw 0).integrable_indicator measurableSet_Ioi).smul_measure
      ENNReal.coe_ne_top
  rw [smul_volume_eq_map_log_ideleNorm hshell,
    integrable_map_measure (measurable_indicator_exp w).aestronglyMeasurable
      (measurable_log_ideleNorm F).aemeasurable] at hG
  rw [IntegrableOn, Set.inter_comm, ← Measure.restrict_restrict (measurableSet_lt_ideleNorm F 1),
    ← IntegrableOn, ← integrable_indicator_iff (measurableSet_lt_ideleNorm F 1)]
  exact hG.congr (Filter.Eventually.of_forall fun y => (indicator_cpow_eq w y).symm)

private theorem setIntegral_cpow_large_half {Ω : Set (AdeleRing (𝓞 F) F)ˣ} {c₀ : ℝ≥0}
    (hshell : ∀ a b : ℝ, 0 < a → a < b →
      ν (Ω ∩ {y | a < ideleNorm F y ∧ ideleNorm F y ≤ b}) = (c₀ : ℝ≥0∞) * ENNReal.ofReal (Real.log b - Real.log a))
    {w : ℂ} (hw : w.re < 0) :
    ∫ y in Ω ∩ {y | 1 < ideleNorm F y}, ((ideleNorm F y : ℝ) : ℂ) ^ w ∂ν = -((c₀ : ℝ) : ℂ) / w := by
  rw [Set.inter_comm, ← Measure.restrict_restrict (measurableSet_lt_ideleNorm F 1),
    ← integral_indicator (measurableSet_lt_ideleNorm F 1),
    integral_congr_ae (Filter.Eventually.of_forall (indicator_cpow_eq w)),
    ← integral_map (measurable_log_ideleNorm F).aemeasurable (measurable_indicator_exp w).aestronglyMeasurable,
    ← smul_volume_eq_map_log_ideleNorm hshell, integral_smul_nnreal_measure,
    integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hw 0, NNReal.smul_def, Complex.real_smul]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

section WeightedTail

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsHaarMeasure]

private theorem integrableOn_tailSum_mul_pow {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) {Ψ : AdeleRing (𝓞 F) F → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat F) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    IntegrableOn (fun y => tailSum F μ Ψ y * ((ideleNorm F y : ℝ) : ℂ) ^ n) (Ω ∩ {y | c < ideleNorm F y}) ν := by
  haveI := countable_numberField F
  haveI := ShellMass.countable_principalRange F
  haveI : MeasurableConstSMul (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun γ => (continuous_const_mul (γ : (AdeleRing (𝓞 F) F)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun γ s _ => measure_preimage_mul ν (γ : (AdeleRing (𝓞 F) F)ˣ) s⟩
  have hΦSB : fourierIntegral (stdAddChar F) μ Ψ ∈ schwartzBruhat F :=
    fourierIntegral_mem_schwartzBruhat F μ (isGlobalAddChar_stdAddChar F) hΨ
  have hΦc : Continuous (fourierIntegral (stdAddChar F) μ Ψ) := continuous_of_mem_schwartzBruhat F hΦSB
  have hwc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F y : ℝ) : ℂ) ^ n :=
    (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).pow n
  have hSm := measurableSet_lt_ideleNorm F c

  have h1c : Continuous (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := by
    rw [show ⇑(1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) = fun _ => 1 from rfl]
    exact continuous_const
  have h1u : AutomorphicForm.IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
  have hre : (1 : ℝ) < (((n + 2 : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < n + 2)
  have hZ := (integrable_zetaIntegrand F ν hΦSB h1c h1u (s := ((n + 2 : ℕ) : ℂ)) hre).norm
  have hZ' : Integrable (fun y : (AdeleRing (𝓞 F) F)ˣ =>
      ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ (n + 2)) ν := by
    refine hZ.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Complex.cpow_natCast]
    simp [Real.norm_of_nonneg (ideleNorm_pos y).le]
  have hZfin : ∫⁻ y, ‖(‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ (n + 2))‖ₑ ∂ν ≠ ∞ :=
    (hasFiniteIntegral_iff_enorm.mp hZ'.2).ne

  have hfun : (fun y => tailSum F μ Ψ y * ((ideleNorm F y : ℝ) : ℂ) ^ n) =
      fun y : (AdeleRing (𝓞 F) F)ˣ => ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral (stdAddChar F) μ Ψ
        (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) *
          ((ideleNorm F y : ℝ) : ℂ) ^ n := by
    funext y
    rw [tailSum, tsum_mul_right]
  rw [IntegrableOn, hfun]
  refine integrable_tsum_of_tsum_lintegral_ne_top (fun ξ => ?_) ?_
  · exact ((hΦc.comp (continuous_const.mul Units.continuous_val)).mul hwc).aestronglyMeasurable

  have hpt : ∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
      {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator
          (fun y : (AdeleRing (𝓞 F) F)ˣ =>
            ‖fourierIntegral (stdAddChar F) μ Ψ y * ((ideleNorm F y : ℝ) : ℂ) ^ n‖ₑ) (principalEquiv F ξ • y) =
        {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator (fun y : (AdeleRing (𝓞 F) F)ˣ =>
          ‖fourierIntegral (stdAddChar F) μ Ψ
            (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) *
              ((ideleNorm F y : ℝ) : ℂ) ^ n‖ₑ) y := by
    intro ξ y
    unfold Set.indicator
    simp only [Set.mem_setOf_eq, ideleNorm_smul]
    rfl
  have key : (∑' ξ : {ξ : F // ξ ≠ 0}, ∫⁻ y in Ω ∩ {y | c < ideleNorm F y},
        ‖fourierIntegral (stdAddChar F) μ Ψ
          (algebraMap F (AdeleRing (𝓞 F) F) ξ * ((y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) *
            ((ideleNorm F y : ℝ) : ℂ) ^ n‖ₑ ∂ν) =
      ∫⁻ y, {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}.indicator
        (fun y : (AdeleRing (𝓞 F) F)ˣ =>
          ‖fourierIntegral (stdAddChar F) μ Ψ y * ((ideleNorm F y : ℝ) : ℂ) ^ n‖ₑ) y ∂ν := by
    rw [hΩ.lintegral_eq_tsum', ← ((principalEquiv F).trans (Equiv.inv (ShellMass.principalRange F))).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, inv_inv, hpt]
    rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]
  rw [key]

  have hcc : c⁻¹ ^ 2 * c ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal (c⁻¹ ^ 2) ≠ ⊤) hZfin) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y}
  · rw [Set.indicator_of_mem hy]
    rw [Set.mem_setOf_eq] at hy
    have hc2 : c ^ 2 ≤ ideleNorm F y ^ 2 := pow_le_pow_left₀ hc.le hy.le 2
    have hX : (0 : ℝ) ≤ ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (ideleNorm_pos y).le n)
    have hX2 : (0 : ℝ) ≤ ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ (n + 2) :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (ideleNorm_pos y).le _)
    have h1 : (1 : ℝ) ≤ c⁻¹ ^ 2 * ideleNorm F y ^ 2 :=
      calc (1 : ℝ) = c⁻¹ ^ 2 * c ^ 2 := hcc.symm
        _ ≤ c⁻¹ ^ 2 * ideleNorm F y ^ 2 := mul_le_mul_of_nonneg_left hc2 (by positivity)
    rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg hX2, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (ideleNorm_pos y).le]
    calc ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ n
        ≤ ‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ n * (c⁻¹ ^ 2 * ideleNorm F y ^ 2) :=
          le_mul_of_one_le_right hX h1
      _ = c⁻¹ ^ 2 * (‖fourierIntegral (stdAddChar F) μ Ψ y‖ * ideleNorm F y ^ (n + 2)) := by ring
  · rw [Set.indicator_of_notMem hy]
    exact zero_le

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

private theorem isInvInvariant_of_isHaarMeasure : ν.IsInvInvariant := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  haveI : TopologicalSpace.PseudoMetrizableSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI : ν.Regular := inferInstance
  infer_instance

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
include μ in

private theorem tsum_principal_eq_finsum {Ψ : AdeleRing (𝓞 F) F → ℂ} (hΨc : HasCompactSupport Ψ)
    (y : (AdeleRing (𝓞 F) F)ˣ) :
    (∑' γ : ShellMass.principalRange F,
        Ψ ((((γ : ShellMass.principalRange F) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) =
      ∑ᶠ η : Fˣ,
        Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
  set e : Fˣ ≃* ShellMass.principalRange F := MonoidHom.ofInjective (unitsMap_injective F) with he
  rw [← e.toEquiv.tsum_eq]
  have hcoe : ∀ η : Fˣ, (((e.toEquiv η : ShellMass.principalRange F) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
      algebraMap F (AdeleRing (𝓞 F) F) (η : F) :=
    fun _ => rfl
  simp_rw [hcoe]
  have hfin : (Function.support fun η : Fˣ =>
      Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))).Finite := by
    refine ((finite_setOf_apply_mul_ne_zero F μ hΨc y).preimage Units.val_injective.injOn).subset ?_
    intro η hη
    exact hη
  have hsub : (Function.support fun η : Fˣ =>
      Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) ⊆
        ↑hfin.toFinset := fun η hη => hfin.mem_toFinset.mpr hη
  rw [tsum_eq_sum' hsub, finsum_eq_sum_of_support_subset _ hsub]

include μ in

private theorem integrableOn_and_zetaIntegral_eq {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
    (hΩ : IsFundamentalDomain (ShellMass.principalRange F) Ω ν) {Ψ : AdeleRing (𝓞 F) F → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat F) (hΨc : HasCompactSupport Ψ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        (∑ᶠ η : Fˣ,
            Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
          ((ideleNorm F y : ℝ) : ℂ) ^ (-s)) Ω ν ∧
      zetaIntegral ν Ψ 1 s = ∫ y in Ω,
        (∑ᶠ η : Fˣ,
            Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
          ((ideleNorm F y : ℝ) : ℂ) ^ (-s) ∂ν := by
  haveI := isInvInvariant_of_isHaarMeasure (ν := ν)
  haveI := ShellMass.countable_principalRange F
  haveI : MeasurableConstSMul (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun γ => (continuous_const_mul (γ : (AdeleRing (𝓞 F) F)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure (ShellMass.principalRange F) (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun γ s _ => measure_preimage_mul ν (γ : (AdeleRing (𝓞 F) F)ˣ) s⟩

  set k : (AdeleRing (𝓞 F) F)ˣ → ℂ := fun x =>
    Ψ ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((ideleNorm F x : ℝ) : ℂ) ^ (-s) with hk
  have h1c : Continuous (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := by
    rw [show ⇑(1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) = fun _ => 1 from rfl]
    exact continuous_const
  have h1u : AutomorphicForm.IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
  have hZ : Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => Ψ x * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
    refine (integrable_zetaIntegrand F ν hΨ h1c h1u hs).congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have harg : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((ideleNorm F x : ℝ) : ℂ).arg ≠ Real.pi := fun x => by
    rw [Complex.arg_ofReal_of_nonneg (ideleNorm_pos x).le]
    exact Real.pi_pos.ne
  have hkx : ∀ x : (AdeleRing (𝓞 F) F)ˣ, k x⁻¹ = Ψ x * ((ideleNorm F x : ℝ) : ℂ) ^ s := by
    intro x
    simp only [hk, inv_inv, ideleNorm_inv', Complex.ofReal_inv]
    rw [Complex.inv_cpow _ _ (harg x), Complex.cpow_neg, inv_inv]
  have hkint : Integrable k ν := by
    refine hZ.comp_inv.congr (Filter.Eventually.of_forall fun x => ?_)
    have h := hkx x⁻¹
    rw [inv_inv] at h
    exact h.symm
  have hZk : zetaIntegral ν Ψ 1 s = ∫ x, k x ∂ν := by
    rw [← integral_inv_eq_self k ν]
    unfold NumberField.TateGlobal.zetaIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hkx]
    simp
  have hkc : Continuous k := by
    simp only [hk]
    exact ((continuous_of_mem_schwartzBruhat F hΨ).comp (Units.continuous_val.comp continuous_inv)).mul
      ((Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
        fun x => Complex.ofReal_mem_slitPlane.mpr (ideleNorm_pos x))
  have hterm : ∀ (γ : ShellMass.principalRange F) (y : (AdeleRing (𝓞 F) F)ˣ), k (γ⁻¹ • y) =
      Ψ ((((γ : ShellMass.principalRange F) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) * ((ideleNorm F y : ℝ) : ℂ) ^ (-s) := by
    intro γ y
    simp only [hk, ideleNorm_smul]
    rw [show (γ⁻¹ • y : (AdeleRing (𝓞 F) F)ˣ) = ((γ : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * y from rfl, mul_inv_rev, inv_inv,
      Units.val_mul, mul_comm ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)]
  have hfun : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (∑' γ : ShellMass.principalRange F, k (γ⁻¹ • y)) =
      (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
        ((ideleNorm F y : ℝ) : ℂ) ^ (-s) := by
    intro y
    simp_rw [hterm]
    rw [tsum_mul_right, tsum_principal_eq_finsum μ hΨc y]
  have hmeas : ∀ γ : ShellMass.principalRange F,
      AEStronglyMeasurable (fun y : (AdeleRing (𝓞 F) F)ˣ => k (γ⁻¹ • y)) (ν.restrict Ω) := fun γ =>
    (hkc.comp (continuous_const_mul ((γ⁻¹ : ShellMass.principalRange F) : (AdeleRing (𝓞 F) F)ˣ))).aestronglyMeasurable
  have hlin : (∑' γ : ShellMass.principalRange F, ∫⁻ y in Ω, ‖k (γ⁻¹ • y)‖ₑ ∂ν) ≠ ∞ := by
    rw [← hΩ.lintegral_eq_tsum' fun x => ‖k x‖ₑ]
    exact (hasFiniteIntegral_iff_enorm.mp hkint.2).ne
  refine ⟨(integrable_tsum_of_tsum_lintegral_ne_top hmeas hlin).congr (Filter.Eventually.of_forall hfun), ?_⟩
  rw [hZk, hΩ.integral_eq_tsum' k hkint, ← integral_tsum hmeas hlin]
  exact integral_congr_ae (Filter.Eventually.of_forall hfun)

end WeightedTail

section Holomorphy

private theorem setIntegral_eq_add_of_forall_eq_zero {Ω : Set (AdeleRing (𝓞 F) F)ˣ} {f : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    {c : ℝ} (hf0 : ∀ y, ideleNorm F y ≤ c → f y = 0)
    (h₁ : IntegrableOn f (Ω ∩ {y | c < ideleNorm F y ∧ ideleNorm F y ≤ 1}) ν)
    (h₂ : IntegrableOn f (Ω ∩ {y | 1 < ideleNorm F y}) ν) :
    ∫ y in Ω, f y ∂ν = (∫ y in Ω ∩ {y | c < ideleNorm F y ∧ ideleNorm F y ≤ 1}, f y ∂ν) +
      ∫ y in Ω ∩ {y | 1 < ideleNorm F y}, f y ∂ν := by
  have hX : MeasurableSet {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y ∧ ideleNorm F y ≤ 1} :=
    (measurableSet_lt_ideleNorm F c).inter (measurableSet_ideleNorm_le F 1)
  have hB := measurableSet_lt_ideleNorm F 1
  have hpt : ∀ y, f y = {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y ∧ ideleNorm F y ≤ 1}.indicator f y +
      {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y}.indicator f y := by
    intro y
    by_cases h1 : 1 < ideleNorm F y
    · rw [Set.indicator_of_mem (show y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y} from h1),
        Set.indicator_of_notMem (fun h => absurd h1 (not_lt.mpr h.2)), zero_add]
    · rw [Set.indicator_of_notMem (show y ∉ {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y} from h1), add_zero]
      by_cases hc : c < ideleNorm F y
      · rw [Set.indicator_of_mem (show y ∈ {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y ∧ ideleNorm F y ≤ 1} from
          ⟨hc, not_lt.mp h1⟩)]
      · rw [Set.indicator_of_notMem (fun h => hc h.1), hf0 y (not_lt.mp hc)]
  have h₁' : IntegrableOn f {y : (AdeleRing (𝓞 F) F)ˣ | c < ideleNorm F y ∧ ideleNorm F y ≤ 1} (ν.restrict Ω) := by
    rw [IntegrableOn, Measure.restrict_restrict hX, Set.inter_comm]
    exact h₁
  have h₂' : IntegrableOn f {y : (AdeleRing (𝓞 F) F)ˣ | 1 < ideleNorm F y} (ν.restrict Ω) := by
    rw [IntegrableOn, Measure.restrict_restrict hB, Set.inter_comm]
    exact h₂
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add ((integrable_indicator_iff hX).mpr h₁') ((integrable_indicator_iff hB).mpr h₂'),
    integral_indicator hX, integral_indicator hB, Measure.restrict_restrict hX, Measure.restrict_restrict hB,
    Set.inter_comm _ Ω, Set.inter_comm _ Ω]

private def IsDominated (T : Set (AdeleRing (𝓞 F) F)ˣ) (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (g : (AdeleRing (𝓞 F) F)ˣ → ℂ) (a : ℂ) : Prop :=
  ∀ σ₀ σ₁ : ℝ, 0 < σ₀ → ∃ D : (AdeleRing (𝓞 F) F)ˣ → ℝ, IntegrableOn D T ν ∧
    ∀ y ∈ T, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
      ‖g y‖ * ideleNorm F y ^ (a.re - s.re) * (1 + |Real.log (ideleNorm F y)|) ≤ D y

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
private theorem norm_mul_cpow (g : (AdeleRing (𝓞 F) F)ˣ → ℂ) (a s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ‖g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)‖ = ‖g y‖ * ideleNorm F y ^ (a.re - s.re) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos y), Complex.sub_re]

private theorem aestronglyMeasurable_mul_cpow {T : Set (AdeleRing (𝓞 F) F)ˣ} {g : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hg : AEStronglyMeasurable g (ν.restrict T)) (w : ℂ) :
    AEStronglyMeasurable (fun y => g y * ((ideleNorm F y : ℝ) : ℂ) ^ w) (ν.restrict T) :=
  hg.mul ((Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
    fun y => Complex.ofReal_mem_slitPlane.mpr (ideleNorm_pos y)).aestronglyMeasurable

private theorem integrableOn_mul_cpow_of_isDominated {T : Set (AdeleRing (𝓞 F) F)ˣ} (hT : NullMeasurableSet T ν)
    {g : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hg : AEStronglyMeasurable g (ν.restrict T)) {a : ℂ} (hdom : IsDominated T ν g a)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)) T ν := by
  obtain ⟨D, hD, hbound⟩ := hdom s.re s.re hs
  refine Integrable.mono' hD (aestronglyMeasurable_mul_cpow hg (a - s)) ?_
  refine (ae_restrict_mem₀ hT).mono fun y hy => ?_
  rw [norm_mul_cpow]
  refine le_trans ?_ (hbound y hy s le_rfl le_rfl)
  exact le_mul_of_one_le_right (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ideleNorm_pos y).le _))
    (by linarith [abs_nonneg (Real.log (ideleNorm F y))])

private theorem differentiableOn_setIntegral_mul_cpow {T : Set (AdeleRing (𝓞 F) F)ˣ} (hT : NullMeasurableSet T ν)
    {g : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hg : AEStronglyMeasurable g (ν.restrict T)) {a : ℂ}
    (hdom : IsDominated T ν g a) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ y in T, g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s) ∂ν) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  rw [Set.mem_setOf_eq] at hs₀
  obtain ⟨D, hD, hbound⟩ := hdom (s₀.re / 2) (s₀.re + 1) (by linarith)
  have hnhds : Complex.re ⁻¹' Set.Ioo (s₀.re / 2) (s₀.re + 1) ∈ nhds s₀ :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (Set.mem_preimage.mpr (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩))
  have hlog : ∀ y : (AdeleRing (𝓞 F) F)ˣ,
      ‖Complex.log ((ideleNorm F y : ℝ) : ℂ)‖ = |Real.log (ideleNorm F y)| := fun y => by
    rw [← Complex.ofReal_log (ideleNorm_pos y).le, Complex.norm_real, Real.norm_eq_abs]
  have hne : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((ideleNorm F y : ℝ) : ℂ) ≠ 0 := fun y =>
    Complex.ofReal_ne_zero.mpr (ideleNorm_pos y).ne'

  set F' : ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ := fun s y =>
    g y * (((ideleNorm F y : ℝ) : ℂ) ^ (a - s) * Complex.log ((ideleNorm F y : ℝ) : ℂ) * (-1)) with hF'
  have hderiv : ∀ (y : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ),
      HasDerivAt (fun s : ℂ => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)) (F' s y) s := fun y s =>
    (((hasDerivAt_id' (x := s)).const_sub a).const_cpow (Or.inl (hne y))).const_mul (g y)
  have hF'norm : ∀ (y : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ),
      ‖F' s y‖ = ‖g y‖ * ideleNorm F y ^ (a.re - s.re) * |Real.log (ideleNorm F y)| := by
    intro y s
    simp only [hF']
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos y), Complex.sub_re, hlog, mul_assoc]
  have hmeasF : ∀ s : ℂ,
      AEStronglyMeasurable (fun y => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)) (ν.restrict T) := fun s =>
    aestronglyMeasurable_mul_cpow hg (a - s)
  have hmeasF' : AEStronglyMeasurable (F' s₀) (ν.restrict T) := by
    simp only [hF']
    refine hg.mul (Measurable.aestronglyMeasurable ?_)
    refine (Measurable.mul ?_ measurable_const)
    refine Measurable.mul ?_ (Complex.measurable_log.comp
      (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).measurable)
    exact ((Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
      fun y => Complex.ofReal_mem_slitPlane.mpr (ideleNorm_pos y)).measurable
  have hF_int : Integrable (fun y => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s₀)) (ν.restrict T) :=
    integrableOn_mul_cpow_of_isDominated hT hg hdom hs₀
  have h_bound : ∀ᵐ y ∂ν.restrict T, ∀ s ∈ Complex.re ⁻¹' Set.Ioo (s₀.re / 2) (s₀.re + 1), ‖F' s y‖ ≤ D y := by
    refine (ae_restrict_mem₀ hT).mono fun y hy s hs => ?_
    have hs' := Set.mem_Ioo.mp hs
    rw [hF'norm]
    refine le_trans ?_ (hbound y hy s hs'.1.le hs'.2.le)
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (ideleNorm_pos y).le _)
    linarith
  have h_diff : ∀ᵐ y ∂ν.restrict T, ∀ s ∈ Complex.re ⁻¹' Set.Ioo (s₀.re / 2) (s₀.re + 1),
      HasDerivAt (fun s : ℂ => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)) (F' s y) s :=
    Filter.Eventually.of_forall fun y s _ => hderiv y s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν.restrict T)
    (F := fun s y => g y * ((ideleNorm F y : ℝ) : ℂ) ^ (a - s)) hnhds (Filter.Eventually.of_forall hmeasF) hF_int
    hmeasF' h_bound hD h_diff
  exact key.2.differentiableAt.differentiableWithinAt

end Holomorphy

end RankOneRegularisation

private theorem exists_differentiableOn_zetaIntegral_eq_add_div
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (Ψ : AdeleRing (𝓞 F) F → ℂ) (hΨ : Ψ ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (hΨc : HasCompactSupport Ψ) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        NumberField.TateGlobal.zetaIntegral ν Ψ 1 s =
          E s + ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
              NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
            (∫ u, Ψ u ∂μ) / (s - 1)) ∧
      E 1 = ∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if 1 < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) ∂ν := by
  classical
  have hΩ' : IsFundamentalDomain (ShellMass.principalRange F) Ω ν := hΩ
  obtain ⟨c₀, hshell, hclosed⟩ := exists_shell_constant F hΩ'

  obtain ⟨c, hc, hc1, hvanish⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ y : (AdeleRing (𝓞 F) F)ˣ,
      NumberField.TateGlobal.ideleNorm F y < c →
        (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) = 0 := by
    obtain ⟨U₀, hU₀⟩ := exists_forall_apply_eq_zero_of_lt_ideleNorm F μ hμ1 hΨc
    refine ⟨(max U₀ 1)⁻¹, inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _)),
      inv_le_one_of_one_le₀ (le_max_right _ _), fun y hy => ?_⟩
    refine finsum_eq_zero_of_forall_eq_zero fun η => ?_
    have h : U₀ < NumberField.TateGlobal.ideleNorm F
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) η * y⁻¹) := by
      rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_unitsMap, one_mul, ideleNorm_inv']
      calc U₀ ≤ max U₀ 1 := le_max_left _ _
        _ = ((max U₀ 1)⁻¹)⁻¹ := (inv_inv _).symm
        _ < (NumberField.TateGlobal.ideleNorm F y)⁻¹ :=
            inv_strictAnti₀ (NumberField.TateGlobal.ideleNorm_pos y) hy
    have h0 := hU₀ _ h
    simpa [Units.coe_map] using h0
  have hpois : ∀ y : (AdeleRing (𝓞 F) F)ˣ,
      (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) =
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ +
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y - Ψ 0 :=
    fun y => finsum_eq_of_poisson F μ hμ1 hΨ hΨc y

  have hTsN : NullMeasurableSet (Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ 1}) ν :=
    hΩ'.nullMeasurableSet.inter
      ((measurableSet_lt_ideleNorm F (c / 2)).inter (measurableSet_ideleNorm_le F 1)).nullMeasurableSet
  have hTlN : NullMeasurableSet (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y}) ν :=
    hΩ'.nullMeasurableSet.inter (measurableSet_lt_ideleNorm F 1).nullMeasurableSet
  have htail_s : IntegrableOn (tailSum F μ Ψ) (Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ 1}) ν :=
    (integrableOn_tailSum F μ hΩ' hΨ (half_pos hc)).mono_set (Set.inter_subset_inter_right _ fun y hy => hy.1)
  have htail_l : IntegrableOn (tailSum F μ Ψ) (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y}) ν :=
    integrableOn_tailSum F μ hΩ' hΨ one_pos
  have hnormc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)

  have hSmeas : AEStronglyMeasurable (fun y : (AdeleRing (𝓞 F) F)ˣ => ∑ᶠ η : Fˣ,
      Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)))
        (ν.restrict (Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
          NumberField.TateGlobal.ideleNorm F y ≤ 1})) := by
    rw [funext hpois]
    exact ((hnormc.aestronglyMeasurable.mul aestronglyMeasurable_const).add
      (hnormc.aestronglyMeasurable.mul htail_s.aestronglyMeasurable)).sub aestronglyMeasurable_const
  have hdom_s : IsDominated (Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ 1}) ν (fun y : (AdeleRing (𝓞 F) F)ˣ => ∑ᶠ η : Fˣ,
        Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) 0 := by
    intro σ₀ σ₁ hσ₀
    have hM : (1 : ℝ) ≤ max 1 (c / 2)⁻¹ := le_max_left _ _
    refine ⟨fun y => (‖tailSum F μ Ψ y‖ + (‖∫ u, Ψ u ∂μ‖ + ‖Ψ 0‖)) * max 1 (c / 2)⁻¹ ^ σ₁ *
      (1 + |Real.log (c / 2)|), ?_, ?_⟩
    · exact ((htail_s.norm.add (integrableOn_const (C := ‖∫ u, Ψ u ∂μ‖ + ‖Ψ 0‖)
        (measure_inter_shell_ne_top F hΩ' (half_pos hc) 1))).mul_const _).mul_const _
    · intro y hy s hs₀ hs₁
      have hy1 : c / 2 < NumberField.TateGlobal.ideleNorm F y := hy.2.1
      have hy2 : NumberField.TateGlobal.ideleNorm F y ≤ 1 := hy.2.2
      have hpos := NumberField.TateGlobal.ideleNorm_pos y
      have h1 : ‖∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
          ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))‖ ≤
            ‖tailSum F μ Ψ y‖ + (‖∫ u, Ψ u ∂μ‖ + ‖Ψ 0‖) := by
        rw [hpois y]
        have hn : ‖((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
          exact hy2
        calc ‖((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ +
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y - Ψ 0‖
            ≤ ‖((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ +
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y‖ + ‖Ψ 0‖ := norm_sub_le _ _
          _ ≤ ‖((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ‖ +
                ‖((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * tailSum F μ Ψ y‖ + ‖Ψ 0‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ ≤ ‖∫ u, Ψ u ∂μ‖ + ‖tailSum F μ Ψ y‖ + ‖Ψ 0‖ := by
              rw [norm_mul, norm_mul]
              exact add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg _) hn)
                (mul_le_of_le_one_left (norm_nonneg _) hn)) le_rfl
          _ = ‖tailSum F μ Ψ y‖ + (‖∫ u, Ψ u ∂μ‖ + ‖Ψ 0‖) := by ring
      have h2 : NumberField.TateGlobal.ideleNorm F y ^ ((0 : ℂ).re - s.re) ≤ max 1 (c / 2)⁻¹ ^ σ₁ := by
        rw [Complex.zero_re, zero_sub, Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
        calc (NumberField.TateGlobal.ideleNorm F y)⁻¹ ^ s.re ≤ max 1 (c / 2)⁻¹ ^ s.re :=
              Real.rpow_le_rpow (inv_pos.mpr hpos).le ((inv_anti₀ (half_pos hc) hy1.le).trans (le_max_right _ _))
                (by linarith)
          _ ≤ max 1 (c / 2)⁻¹ ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hM hs₁
      have h3 : 1 + |Real.log (NumberField.TateGlobal.ideleNorm F y)| ≤ 1 + |Real.log (c / 2)| := by
        have hl1 : Real.log (c / 2) < Real.log (NumberField.TateGlobal.ideleNorm F y) :=
          Real.log_lt_log (half_pos hc) hy1
        have hl2 : Real.log (NumberField.TateGlobal.ideleNorm F y) ≤ 0 := Real.log_nonpos hpos.le hy2
        have h4 : |Real.log (NumberField.TateGlobal.ideleNorm F y)| ≤ |Real.log (c / 2)| :=
          abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (c / 2))], by linarith [abs_nonneg (Real.log (c / 2))]⟩
        linarith
      exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hpos.le _) (by positivity)) h3 (by positivity)
        (mul_nonneg (by positivity) (Real.rpow_nonneg (zero_le_one.trans hM) _))

  have hdom_l : IsDominated (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y}) ν (tailSum F μ Ψ) 1 := by
    intro σ₀ σ₁ hσ₀
    refine ⟨fun y => ‖tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ 2‖,
      (integrableOn_tailSum_mul_pow μ hΩ' hΨ one_pos 2).norm, ?_⟩
    intro y hy s hs₀ _
    have hy1 : 1 < NumberField.TateGlobal.ideleNorm F y := hy.2
    have hpos := NumberField.TateGlobal.ideleNorm_pos y
    show _ ≤ ‖tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ 2‖
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le, Complex.one_re]
    have h2 : NumberField.TateGlobal.ideleNorm F y ^ (1 - s.re) ≤ NumberField.TateGlobal.ideleNorm F y :=
      calc NumberField.TateGlobal.ideleNorm F y ^ (1 - s.re) ≤ NumberField.TateGlobal.ideleNorm F y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith)
        _ = NumberField.TateGlobal.ideleNorm F y := Real.rpow_one _
    have h3 : 1 + |Real.log (NumberField.TateGlobal.ideleNorm F y)| ≤ NumberField.TateGlobal.ideleNorm F y := by
      rw [abs_of_pos (Real.log_pos hy1)]
      linarith [Real.log_le_sub_one_of_pos hpos]
    calc ‖tailSum F μ Ψ y‖ * NumberField.TateGlobal.ideleNorm F y ^ (1 - s.re) *
          (1 + |Real.log (NumberField.TateGlobal.ideleNorm F y)|)
        ≤ ‖tailSum F μ Ψ y‖ * NumberField.TateGlobal.ideleNorm F y * NumberField.TateGlobal.ideleNorm F y :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) h3 (by positivity)
            (mul_nonneg (norm_nonneg _) hpos.le)
      _ = ‖tailSum F μ Ψ y‖ * NumberField.TateGlobal.ideleNorm F y ^ 2 := by ring
  have hsmall := differentiableOn_setIntegral_mul_cpow hTsN hSmeas hdom_s
  have hlarge := differentiableOn_setIntegral_mul_cpow hTlN htail_l.aestronglyMeasurable hdom_l
  have h01 : (0 : ℝ) < (1 : ℂ).re := by
    rw [Complex.one_re]
    exact one_pos
  have hneg1 : (-1 : ℂ).re < 0 := by
    rw [Complex.neg_re, Complex.one_re]
    exact neg_one_lt_zero
  refine ⟨fun s => (∫ y in Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ 1},
        (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
            ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((0 : ℂ) - s) ∂ν) +
      (∫ y in Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y},
        tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s) ∂ν) -
      Ψ 0 * (-((c₀ : ℝ) : ℂ) / (-s)), ?_, ?_, ?_⟩
  ·
    refine (hsmall.add hlarge).sub ((differentiableOn_const _).mul ?_)
    have hneg : DifferentiableOn ℂ (fun s : ℂ => -s) {s : ℂ | 0 < s.re} := differentiableOn_id.neg
    refine (differentiableOn_const _).div hneg fun s hs h0 => ?_
    simp only [Set.mem_setOf_eq] at hs
    simp only [neg_eq_zero] at h0
    rw [h0, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  ·
    intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hint, hZ⟩ := integrableOn_and_zetaIntegral_eq μ hΩ' hΨ hΨc hs
    rw [hZ, hclosed, ENNReal.coe_toReal]
    have hf0 : ∀ y : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F y ≤ c / 2 →
        (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
            ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s) = 0 := by
      intro y hy
      rw [hvanish y (by linarith), zero_mul]
    rw [setIntegral_eq_add_of_forall_eq_zero hf0 (hint.mono_set Set.inter_subset_left)
      (hint.mono_set Set.inter_subset_left)]
    have hsm : (∫ y in Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧
        NumberField.TateGlobal.ideleNorm F y ≤ 1},
          (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
              ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((0 : ℂ) - s) ∂ν) =
        ∫ y in Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧ NumberField.TateGlobal.ideleNorm F y ≤ 1},
          (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
              ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s) ∂ν := by
      simp only [zero_sub]
    have hlg_pt : ∀ y : (AdeleRing (𝓞 F) F)ˣ,
        (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
            ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s) =
          tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s) +
            ((∫ u, Ψ u ∂μ) * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s) -
              Ψ 0 * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s)) := by
      intro y
      have hx : ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (NumberField.TateGlobal.ideleNorm_pos y).ne'
      have hpow : ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s) =
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) *
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s) := by
        rw [sub_eq_add_neg, Complex.cpow_add _ _ hx, Complex.cpow_one]
      rw [hpois y, hpow]
      ring
    have hA : Integrable (fun y => tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) :=
      integrableOn_mul_cpow_of_isDominated hTlN htail_l.aestronglyMeasurable hdom_l hs0
    have hB : Integrable (fun y => (∫ u, Ψ u ∂μ) * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) :=
      (integrableOn_cpow_large_half hshell (by rw [Complex.sub_re, Complex.one_re]; linarith)).const_mul _
    have hC : Integrable (fun y => Ψ 0 * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) :=
      (integrableOn_cpow_large_half hshell (by rw [Complex.neg_re]; linarith)).const_mul _
    have hBC : Integrable (fun y => (∫ u, Ψ u ∂μ) * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - s) -
        Ψ 0 * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-s))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) := hB.sub hC
    rw [integral_congr_ae (μ := ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y}))
        (Filter.Eventually.of_forall hlg_pt),
      integral_add hA hBC, integral_sub hB hC, integral_const_mul, integral_const_mul]
    simp only [hsm]
    rw [setIntegral_cpow_large_half hshell (w := (1 : ℂ) - s) (by rw [Complex.sub_re, Complex.one_re]; linarith),
      setIntegral_cpow_large_half hshell (w := -s) (by rw [Complex.neg_re]; linarith)]
    have hkey : -((c₀ : ℝ) : ℂ) / ((1 : ℂ) - s) = ((c₀ : ℝ) : ℂ) / (s - 1) := by
      rw [neg_div, ← div_neg, neg_sub]
    rw [hkey]
    ring
  ·

    have hT1 : ∀ y ∈ Ω ∩ {y | c / 2 < NumberField.TateGlobal.ideleNorm F y ∧ NumberField.TateGlobal.ideleNorm F y ≤ 1},
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
                ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) -
              (if 1 < NumberField.TateGlobal.ideleNorm F y then
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) =
          (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
              ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) *
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((0 : ℂ) - 1) := by
      intro y hy
      have hy2 : NumberField.TateGlobal.ideleNorm F y ≤ 1 := hy.2.2
      rw [if_neg (not_lt.mpr hy2), sub_zero, zero_sub, Complex.cpow_neg_one]
      exact mul_comm _ _
    have hT2 : ∀ y ∈ Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y},
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
                ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) -
              (if 1 < NumberField.TateGlobal.ideleNorm F y then
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) =
          tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - 1) -
            Ψ 0 * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-1 : ℂ) := by
      intro y hy
      have hy1 : 1 < NumberField.TateGlobal.ideleNorm F y := hy.2
      rw [integrand_eq F μ hμ1 hΨ hΨc 1 y, if_pos hy1, sub_self, Complex.cpow_zero, Complex.cpow_neg_one]
      ring
    have hf0 : ∀ y : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F y ≤ c / 2 →
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
              ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) -
            (if 1 < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) = 0 := by
      intro y hy
      rw [hvanish y (by linarith), if_neg (not_lt.mpr (by linarith)), sub_zero, mul_zero]
    have hA1 : Integrable (fun y => tailSum F μ Ψ y * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ ((1 : ℂ) - 1))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) :=
      integrableOn_mul_cpow_of_isDominated hTlN htail_l.aestronglyMeasurable hdom_l h01
    have hC1 : Integrable (fun y => Ψ 0 * ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ^ (-1 : ℂ))
        (ν.restrict (Ω ∩ {y | 1 < NumberField.TateGlobal.ideleNorm F y})) :=
      (integrableOn_cpow_large_half hshell hneg1).const_mul _
    have h₁ := (integrableOn_mul_cpow_of_isDominated hTsN hSmeas hdom_s h01).congr
      ((ae_restrict_mem₀ hTsN).mono fun y hy => (hT1 y hy).symm)
    have h₂ := (hA1.sub hC1).congr ((ae_restrict_mem₀ hTlN).mono fun y hy => (hT2 y hy).symm)
    rw [setIntegral_eq_add_of_forall_eq_zero hf0 h₁ h₂, integral_congr_ae ((ae_restrict_mem₀ hTsN).mono hT1),
      integral_congr_ae ((ae_restrict_mem₀ hTlN).mono hT2), integral_sub hA1 hC1, integral_const_mul,
      setIntegral_cpow_large_half hshell hneg1]
    ring

section FiniteParts

private theorem localChar_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.TateGlobal.localChar (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) v = 1 := by
  simp [NumberField.TateGlobal.localChar]

private theorem isOpen_rePos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem isOpen_reGtOne : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem isPreconnected_rePos : IsPreconnected {s : ℂ | 0 < s.re} :=
  (convex_halfSpace_re_gt (r := 0)).isPreconnected

private theorem sub_one_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 := by
  intro h0
  have h1 : (s - 1).re = 0 := by rw [h0, Complex.zero_re]
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith

private theorem eqOn_rePos_of_eqOn_reGtOne {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f {s : ℂ | 0 < s.re})
    (hg : DifferentiableOn ℂ g {s : ℂ | 0 < s.re}) (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) :
    Set.EqOn f g {s : ℂ | 0 < s.re} := by
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  refine (hf.analyticOnNhd isOpen_rePos).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd isOpen_rePos)
    isPreconnected_rePos h2 ?_
  refine Filter.eventuallyEq_of_mem (isOpen_reGtOne.mem_nhds ?_) (fun s hs => hfg s hs)
  simp

private theorem eq_div_mul_add_div_mul_of_cross {ℓθ Pθ Dθ rθ ℓ₀ P₀ D₀ r₀ : ℂ} (hP₀ : P₀ ≠ 0)
    (hv : rθ * P₀ = r₀ * Pθ) (hd : ℓθ * P₀ + rθ * D₀ = ℓ₀ * Pθ + r₀ * Dθ) :
    ℓθ = (ℓ₀ - r₀ / P₀ * D₀) / P₀ * Pθ + r₀ / P₀ * Dθ := by
  have h1 : r₀ / P₀ * Pθ = rθ := by
    rw [div_mul_eq_mul_div, ← hv, mul_div_assoc, div_self hP₀, mul_one]
  have h2 : r₀ / P₀ * P₀ = r₀ := div_mul_cancel₀ r₀ hP₀
  have hc₀ : (ℓ₀ - r₀ / P₀ * D₀) / P₀ * P₀ = ℓ₀ - r₀ / P₀ * D₀ := div_mul_cancel₀ _ hP₀
  refine mul_right_cancel₀ hP₀ ?_
  linear_combination hd - Pθ * hc₀ + D₀ * h1 - Dθ * h2

end FiniteParts

private theorem exists_forall_zetaIntegral_mul_tprod_eq_mul_prod_localZeta
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (g : InfiniteAdeleRing F → ℂ) :
    ∃ A : ℂ → ℂ, ∀ (hS : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (Ψ : AdeleRing (𝓞 F) F → ℂ),
      (∀ x, Ψ x = (NumberField.TateGlobal.integralOutside S).indicator
        (fun x => g x.1 * ∏ v ∈ S, hS v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x) →
      Ψ ∈ NumberField.AdelicFourier.schwartzBruhat F → HasCompactSupport Ψ →
      ∀ s : ℂ, 1 < s.re →
        NumberField.TateGlobal.zetaIntegral ν Ψ 1 s *
            ∏' v : {v // v ∉ S}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) =
          A s * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (hS v) 1 s := by

  obtain ⟨A, hA⟩ :=
    NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator F ν S μf
      (fun v => NumberField.AdelicLevel.uniformizerUnit F v)
      (fun v => NumberField.AdelicLevel.valued_uniformizerUnit F v)
  refine ⟨fun s => A g 1 s, fun hS Ψ hΨ _ _ s hs => ?_⟩

  have h1 : ∀ v : HeightOneSpectrum (𝓞 F),
      NumberField.TateGlobal.localChar (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) v = 1 :=
    fun v => MonoidHom.ext fun t => by rw [NumberField.TateGlobal.localChar_apply]; rfl
  have key := hA Ψ g hS hΨ 1 continuous_const (fun x => by simp)
    (fun v _ t _ _ => by rw [h1]; rfl) s hs
  simpa only [h1, MonoidHom.one_apply, Units.val_one, one_mul] using key

private theorem exists_forall_eq_mul_prod_localZeta_add_div_prod_localZeta_mul_sum_deriv_localZeta
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ)
    (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) (hΨc : ∀ θ, HasCompactSupport (Ψ θ))
    (r ℓ : Θ → ℂ)
    (hZ : ∀ θ, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → NumberField.TateGlobal.zetaIntegral ν (Ψ θ) 1 s = E s + r θ / (s - 1)) ∧
      E 1 = ℓ θ)
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₀ : ℂ, ∀ θ : Θ, ℓ θ =
      c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
        r θ₀ / (∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1) *
          ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
            ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := by
  obtain ⟨A, hA⟩ := exists_forall_zetaIntegral_mul_tprod_eq_mul_prod_localZeta F ν S μf g

  obtain ⟨Zd, -, -, -, -, hZd, -⟩ :=
    NumberField.exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul F S
  choose E hE using hZ

  obtain ⟨P, hP⟩ : ∃ P : Θ → ℂ → ℂ,
      P = fun θ s => ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 s := ⟨_, rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : Θ → ℂ, Dv = fun θ =>
      ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
        ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := ⟨_, rfl⟩
  have hPs : ∀ θ (s : ℂ), P θ s = ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 s :=
    fun θ s => by rw [hP]
  have hDvs : ∀ θ, Dv θ =
      ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
        ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 :=
    fun θ => by rw [hDv]
  have h1mem : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hPdiff : ∀ θ, DifferentiableOn ℂ (P θ) {s : ℂ | 0 < s.re} := fun θ => by
    rw [hP]
    exact DifferentiableOn.fun_finsetProd fun i _ => hloc θ i.1 i.2
  have hPderiv : ∀ θ, HasDerivAt (P θ) (Dv θ) 1 := fun θ => by
    rw [hP, hDv]
    refine (HasDerivAt.fun_finsetProd fun i _ =>
      ((hloc θ i.1 i.2).differentiableAt (isOpen_rePos.mem_nhds h1mem)).hasDerivAt).congr_deriv ?_
    beta_reduce
    exact Finset.sum_congr rfl fun p _ => by rw [smul_eq_mul, mul_comm]

  have hsplit : ∀ θ (s : ℂ),
      (∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (if v ∈ T then h θ v else h₀ v) 1 s)
        = (∏ v ∈ S \ T, LanglandsTunnell.TateLocal.localZeta (μf v) (h₀ v) 1 s) * P θ s := fun θ s => by
    rw [← Finset.prod_sdiff hT, hPs,
      Finset.prod_coe_sort T (fun v => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s)]
    congr 1
    · exact Finset.prod_congr rfl fun v hv => by simp only [if_neg (Finset.mem_sdiff.mp hv).2]
    · exact Finset.prod_congr rfl fun v hv => by simp only [if_pos hv]
  have hfact : ∀ θ (s : ℂ), 1 < s.re →
      NumberField.TateGlobal.zetaIntegral ν (Ψ θ) 1 s *
          ∏' v : {v // v ∉ S}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
        = (A s * ∏ v ∈ S \ T, LanglandsTunnell.TateLocal.localZeta (μf v) (h₀ v) 1 s) * P θ s := fun θ s hs => by
    have hr := hA (fun v => if v ∈ T then h θ v else h₀ v) (Ψ θ) (hΨ θ) (hΨs θ) (hΨc θ) s hs
    rw [hsplit] at hr
    exact hr.trans (by ring)

  obtain ⟨Lf, hLf⟩ : ∃ Lf : Θ → ℂ → ℂ, Lf = fun θ s => (s - 1) * E θ s + r θ := ⟨_, rfl⟩
  have hLdiff : ∀ θ, DifferentiableOn ℂ (Lf θ) {s : ℂ | 0 < s.re} := fun θ => by
    rw [hLf]
    exact ((differentiableOn_id.sub_const 1).mul (hE θ).1).add_const (r θ)
  have hL1 : ∀ θ, Lf θ 1 = r θ := fun θ => by rw [hLf]; simp
  have hLderiv : ∀ θ, HasDerivAt (Lf θ) (ℓ θ) 1 := fun θ => by
    rw [hLf]
    have hEd : HasDerivAt (E θ) (deriv (E θ) 1) 1 :=
      ((hE θ).1.differentiableAt (isOpen_rePos.mem_nhds h1mem)).hasDerivAt
    refine ((((hasDerivAt_id' (1 : ℂ)).sub_const 1).mul hEd).add_const (r θ)).congr_deriv ?_
    rw [(hE θ).2.2]
    ring
  have hcross₁ : ∀ θ (s : ℂ), 1 < s.re → Lf θ s * P θ₀ s = Lf θ₀ s * P θ s := fun θ s hs => by
    have hprod : (∏' v : {v // v ∉ S}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) ≠ 0 :=
      right_ne_zero_of_mul_eq_one (hZd s hs).2
    have hZ1 := hfact θ s hs
    have hZ2 := hfact θ₀ s hs
    have hZP : NumberField.TateGlobal.zetaIntegral ν (Ψ θ) 1 s * P θ₀ s =
        NumberField.TateGlobal.zetaIntegral ν (Ψ θ₀) 1 s * P θ s := by
      refine mul_right_cancel₀ hprod ?_
      linear_combination P θ₀ s * hZ1 - P θ s * hZ2
    have hs1 := sub_one_ne_zero_of_one_lt_re hs
    have hL : ∀ θ', Lf θ' s = (s - 1) * NumberField.TateGlobal.zetaIntegral ν (Ψ θ') 1 s := fun θ' => by
      rw [hLf, (hE θ').2.1 s hs, mul_add, mul_div_cancel₀ _ hs1]
    rw [hL θ, hL θ₀]
    linear_combination (s - 1) * hZP
  have hP₀ : P θ₀ 1 ≠ 0 := by rw [hPs]; exact hθ₀

  refine ⟨(ℓ θ₀ - r θ₀ / P θ₀ 1 * Dv θ₀) / P θ₀ 1, fun θ => ?_⟩
  rw [← hPs θ 1, ← hPs θ₀ 1, ← hDvs θ]
  have hEqOn := eqOn_rePos_of_eqOn_reGtOne ((hLdiff θ).mul (hPdiff θ₀)) ((hLdiff θ₀).mul (hPdiff θ)) (hcross₁ θ)
  have hv : r θ * P θ₀ 1 = r θ₀ * P θ 1 := by
    have hv' : Lf θ 1 * P θ₀ 1 = Lf θ₀ 1 * P θ 1 := hEqOn h1mem
    rwa [hL1, hL1] at hv'
  have hdf : HasDerivAt (fun s => Lf θ s * P θ₀ s) (ℓ θ * P θ₀ 1 + r θ * Dv θ₀) 1 := by
    have hm := (hLderiv θ).mul (hPderiv θ₀)
    rwa [hL1] at hm
  have hdg : HasDerivAt (fun s => Lf θ₀ s * P θ s) (ℓ θ₀ * P θ 1 + r θ₀ * Dv θ) 1 := by
    have hm := (hLderiv θ₀).mul (hPderiv θ)
    rwa [hL1] at hm
  have hd : ℓ θ * P θ₀ 1 + r θ * Dv θ₀ = ℓ θ₀ * P θ 1 + r θ₀ * Dv θ := by
    rw [← hdf.deriv, ← hdg.deriv]
    exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_rePos.mem_nhds h1mem) hEqOn)
  exact eq_div_mul_add_div_mul_of_cross hP₀ hv hd

private theorem exists_forall_eq_mul_prod_localZeta_add_mul_sum_deriv_localZeta
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ)
    (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) (hΨc : ∀ θ, HasCompactSupport (Ψ θ))
    (r ℓ : Θ → ℂ)
    (hZ : ∀ θ, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → NumberField.TateGlobal.zetaIntegral ν (Ψ θ) 1 s = E s + r θ / (s - 1)) ∧
      E 1 = ℓ θ)
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₀ c₁ : ℂ, ∀ θ : Θ, ℓ θ =
      c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
        c₁ * ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
          ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := by
  obtain ⟨c₀, hc⟩ :=
    exists_forall_eq_mul_prod_localZeta_add_div_prod_localZeta_mul_sum_deriv_localZeta
      F ν S μf T hT g h₀ Θ h Ψ hΨ hΨs hΨc r ℓ hZ hloc θ₀ hθ₀
  exact ⟨c₀, _, hc⟩

private theorem setIntegral_finsum_sub_indicator_sub_eq_mul_log_sub_log
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (Ψ : AdeleRing (𝓞 F) F → ℂ) (hΨ : Ψ ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (hΨc : HasCompactSupport Ψ) :
    (∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0))) Ω ν) ∧
    ∀ X₁ X₂ : ℝ, 0 < X₁ → X₁ ≤ X₂ →
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X₂ < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) ∂ν) -
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X₁ < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ u ∂μ) * ((Real.log X₂ - Real.log X₁ : ℝ) : ℂ) := by
  classical
  have hΩ' : IsFundamentalDomain (ShellMass.principalRange F) Ω ν := hΩ
  obtain ⟨c₀, hshell, hclosed⟩ := exists_shell_constant F hΩ'
  obtain ⟨U₀, hU₀⟩ := exists_forall_apply_eq_zero_of_lt_ideleNorm F μ hμ1 hΨc

  have hc : (0 : ℝ) < (max U₀ 1)⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hvanish : ∀ y : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹ →
      (∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
        ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) = 0 := by
    intro y hy
    refine finsum_eq_zero_of_forall_eq_zero fun η => ?_
    have h : U₀ < NumberField.TateGlobal.ideleNorm F
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) η * y⁻¹) := by
      rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_unitsMap, one_mul, ideleNorm_inv']
      calc U₀ ≤ max U₀ 1 := le_max_left _ _
        _ = ((max U₀ 1)⁻¹)⁻¹ := (inv_inv _).symm
        _ < (NumberField.TateGlobal.ideleNorm F y)⁻¹ :=
            inv_strictAnti₀ (NumberField.TateGlobal.ideleNorm_pos y) hy
    have h0 := hU₀ _ h
    simpa [Units.coe_map] using h0

  have hint : ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0))) Ω ν := by
    intro X hX

    have hA : IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)))
        (Ω ∩ {y | (max U₀ 1)⁻¹ / 2 < NumberField.TateGlobal.ideleNorm F y}) ν := by
      have hfun : (fun y : (AdeleRing (𝓞 F) F)ˣ =>
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
                AdeleRing (𝓞 F) F))) -
              (if X < NumberField.TateGlobal.ideleNorm F y then
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0))) =
          fun y => tailSum F μ Ψ y + (if X < NumberField.TateGlobal.ideleNorm F y then 0 else ∫ u, Ψ u ∂μ) -
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ * Ψ 0 :=
        funext fun y => integrand_eq F μ hμ1 hΨ hΨc X y
      rw [hfun]
      refine ((integrableOn_tailSum F μ hΩ' hΨ (half_pos hc)).add ?_).sub ?_
      · have hite : (fun y : (AdeleRing (𝓞 F) F)ˣ =>
            if X < NumberField.TateGlobal.ideleNorm F y then (0 : ℂ) else ∫ u, Ψ u ∂μ) =
            {y : (AdeleRing (𝓞 F) F)ˣ | NumberField.TateGlobal.ideleNorm F y ≤ X}.indicator fun _ => ∫ u, Ψ u ∂μ := by
          funext y
          by_cases h : X < NumberField.TateGlobal.ideleNorm F y
          · rw [if_pos h, Set.indicator_of_notMem (by rw [Set.mem_setOf_eq]; exact not_le.mpr h)]
          · rw [if_neg h, Set.indicator_of_mem (by rw [Set.mem_setOf_eq]; exact not_lt.mp h)]
        rw [hite]
        refine integrableOn_indicator_const F (measurableSet_ideleNorm_le F X) ?_ _
        refine ne_top_of_le_ne_top (measure_inter_shell_ne_top F hΩ' (half_pos hc) X) (measure_mono ?_)
        rintro y ⟨hyX, hyΩ, hyc⟩
        exact ⟨hyΩ, hyc, hyX⟩
      · have h := (integrableOn_inv_ideleNorm F hΩ' (half_pos hc)).ofReal.mul_const (Ψ 0)
        refine h.congr (Filter.Eventually.of_forall fun y => ?_)
        exact congrArg (· * Ψ 0) (Complex.ofReal_inv (NumberField.TateGlobal.ideleNorm F y))

    have hV : IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)))
        (Ω ∩ {y | NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹}) ν := by
      have hfun : ∀ y ∈ Ω ∩ {y | NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹},
          {y : (AdeleRing (𝓞 F) F)ˣ | X < NumberField.TateGlobal.ideleNorm F y}.indicator
              (fun _ => -∫ u, Ψ u ∂μ) y =
            ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
              ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
                  AdeleRing (𝓞 F) F))) -
                (if X < NumberField.TateGlobal.ideleNorm F y then
                  ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) := by
        rintro y ⟨-, hy⟩
        rw [Set.mem_setOf_eq] at hy
        have hy0 : ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (NumberField.TateGlobal.ideleNorm_pos y).ne'
        rw [hvanish y hy, zero_sub]
        by_cases h : X < NumberField.TateGlobal.ideleNorm F y
        · rw [if_pos h, Set.indicator_of_mem (by rw [Set.mem_setOf_eq]; exact h), mul_neg, ← mul_assoc,
            inv_mul_cancel₀ hy0, one_mul]
        · rw [if_neg h, Set.indicator_of_notMem (by rw [Set.mem_setOf_eq]; exact h), neg_zero, mul_zero]
      have hnm : NullMeasurableSet (Ω ∩ {y | NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹}) ν :=
        hΩ'.nullMeasurableSet.inter
          (measurableSet_lt (NumberField.TateGlobal.continuous_ideleNorm F).measurable
            measurable_const).nullMeasurableSet
      have hfin : ν ({y : (AdeleRing (𝓞 F) F)ˣ | X < NumberField.TateGlobal.ideleNorm F y} ∩
          (Ω ∩ {y | NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹})) ≠ ⊤ := by
        refine ne_top_of_le_ne_top (measure_inter_shell_ne_top F hΩ' hX (max U₀ 1)⁻¹) (measure_mono ?_)
        rintro y ⟨hyX, hyΩ, hyc⟩
        exact ⟨hyΩ, hyX, le_of_lt hyc⟩
      exact (integrableOn_indicator_const F (measurableSet_lt_ideleNorm F X) hfin _).congr
        ((ae_restrict_mem₀ hnm).mono fun y hy => hfun y hy)
    refine (hA.union hV).mono_set fun y hy => ?_
    by_cases h : NumberField.TateGlobal.ideleNorm F y < (max U₀ 1)⁻¹
    · exact Or.inr ⟨hy, h⟩
    · exact Or.inl ⟨hy, lt_of_lt_of_le (half_lt_self hc) (not_lt.mp h)⟩
  refine ⟨hint, fun X₁ X₂ hX₁ hX₁₂ => ?_⟩

  have hX₂ : 0 < X₂ := lt_of_lt_of_le hX₁ hX₁₂
  rw [← integral_sub (hint X₂ hX₂) (hint X₁ hX₁)]
  have hpt : ∀ y : (AdeleRing (𝓞 F) F)ˣ,
      ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X₂ < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) -
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X₁ < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ u ∂μ else 0)) =
      {y : (AdeleRing (𝓞 F) F)ˣ | X₁ < NumberField.TateGlobal.ideleNorm F y ∧
          NumberField.TateGlobal.ideleNorm F y ≤ X₂}.indicator (fun _ => ∫ u, Ψ u ∂μ) y := by
    intro y
    have hy0 : ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NumberField.TateGlobal.ideleNorm_pos y).ne'
    have h1 : ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hy0
    by_cases h2 : X₂ < NumberField.TateGlobal.ideleNorm F y
    · have h1' : X₁ < NumberField.TateGlobal.ideleNorm F y := lt_of_le_of_lt hX₁₂ h2
      rw [if_pos h2, if_pos h1', Set.indicator_of_notMem (fun hmem => absurd h2 (not_lt.mpr hmem.2))]
      ring
    · by_cases h1'' : X₁ < NumberField.TateGlobal.ideleNorm F y
      · rw [if_neg h2, if_pos h1'', Set.indicator_of_mem (by rw [Set.mem_setOf_eq]; exact ⟨h1'', not_lt.mp h2⟩)]
        linear_combination (∫ u, Ψ u ∂μ) * h1
      · rw [if_neg h2, if_neg h1'', Set.indicator_of_notMem (fun hmem => h1'' hmem.1)]
        ring
  have hmeas : MeasurableSet {y : (AdeleRing (𝓞 F) F)ˣ | X₁ < NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ X₂} :=
    (measurableSet_lt_ideleNorm F X₁).inter (measurableSet_ideleNorm_le F X₂)
  refine (integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y)).trans ?_
  rw [integral_indicator_const _ hmeas, measureReal_def, Measure.restrict_apply hmeas, Complex.real_smul]
  rcases hX₁₂.eq_or_lt with rfl | hlt
  · have hempty : {y : (AdeleRing (𝓞 F) F)ˣ | X₁ < NumberField.TateGlobal.ideleNorm F y ∧
        NumberField.TateGlobal.ideleNorm F y ≤ X₁} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y ⟨ha, hb⟩ => absurd hb (not_le.mpr ha)
    rw [hempty, Set.empty_inter, measure_empty, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul, sub_self,
      Complex.ofReal_zero, mul_zero]
  · rw [Set.inter_comm, hshell X₁ X₂ hX₁ hlt, hclosed, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log hX₁ hlt.le))]
    push_cast
    ring

private theorem integral_monoidHom_eq_zero_of_ne_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (χ : G →* ℂˣ) (hχ : Continuous χ) (h1 : χ ≠ 1) :
    ∫ g, ((χ g : ℂˣ) : ℂ) ∂μ = 0 := by
  have _ := hχ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, χ g₀ ≠ 1 := by
    by_contra h
    exact h1 (MonoidHom.ext fun g => (of_not_not (not_exists.mp h g)).trans (MonoidHom.one_apply g).symm)
  have hg₀' : ((χ g₀ : ℂˣ) : ℂ) ≠ 1 := fun h => hg₀ (Units.val_eq_one.mp h)
  have hinv : ∫ g, ((χ (g₀ * g) : ℂˣ) : ℂ) ∂μ = ∫ g, ((χ g : ℂˣ) : ℂ) ∂μ :=
    integral_mul_left_eq_self (fun g => ((χ g : ℂˣ) : ℂ)) g₀
  simp only [map_mul, Units.val_mul, integral_const_mul] at hinv
  have h : (((χ g₀ : ℂˣ) : ℂ) - 1) * ∫ g, ((χ g : ℂˣ) : ℂ) ∂μ = 0 := by
    rw [sub_mul, one_mul, hinv, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hg₀')

private theorem exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ)
    (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) (hΨc : ∀ θ, HasCompactSupport (Ψ θ))
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₀ c₁ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0))) Ω ν ∧
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ θ u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          c₁ * (∫ u, Ψ θ₀ u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1) := by

  have hb0 := fun θ =>
    setIntegral_finsum_sub_indicator_sub_eq_mul_log_sub_log F μ hμ1 ν Ω hΩ (Ψ θ) (hΨs θ) (hΨc θ)
  obtain ⟨c₀, hc⟩ := exists_forall_eq_mul_prod_localZeta_add_div_prod_localZeta_mul_sum_deriv_localZeta F ν S μf T hT
    g h₀ Θ h Ψ hΨ hΨs hΨc
    (fun θ => ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) * ∫ u, Ψ θ u ∂μ)
    (fun θ => ∫ y in Ω,
          ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
                AdeleRing (𝓞 F) F))) -
              (if 1 < NumberField.TateGlobal.ideleNorm F y then
                ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν)
    (fun θ => exists_differentiableOn_zetaIntegral_eq_add_div F μ hμ1 ν Ω hΩ (Ψ θ) (hΨs θ) (hΨc θ)) hloc θ₀ hθ₀
  refine ⟨c₀, ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
      NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) /
    ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1, fun θ X hX => ⟨(hb0 θ).1 X hX, ?_⟩⟩
  have hℓ :
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if 1 < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν) =
        c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
                NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) * (∫ u, Ψ θ₀ u ∂μ) /
              (∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 := hc θ
  rcases le_total 1 X with h1X | hX1
  · have h2 := (hb0 θ).2 1 X one_pos h1X
    rw [Real.log_one, sub_zero] at h2
    linear_combination h2 + hℓ
  · have h2 := (hb0 θ).2 X 1 hX hX1
    rw [Real.log_one, zero_sub, Complex.ofReal_neg] at h2
    linear_combination -h2 + hℓ

end TwistedUnipotentTerm

theorem solution
    (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (hμ1 : μ (NumberField.AdelicBox.adelicBox F) = 1)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T ⊆ S)
    (g : InfiniteAdeleRing F → ℂ)
    (h₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Θ : Type) (h : Θ → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Ψ : Θ → AdeleRing (𝓞 F) F → ℂ)
    (hΨ : ∀ θ x, Ψ θ x = (NumberField.TateGlobal.integralOutside S).indicator
      (fun x => g x.1 * ∏ v ∈ S, (if v ∈ T then h θ v else h₀ v) ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
    (hΨs : ∀ θ, Ψ θ ∈ NumberField.AdelicFourier.schwartzBruhat F) (hΨc : ∀ θ, HasCompactSupport (Ψ θ))
    (hloc : ∀ θ, ∀ v ∈ T, DifferentiableOn ℂ
      (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf v) (h θ v) 1 s) {s : ℂ | 0 < s.re})
    (θ₀ : Θ) (hθ₀ : ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ₀ i) 1 1 ≠ 0) :
    ∃ c₀ c₁ : ℂ, ∀ θ : Θ, ∀ X : ℝ, 0 < X →
      IntegrableOn (fun y : (AdeleRing (𝓞 F) F)ˣ =>
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0))) Ω ν ∧
      (∫ y in Ω,
        ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ)⁻¹ *
          ((∑ᶠ η : Fˣ, Ψ θ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
              AdeleRing (𝓞 F) F))) -
            (if X < NumberField.TateGlobal.ideleNorm F y then
              ((NumberField.TateGlobal.ideleNorm F y : ℝ) : ℂ) * ∫ u, Ψ θ u ∂μ else 0)) ∂ν) =
        ((ν (Ω ∩ {y | 1 ≤ NumberField.TateGlobal.ideleNorm F y ∧
            NumberField.TateGlobal.ideleNorm F y ≤ Real.exp 1})).toReal : ℂ) *
          (∫ u, Ψ θ u ∂μ) * (Real.log X : ℂ) +
        (c₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1 +
          c₁ * (∫ u, Ψ θ₀ u ∂μ) *
            ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p) (h θ p) 1 s) 1 *
              ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i) (h θ i) 1 1)  :=
  TwistedUnipotentTerm.exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
    F μ hμ1 ν Ω hΩ S μf T hT g h₀ Θ h Ψ hΨ hΨs hΨc hloc θ₀ hθ₀

#print axioms TwistedUnipotentTerm.exists_forall_zetaIntegral_mul_tprod_eq_mul_prod_localZeta
#print axioms solution

end S_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator
end P2MW
export P2MW.S_TwistedUnipotentTerm_exists_forall_integrableOn_and_setIntegral_finsum_sub_indicator_eq_mul_log_add_of_eq_indicator (solution)
