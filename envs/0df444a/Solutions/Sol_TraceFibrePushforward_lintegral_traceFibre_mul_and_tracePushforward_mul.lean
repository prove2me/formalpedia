-- Prove2me | solution 1 for TraceFibrePushforward.lintegral_traceFibre_mul_and_tracePushforward_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/357c2ef4-2b6e-57f7-92df-3963d35ff128

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
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal NNReal TensorProduct Pointwise

namespace AdelicTraceCoordinates

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

section BaseChangeCoordinates

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end BaseChangeCoordinates

end

end AdelicTraceCoordinates

namespace AdelicTracePushforward

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private noncomputable def piSMulEquiv {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (ι : Type*) (g : G) :
    (ι → A) ≃ᵐ (ι → A) where
  toEquiv := MulAction.toPerm g
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (continuous_const_smul g).measurable.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (continuous_const_smul g⁻¹).measurable.comp (measurable_pi_apply i)

private theorem map_smul_pi_eq_smul_pi {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ι : Type*) [Fintype ι] (g : G) :
    Measure.map (fun w : ι → A => fun i => g • w i) (Measure.pi fun _ : ι => μ) =
      ((distribHaarChar A g : ℝ≥0∞)⁻¹ ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  have h0 : (distribHaarChar A g : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
  have ht : (distribHaarChar A g : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hpre : ∀ s : ι → Set A,
      (fun w : ι → A => fun i => g • w i) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => g⁻¹ • s i := by
    intro s
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  have hmeas : Measurable fun w : ι → A => fun i => g • w i := (piSMulEquiv ι g).measurable
  have key : Measure.pi (fun _ : ι => μ) =
      ((distribHaarChar A g : ℝ≥0∞) ^ Fintype.card ι) •
        Measure.map (fun w : ι → A => fun i => g • w i) (Measure.pi fun _ : ι => μ) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre,
      Measure.pi_pi]
    simp_rw [← distribHaarChar_mul μ g⁻¹]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_inv, ENNReal.coe_inv
      distribHaarChar_pos.ne', ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 ht, one_pow, one_mul]
  conv_rhs => rw [key]
  rw [smul_smul, ← mul_pow, ENNReal.inv_mul_cancel h0 ht, one_pow, one_smul]

private theorem lintegral_comp_smul_pi {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ι : Type*) [Fintype ι] (g : G) (F : (ι → A) → ℝ≥0∞) :
    ∫⁻ w, F (fun i => g • w i) ∂(Measure.pi fun _ : ι => μ) =
      ((distribHaarChar A g : ℝ≥0∞)⁻¹ ^ Fintype.card ι) * ∫⁻ w, F w ∂(Measure.pi fun _ : ι => μ) := by
  calc ∫⁻ w, F (fun i => g • w i) ∂(Measure.pi fun _ : ι => μ)
      = ∫⁻ w, F w ∂(Measure.map (piSMulEquiv ι g) (Measure.pi fun _ : ι => μ)) :=
        (lintegral_map_equiv F (piSMulEquiv ι g)).symm
    _ = _ := by
        rw [show ((piSMulEquiv ι g : (ι → A) ≃ᵐ (ι → A)) : (ι → A) → ι → A) = fun w i => g • w i from rfl,
          map_smul_pi_eq_smul_pi μ ι g, lintegral_smul_measure, smul_eq_mul]

private theorem integral_comp_smul_pi {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ι : Type*) [Fintype ι] (g : G) (F : (ι → A) → ℂ) :
    ∫ w, F (fun i => g • w i) ∂(Measure.pi fun _ : ι => μ) =
      ((((distribHaarChar A g : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) *
        ∫ w, F w ∂(Measure.pi fun _ : ι => μ) := by
  have h : ∫ w, F w ∂(Measure.map (fun w : ι → A => fun i => g • w i) (Measure.pi fun _ : ι => μ)) =
      ∫ w, F (fun i => g • w i) ∂(Measure.pi fun _ : ι => μ) := by
    rw [show (fun w : ι → A => fun i => g • w i) = piSMulEquiv ι g from rfl]
    exact integral_map_equiv (piSMulEquiv ι g) F
  rw [← h, map_smul_pi_eq_smul_pi μ ι g, integral_smul_measure]
  refine Complex.real_smul.trans ?_
  exact congrArg (fun r : ℝ => (r : ℂ) * ∫ w, F w ∂(Measure.pi fun _ : ι => μ))
    (by rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal, inv_pow])

section AdeleProjections

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

end AdeleProjections

section MeasureSplitting

open MeasureTheory
open scoped NNReal
section Factors

end Factors

section Coordinates

variable {G₁ G₂ ι : Type} [TopologicalSpace G₁] [TopologicalSpace G₂]

end Coordinates

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  [LocallyCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂]
  [MeasurableSpace G₂] [BorelSpace G₂] [SecondCountableTopology (G₁ × G₂)]
  {ι : Type} [Fintype ι]

section Ambient

variable [mP : MeasurableSpace (G₁ × G₂)] [BorelSpace (G₁ × G₂)] (μ : Measure (G₁ × G₂)) [μ.IsAddHaarMeasure]

end Ambient

end MeasureSplitting
section ProperSlices

open MeasureTheory
section Slices

variable {X Y Y' : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y']
  {Ψ : X × Y → Y'} (hΨ : Continuous Ψ) (hprop : ∀ C : Set Y', IsCompact C → IsCompact {p : X × Y | Ψ p ∈ C})

end Slices

section Sums

variable {X ι : Type} [TopologicalSpace X] [T2Space X]

end Sums

end ProperSlices
section FibreIntegrals

open MeasureTheory Set
open scoped Topology

section Smooth

variable {V V' W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [MeasurableSpace W] [OpensMeasurableSpace W]
  {μ : Measure W} [IsFiniteMeasureOnCompacts μ]
  (A : V →L[ℝ] V') {B : W → V'} (hB : Continuous B)
  (hAB : ∀ C : Set V', IsCompact C → IsCompact {p : V × W | A p.1 + B p.2 ∈ C})

end Smooth

section LocallyConstant

variable {X Y E : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [MeasurableSpace Y]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E] (ν : Measure Y)

end LocallyConstant

end FibreIntegrals

section SchwartzBruhatClass

open scoped Classical

section AdeleComponents

variable {F : Type} [Field F] [NumberField F]

end AdeleComponents

end SchwartzBruhatClass

section SchwartzBruhatSums

open scoped Classical

end SchwartzBruhatSums

namespace ArchSplit

end ArchSplit

section ProductFormula

section LocalTraceIntegers

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end LocalTraceIntegers

end ProductFormula

section Factorization

open scoped Classical NumberField.LiesOver

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

end Factorization

section FactorizationFinite

open scoped Classical TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

end FactorizationFinite

private theorem lintegral_traceFibre_mul_and_tracePushforward_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (∀ (G : AdeleRing (𝓞 L) L → ℝ≥0∞) (r : AdeleRing (𝓞 K) K),
      ∫⁻ w, G (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * traceFibre K L r w)
          ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) =
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹) *
          ∫⁻ w, G (traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)) ∧
    (∀ (F : AdeleRing (𝓞 L) L → ℂ) (r : AdeleRing (𝓞 K) K),
      tracePushforward K L (fun x => F (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * x)) r =
        (((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹ : ℝ) : ℂ) *
          tracePushforward K L F ((a : AdeleRing (𝓞 K) K) * r)) := by
  classical
  haveI : ContinuousConstSMul (AdeleRing (𝓞 K) K)ˣ (AdeleRing (𝓞 K) K) :=
    ⟨fun u => (continuous_const.mul continuous_id : Continuous fun x : AdeleRing (𝓞 K) K => (u : AdeleRing (𝓞 K) K) *
          x)⟩
  haveI : (adelicAddHaar (𝓞 K) K).Regular := by
    delta NumberField.AdelicHaar.adelicAddHaar MeasureTheory.Measure.addHaar
    infer_instance
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hm : Module.finrank K (LinearMap.ker (Algebra.trace K L)) = Module.finrank K L - 1 := by
    have hr : LinearMap.range (Algebra.trace K L) = ⊤ := LinearMap.range_eq_top.mpr fun k =>
      ⟨algebraMap K L (k / Module.finrank K L), by
        rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ k hn]⟩
    have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have hcard : Fintype.card (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) = Module.finrank K L - 1 := by
    rw [Fintype.card_fin, hm]
  have hT : ∀ (r : AdeleRing (𝓞 K) K)
      (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
      M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * traceFibre K L r w =
        traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) (fun i => a • w i) := by
    intro r w
    simp only [traceFibre, mul_add, Finset.mul_sum, map_mul, mul_assoc, Units.smul_def, smul_eq_mul]
  have hΔ : (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = NumberField.TateGlobal.ideleNorm K a := rfl
  refine ⟨fun G r => ?_, fun F r => ?_⟩
  · simp_rw [hT]
    rw [lintegral_comp_smul_pi (adelicAddHaar (𝓞 K) K) _ a fun w => G (traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) w),
      hcard]
    congr 1
    rw [← hΔ, ← NNReal.coe_pow, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_inv (pow_ne_zero _ distribHaarChar_pos.ne'), ENNReal.coe_pow, ← ENNReal.inv_pow]
  · simp only [tracePushforward]
    simp_rw [hT]
    rw [integral_comp_smul_pi (adelicAddHaar (𝓞 K) K) _ a fun w => F (traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) w),
      hcard, hΔ]

end

end AdelicTracePushforward

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (∀ (G : AdeleRing (𝓞 L) L → ℝ≥0∞) (r : AdeleRing (𝓞 K) K),
      ∫⁻ w, G (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * traceFibre K L r w)
          ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) =
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹) *
          ∫⁻ w, G (traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)) ∧
    (∀ (F : AdeleRing (𝓞 L) L → ℂ) (r : AdeleRing (𝓞 K) K),
      tracePushforward K L (fun x => F (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * x)) r =
        (((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹ : ℝ) : ℂ) *
          tracePushforward K L F ((a : AdeleRing (𝓞 K) K) * r)) :=
  AdelicTracePushforward.lintegral_traceFibre_mul_and_tracePushforward_mul K L a

#print axioms solution

end S_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul
end P2MW
export P2MW.S_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul (solution)
