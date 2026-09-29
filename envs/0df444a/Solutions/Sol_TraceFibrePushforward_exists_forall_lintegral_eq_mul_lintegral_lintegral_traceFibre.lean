-- Prove2me | solution 1 for TraceFibrePushforward.exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c5a5845e-a9ae-5940-9083-e74485e6222f

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
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TraceFibrePushforward_exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

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

private theorem genuineTensorEquiv_tmul (w : AdeleRing (𝓞 K) K) (l : L) :
    M4aHerbrand.Bridge.genuineTensorEquiv K L (w ⊗ₜ[K] l) =
      M4aHerbrand.Bridge.genuineβ K L w * algebraMap L (AdeleRing (𝓞 L) L) l := by
  have h : (w ⊗ₜ[K] l : AdeleRing (𝓞 K) K ⊗[K] L) = (w ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]

private theorem sum_eq_genuineTensorEquiv {ι : Type} [Fintype ι] (c : ι → L) (w : ι → AdeleRing (𝓞 K) K) :
    (∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (c i)) =
      M4aHerbrand.Bridge.genuineTensorEquiv K L (∑ i, w i ⊗ₜ[K] c i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (genuineTensorEquiv_tmul K L (w i) (c i)).symm

end BaseChangeCoordinates

private theorem act_sum_mul_algebraMap_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) (w : ι → AdeleRing (𝓞 K) K) :
    D.act g
        (∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i)) =
      ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (g (b i)) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act, sum_eq_genuineTensorEquiv K L (fun i => b i) w,
    sum_eq_genuineTensorEquiv K L (fun i => g (b i)) w]
  show M4aHerbrand.Bridge.genuineTensorEquiv K L
      ((Algebra.TensorProduct.congr AlgEquiv.refl g) ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm
        (M4aHerbrand.Bridge.genuineTensorEquiv K L (∑ i, w i ⊗ₜ[K] b i)))) = _
  rw [AlgEquiv.symm_apply_apply]
  congr 1
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom,
      AlgHom.id_apply, AlgEquiv.coe_algHom]

private theorem exists_continuousAddEquiv_pi_map_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K L) :
    ∃ e : (ι → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ w : ι → AdeleRing (𝓞 K) K,
        e w = ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i)) ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        Measure.map e (Measure.pi fun _ : ι => adelicAddHaar (𝓞 K) K) = c • adelicAddHaar (𝓞 L) L := by
  classical
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L (M4aHerbrand.Bridge.continuous_genuineβ K L)
      (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 L) L

  let bL : Module.Basis ι (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) b).map (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  let eL : (ι → AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L := bL.equivFun.symm
  have heL : ∀ w : ι → AdeleRing (𝓞 K) K,
      eL w = ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i) := by
    intro w
    simp only [eL, bL, Module.Basis.equivFun_symm_apply, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Algebra.TensorProduct.basis_apply, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let e : (ι → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L :=
    { eL.toAddEquiv with continuous_toFun := hc₁, continuous_invFun := hc₂ }
  refine ⟨e, fun w => heL w, ?_⟩

  refine ⟨(Measure.addHaarScalarFactor (Measure.map e (Measure.pi fun _ : ι => adelicAddHaar (𝓞 K) K))
      (adelicAddHaar (𝓞 L) L) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  · rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul _ _

end

end AdelicTraceCoordinates

namespace AdelicTracePushforward

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem genuineTensorEquiv_tmul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : AdeleRing (𝓞 K) K) (l : L) :
    M4aHerbrand.Bridge.genuineTensorEquiv K L (w ⊗ₜ[K] l) =
      M4aHerbrand.Bridge.genuineβ K L w * algebraMap L (AdeleRing (𝓞 L) L) l := by
  have h : (w ⊗ₜ[K] l : AdeleRing (𝓞 K) K ⊗[K] L) = (w ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]

private theorem lintegral_pi_succ {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m : ℕ)
    {H : (Fin (m + 1) → α) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ w, H w ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
      ∫⁻ r, ∫⁻ w, H (Fin.cons r w) ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
  rw [← hmp.lintegral_comp hH,
    lintegral_prod (fun p : α × (Fin m → α) => H ((MeasurableEquiv.piFinSuccAbove (fun _ => α) 0).symm p))
      (hH.comp hmp.measurable).aemeasurable]
  refine lintegral_congr fun r => lintegral_congr fun w => ?_
  congr 1
  exact Fin.insertNth_zero' r w

private theorem integral_pi_succ {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m : ℕ)
    {H : (Fin (m + 1) → α) → ℂ} (hH : Integrable H (Measure.pi fun _ : Fin (m + 1) => μ)) :
    Integrable (fun r => ∫ w, H (Fin.cons r w) ∂(Measure.pi fun _ : Fin m => μ)) μ ∧
    ∫ w, H w ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
      ∫ r, ∫ w, H (Fin.cons r w) ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
  have hH' : Integrable (fun p : α × (Fin m → α) => H (Fin.cons p.1 p.2))
      (μ.prod (Measure.pi fun _ : Fin m => μ)) := by
    have h := hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hH
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    show H _ = H _
    congr 1
    exact Fin.insertNth_zero' p.1 p.2
  refine ⟨hH'.integral_prod_left, ?_⟩
  rw [← integral_prod _ hH', ← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show H _ = H _
  congr 1
  exact Fin.insertNth_zero' p.1 p.2

private theorem exists_eq_smul_of_isAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧ μ' = a • μ :=
  ⟨μ'.addHaarScalarFactor μ, by exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ).ne',
    ENNReal.coe_ne_top, by rw [← ENNReal.smul_def]; exact Measure.isAddLeftInvariant_eq_smul μ' μ⟩

private theorem integral_smul_measure_complex {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ≥0∞)
    (f : α → ℂ) : ∫ x, f x ∂(c • μ) = (c.toReal : ℂ) * ∫ x, f x ∂μ :=
  (integral_smul_measure f c).trans Complex.real_smul

private theorem mul_mul_eq_mul_inv_mul {a c k J : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ∞) :
    a * (c * J) = a * c * k⁻¹ * (k * J) := by
  rw [show a * c * k⁻¹ * (k * J) = a * (c * J) * (k⁻¹ * k) by ring, ENNReal.inv_mul_cancel hk0 hkt, mul_one]

section AdeleProjections

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

end AdeleProjections

private theorem exists_traceCoords (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ e : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        e (Fin.cons r w) = traceFibre K L r w) ∧
      (∀ (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) (r : AdeleRing (𝓞 K) K)
        (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        D.act g (e (Fin.cons r w)) =
          M4aHerbrand.Bridge.genuineβ K L r * algebraMap L (AdeleRing (𝓞 L) L) (Module.finrank K L : L)⁻¹ +
            ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) *
              algebraMap L (AdeleRing (𝓞 L) L) (g (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i))) ∧
      (∀ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
        e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j)) =
          algebraMap L (AdeleRing (𝓞 L) L)
            (k 0 • (Module.finrank K L : L)⁻¹ + ∑ i, k (Fin.succ i) • (Module.finBasis K (LinearMap.ker
                  (Algebra.trace K L)) i : L))) ∧
      (∀ l : L, ∃ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
        algebraMap L (AdeleRing (𝓞 L) L) l = e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j))) ∧
      ∃ c₁ : ℝ≥0∞, c₁ ≠ 0 ∧ c₁ ≠ ∞ ∧
        Measure.map e (Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
              adelicAddHaar (𝓞 K) K) =
          c₁ • adelicAddHaar (𝓞 L) L := by
  classical

  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have h1 : Algebra.trace K L (Module.finrank K L : L)⁻¹ = 1 := by
    rw [show ((Module.finrank K L : L))⁻¹ = algebraMap K L ((Module.finrank K L : K)⁻¹) by
        rw [map_inv₀, map_natCast],
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hm : Module.finrank K (LinearMap.ker (Algebra.trace K L)) = Module.finrank K L - 1 := by
    have hr : LinearMap.range (Algebra.trace K L) = ⊤ := LinearMap.range_eq_top.mpr fun k =>
      ⟨algebraMap K L (k / Module.finrank K L), by
        rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ k hn]⟩
    have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have hli : LinearIndependent K
      (Fin.cons ((Module.finrank K L : L))⁻¹ (fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) :
        Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → L) := by
    refine linearIndependent_finCons.mpr ⟨?_, fun hmem => ?_⟩
    · exact (Module.finBasis K (LinearMap.ker (Algebra.trace K L))).linearIndependent.map'
        (LinearMap.ker (Algebra.trace K L)).subtype (Submodule.ker_subtype _)
    · have hle : Submodule.span K (Set.range fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) ≤
          LinearMap.ker (Algebra.trace K L) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K
              L)) i).2)
      have h0 := LinearMap.mem_ker.mp (hle hmem)
      rw [h1] at h0
      exact one_ne_zero h0
  have hcard : Fintype.card (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1)) = Module.finrank K L := by
    rw [Fintype.card_fin, hm]
    have : 0 < Module.finrank K L := Module.finrank_pos
    omega
  have hb := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  obtain ⟨e, he, c₁, hc₁0, hc₁t, hmap⟩ := AdelicTraceCoordinates.exists_continuousAddEquiv_pi_map_eq_smul K L
    (basisOfLinearIndependentOfCardEqFinrank hli hcard)
  have hek : ∀ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
      e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j)) =
        algebraMap L (AdeleRing (𝓞 L) L) (∑ j, k j • basisOfLinearIndependentOfCardEqFinrank hli hcard j) := by
    intro k
    rw [he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M4aHerbrand.Bridge.genuineβ_compat, Algebra.smul_def, map_mul]
  refine ⟨e, fun r w => ?_, fun D g r w => ?_, fun k => ?_, fun l => ?_, c₁, hc₁0, hc₁t, hmap⟩
  · rw [he, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ, traceFibre]
  · rw [he, AdelicTraceCoordinates.act_sum_mul_algebraMap_eq, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ, map_inv₀, map_natCast]
  · rw [hek, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ]
  · refine ⟨(basisOfLinearIndependentOfCardEqFinrank hli hcard).equivFun l, ?_⟩
    rw [hek]
    simp only [Module.Basis.equivFun_apply, Module.Basis.sum_repr]

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

private theorem exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (μL : Measure (AdeleRing (𝓞 L) L)) [μL.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, Measurable G →
      ∫⁻ x, G x ∂μL =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) ∂μK) ∧
    (∀ F : AdeleRing (𝓞 L) L → ℂ, Integrable F μL →
      Integrable (tracePushforward K L F) μK ∧
      ∫ x, F x ∂μL = (c.toReal : ℂ) * ∫ r, tracePushforward K L F r ∂μK) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  obtain ⟨e, htr, -, -, -, c₁, hc₁0, hc₁t, hmap⟩ := exists_traceCoords K L
  have hme : MeasurableEmbedding (e : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞
        K) K) →
      AdeleRing (𝓞 L) L) :=
    e.toHomeomorph.measurableEmbedding

  obtain ⟨aL, haL0, haLt, hμL⟩ := exists_eq_smul_of_isAddHaarMeasure μL (adelicAddHaar (𝓞 L) L)
  obtain ⟨aK, haK0, haKt, hμK⟩ := exists_eq_smul_of_isAddHaarMeasure μK (adelicAddHaar (𝓞 K) K)
  refine ⟨aL * c₁⁻¹ * aK⁻¹, ?_, ?_, fun G hG => ?_, fun F hF => ?_⟩
  · exact mul_ne_zero (mul_ne_zero haL0 (ENNReal.inv_ne_zero.mpr hc₁t)) (ENNReal.inv_ne_zero.mpr haKt)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top haLt (ENNReal.inv_ne_top.mpr hc₁0)) (ENNReal.inv_ne_top.mpr haK0)
  ·
    have hA : ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c₁⁻¹ * ∫⁻ w, G (e w) ∂(Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
              adelicAddHaar (𝓞 K) K) := by
      have h := hme.lintegral_map
        (μ := Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
          adelicAddHaar (𝓞 K) K) G
      rw [hmap, lintegral_smul_measure, smul_eq_mul] at h
      rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel hc₁0 hc₁t, one_mul]
    have hB : ∫⁻ w, G (e w) ∂(Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
          adelicAddHaar (𝓞 K) K) =
        ∫⁻ r, ∫⁻ w, G (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) ∂(adelicAddHaar (𝓞 K) K) := by
      rw [lintegral_pi_succ (adelicAddHaar (𝓞 K) K) (Module.finrank K (LinearMap.ker (Algebra.trace K L))) (H := fun
            w => G (e w))
        (hG.comp e.continuous.measurable)]
      simp only [htr]
    rw [hμL, lintegral_smul_measure, smul_eq_mul, hA, hB, hμK, lintegral_smul_measure, smul_eq_mul]
    exact mul_mul_eq_mul_inv_mul haK0 haKt
  ·
    have hFL : Integrable F (adelicAddHaar (𝓞 L) L) := (integrable_smul_measure haL0 haLt).mp (hμL ▸ hF)
    have hFe : Integrable (fun w => F (e w)) (Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace
          K L)) + 1) => adelicAddHaar (𝓞 K) K) :=
      hme.integrable_map_iff.mp (hmap ▸ hFL.smul_measure hc₁t)
    have hP := integral_pi_succ (adelicAddHaar (𝓞 K) K) (Module.finrank K (LinearMap.ker (Algebra.trace K L))) hFe
    simp only [htr] at hP
    obtain ⟨hPi, hPe⟩ := hP
    have hc₁C : (c₁.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hc₁0 hc₁t).ne'
    have haKC : (aK.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos haK0 haKt).ne'
    have hA : ∫ x, F x ∂(adelicAddHaar (𝓞 L) L) =
        ((c₁.toReal : ℂ))⁻¹ * ∫ w, F (e w) ∂(Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K
              L)) + 1) => adelicAddHaar (𝓞 K) K) := by
      have h := hme.integral_map
        (μ := Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
          adelicAddHaar (𝓞 K) K) F
      rw [hmap, integral_smul_measure_complex] at h
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hc₁C, one_mul]
    refine ⟨?_, ?_⟩
    · rw [hμK]
      exact hPi.smul_measure haKt
    · have hQ : ∫ r, tracePushforward K L F r ∂μK =
          (aK.toReal : ℂ) * ∫ r, tracePushforward K L F r ∂(adelicAddHaar (𝓞 K) K) := by
        rw [hμK, integral_smul_measure_complex]
      have hQ' : ∫ r, tracePushforward K L F r ∂(adelicAddHaar (𝓞 K) K) =
          ((aK.toReal : ℂ))⁻¹ * ∫ r, tracePushforward K L F r ∂μK := by
        rw [hQ, ← mul_assoc, inv_mul_cancel₀ haKC, one_mul]
      rw [hμL, integral_smul_measure_complex, hA, hPe]
      show (aL.toReal : ℂ) * (((c₁.toReal : ℂ))⁻¹ * ∫ r, tracePushforward K L F r ∂(adelicAddHaar (𝓞 K) K)) = _
      rw [hQ', ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, Complex.ofReal_mul,
        Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
      ring

end

end AdelicTracePushforward

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (μL : Measure (AdeleRing (𝓞 L) L)) [μL.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, Measurable G →
      ∫⁻ x, G x ∂μL =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) ∂μK) ∧
    (∀ F : AdeleRing (𝓞 L) L → ℂ, Integrable F μL →
      Integrable (tracePushforward K L F) μK ∧
      ∫ x, F x ∂μL = (c.toReal : ℂ) * ∫ r, tracePushforward K L F r ∂μK) :=
  AdelicTracePushforward.exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre K L μK μL

#print axioms solution

end S_TraceFibrePushforward_exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre
end P2MW
export P2MW.S_TraceFibrePushforward_exists_forall_lintegral_eq_mul_lintegral_lintegral_traceFibre (solution)
