-- Prove2me | solution 1 for TraceFibrePushforward.exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fd030212-f022-5eaa-a292-7d72236f5833

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

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
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

section AdeleProjections

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

private theorem adele_fst_add (x y : AdeleRing R F) : (x + y).1 = x.1 + y.1 := rfl

private theorem adele_fst_mul (x y : AdeleRing R F) : (x * y).1 = x.1 * y.1 := rfl

private theorem adele_snd_add (x y : AdeleRing R F) : (x + y).2 = x.2 + y.2 := rfl

private theorem adele_snd_mul (x y : AdeleRing R F) : (x * y).2 = x.2 * y.2 := rfl

private theorem adele_fst_sum {ι : Type*} (s : Finset ι) (f : ι → AdeleRing R F) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, adele_fst_add, ih]

private theorem adele_snd_sum {ι : Type*} (s : Finset ι) (f : ι → AdeleRing R F) :
    (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, adele_snd_add, ih]

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

private theorem secondCountable_fst_of_prod (G₁ G₂ : Type) [Zero G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [SecondCountableTopology (G₁ × G₂)] : SecondCountableTopology G₁ :=
  (Topology.IsEmbedding.of_comp (continuous_id.prodMk continuous_const : Continuous fun x : G₁ => (x, (0 : G₂)))
    continuous_fst Topology.IsEmbedding.id).secondCountableTopology

private theorem secondCountable_snd_of_prod (G₁ G₂ : Type) [Zero G₁] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [SecondCountableTopology (G₁ × G₂)] : SecondCountableTopology G₂ :=
  (Topology.IsEmbedding.of_comp (continuous_const.prodMk continuous_id : Continuous fun y : G₂ => ((0 : G₁), y))
    continuous_snd Topology.IsEmbedding.id).secondCountableTopology

end Factors

section Coordinates

variable {G₁ G₂ ι : Type} [TopologicalSpace G₁] [TopologicalSpace G₂]

private noncomputable def prodArrowHomeomorph (G₁ G₂ ι : Type) [TopologicalSpace G₁] [TopologicalSpace G₂] :
    (ι → G₁) × (ι → G₂) ≃ₜ (ι → G₁ × G₂) where
  toEquiv := (Equiv.arrowProdEquivProdArrow ι (fun _ => G₁) fun _ => G₂).symm
  continuous_toFun := continuous_pi fun j =>
    ((continuous_apply j).comp continuous_fst).prodMk ((continuous_apply j).comp continuous_snd)
  continuous_invFun :=
    (continuous_pi fun j => continuous_fst.comp (continuous_apply j)).prodMk
      (continuous_pi fun j => continuous_snd.comp (continuous_apply j))

private theorem map_add_prodArrowHomeomorph [Add G₁] [Add G₂] (p q : (ι → G₁) × (ι → G₂)) :
    prodArrowHomeomorph G₁ G₂ ι (p + q) = prodArrowHomeomorph G₁ G₂ ι p + prodArrowHomeomorph G₁ G₂ ι q := rfl

end Coordinates

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  [LocallyCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂]
  [MeasurableSpace G₂] [BorelSpace G₂] [SecondCountableTopology (G₁ × G₂)]
  {ι : Type} [Fintype ι]

section Ambient

variable [mP : MeasurableSpace (G₁ × G₂)] [BorelSpace (G₁ × G₂)] (μ : Measure (G₁ × G₂)) [μ.IsAddHaarMeasure]

private theorem exists_integral_pi_eq_mul_integral_prod :
    ∃ (μ₁ : Measure G₁) (μ₂ : Measure G₂) (a : ℝ), μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ 0 < a ∧
      ∀ Φ : (ι → G₁ × G₂) → ℂ,
        ∫ w, Φ w ∂(Measure.pi fun _ : ι => μ) =
          a * ∫ p, Φ (fun j => (p.1 j, p.2 j)) ∂((Measure.pi fun _ : ι => μ₁).prod (Measure.pi fun _ : ι => μ₂)) := by
  haveI : SecondCountableTopology G₁ := secondCountable_fst_of_prod G₁ G₂
  haveI : SecondCountableTopology G₂ := secondCountable_snd_of_prod G₁ G₂
  set μP : Measure ((ι → G₁) × (ι → G₂)) :=
    (Measure.pi fun _ : ι => (Measure.addHaar : Measure G₁)).prod
      (Measure.pi fun _ : ι => (Measure.addHaar : Measure G₂)) with hμP
  set h : (ι → G₁) × (ι → G₂) ≃ₜ (ι → G₁ × G₂) := prodArrowHomeomorph G₁ G₂ ι with hh
  set Q : Measure (ι → G₁ × G₂) := Measure.map h.toMeasurableEquiv μP with hQ

  haveI : Q.IsAddHaarMeasure := by
    let f : (ι → G₁) × (ι → G₂) →+ (ι → G₁ × G₂) :=
      { toFun := h, map_zero' := rfl, map_add' := map_add_prodArrowHomeomorph }
    have hfQ : Q = Measure.map f μP := rfl
    rw [hfQ]
    exact Measure.isAddHaarMeasure_map μP f h.continuous h.surjective h.isClosedEmbedding.tendsto_cocompact

  have huniq : (Measure.pi fun _ : ι => μ) = Measure.addHaarScalarFactor (Measure.pi fun _ : ι => μ) Q • Q :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨Measure.addHaar, Measure.addHaar, (Measure.addHaarScalarFactor (Measure.pi fun _ : ι => μ) Q : ℝ),
    inferInstance, inferInstance, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun Φ => ?_⟩
  have hint : (∫ x, Φ x ∂Q) = (∫ p, Φ (h.toMeasurableEquiv p) ∂μP) := by
    rw [hQ, integral_map_equiv]
  conv_lhs => rw [huniq]
  rw [integral_smul_nnreal_measure, hint, NNReal.smul_def]
  exact Complex.real_smul

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

omit [T2Space X] in

private theorem isLocallyConstant_integral_of_hasCompactSupport {Θ : X × Y → E} (hΘ : IsLocallyConstant Θ)
    (hc : HasCompactSupport Θ) : IsLocallyConstant fun x => ∫ y, Θ (x, y) ∂ν := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x₀ => ?_

  have hbox : ∀ y : Y, ∃ U : Set X, ∃ Vy : Set Y, IsOpen U ∧ IsOpen Vy ∧ x₀ ∈ U ∧ y ∈ Vy ∧
      ∀ p ∈ U ×ˢ Vy, Θ p = Θ (x₀, y) := by
    intro y
    have hopen : IsOpen {p : X × Y | Θ p = Θ (x₀, y)} := hΘ.isOpen_fiber _
    obtain ⟨U, Vy, hU, hV, hxU, hyV, hsub⟩ := isOpen_prod_iff.1 hopen x₀ y rfl
    exact ⟨U, Vy, hU, hV, hxU, hyV, fun p hp => hsub hp⟩
  choose U Vy hU hV hxU hyV hconst using hbox

  have hK : IsCompact (Prod.snd '' tsupport Θ) := hc.image continuous_snd
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover Vy fun y _ => (hV y).mem_nhds (hyV y)
  refine ⟨⋂ y ∈ t, U y, isOpen_biInter_finset fun y _ => hU y, mem_iInter₂.2 fun y _ => hxU y, fun x hx => ?_⟩
  have hslice : ∀ y, Θ (x, y) = Θ (x₀, y) := by
    intro y
    by_cases hy : y ∈ Prod.snd '' tsupport Θ
    · obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht hy)
      have hxz : x ∈ U z := mem_iInter₂.1 hx z hzt
      rw [hconst z (x, y) ⟨hxz, hyz⟩, hconst z (x₀, y) ⟨hxU z, hyz⟩]
    · have h1 : (x, y) ∉ tsupport Θ := fun h => hy ⟨(x, y), h, rfl⟩
      have h2 : (x₀, y) ∉ tsupport Θ := fun h => hy ⟨(x₀, y), h, rfl⟩
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
  simp only [hslice]

private theorem hasCompactSupport_integral_of_hasCompactSupport {Θ : X × Y → E} (hc : HasCompactSupport Θ) :
    HasCompactSupport fun x => ∫ y, Θ (x, y) ∂ν := by
  refine HasCompactSupport.intro (hc.image continuous_fst) fun x hx => ?_
  have hzero : ∀ y, Θ (x, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, y), h, rfl⟩
  simp only [hzero, integral_zero]

end LocallyConstant

end FibreIntegrals

section SchwartzBruhatClass

open scoped Classical

section AdeleComponents

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_adeleFst : Continuous fun x : AdeleRing (𝓞 F) F => x.1 :=
  continuous_fst

private theorem continuous_adeleOfInf : Continuous fun ρ : InfiniteAdeleRing F => ((ρ, 0) : AdeleRing (𝓞 F) F) :=
  continuous_id.prodMk continuous_const

end AdeleComponents

private theorem continuous_traceFibre_uncurry (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    Continuous fun p : AdeleRing (𝓞 K) K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      AdeleRing (𝓞 K) K) => traceFibre K L p.1 p.2 := by
  simp only [traceFibre]
  refine (((M4aHerbrand.Bridge.continuous_genuineβ K L).comp continuous_fst).mul continuous_const).add
    (continuous_finsetSum _ fun i _ => ?_)
  exact ((M4aHerbrand.Bridge.continuous_genuineβ K L).comp ((continuous_apply i).comp continuous_snd)).mul
    continuous_const

private noncomputable def traceFibreInf (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ρ : InfiniteAdeleRing K)
    (u : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) : InfiniteAdeleRing L :=
  (traceFibre K L (ρ, 0) fun j => (u j, 0)).1

private noncomputable def traceFibreFin (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ρ : FiniteAdeleRing (𝓞 K) K)
    (v : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 L) L :=
  (traceFibre K L (0, ρ) fun j => (0, v j)).2

private theorem traceFibre_eq_components (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (r : AdeleRing (𝓞 K) K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    traceFibre K L r w = (traceFibreInf K L r.1 fun j => (w j).1, traceFibreFin K L r.2 fun j => (w j).2) := by
  refine Prod.ext ?_ ?_
  · simp only [traceFibreInf, traceFibre, adele_fst_add, adele_fst_mul, adele_fst_sum, M4aHerbrand.Bridge.genuineβ_fst]
  · simp only [traceFibreFin, traceFibre, adele_snd_add, adele_snd_mul, adele_snd_sum, M4aHerbrand.Bridge.genuineβ_snd]

private theorem continuous_traceFibreInf (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    Continuous fun p : InfiniteAdeleRing K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      InfiniteAdeleRing K) => traceFibreInf K L p.1 p.2 := by
  have hpair : Continuous fun p : InfiniteAdeleRing K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) =>
      (((p.1, 0) : AdeleRing (𝓞 K) K), fun j => ((p.2 j, 0) : AdeleRing (𝓞 K) K)) :=
    (continuous_adeleOfInf.comp continuous_fst).prodMk
      (continuous_pi fun j => continuous_adeleOfInf.comp ((continuous_apply j).comp continuous_snd))
  have h := (continuous_traceFibre_uncurry K L).comp hpair
  exact continuous_adeleFst.comp h

private theorem isCompact_preimage_traceFibreInf (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {C : Set (InfiniteAdeleRing L)} (hC : IsCompact C) :
    IsCompact {p : InfiniteAdeleRing K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      InfiniteAdeleRing K) | traceFibreInf K L p.1 p.2 ∈ C} := by
  obtain ⟨e, htr, -⟩ := exists_traceCoords K L
  set z₀ : FiniteAdeleRing (𝓞 L) L := traceFibreFin K L 0 fun _ => 0
  have hT : IsCompact (e ⁻¹' (C ×ˢ {z₀})) :=
    e.toHomeomorph.isCompact_preimage.2 (hC.prod isCompact_singleton)
  have hπ : Continuous fun x : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K =>
      ((x 0).1, fun j => (x (Fin.succ j)).1) :=
    (continuous_apply (0 : Fin _)).fst.prodMk (continuous_pi fun j => (continuous_apply (Fin.succ j)).fst)
  refine (hT.image hπ).of_isClosed_subset (hC.isClosed.preimage (continuous_traceFibreInf K L)) ?_
  rintro ⟨ρ, u⟩ hp
  refine ⟨Fin.cons (ρ, 0) fun j => (u j, 0), ?_, ?_⟩
  · show e _ ∈ C ×ˢ {z₀}
    rw [htr, traceFibre_eq_components]
    exact ⟨hp, rfl⟩
  · simp only [Fin.cons_zero, Fin.cons_succ]

private theorem exists_mixedHomeomorph (K : Type) [Field K] [NumberField K] :
    ∃ φ : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K,
      (∀ x, φ x = InfiniteAdeleRing.ringEquiv_mixedSpace K x) ∧
        ∀ y, φ.symm y = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y := by
  have hcont : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := AdelicBox.continuous_ringEquiv_mixedSpace K
  have hopen : IsOpenMap (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
    let f : InfiniteAdeleRing K →+ mixedEmbedding.mixedSpace K :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.toAddMonoidHom
    have hfs : Function.Surjective f := (InfiniteAdeleRing.ringEquiv_mixedSpace K).surjective
    have hfc : Continuous f := hcont
    exact f.isOpenMap_of_sigmaCompact hfs hfc
  exact ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv.toHomeomorphOfContinuousOpen hcont hopen,
    fun _ => rfl, fun _ => rfl⟩

end SchwartzBruhatClass

section SchwartzBruhatSums

open scoped Classical

end SchwartzBruhatSums

private theorem snd_algebraMap_adeleRing (L : Type) [Field L] [NumberField L] (l : L) :
    (algebraMap L (AdeleRing (𝓞 L) L) l).2 = algebraMap L (FiniteAdeleRing (𝓞 L) L) l :=
  rfl

private theorem semiLocalEval_finiteConorm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K) :
    AutomorphicForm.semiLocalEval K L v (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) x) = 1 ⊗ₜ[K] x v := by
  apply (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective
  rw [show AutomorphicForm.semiLocalEval K L v (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) x) =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w => M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) x w.1) from rfl,
    AlgEquiv.apply_symm_apply]
  funext w
  obtain ⟨w, rfl⟩ := w
  simp only [HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv, AlgEquiv.ofBijective_apply,
    HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul, M4aHerbrand.Bridge.finiteConorm_apply,
    RingHom.algebraMap_toAlgebra]
  rfl

private theorem semiLocalEval_algebraMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (l : L) :
    AutomorphicForm.semiLocalEval K L v (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) = l ⊗ₜ[K] 1 := by
  apply (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective
  rw [show AutomorphicForm.semiLocalEval K L v (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w => algebraMap L (FiniteAdeleRing (𝓞 L) L) l w.1) from rfl,
    AlgEquiv.apply_symm_apply]
  funext w
  simp only [HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv, AlgEquiv.ofBijective_apply,
    HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, mul_one, FiniteAdeleRing.algebraMap_apply]
  rfl

private theorem semiLocalEval_traceFibre_snd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (r : AdeleRing (𝓞 K) K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    AutomorphicForm.semiLocalEval K L v (traceFibre K L r w).2 = localTraceFibre K L v (r.2 v) fun i => (w i).2 v := by
  simp only [traceFibre, localTraceFibre, adele_snd_add, adele_snd_mul, adele_snd_sum, M4aHerbrand.Bridge.genuineβ_snd,
    snd_algebraMap_adeleRing, map_add, map_sum, map_mul, semiLocalEval_finiteConorm, semiLocalEval_algebraMap,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

namespace ArchSplit

end ArchSplit

section ProductFormula

namespace BoxProductFormula

section SplittingInProductForm

open MeasureTheory

variable {ι : Type} [Fintype ι] {G₁ G₂ : Type} [AddCommGroup G₁] [AddCommGroup G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalAddGroup G₁] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₁]
  [LocallyCompactSpace G₂] [SecondCountableTopology (G₁ × G₂)] [MeasurableSpace G₁] [BorelSpace G₁]
  [MeasurableSpace G₂] [BorelSpace G₂] [mP : MeasurableSpace (G₁ × G₂)] [BorelSpace (G₁ × G₂)]

private theorem exists_integral_pi_mul_eq_mul_integral_mul_integral (μ : Measure (G₁ × G₂)) [μ.IsAddHaarMeasure] :
    ∃ (μ₁ : Measure G₁) (μ₂ : Measure G₂) (a : ℝ), μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ 0 < a ∧
      ∀ (A : (ι → G₁) → ℂ) (B : (ι → G₂) → ℂ),
        ∫ w, A (fun i => (w i).1) * B (fun i => (w i).2) ∂(Measure.pi fun _ : ι => μ) =
          a * ((∫ x, A x ∂(Measure.pi fun _ : ι => μ₁)) * ∫ y, B y ∂(Measure.pi fun _ : ι => μ₂)) := by
  obtain ⟨μ₁, μ₂, a, h₁, h₂, ha, hΦ⟩ := exists_integral_pi_eq_mul_integral_prod (ι := ι) (mP := mP) μ
  haveI : SecondCountableTopology G₁ := secondCountable_fst_of_prod G₁ G₂
  haveI : SecondCountableTopology G₂ := secondCountable_snd_of_prod G₁ G₂
  haveI := h₁
  haveI := h₂
  refine ⟨μ₁, μ₂, a, h₁, h₂, ha, fun A B => ?_⟩
  rw [hΦ fun w => A (fun i => (w i).1) * B (fun i => (w i).2)]
  congr 1
  exact integral_prod_mul A B

end SplittingInProductForm

section SlicingAndTransport

open MeasureTheory
open scoped ENNReal

section Transport

variable {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G']
  [LocallyCompactSpace G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']

private theorem exists_pos_forall_integral_comp_eq_mul (μ : Measure G) [μ.IsAddHaarMeasure] (ν : Measure G')
    [ν.IsAddHaarMeasure] (e : G ≃ₜ G') (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : G' → ℂ, ∫ x, Φ (e x) ∂μ = c * ∫ y, Φ y ∂ν := by
  set Q : Measure G' := Measure.map e.toMeasurableEquiv μ with hQ
  haveI : Q.IsAddHaarMeasure := by
    let f : G →+ G' := { toFun := e, map_zero' := by simpa using he 0 0, map_add' := he }
    have hfQ : Q = Measure.map f μ := rfl
    rw [hfQ]
    exact Measure.isAddHaarMeasure_map μ f e.continuous e.surjective e.isClosedEmbedding.tendsto_cocompact
  have huniq : Q = Measure.addHaarScalarFactor Q ν • ν := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(Measure.addHaarScalarFactor Q ν : ℝ), Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    fun Φ => ?_⟩
  have hint : (∫ x, Φ (e x) ∂μ) = (∫ y, Φ y ∂Q) := by
    rw [hQ, integral_map_equiv]
    rfl
  rw [hint]
  conv_lhs => rw [huniq]
  rw [integral_smul_nnreal_measure, NNReal.smul_def]
  exact Complex.real_smul

end Transport

section Slice

variable {H : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H]

private theorem integral_eq_addHaarScalarFactor_mul_integral (ν : Measure H) [ν.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (μH : Measure H) [μH.IsAddHaarMeasure] {b : H → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) :
    ∫ y, b y ∂ν = ((Measure.addHaarScalarFactor ν μH : ℝ) : ℂ) * ∫ y, b y ∂μH := by
  have hre : ∫ y, RCLike.re (b y) ∂ν = (Measure.addHaarScalarFactor ν μH : ℝ) * ∫ y, RCLike.re (b y) ∂μH := by
    have h := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport ν μH
      (f := fun y => RCLike.re (b y)) (RCLike.continuous_re.comp hb) (hbc.comp_left (map_zero _))
    rw [h, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have him : ∫ y, RCLike.im (b y) ∂ν = (Measure.addHaarScalarFactor ν μH : ℝ) * ∫ y, RCLike.im (b y) ∂μH := by
    have h := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport ν μH
      (f := fun y => RCLike.im (b y)) (RCLike.continuous_im.comp hb) (hbc.comp_left (map_zero _))
    rw [h, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have h1 : ∫ y, b y ∂ν =
      ((∫ y, RCLike.re (b y) ∂ν : ℝ) : ℂ) + ((∫ y, RCLike.im (b y) ∂ν : ℝ) : ℂ) * RCLike.I :=
    (integral_re_add_im (hb.integrable_of_hasCompactSupport hbc : Integrable b ν)).symm
  have h2 : ∫ y, b y ∂μH =
      ((∫ y, RCLike.re (b y) ∂μH : ℝ) : ℂ) + ((∫ y, RCLike.im (b y) ∂μH : ℝ) : ℂ) * RCLike.I :=
    (integral_re_add_im (hb.integrable_of_hasCompactSupport hbc : Integrable b μH)).symm
  rw [h1, h2, hre, him]
  push_cast
  ring

variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [T2Space H]

private theorem exists_forall_integral_mul_comp_eq_integral_mul (μ : Measure G) [μ.IsAddLeftInvariant]
    (μH : Measure H) [μH.IsAddHaarMeasure] (p : G →+ H) (hp : Measurable p) (sec : H → G)
    (hsec : ∀ y, p (sec y) = y) (Q : G → ℂ) (hQm : Measurable Q) (hQfin : (Set.range Q).Finite)
    (hQinv : ∀ y g, Q (sec y + g) = Q g) (hQ : ∀ C : Set H, IsCompact C → μ (Function.support Q ∩ p ⁻¹' C) < ∞) :
    ∃ κ : ℂ, ∀ b : H → ℂ, Continuous b → HasCompactSupport b →
      ∫ g, Q g * b (p g) ∂μ = (∫ y, b y ∂μH) * κ := by
  classical

  set W : ℂ → Set G := fun c => Q ⁻¹' {c} ∩ Function.support Q with hW
  have hWm : ∀ c, MeasurableSet (W c) := fun c =>
    (hQm (measurableSet_singleton c)).inter (hQm (measurableSet_singleton 0)).compl
  have hWsub : ∀ c, W c ⊆ Function.support Q := fun c => Set.inter_subset_right
  set ν : ℂ → Measure H := fun c => Measure.map p (μ.restrict (W c)) with hν
  have hνinv : ∀ c, (ν c).IsAddLeftInvariant := by
    intro c
    constructor
    intro y
    have hpre : (fun g : G => sec y + g) ⁻¹' W c = W c := by
      ext g
      simp only [hW, Set.mem_preimage, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Function.mem_support, hQinv]
    calc Measure.map (fun h : H => y + h) (ν c)
        = Measure.map (fun g : G => p (sec y + g)) (μ.restrict (W c)) := by
          rw [hν]
          dsimp only
          rw [Measure.map_map (measurable_const_add y) hp]
          congr 1
          funext g
          simp [map_add, hsec]
      _ = Measure.map p (Measure.map (fun g : G => sec y + g) (μ.restrict (W c))) := by
          rw [Measure.map_map hp (measurable_const_add _)]
          rfl
      _ = ν c := by
          rw [show Measure.map (fun g : G => sec y + g) (μ.restrict (W c)) = μ.restrict (W c) by
            conv_lhs => rw [← hpre]
            rw [← Measure.restrict_map (measurable_const_add _) (hWm c), map_add_left_eq_self μ (sec y)]]
  have hνfin : ∀ c, IsFiniteMeasureOnCompacts (ν c) := by
    intro c
    constructor
    intro C hC
    rw [hν]
    dsimp only
    rw [Measure.map_apply hp hC.isClosed.measurableSet, Measure.restrict_apply (hp hC.isClosed.measurableSet)]
    refine (measure_mono ?_).trans_lt (hQ C hC)
    intro g hg
    exact ⟨hWsub c hg.2, hg.1⟩

  let s : ℂ → ℝ := fun c =>
    haveI := hνinv c
    haveI := hνfin c
    (Measure.addHaarScalarFactor (ν c) μH : ℝ)
  set T : Finset ℂ := hQfin.toFinset.erase 0 with hT
  refine ⟨∑ c ∈ T, c * (s c : ℂ), fun b hb hbc => ?_⟩

  have hexpand : ∀ g, Q g * b (p g) = ∑ c ∈ T, (W c).indicator (fun g' => c * b (p g')) g := by
    intro g
    by_cases h0 : Q g = 0
    · rw [h0, zero_mul]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hgc : g ∉ W c := fun hg => hg.2 h0
      simp [hgc]
    · have hmem : Q g ∈ T := by
        rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨h0, Set.mem_range_self g⟩
      rw [Finset.sum_eq_single_of_mem (Q g) hmem]
      · have hg : g ∈ W (Q g) := ⟨rfl, h0⟩
        simp [hg]
      · intro c _ hc
        have hgc : g ∉ W c := fun hg => hc hg.1.symm
        simp [hgc]

  obtain ⟨M, hM⟩ := hbc.exists_bound_of_continuous hb
  have hbp : Measurable fun g => b (p g) := (hb.measurable.comp hp)
  have hterm : ∀ c ∈ T, Integrable ((W c).indicator fun g' => c * b (p g')) μ := by
    intro c _
    rw [integrable_indicator_iff (hWm c)]
    have hfinite : μ (W c ∩ p ⁻¹' tsupport b) < ∞ := by
      refine (measure_mono ?_).trans_lt (hQ _ hbc)
      intro g hg
      exact ⟨hWsub c hg.1, hg.2⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := W c ∩ p ⁻¹' tsupport b) ?_ (hWm c) fun g hg => ?_
    · refine Measure.integrableOn_of_bounded (M := ‖c‖ * M) hfinite.ne ((hbp.const_mul c).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun g => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    · have hout : p g ∉ tsupport b := fun h => hg.2 ⟨hg.1, h⟩
      rw [image_eq_zero_of_notMem_tsupport hout, mul_zero]

  have hvalue : ∀ c ∈ T, ∫ g, (W c).indicator (fun g' => c * b (p g')) g ∂μ = c * ((s c : ℂ) * ∫ y, b y ∂μH) := by
    intro c _
    haveI := hνinv c
    haveI := hνfin c
    rw [integral_indicator (hWm c)]
    have hcm : ∫ g in W c, c * b (p g) ∂μ = c * ∫ g in W c, b (p g) ∂μ := integral_const_mul c _
    rw [hcm]
    congr 1
    have hmap : ∫ y, b y ∂(ν c) = ∫ g in W c, b (p g) ∂μ := by
      rw [hν]
      exact integral_map hp.aemeasurable hb.aestronglyMeasurable
    rw [← hmap, integral_eq_addHaarScalarFactor_mul_integral (ν c) μH hb hbc]
  simp_rw [hexpand]
  rw [integral_finsetSum T hterm, Finset.sum_congr rfl hvalue, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end Slice

section FiniteRange

variable {X : Type} [TopologicalSpace X]

private theorem finite_range_of_isLocallyConstant_of_hasCompactSupport {b : X → ℂ} (hb : IsLocallyConstant b)
    (hbc : HasCompactSupport b) : (Set.range b).Finite := by
  have hsub : Set.range b ⊆ insert 0 (b '' tsupport b) := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport b
    · exact Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact Set.mem_insert _ _
  refine Set.Finite.subset (Set.Finite.insert 0 ?_) hsub
  have : CompactSpace (tsupport b) := isCompact_iff_compactSpace.1 hbc
  have hlc : IsLocallyConstant fun x : tsupport b => b x := hb.comp_continuous continuous_subtype_val
  have hrange : b '' tsupport b = Set.range fun x : tsupport b => b x := (Set.image_eq_range _ _)
  rw [hrange]
  exact hlc.range_finite

private theorem finite_range_mul {Y : Type} {f g : Y → ℂ} (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) :
    (Set.range fun y => f y * g y).Finite := by
  refine Set.Finite.subset ((hf.prod hg).image fun q : ℂ × ℂ => q.1 * q.2) ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨(f y, g y), ⟨Set.mem_range_self y, Set.mem_range_self y⟩, rfl⟩

private theorem finite_range_ite {Y : Type} (P : Y → Prop) [DecidablePred P] :
    (Set.range fun y => if P y then (1 : ℂ) else 0).Finite := by
  refine Set.Finite.subset (Set.toFinite {(1 : ℂ), 0}) ?_
  rintro _ ⟨y, rfl⟩
  by_cases h : P y <;> simp [h]

end FiniteRange

end SlicingAndTransport

section AdelicProductFormula

open scoped Classical RestrictedProduct

variable (K : Type) [Field K] [NumberField K]

private scoped instance countable_numberField : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)

private scoped instance separableSpace_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense := by
    refine ⟨_, ?_, (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective (K := K) (v := v)).denseRange.comp
      UniformSpace.Completion.denseRange_coe
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v)⟩
    have : Countable (WithVal (HeightOneSpectrum.valuation K v)) :=
      Countable.of_equiv _ (WithVal.equiv (HeightOneSpectrum.valuation K v)).symm.toEquiv
    exact Set.countable_range _

private theorem secondCountable_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) :=
  inferInstance

private noncomputable def faSingle (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x

private theorem faSingle_apply_same (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : faSingle K v x v = x :=
  Pi.single_eq_same v x

private theorem faSingle_apply_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : v.adicCompletion K) :
    faSingle K v x w = 0 :=
  Pi.single_eq_of_ne h x

private theorem fa_add_apply (x y : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) : (x + y) w = x w + y w :=
  rfl

private theorem continuous_faComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun x : FiniteAdeleRing (𝓞 K) K => x v :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum (𝓞 K), [w.adicCompletion K, w.adicCompletionIntegers K] => x v)

private theorem isOpen_integers (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

private theorem isClosed_integers (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring _

private theorem isCompact_integers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))

private def faBox (T : Finset (HeightOneSpectrum (𝓞 K)))
    (E : (v : HeightOneSpectrum (𝓞 K)) → Set (v.adicCompletion K)) : Set (FiniteAdeleRing (𝓞 K) K) :=
  {x | (∀ v ∈ T, x v ∈ E v) ∧ ∀ v ∉ T, x v ∈ v.adicCompletionIntegers K}

private theorem faBox_empty (E : (v : HeightOneSpectrum (𝓞 K)) → Set (v.adicCompletion K)) :
    faBox K ∅ E = NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K := by
  ext x
  simp [faBox, NumberField.AdelicBox.integralFiniteAdeles]

private theorem measure_faBox_lt_top [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
    (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (E : (v : HeightOneSpectrum (𝓞 K)) → Set (v.adicCompletion K)) (hE : ∀ v ∈ T, IsCompact (E v)) :
    μf (faBox K T E) < ⊤ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [faBox_empty]
    exact (NumberField.AdelicBox.isCompact_integralFiniteAdeles K).measure_lt_top
  | insert v₀ T hv₀ ih =>
    have ih' := ih fun v hv => hE v (Finset.mem_insert_of_mem hv)

    obtain ⟨F, -, hF⟩ := (hE v₀ (Finset.mem_insert_self v₀ T)).elim_nhds_subcover
      (fun t : v₀.adicCompletion K => {z | z - t ∈ v₀.adicCompletionIntegers K}) fun t _ =>
        ((isOpen_integers K v₀).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
    have hsub : faBox K (insert v₀ T) E ⊆ ⋃ t ∈ F, (fun x => -faSingle K v₀ t + x) ⁻¹' faBox K T E := by
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      have hx₀ : x v₀ ∈ ⋃ t ∈ F, {z | z - t ∈ v₀.adicCompletionIntegers K} := hF (h1 v₀ (Finset.mem_insert_self _ _))
      obtain ⟨t, htF, hxt⟩ := Set.mem_iUnion₂.1 hx₀
      refine Set.mem_iUnion₂.2 ⟨t, htF, ?_⟩
      rw [Set.mem_preimage]
      unfold faBox
      refine And.intro (fun v hv => ?_) (fun v hv => ?_)
      · have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
        show (-faSingle K v₀ t + x) v ∈ E v
        rw [fa_add_apply, show (-faSingle K v₀ t) v = -(faSingle K v₀ t v) from rfl, faSingle_apply_of_ne K hne,
          neg_zero, zero_add]
        exact h1 v (Finset.mem_insert_of_mem hv)
      · show (-faSingle K v₀ t + x) v ∈ v.adicCompletionIntegers K
        rw [fa_add_apply, show (-faSingle K v₀ t) v = -(faSingle K v₀ t v) from rfl]
        by_cases hvv : v = v₀
        · subst hvv
          rw [faSingle_apply_same, neg_add_eq_sub]
          exact hxt
        · rw [faSingle_apply_of_ne K hvv, neg_zero, zero_add]
          exact h2 v (by simp [hvv, hv])
    refine (measure_mono hsub).trans_lt ((measure_biUnion_finset_le F _).trans_lt ?_)
    refine ENNReal.sum_lt_top.mpr fun t _ => ?_
    rw [measure_preimage_add]
    exact ih'

variable (m : ℕ)

private noncomputable def pFin (v : HeightOneSpectrum (𝓞 K)) :
    (Fin m → FiniteAdeleRing (𝓞 K) K) →+ (Fin m → v.adicCompletion K) where
  toFun y i := y i v
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem pFin_apply (v : HeightOneSpectrum (𝓞 K)) (y : Fin m → FiniteAdeleRing (𝓞 K) K) (i : Fin m) :
    pFin K m v y i = y i v :=
  rfl

private theorem continuous_pFin (v : HeightOneSpectrum (𝓞 K)) : Continuous (pFin K m v) :=
  continuous_pi fun i => (continuous_faComponent K v).comp (continuous_apply i)

private noncomputable def secFin (v : HeightOneSpectrum (𝓞 K)) (z : Fin m → v.adicCompletion K) :
    Fin m → FiniteAdeleRing (𝓞 K) K :=
  fun i => faSingle K v (z i)

private theorem pFin_secFin (v : HeightOneSpectrum (𝓞 K)) (z : Fin m → v.adicCompletion K) :
    pFin K m v (secFin K m v z) = z :=
  funext fun i => faSingle_apply_same K v (z i)

private theorem pFin_secFin_add_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (z : Fin m → v.adicCompletion K)
    (y : Fin m → FiniteAdeleRing (𝓞 K) K) : pFin K m w (secFin K m v z + y) = pFin K m w y := by
  funext i
  show (faSingle K v (z i) + y i) w = y i w
  rw [fa_add_apply, faSingle_apply_of_ne K h, zero_add]

private def OffIntegral (T : Finset (HeightOneSpectrum (𝓞 K))) (y : Fin m → FiniteAdeleRing (𝓞 K) K) : Prop :=
  ∀ i, ∀ v ∉ T, pFin K m v y i ∈ v.adicCompletionIntegers K

private theorem offIntegral_insert_iff {v₀ : HeightOneSpectrum (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hv₀ : v₀ ∉ S) (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    OffIntegral K m S y ↔ OffIntegral K m (insert v₀ S) y ∧ ∀ i, pFin K m v₀ y i ∈ v₀.adicCompletionIntegers K := by
  constructor
  · intro h
    exact ⟨fun i v hv => h i v fun hvS => hv (Finset.mem_insert_of_mem hvS), fun i => h i v₀ hv₀⟩
  · rintro ⟨h, h₀⟩ i v hv
    by_cases hvv : v = v₀
    · subst hvv
      exact h₀ i
    · exact h i v (by simp [hvv, hv])

private theorem offIntegral_secFin_add {v₀ : HeightOneSpectrum (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (z : Fin m → v₀.adicCompletion K) (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    OffIntegral K m (insert v₀ S) (secFin K m v₀ z + y) ↔ OffIntegral K m (insert v₀ S) y := by
  unfold OffIntegral
  refine forall_congr' fun i => forall_congr' fun v => imp_congr_right fun hv => ?_
  have hne : v ≠ v₀ := fun h => hv (h ▸ Finset.mem_insert_self v₀ S)
  rw [pFin_secFin_add_of_ne K m hne]

private theorem isClosed_offIntegral (T : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClosed {y : Fin m → FiniteAdeleRing (𝓞 K) K | OffIntegral K m T y} := by
  have : {y : Fin m → FiniteAdeleRing (𝓞 K) K | OffIntegral K m T y} =
      ⋂ i : Fin m, ⋂ v : HeightOneSpectrum (𝓞 K), ⋂ (_ : v ∉ T),
        (fun y : Fin m → FiniteAdeleRing (𝓞 K) K => pFin K m v y i) ⁻¹'
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext y
    simp [OffIntegral]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun v => isClosed_iInter fun _ =>
    (isClosed_integers K v).preimage ((continuous_apply i).comp (continuous_pFin K m v))

private noncomputable def finIntegrand (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ) (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    ℂ :=
  (∏ v ∈ S, b v (pFin K m v y)) * if OffIntegral K m S y then 1 else 0

private noncomputable def stepQ (S : Finset (HeightOneSpectrum (𝓞 K))) (v₀ : HeightOneSpectrum (𝓞 K))
    (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ) (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    ℂ :=
  (∏ v ∈ S, b v (pFin K m v y)) * if OffIntegral K m (insert v₀ S) y then 1 else 0

private def unitBox (v : HeightOneSpectrum (𝓞 K)) : Set (Fin m → v.adicCompletion K) :=
  Set.pi Set.univ fun _ => (v.adicCompletionIntegers K : Set (v.adicCompletion K))

private theorem finIntegrand_insert {S : Finset (HeightOneSpectrum (𝓞 K))} {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∉ S) (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ)
    (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    finIntegrand K m (insert v₀ S) b y = stepQ K m S v₀ b y * b v₀ (pFin K m v₀ y) := by
  rw [finIntegrand, stepQ, Finset.prod_insert hv₀]
  ring

private theorem stepQ_mul_indicator {S : Finset (HeightOneSpectrum (𝓞 K))} {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∉ S) (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ)
    (y : Fin m → FiniteAdeleRing (𝓞 K) K) :
    stepQ K m S v₀ b y * (unitBox K m v₀).indicator (fun _ => (1 : ℂ)) (pFin K m v₀ y) = finIntegrand K m S b y := by
  have hbox : pFin K m v₀ y ∈ unitBox K m v₀ ↔ ∀ i, pFin K m v₀ y i ∈ v₀.adicCompletionIntegers K := by
    simp [unitBox]
  simp only [stepQ, finIntegrand, Set.indicator_apply, offIntegral_insert_iff K m hv₀, hbox]
  by_cases h₁ : OffIntegral K m (insert v₀ S) y <;>
    by_cases h₂ : ∀ i, pFin K m v₀ y i ∈ v₀.adicCompletionIntegers K <;> simp [h₁, h₂]

private theorem stepQ_secFin_add {S : Finset (HeightOneSpectrum (𝓞 K))} {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S)
    (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ) (z : Fin m → v₀.adicCompletion K)
    (y : Fin m → FiniteAdeleRing (𝓞 K) K) : stepQ K m S v₀ b (secFin K m v₀ z + y) = stepQ K m S v₀ b y := by
  rw [stepQ, stepQ]
  simp only [offIntegral_secFin_add]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [pFin_secFin_add_of_ne K m (ne_of_mem_of_not_mem hv hv₀)]

private theorem measurable_stepQ [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
    [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)] {S : Finset (HeightOneSpectrum (𝓞 K))}
    (v₀ : HeightOneSpectrum (𝓞 K)) {b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ}
    (hb : ∀ v ∈ S, IsLocallyConstant (b v)) : Measurable (stepQ K m S v₀ b) := by
  unfold stepQ
  refine Measurable.mul (Finset.measurable_prod S fun v hv => ?_) ?_
  · exact ((hb v hv).continuous.comp (continuous_pFin K m v)).measurable
  · exact Measurable.ite (isClosed_offIntegral K m _).measurableSet measurable_const measurable_const

private theorem finite_range_prodFactors {S : Finset (HeightOneSpectrum (𝓞 K))}
    {b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ}
    (hb : ∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) :
    (Set.range fun y : Fin m → FiniteAdeleRing (𝓞 K) K => ∏ v ∈ S, b v (pFin K m v y)).Finite := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (Set.finite_singleton (1 : ℂ)).subset (by rintro _ ⟨y, rfl⟩; exact Set.mem_singleton _)
  | insert v₀ S hv₀ ih =>
    simp only [Finset.prod_insert hv₀]
    have h₀ := hb v₀ (Finset.mem_insert_self v₀ S)
    refine finite_range_mul ?_ (ih fun v hv => hb v (Finset.mem_insert_of_mem hv))
    exact (finite_range_of_isLocallyConstant_of_hasCompactSupport h₀.1 h₀.2).subset
      (Set.range_comp_subset_range (pFin K m v₀) (b v₀))

private theorem finite_range_stepQ {S : Finset (HeightOneSpectrum (𝓞 K))} (v₀ : HeightOneSpectrum (𝓞 K))
    {b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ}
    (hb : ∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) : (Set.range (stepQ K m S v₀ b)).Finite := by
  unfold stepQ
  exact finite_range_mul (finite_range_prodFactors K m hb) (finite_range_ite fun y => OffIntegral K m (insert v₀ S) y)

private theorem measure_support_stepQ_inter_lt_top [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
    [BorelSpace (FiniteAdeleRing (𝓞 K) K)] [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)]
    (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S)
    {b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ}
    (hb : ∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) (C : Set (Fin m → v₀.adicCompletion K))
    (hC : IsCompact C) :
    (Measure.pi fun _ : Fin m => μf) (Function.support (stepQ K m S v₀ b) ∩ pFin K m v₀ ⁻¹' C) < ⊤ := by

  set D : (v : HeightOneSpectrum (𝓞 K)) → Set (Fin m → v.adicCompletion K) :=
    Function.update (fun v => tsupport (b v)) v₀ C with hD
  have hDc : ∀ v ∈ insert v₀ S, IsCompact (D v) := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hvS
    · simpa [hD] using hC
    · have hne : v ≠ v₀ := ne_of_mem_of_not_mem hvS hv₀
      simp only [hD, Function.update_of_ne hne]
      exact (hb v hvS).2

  set E : Fin m → (v : HeightOneSpectrum (𝓞 K)) → Set (v.adicCompletion K) :=
    fun i v => (fun z : Fin m → v.adicCompletion K => z i) '' D v with hE
  have hEc : ∀ i, ∀ v ∈ insert v₀ S, IsCompact (E i v) := fun i v hv => (hDc v hv).image (continuous_apply i)
  have hsub : Function.support (stepQ K m S v₀ b) ∩ pFin K m v₀ ⁻¹' C ⊆
      Set.pi Set.univ fun i => faBox K (insert v₀ S) (E i) := by
    rintro y ⟨hy, hyC⟩ i -
    have hy' : (∏ v ∈ S, b v (pFin K m v y)) * (if OffIntegral K m (insert v₀ S) y then (1 : ℂ) else 0) ≠ 0 :=
      Function.mem_support.1 hy
    have hprod : ∏ v ∈ S, b v (pFin K m v y) ≠ 0 := left_ne_zero_of_mul hy'
    have hoff : OffIntegral K m (insert v₀ S) y := by
      by_contra h
      rw [if_neg h, mul_zero] at hy'
      exact hy' rfl
    refine ⟨fun v hv => ?_, fun v hv => hoff i v hv⟩
    have hmem : pFin K m v y ∈ D v := by
      rcases Finset.mem_insert.1 hv with rfl | hvS
      · simpa [hD] using hyC
      · have hne : v ≠ v₀ := ne_of_mem_of_not_mem hvS hv₀
        rw [hD, Function.update_of_ne hne]
        exact subset_tsupport _ (Finset.prod_ne_zero_iff.1 hprod v hvS)
    exact ⟨pFin K m v y, hmem, rfl⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top fun i _ => measure_faBox_lt_top K μf _ (E i) (hEc i)

private noncomputable def locFactor (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : Measure (v.adicCompletion K) :=
  ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
    (Measure.addHaar : Measure (v.adicCompletion K))

private theorem addHaar_integers_ne_zero (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] :
    (Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ 0 :=
  (isOpen_integers K v).measure_ne_zero _ ⟨0, zero_mem _⟩

private theorem addHaar_integers_ne_top (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] :
    (Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ ⊤ :=
  (isCompact_integers K v).measure_ne_top

private theorem isAddHaarMeasure_locFactor (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : (locFactor K v).IsAddHaarMeasure := by
  unfold locFactor
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (addHaar_integers_ne_top K v))
    (ENNReal.inv_ne_top.2 (addHaar_integers_ne_zero K v))

private theorem locFactor_integers (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : locFactor K v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
  rw [locFactor, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (addHaar_integers_ne_zero K v) (addHaar_integers_ne_top K v)

private noncomputable def locMeasure (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : Measure (Fin m → v.adicCompletion K) :=
  Measure.pi fun _ : Fin m => locFactor K v

private theorem isAddHaarMeasure_locMeasure (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : (locMeasure K m v).IsAddHaarMeasure := by
  haveI := isAddHaarMeasure_locFactor K v
  haveI := secondCountable_adicCompletion K v
  haveI hSF : SigmaFinite (locFactor K v) := inferInstance
  haveI hMA : MeasurableAdd (v.adicCompletion K) := inferInstance
  haveI : ∀ _ : Fin m, SigmaFinite (locFactor K v) := fun _ => hSF
  haveI : ∀ _ : Fin m, MeasurableAdd (v.adicCompletion K) := fun _ => hMA
  unfold locMeasure
  exact Measure.pi.isAddHaarMeasure _

private theorem locMeasure_unitBox (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : locMeasure K m v (unitBox K m v) = 1 := by
  haveI := isAddHaarMeasure_locFactor K v
  haveI := secondCountable_adicCompletion K v
  haveI hSF : SigmaFinite (locFactor K v) := inferInstance
  haveI : ∀ _ : Fin m, SigmaFinite (locFactor K v) := fun _ => hSF
  rw [locMeasure, unitBox, Measure.pi_pi]
  simp [locFactor_integers]

private theorem isClopen_unitBox (v : HeightOneSpectrum (𝓞 K)) : IsClopen (unitBox K m v) :=
  ⟨isClosed_set_pi fun _ _ => isClosed_integers K v, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers K v⟩

private theorem isCompact_unitBox (v : HeightOneSpectrum (𝓞 K)) : IsCompact (unitBox K m v) :=
  isCompact_univ_pi fun _ => isCompact_integers K v

private theorem measurableSet_unitBox (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] : MeasurableSet (unitBox K m v) :=
  MeasurableSet.univ_pi fun _ => (isClosed_integers K v).measurableSet

private theorem continuous_unitBoxIndicator (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ((unitBox K m v).indicator fun _ => (1 : ℂ)) :=
  (isClopen_unitBox K m v).continuous_indicator continuous_const

private theorem hasCompactSupport_unitBoxIndicator (v : HeightOneSpectrum (𝓞 K)) :
    HasCompactSupport ((unitBox K m v).indicator fun _ => (1 : ℂ)) :=
  HasCompactSupport.intro (isCompact_unitBox K m v) fun _ hz => Set.indicator_of_notMem hz _

private theorem integral_unitBoxIndicator (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] :
    ∫ z, (unitBox K m v).indicator (fun _ => (1 : ℂ)) z ∂(locMeasure K m v) = 1 := by
  rw [integral_indicator_const _ (measurableSet_unitBox K m v), measureReal_def, locMeasure_unitBox]
  simp

private theorem integral_finIntegrand [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
    [BorelSpace (FiniteAdeleRing (𝓞 K) K)] [SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)]
    (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ)
    (hb : ∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) :
    ∫ y, finIntegrand K m S b y ∂(Measure.pi fun _ : Fin m => μf) =
      (∏ v ∈ S, ∫ t, b v t ∂(locMeasure K m v)) * ∫ y, finIntegrand K m ∅ b y ∂(Measure.pi fun _ : Fin m => μf) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul]
  | insert v₀ S hv₀ ih =>
    have hb' : ∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v) := fun v hv =>
      hb v (Finset.mem_insert_of_mem hv)
    have hb₀ := hb v₀ (Finset.mem_insert_self v₀ S)
    haveI := isAddHaarMeasure_locMeasure K m v₀

    obtain ⟨κ, hκ⟩ := exists_forall_integral_mul_comp_eq_integral_mul (Measure.pi fun _ : Fin m => μf)
      (locMeasure K m v₀) (pFin K m v₀) (continuous_pFin K m v₀).measurable (secFin K m v₀) (pFin_secFin K m v₀)
      (stepQ K m S v₀ b) (measurable_stepQ K m v₀ fun v hv => (hb' v hv).1) (finite_range_stepQ K m v₀ hb')
      (fun z y => stepQ_secFin_add K m hv₀ b z y) (fun C hC => measure_support_stepQ_inter_lt_top K m μf hv₀ hb' C hC)

    have h₁ := hκ (b v₀) hb₀.1.continuous hb₀.2
    have h₂ := hκ _ (continuous_unitBoxIndicator K m v₀) (hasCompactSupport_unitBoxIndicator K m v₀)
    simp_rw [stepQ_mul_indicator K m hv₀ b] at h₂
    rw [integral_unitBoxIndicator, one_mul] at h₂
    simp_rw [finIntegrand_insert K m hv₀ b]
    rw [h₁, ← h₂, ih hb', Finset.prod_insert hv₀]
    ring

private theorem exists_pos_forall_integral_arch_eq [MeasurableSpace (InfiniteAdeleRing K)]
    [BorelSpace (InfiniteAdeleRing K)] [SecondCountableTopology (InfiniteAdeleRing K)]
    (muArch : Measure (InfiniteAdeleRing K)) [muArch.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ a : (Fin m → mixedEmbedding.mixedSpace K) → ℂ,
      ∫ x, a (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (x i)) ∂(Measure.pi fun _ : Fin m => muArch) =
        c * ∫ t, a t := by
  obtain ⟨φ, hφ, -⟩ := exists_mixedHomeomorph K
  set e : (Fin m → InfiniteAdeleRing K) ≃ₜ (Fin m → mixedEmbedding.mixedSpace K) :=
    Homeomorph.piCongrRight fun _ => φ with he
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    funext i
    simp only [he, Homeomorph.piCongrRight_apply, Pi.add_apply, hφ, map_add]
  haveI hvol : (Measure.pi fun _ : Fin m => (volume : Measure (mixedEmbedding.mixedSpace K))).IsAddHaarMeasure := by
    haveI hMA : MeasurableAdd (mixedEmbedding.mixedSpace K) := inferInstance
    haveI hSF : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace K)) := inferInstance
    haveI : ∀ _ : Fin m, MeasurableAdd (mixedEmbedding.mixedSpace K) := fun _ => hMA
    haveI : ∀ _ : Fin m, SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace K)) := fun _ => hSF
    exact Measure.pi.isAddHaarMeasure _
  haveI hμ : (Measure.pi fun _ : Fin m => muArch).IsAddHaarMeasure := by
    haveI hMA : MeasurableAdd (InfiniteAdeleRing K) := inferInstance
    haveI hSF : SigmaFinite muArch := inferInstance
    haveI : ∀ _ : Fin m, MeasurableAdd (InfiniteAdeleRing K) := fun _ => hMA
    haveI : ∀ _ : Fin m, SigmaFinite muArch := fun _ => hSF
    exact Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc, h⟩ := exists_pos_forall_integral_comp_eq_mul (Measure.pi fun _ : Fin m => muArch)
    (Measure.pi fun _ : Fin m => (volume : Measure (mixedEmbedding.mixedSpace K))) e hadd
  refine ⟨c, hc, fun a => ?_⟩
  have hea : ∀ x : Fin m → InfiniteAdeleRing K,
      a (e x) = a fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (x i) := by
    intro x
    congr 1
    funext i
    simp only [he, Homeomorph.piCongrRight_apply, hφ]
  have h' := h a
  simp_rw [hea] at h'
  exact h'

end AdelicProductFormula

open scoped Classical in

private theorem
exists_pos_integral_pi_adelicAddHaar_eq_mul_integral_mul_prod_integral
    (K : Type) [Field K] [NumberField K]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] (m : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : (Fin m → mixedEmbedding.mixedSpace K) → ℂ)
        (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ),
        Continuous a → HasCompactSupport a → (∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) →
          ∫ w, a (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (w i).1) *
                ((∏ v ∈ S, b v fun i => ((w i).2 : FiniteAdeleRing (𝓞 K) K) v) *
                  if ∀ i, ∀ v ∉ S, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K then 1 else 0)
              ∂(Measure.pi fun _ : Fin m => adelicAddHaar (𝓞 K) K) =
            κ * ((∫ t, a t) * ∏ v ∈ S, ∫ t, b v t
              ∂(Measure.pi fun _ : Fin m =>
                ((Measure.addHaar : Measure (v.adicCompletion K))
                  (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
                  (Measure.addHaar : Measure (v.adicCompletion K)))) := by

  haveI hsc : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (InfiniteAdeleRing K) :=
    secondCountable_fst_of_prod (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
    secondCountable_snd_of_prod (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  letI : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI hBK : @BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _ (adeleBorel (𝓞 K) K) :=
    borelSpace_adeleBorel (𝓞 K) K
  haveI hHK : @Measure.IsAddHaarMeasure (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _ _ (adeleBorel (𝓞 K) K)
      (adelicAddHaar (𝓞 K) K) := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  obtain ⟨μ₁, μ₂, a₀, hμ₁, hμ₂, ha₀, hsplit⟩ :=
    exists_integral_pi_mul_eq_mul_integral_mul_integral (ι := Fin m) (mP := adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K)
  haveI := hμ₁
  haveI := hμ₂

  obtain ⟨cArch, hcArch, harch⟩ := exists_pos_forall_integral_arch_eq K m μ₁

  haveI hSF₂ : SigmaFinite μ₂ := inferInstance
  haveI hMA₂ : MeasurableAdd (FiniteAdeleRing (𝓞 K) K) := inferInstance
  haveI : ∀ _ : Fin m, SigmaFinite μ₂ := fun _ => hSF₂
  haveI : ∀ _ : Fin m, MeasurableAdd (FiniteAdeleRing (𝓞 K) K) := fun _ => hMA₂
  haveI hπ₂ : (Measure.pi fun _ : Fin m => μ₂).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set I₀ : Set (Fin m → FiniteAdeleRing (𝓞 K) K) :=
    Set.pi Set.univ fun _ => NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K with hI₀
  set κ₀ : ℝ := ((Measure.pi fun _ : Fin m => μ₂) I₀).toReal with hκ₀
  have hI₀open : IsOpen I₀ :=
    isOpen_set_pi Set.finite_univ fun _ _ => NumberField.AdelicBox.isOpen_integralFiniteAdeles K
  have hI₀compact : IsCompact I₀ :=
    isCompact_univ_pi fun _ => NumberField.AdelicBox.isCompact_integralFiniteAdeles K
  have hI₀ne : I₀.Nonempty := by
    refine ⟨fun _ => 0, fun i _ => ?_⟩
    intro v
    show (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K
    exact zero_mem _
  have hκ₀pos : 0 < κ₀ := ENNReal.toReal_pos (hI₀open.measure_ne_zero _ hI₀ne) hI₀compact.measure_ne_top
  have hfin₀ : ∀ b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ,
      ∫ y, finIntegrand K m ∅ b y ∂(Measure.pi fun _ : Fin m => μ₂) = (κ₀ : ℂ) := by
    intro b
    have hfun : finIntegrand K m ∅ b = I₀.indicator fun _ => (1 : ℂ) := by
      funext y
      simp only [finIntegrand, OffIntegral, Finset.prod_empty, one_mul, Finset.notMem_empty, not_false_eq_true,
        forall_const, pFin_apply, Set.indicator_apply, hI₀, Set.mem_univ_pi,
        NumberField.AdelicBox.integralFiniteAdeles, Set.mem_setOf_eq]
    rw [hfun, integral_indicator_const _ (hI₀open.measurableSet), measureReal_def, ← hκ₀]
    simp

  refine ⟨a₀ * cArch * κ₀, by positivity, fun S a b ha hac hb => ?_⟩
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K),
      (Measure.pi fun _ : Fin m =>
        ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
          (Measure.addHaar : Measure (v.adicCompletion K))) = locMeasure K m v := fun _ => rfl
  have key : ∫ w : Fin m → InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K,
      a (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (w i).1) * finIntegrand K m S b (fun i => (w i).2)
        ∂(Measure.pi fun _ : Fin m => adelicAddHaar (𝓞 K) K) =
      ((a₀ * cArch * κ₀ : ℝ) : ℂ) * ((∫ t, a t) * ∏ v ∈ S, ∫ t, b v t ∂(locMeasure K m v)) := by
    have h₁ := hsplit (fun x => a fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (x i)) (finIntegrand K m S b)
    beta_reduce at h₁
    refine h₁.trans ?_
    rw [integral_finIntegrand K m μ₂ S b hb, hfin₀ b, harch a]
    push_cast
    ring

  have hbridge : ∀ w : Fin m → AdeleRing (𝓞 K) K,
      ((∏ v ∈ S, b v fun i => ((w i).2 : FiniteAdeleRing (𝓞 K) K) v) *
          if ∀ i, ∀ v ∉ S, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K then (1 : ℂ) else 0)
        = finIntegrand K m S b (fun i => (w i).2) := by
    intro w
    by_cases h : ∀ i, ∀ v ∉ S, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K
    · rw [if_pos h]
      unfold finIntegrand
      rw [if_pos (show OffIntegral K m S (fun i => (w i).2) from h)]
      rfl
    · rw [if_neg h]
      unfold finIntegrand
      rw [if_neg (show ¬ OffIntegral K m S (fun i => (w i).2) from h)]
      rfl
  simp only [hloc, hbridge]
  exact key

end BoxProductFormula
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

open scoped Classical in

private theorem _root_.AdelicTracePushforward.exists_pos_integral_pi_adelicAddHaar_eq_mul_integral_mul_prod_integral (K : Type) [Field K]
    [NumberField K]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] (m : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : (Fin m → mixedEmbedding.mixedSpace K) → ℂ)
        (b : (v : HeightOneSpectrum (𝓞 K)) → (Fin m → v.adicCompletion K) → ℂ),
        Continuous a → HasCompactSupport a → (∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) →
          ∫ w, a (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (w i).1) *
                ((∏ v ∈ S, b v fun i => ((w i).2 : FiniteAdeleRing (𝓞 K) K) v) *
                  if ∀ i, ∀ v ∉ S, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K then 1 else 0)
              ∂(Measure.pi fun _ : Fin m => adelicAddHaar (𝓞 K) K) =
            κ * ((∫ t, a t) * ∏ v ∈ S, ∫ t, b v t
              ∂(Measure.pi fun _ : Fin m =>
                ((Measure.addHaar : Measure (v.adicCompletion K))
                  (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
                  (Measure.addHaar : Measure (v.adicCompletion K)))) :=
  BoxProductFormula.exists_pos_integral_pi_adelicAddHaar_eq_mul_integral_mul_prod_integral K m

p2m_export "AdelicTracePushforward" "exists_pos_integral_pi_adelicAddHaar_eq_mul_integral_mul_prod_integral"
section LocalTraceIntegers

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private noncomputable def functionalLift (v : HeightOneSpectrum (𝓞 K)) (ℓ : L →ₗ[K] K) :
    L ⊗[K] v.adicCompletion K →ₗ[K] v.adicCompletion K :=
  TensorProduct.lift ((LinearMap.lsmul K (v.adicCompletion K)).comp ℓ)

omit [NumberField L] in
private theorem functionalLift_tmul (v : HeightOneSpectrum (𝓞 K)) (ℓ : L →ₗ[K] K) (l : L)
    (a : v.adicCompletion K) : functionalLift K L v ℓ (l ⊗ₜ[K] a) = ℓ l • a := by
  simp [functionalLift]

private theorem functionalLift_localTraceFibre (v : HeightOneSpectrum (𝓞 K)) (ℓ : L →ₗ[K] K)
    (r : v.adicCompletion K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) :
    functionalLift K L v ℓ (localTraceFibre K L v r w) =
      ℓ ((Module.finrank K L : L)⁻¹) • r +
        ∑ i, ℓ (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) • w i := by
  simp [localTraceFibre, functionalLift_tmul, map_sum]

private theorem trace_inv_finrank : Algebra.trace K L ((Module.finrank K L : L)⁻¹) = 1 := by
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [← map_natCast (algebraMap K L) (Module.finrank K L), ← map_inv₀, Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_inv_cancel₀ hn]

private noncomputable def kerProjection : L →ₗ[K] LinearMap.ker (Algebra.trace K L) :=
  LinearMap.codRestrict (LinearMap.ker (Algebra.trace K L))
    (LinearMap.id - (Algebra.trace K L).smulRight ((Module.finrank K L : L)⁻¹)) fun l => by
      simp [LinearMap.mem_ker, trace_inv_finrank]

private theorem kerProjection_inv_finrank : kerProjection K L ((Module.finrank K L : L)⁻¹) = 0 := by
  apply Subtype.ext
  simp [kerProjection, trace_inv_finrank]

private theorem kerProjection_finBasis (i : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) :
    kerProjection K L (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) =
      Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i := by
  apply Subtype.ext
  simp [kerProjection]

private noncomputable def coordFunctional (j : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) :
    L →ₗ[K] K :=
  (Module.finBasis K (LinearMap.ker (Algebra.trace K L))).coord j ∘ₗ kerProjection K L

private theorem coordFunctional_inv_finrank (j : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) :
    coordFunctional K L j ((Module.finrank K L : L)⁻¹) = 0 := by
  simp [coordFunctional, kerProjection_inv_finrank]

private theorem coordFunctional_finBasis (j i : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) :
    coordFunctional K L j (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) = if i = j then 1 else 0 := by
  simp [coordFunctional, kerProjection_finBasis, Module.Basis.coord, Module.Basis.repr_self, Finsupp.single_apply]

private theorem functionalLift_trace_localTraceFibre (v : HeightOneSpectrum (𝓞 K)) (r : v.adicCompletion K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) :
    functionalLift K L v (Algebra.trace K L) (localTraceFibre K L v r w) = r := by
  simp [functionalLift_localTraceFibre, trace_inv_finrank]

private theorem functionalLift_coord_localTraceFibre (v : HeightOneSpectrum (𝓞 K)) (r : v.adicCompletion K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K)
    (j : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) :
    functionalLift K L v (coordFunctional K L j) (localTraceFibre K L v r w) = w j := by
  simp [functionalLift_localTraceFibre, coordFunctional_inv_finrank, coordFunctional_finBasis, ite_smul]

private theorem exists_denominator {ι : Type} [Fintype ι] (ℓ : ι → (L →ₗ[K] K)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ (i : ι) (b : 𝓞 L), ∃ c : 𝓞 K,
      algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d * ℓ i (algebraMap (𝓞 L) L b) := by
  classical
  haveI := M4aHerbrand.Bridge.moduleFinite_ringOfIntegers K L
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite (𝓞 K) (𝓞 L)›
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) (Finset.univ ×ˢ s)
    fun p : ι × 𝓞 L => ℓ p.1 (algebraMap (𝓞 L) L p.2)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.2, fun i b => ?_⟩
  have hb : b ∈ Submodule.span (𝓞 K) (s : Set (𝓞 L)) := by rw [hs]; exact Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c, hc⟩ := RingHom.mem_rangeS.mp (hd (i, b) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hb⟩))
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  | zero => exact ⟨0, by simp⟩
  | add b₁ b₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁⟩ := h₁
    obtain ⟨c₂, hc₂⟩ := h₂
    exact ⟨c₁ + c₂, by simp [map_add, hc₁, hc₂, mul_add]⟩
  | smul a b _ h =>
    obtain ⟨c, hc⟩ := h
    have key : ℓ i (algebraMap (𝓞 L) L (a • b)) = algebraMap (𝓞 K) K a * ℓ i (algebraMap (𝓞 L) L b) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, ← Algebra.smul_def, map_smul, smul_eq_mul]
    refine ⟨a * c, ?_⟩
    rw [key, map_mul, hc]
    ring

omit [NumberField L] in

private theorem coe_mul_functionalLift_mem (v : HeightOneSpectrum (𝓞 K)) (ℓ : L →ₗ[K] K) (d : 𝓞 K)
    (hd : ∀ b : 𝓞 L, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d * ℓ (algebraMap (𝓞 L) L b))
    {x : L ⊗[K] v.adicCompletion K} (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) :
    ((algebraMap (𝓞 K) K d : K) : v.adicCompletion K) * functionalLift K L v ℓ x ∈ v.adicCompletionIntegers K := by
  rw [AutomorphicForm.semiLocalIntegers] at hx
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    obtain ⟨c, hc⟩ := hd b
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, functionalLift_tmul, Algebra.smul_def,
      ← mul_assoc,
      show ((algebraMap (𝓞 K) K d : K) : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K d) from rfl,
      ← map_mul (algebraMap K (v.adicCompletion K))]
    show ((algebraMap (𝓞 K) K d * ℓ (algebraMap (𝓞 L) L b) : K) : v.adicCompletion K) * (a : v.adicCompletion K) ∈
      v.adicCompletionIntegers K
    rw [← hc]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 K) (K := K) (v := v) c) a.2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add, mul_add]
    exact add_mem h₁ h₂

private theorem mem_of_coe_mul_mem (v : HeightOneSpectrum (𝓞 K)) {u : 𝓞 K} (hu : v.intValuation u = 1)
    {x : v.adicCompletion K}
    (hx : ((algebraMap (𝓞 K) K u : K) : v.adicCompletion K) * x ∈ v.adicCompletionIntegers K) :
    x ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rwa [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hu,
    one_mul] at hx

private theorem coe_inv_mul_mem (v : HeightOneSpectrum (𝓞 K)) {u : 𝓞 K} (hu : v.intValuation u = 1)
    {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    (((algebraMap (𝓞 K) K u)⁻¹ : K) : v.adicCompletion K) * x ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
    HeightOneSpectrum.valuation_of_algebraMap, hu, inv_one, one_mul]
  exact hx

omit [NumberField L] in

private theorem tmul_eq_tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum (𝓞 K)) {y : 𝓞 K}
    (hy : v.intValuation y = 1) {e : L} (he : IsIntegral (𝓞 K) (y • e)) {a : v.adicCompletion K}
    (ha : a ∈ v.adicCompletionIntegers K) :
    e ⊗ₜ[K] a = HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v
      ((⟨y • e, isIntegral_trans (y • e) he⟩ : 𝓞 L) ⊗ₜ[𝓞 K]
        (⟨(((algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) * a, coe_inv_mul_mem K v hy ha⟩ :
          v.adicCompletionIntegers K)) := by
  have hy' : y ≠ 0 := fun h => HeightOneSpectrum.intValuation_eq_one_iff.mp hy (h ▸ v.asIdeal.zero_mem)
  have hy0 : algebraMap (𝓞 K) K y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hy'
  rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]
  change e ⊗ₜ[K] a = (y • e) ⊗ₜ[K] ((((algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) * a)
  rw [← algebraMap_smul (A := K) y e, TensorProduct.smul_tmul, Algebra.smul_def,
    ← mul_assoc,
    show (((algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) ((algebraMap (𝓞 K) K y)⁻¹) from rfl,
    ← map_mul (algebraMap K (v.adicCompletion K))]
  show e ⊗ₜ[K] a =
    e ⊗ₜ[K] (((algebraMap (𝓞 K) K y * (algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) * a)
  rw [mul_inv_cancel₀ hy0]
  show e ⊗ₜ[K] a = e ⊗ₜ[K] ((1 : v.adicCompletion K) * a)
  rw [one_mul]

end LocalTraceIntegers
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

private theorem exists_finset_forall_localTraceFibre_mem_semiLocalIntegers_iff
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S₀,
      ∀ (r : v.adicCompletion K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K),
        localTraceFibre K L v r w ∈ AutomorphicForm.semiLocalIntegers K L v ↔
          r ∈ v.adicCompletionIntegers K ∧ ∀ i, w i ∈ v.adicCompletionIntegers K := by
  classical
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

  obtain ⟨d, hd0, hd⟩ := exists_denominator K L
    fun o : Option (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) =>
      o.elim (Algebra.trace K L) (coordFunctional K L)

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples (𝓞 K) K
    (insert ((Module.finrank K L : L)⁻¹)
      (Finset.univ.image fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)))
  have hdy : Ideal.span {d * y} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hd0 hy0
  refine ⟨(Ideal.finite_factors hdy).toFinset, fun v hv r w => ?_⟩
  have hv' : d * y ∉ v.asIdeal := by
    intro h
    exact hv ((Ideal.finite_factors hdy).mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
  have hdv : v.intValuation d = 1 :=
    HeightOneSpectrum.intValuation_eq_one_iff.mpr fun h => hv' (v.asIdeal.mul_mem_right y h)
  have hyv : v.intValuation y = 1 :=
    HeightOneSpectrum.intValuation_eq_one_iff.mpr fun h => hv' (v.asIdeal.mul_mem_left d h)
  constructor
  · intro hx
    refine ⟨mem_of_coe_mul_mem K v hdv ?_, fun i => mem_of_coe_mul_mem K v hdv ?_⟩
    · have h := coe_mul_functionalLift_mem K L v (Algebra.trace K L) d (hd none) hx
      rwa [functionalLift_trace_localTraceFibre] at h
    · have h := coe_mul_functionalLift_mem K L v (coordFunctional K L i) d (hd (some i)) hx
      rwa [functionalLift_coord_localTraceFibre] at h
  · rintro ⟨hr, hw⟩
    have hn : IsIntegral (𝓞 K) (y • (Module.finrank K L : L)⁻¹) := hy _ (Finset.mem_insert_self _ _)
    have hc : ∀ i, IsIntegral (𝓞 K) (y • (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) := fun i =>
      hy _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    rw [AutomorphicForm.semiLocalIntegers]
    let z₀ : 𝓞 L := ⟨y • (Module.finrank K L : L)⁻¹, isIntegral_trans _ hn⟩
    let zc : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → 𝓞 L := fun i =>
      ⟨y • (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L), isIntegral_trans _ (hc i)⟩
    let a₀ : v.adicCompletionIntegers K :=
      ⟨(((algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) * r, coe_inv_mul_mem K v hyv hr⟩
    let ac : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletionIntegers K := fun i =>
      ⟨(((algebraMap (𝓞 K) K y)⁻¹ : K) : v.adicCompletion K) * w i, coe_inv_mul_mem K v hyv (hw i)⟩
    refine ⟨z₀ ⊗ₜ[𝓞 K] a₀ + ∑ i, zc i ⊗ₜ[𝓞 K] ac i, ?_⟩
    rw [map_add, map_sum, localTraceFibre]
    congr 1
    · exact (tmul_eq_tensorAdicCompletionIntegersTo_tmul K L v hyv hn hr).symm
    · exact Finset.sum_congr rfl fun i _ => (tmul_eq_tensorAdicCompletionIntegersTo_tmul K L v hyv (hc i) (hw i)).symm

end ProductFormula
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

section Factorization

open scoped Classical NumberField.LiesOver

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private noncomputable def infIntegrand (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (gL : InfiniteAdeleRing L → ℂ) (ρ : InfiniteAdeleRing K)
    (s : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → mixedEmbedding.mixedSpace K) : ℂ :=
  gL (traceFibreInf K L ρ fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s i))

private theorem apply_traceFibreInf_eq_infIntegrand (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (gL : InfiniteAdeleRing L → ℂ) (ρ : InfiniteAdeleRing K)
    (y : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) :
    gL (traceFibreInf K L ρ y) = infIntegrand K L gL ρ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (y i) := by
  simp only [infIntegrand, RingEquiv.symm_apply_apply]

private noncomputable def infPush (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (gL : InfiniteAdeleRing L → ℂ) (κ : ℝ) (ρ : InfiniteAdeleRing K) : ℂ :=
  κ * ∫ s, infIntegrand K L gL ρ s

private theorem continuous_infIntegrand (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (gL : InfiniteAdeleRing L → ℂ) (hgL : Continuous gL) (ρ : InfiniteAdeleRing K) :
    Continuous (infIntegrand K L gL ρ) := by
  obtain ⟨φ, -, hφs⟩ := exists_mixedHomeomorph K
  have hS : Continuous fun s : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      mixedEmbedding.mixedSpace K => fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s i) := by
    simp only [← hφs]
    exact continuous_pi fun i => φ.symm.continuous.comp (continuous_apply i)
  exact hgL.comp (((continuous_traceFibreInf K L).comp (Continuous.prodMk_right ρ)).comp hS)

private theorem hasCompactSupport_infIntegrand (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (gL : InfiniteAdeleRing L → ℂ) (hgL : HasCompactSupport gL) (ρ : InfiniteAdeleRing K) :
    HasCompactSupport (infIntegrand K L gL ρ) := by
  obtain ⟨φ, hφ, -⟩ := exists_mixedHomeomorph K
  have hT := isCompact_preimage_traceFibreInf K L hgL.isCompact
  have hslice : IsCompact {y : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K |
      traceFibreInf K L ρ y ∈ tsupport gL} := by
    refine ((hT.inter_right ((isClosed_singleton (x := ρ)).prod isClosed_univ)).image
      continuous_snd).of_isClosed_subset
      ((isClosed_tsupport gL).preimage ((continuous_traceFibreInf K L).comp (Continuous.prodMk_right ρ))) ?_
    intro y hy
    exact ⟨(ρ, y), ⟨hy, Set.mem_singleton ρ, Set.mem_univ y⟩, rfl⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (hslice.image (continuous_pi fun i => φ.continuous.comp (continuous_apply i))) fun s hs => ?_
  have hne : gL (traceFibreInf K L ρ fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s i)) ≠ 0 :=
    Function.mem_support.1 hs
  refine ⟨fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s i), subset_tsupport _ hne,
    funext fun i => ?_⟩
  show φ ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s i)) = s i
  rw [hφ, RingEquiv.apply_symm_apply]

end Factorization
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

section FactorizationFinite

open scoped Classical TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem exists_traceAdaptedBasis (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ b : Module.Basis (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1)) K L,
      ⇑b = Fin.cons ((Module.finrank K L : L))⁻¹
        (fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) := by
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
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩

private theorem exists_localTraceCoords (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → v.adicCompletion K) ≃ₜ
        L ⊗[K] v.adicCompletion K,
      ∀ (t : v.adicCompletion K) (z : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K),
        e (Fin.cons t z) = localTraceFibre K L v t z := by
  classical
  obtain ⟨b, hb⟩ := exists_traceAdaptedBasis K L
  let b' : Module.Basis (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1)) (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K) := b.rightBaseChange L
  let equiv : L ⊗[K] v.adicCompletion K ≃L[v.adicCompletion K]
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → v.adicCompletion K) :=
    IsModuleTopology.continuousLinearEquiv b'.equivFun
  refine ⟨equiv.symm.toHomeomorph, fun t z => ?_⟩
  show equiv.symm (Fin.cons t z) = _
  rw [IsModuleTopology.continuousLinearEquiv_symm_apply, Module.Basis.equivFun_symm_apply, Fin.sum_univ_succ]
  simp only [b', Module.Basis.rightBaseChange_apply, hb, Fin.cons_zero, Fin.cons_succ, localTraceFibre,
    TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.comm_symm_tmul]

private theorem continuous_localTraceFibre_uncurry (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun p : v.adicCompletion K ×
        (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) =>
      localTraceFibre K L v p.1 p.2 := by
  obtain ⟨e, he⟩ := exists_localTraceCoords K L v
  have h : (fun p : v.adicCompletion K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      v.adicCompletion K) => localTraceFibre K L v p.1 p.2) = fun p => e (Fin.cons p.1 p.2) :=
    funext fun p => (he p.1 p.2).symm
  rw [h]
  exact e.continuous.comp (Continuous.finCons (A := fun _ => v.adicCompletion K) continuous_fst continuous_snd)

private theorem isCompact_preimage_localTraceFibre (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) {C : Set (L ⊗[K] v.adicCompletion K)}
    (hC : IsCompact C) :
    IsCompact {p : v.adicCompletion K ×
        (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) |
      localTraceFibre K L v p.1 p.2 ∈ C} := by
  obtain ⟨e, he⟩ := exists_localTraceCoords K L v
  have hπ : Continuous fun x : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → v.adicCompletion K =>
      (x 0, Fin.tail x) :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply (Fin.succ i))
  have hS : {p : v.adicCompletion K ×
        (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) |
      localTraceFibre K L v p.1 p.2 ∈ C} =
      (fun x : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → v.adicCompletion K =>
        (x 0, Fin.tail x)) '' (e ⁻¹' C) := by
    ext p
    constructor
    · intro hp
      refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
      · show e (Fin.cons p.1 p.2) ∈ C
        rw [he]
        exact hp
      · simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta]
    · rintro ⟨x, hx, rfl⟩
      show localTraceFibre K L v (x 0) (Fin.tail x) ∈ C
      rw [← he, Fin.cons_self_tail]
      exact hx
  rw [hS]
  exact (e.isCompact_preimage.2 hC).image hπ

private theorem isLocallyConstant_and_hasCompactSupport_localTracePushforward (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (f : L ⊗[K] v.adicCompletion K → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    IsLocallyConstant (localTracePushforward K L v f) ∧ HasCompactSupport (localTracePushforward K L v f) := by
  have hΘ : IsLocallyConstant fun p : v.adicCompletion K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) =>
        f (localTraceFibre K L v p.1 p.2) :=
    hf.comp_continuous (continuous_localTraceFibre_uncurry K L v)
  have hΘc : HasCompactSupport fun p : v.adicCompletion K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) =>
        f (localTraceFibre K L v p.1 p.2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_preimage_localTraceFibre K L v hfc) fun _ hp =>
      subset_tsupport f (Function.mem_support.1 hp)
  have h1 := isLocallyConstant_integral_of_hasCompactSupport
    (Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) =>
      ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
        (Measure.addHaar : Measure (v.adicCompletion K))) hΘ hΘc
  have h2 := hasCompactSupport_integral_of_hasCompactSupport
    (Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) =>
      ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
        (Measure.addHaar : Measure (v.adicCompletion K))) hΘc
  show IsLocallyConstant (fun r => ∫ w, f (localTraceFibre K L v r w)
      ∂(Measure.pi fun _ =>
        ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
          (Measure.addHaar : Measure (v.adicCompletion K)))) ∧
    HasCompactSupport (fun r => ∫ w, f (localTraceFibre K L v r w)
      ∂(Measure.pi fun _ =>
        ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
          (Measure.addHaar : Measure (v.adicCompletion K))))
  exact ⟨h1, h2⟩

private theorem indicator_traceFibre_eq_of_inf (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {S₀ SK : Finset (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ SK)
    (hS₀ : ∀ v ∉ S₀, ∀ (r : v.adicCompletion K)
      (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K),
      localTraceFibre K L v r w ∈ AutomorphicForm.semiLocalIntegers K L v ↔
        r ∈ v.adicCompletionIntegers K ∧ ∀ i, w i ∈ v.adicCompletionIntegers K)
    (gL : InfiniteAdeleRing L → ℂ) (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    (semiLocalIntegralOutside K L SK).indicator
        (fun x => gL x.1 * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) (traceFibre K L r w) =
      (NumberField.TateGlobal.integralOutside SK).indicator (fun _ => (1 : ℂ)) r *
        (infIntegrand K L gL r.1 (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (w i).1) *
          ((∏ v ∈ SK, Fv v (localTraceFibre K L v (r.2 v) fun i => ((w i).2 : FiniteAdeleRing (𝓞 K) K) v)) *
            if ∀ i, ∀ v ∉ SK, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K then 1 else 0)) := by
  have hmem : traceFibre K L r w ∈ semiLocalIntegralOutside K L SK ↔
      r ∈ NumberField.TateGlobal.integralOutside SK ∧
        ∀ i, ∀ v ∉ SK, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K := by
    simp only [semiLocalIntegralOutside, NumberField.TateGlobal.integralOutside, Set.mem_setOf_eq,
      semiLocalEval_traceFibre_snd]
    constructor
    · intro h
      exact ⟨fun v hv => ((hS₀ v (fun h0 => hv (hS h0)) _ _).1 (h v hv)).1,
        fun i v hv => ((hS₀ v (fun h0 => hv (hS h0)) _ _).1 (h v hv)).2 i⟩
    · rintro ⟨hr, hw⟩ v hv
      exact (hS₀ v (fun h0 => hv (hS h0)) _ _).2 ⟨hr v hv, fun i => hw i v hv⟩
  by_cases hr : r ∈ NumberField.TateGlobal.integralOutside SK
  · by_cases hw : ∀ i, ∀ v ∉ SK, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K
    · have hfst : (traceFibre K L r w).1 = traceFibreInf K L r.1 fun j => (w j).1 := by rw [traceFibre_eq_components]
      rw [Set.indicator_of_mem (hmem.2 ⟨hr, hw⟩), Set.indicator_of_mem hr, if_pos hw]
      simp only [semiLocalEval_traceFibre_snd, hfst, apply_traceFibreInf_eq_infIntegrand K L gL, one_mul, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hw (hmem.1 h).2), if_neg hw, mul_zero, mul_zero, mul_zero]
  · rw [Set.indicator_of_notMem (fun h => hr (hmem.1 h).1), Set.indicator_of_notMem hr, zero_mul]

private theorem tracePushforward_eq_indicator_of_productFormula (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] {κ : ℝ}
    (hκ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (a : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → mixedEmbedding.mixedSpace K) → ℂ)
      (b : (v : HeightOneSpectrum (𝓞 K)) →
        (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) → ℂ),
      Continuous a → HasCompactSupport a → (∀ v ∈ S, IsLocallyConstant (b v) ∧ HasCompactSupport (b v)) →
        ∫ w, a (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K (w i).1) *
              ((∏ v ∈ S, b v fun i => ((w i).2 : FiniteAdeleRing (𝓞 K) K) v) *
                if ∀ i, ∀ v ∉ S, ((w i).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K then 1 else 0)
            ∂(Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) => adelicAddHaar (𝓞 K) K) =
          κ * ((∫ t, a t) * ∏ v ∈ S, ∫ t, b v t
            ∂(Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) =>
              ((Measure.addHaar : Measure (v.adicCompletion K))
                (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
                (Measure.addHaar : Measure (v.adicCompletion K)))))
    {S₀ SK : Finset (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ SK)
    (hS₀ : ∀ v ∉ S₀, ∀ (r : v.adicCompletion K)
      (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K),
      localTraceFibre K L v r w ∈ AutomorphicForm.semiLocalIntegers K L v ↔
        r ∈ v.adicCompletionIntegers K ∧ ∀ i, w i ∈ v.adicCompletionIntegers K)
    (gL : InfiniteAdeleRing L → ℂ) (hgLc : Continuous gL) (hgLs : HasCompactSupport gL)
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (hFv : ∀ v ∈ SK, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) (F : AdeleRing (𝓞 L) L → ℂ)
    (hF : ∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
      (fun x => gL x.1 * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x)
    (r : AdeleRing (𝓞 K) K) :
    tracePushforward K L F r = (NumberField.TateGlobal.integralOutside SK).indicator
      (fun r => infPush K L gL κ r.1 *
        ∏ v ∈ SK, localTracePushforward K L v (Fv v) ((r.2 : FiniteAdeleRing (𝓞 K) K) v)) r := by

  have ha : Continuous (infIntegrand K L gL r.1) := continuous_infIntegrand K L gL hgLc r.1
  have hac : HasCompactSupport (infIntegrand K L gL r.1) := hasCompactSupport_infIntegrand K L gL hgLs r.1
  have hb : ∀ v ∈ SK, IsLocallyConstant (fun z => Fv v (localTraceFibre K L v (r.2 v) z)) ∧
      HasCompactSupport fun z => Fv v (localTraceFibre K L v (r.2 v) z) := by
    intro v hv
    have hcont : Continuous fun z : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K =>
        localTraceFibre K L v (r.2 v) z :=
      (continuous_localTraceFibre_uncurry K L v).comp (Continuous.prodMk_right (r.2 v))
    refine ⟨(hFv v hv).1.comp_continuous hcont, ?_⟩
    have hT := isCompact_preimage_localTraceFibre K L v (hFv v hv).2
    refine HasCompactSupport.of_support_subset_isCompact
      ((hT.inter_right ((isClosed_singleton (x := ((r.2 : FiniteAdeleRing (𝓞 K) K) v))).prod
        isClosed_univ)).image continuous_snd) fun z hz => ?_
    exact ⟨((r.2 : FiniteAdeleRing (𝓞 K) K) v, z),
      ⟨subset_tsupport _ (Function.mem_support.1 hz), Set.mem_singleton _, Set.mem_univ _⟩, rfl⟩
  have hint := hκ SK (infIntegrand K L gL r.1) (fun v z => Fv v (localTraceFibre K L v (r.2 v) z)) ha hac hb

  beta_reduce at hint
  unfold tracePushforward
  simp only [hF, indicator_traceFibre_eq_of_inf K L hS hS₀ gL Fv r]
  rw [integral_const_mul, hint]
  by_cases hr : r ∈ NumberField.TateGlobal.integralOutside SK
  · simp only [Set.indicator_of_mem hr, infPush, localTracePushforward]
    ring
  · simp only [Set.indicator_of_notMem hr, zero_mul]

end FactorizationFinite
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

open scoped TensorProduct.RightActions in

private theorem exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ gL : InfiniteAdeleRing L → ℂ, Continuous gL → HasCompactSupport gL →
      ∃ gK : InfiniteAdeleRing K → ℂ,
      ∀ (SK : Finset (HeightOneSpectrum (𝓞 K))) (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
        (F : AdeleRing (𝓞 L) L → ℂ),
        S₀ ⊆ SK →
        (∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
          (fun x => gL x.1 * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x) →
        (∀ v ∈ SK, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) →
        (∀ r, tracePushforward K L F r = (NumberField.TateGlobal.integralOutside SK).indicator
          (fun r => gK r.1 * ∏ v ∈ SK, localTracePushforward K L v (Fv v) ((r.2 : FiniteAdeleRing (𝓞 K) K) v)) r) ∧
          ∀ v ∈ SK, IsLocallyConstant (localTracePushforward K L v (Fv v)) ∧
            HasCompactSupport (localTracePushforward K L v (Fv v)) := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_forall_localTraceFibre_mem_semiLocalIntegers_iff K L
  obtain ⟨κ, -, hκ⟩ := exists_pos_integral_pi_adelicAddHaar_eq_mul_integral_mul_prod_integral K
    (Module.finrank K (LinearMap.ker (Algebra.trace K L)))
  refine ⟨S₀, fun gL hgLc hgLs => ⟨infPush K L gL κ, fun SK Fv F hS hF hFv => ⟨fun r => ?_, fun v hv => ?_⟩⟩⟩
  · exact tracePushforward_eq_indicator_of_productFormula K L hκ hS hS₀ gL hgLc hgLs Fv hFv F hF r
  · exact isLocallyConstant_and_hasCompactSupport_localTracePushforward K L v (Fv v) (hFv v hv).1 (hFv v hv).2

end
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula"

end AdelicTracePushforward
p2m_reactivate "P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward.BoxProductFormula P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.AdelicTracePushforward"

open NumberField IsDedekindDomain
open AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ gL : InfiniteAdeleRing L → ℂ, Continuous gL → HasCompactSupport gL →
      ∃ gK : InfiniteAdeleRing K → ℂ,
      ∀ (SK : Finset (HeightOneSpectrum (𝓞 K))) (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
        (F : AdeleRing (𝓞 L) L → ℂ),
        S₀ ⊆ SK →
        (∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
          (fun x => gL x.1 * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x) →
        (∀ v ∈ SK, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) →
        (∀ r, tracePushforward K L F r = (NumberField.TateGlobal.integralOutside SK).indicator
          (fun r => gK r.1 * ∏ v ∈ SK, localTracePushforward K L v (Fv v) ((r.2 : FiniteAdeleRing (𝓞 K) K) v)) r) ∧
          ∀ v ∈ SK, IsLocallyConstant (localTracePushforward K L v (Fv v)) ∧
            HasCompactSupport (localTracePushforward K L v (Fv v)) :=
  AdelicTracePushforward.exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator K L

#print axioms solution

end S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
end P2MW
export P2MW.S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator (solution)
