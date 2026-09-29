-- Prove2me | solution 1 for TraceFibrePushforward.tracePushforward_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9c54486c-4d27-5e4a-b3cf-6cca85d3fbd7

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
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TraceFibrePushforward_tracePushforward_mem_schwartzBruhat
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

private theorem cons_add_cons {α : Type*} [Add α] {m : ℕ} (a b : α) (u v : Fin m → α) :
    (Fin.cons a u : Fin (m + 1) → α) + Fin.cons b v = Fin.cons (a + b) (u + v) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Pi.add_apply, Fin.cons_zero]
  · simp only [Pi.add_apply, Fin.cons_succ]

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

include hprop in

private theorem hasCompactSupport_comp_of_isCompact_preimage {k : Y' → ℂ} (hkc : HasCompactSupport k) :
    HasCompactSupport fun p : X × Y => k (Ψ p) :=
  HasCompactSupport.of_support_subset_isCompact (hprop _ hkc) fun _ hp =>
    subset_tsupport k (Function.mem_support.1 hp)

omit [T2Space X] in
include hΨ hprop in

private theorem integrable_comp_slice [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    [IsFiniteMeasureOnCompacts ν] {k : Y' → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) (x : X) :
    Integrable (fun y => k (Ψ (x, y))) ν := by
  have hS : IsCompact {p : X × Y | Ψ p ∈ tsupport k} := hprop _ hkc
  have hcont : Continuous fun y => k (Ψ (x, y)) := hk.comp (hΨ.comp (Continuous.prodMk_right x))
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (hS.image continuous_snd) fun y hy => ?_)
  exact image_eq_zero_of_notMem_tsupport fun hmem => hy ⟨(x, y), hmem, rfl⟩

end Slices

section Sums

variable {X ι : Type} [TopologicalSpace X] [T2Space X]

private theorem hasCompactSupport_finset_sum (s : Finset ι) {t : ι → X → ℂ} (ht : ∀ i ∈ s, HasCompactSupport (t i)) :
    HasCompactSupport fun x => ∑ i ∈ s, t i x :=
  HasCompactSupport.of_support_subset_isCompact (s.isCompact_biUnion fun i hi => ht i hi) fun x hx => by
    by_contra hout
    refine Function.mem_support.1 hx (Finset.sum_eq_zero fun i hi => ?_)
    exact image_eq_zero_of_notMem_tsupport fun hmem => hout (Set.mem_iUnion₂.2 ⟨i, hi, hmem⟩)

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

omit [SecondCountableTopology W] in
include hAB in

private theorem exists_integrable_bound_comp_add {E : Type} [NormedAddCommGroup E] {k : V' → E} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    ∃ bound : W → ℝ, Integrable bound μ ∧ ∀ (ρ : V) (w : W), ‖k (A ρ + B w)‖ ≤ bound w := by
  obtain ⟨M, hM⟩ := hkc.exists_bound_of_continuous hk
  have hS : IsCompact {p : V × W | A p.1 + B p.2 ∈ tsupport k} := hAB _ hkc
  have hK : IsCompact (Prod.snd '' {p : V × W | A p.1 + B p.2 ∈ tsupport k}) := hS.image continuous_snd
  refine ⟨(Prod.snd '' {p : V × W | A p.1 + B p.2 ∈ tsupport k}).indicator fun _ => max M 0,
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet, fun ρ w => ?_⟩
  by_cases hw : w ∈ Prod.snd '' {p : V × W | A p.1 + B p.2 ∈ tsupport k}
  · rw [indicator_of_mem hw]
    exact (hM _).trans (le_max_left _ _)
  · rw [indicator_of_notMem hw]
    have hnot : A ρ + B w ∉ tsupport k := fun h => hw ⟨(ρ, w), h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot, norm_zero]

include hB hAB in

private theorem contDiff_integral_comp_add_aux (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : V' → E), ContDiff ℝ n g →
      HasCompactSupport g → ContDiff ℝ n fun ρ : V => ∫ w, g (A ρ + B w) ∂μ := by
  induction n with
  | zero =>
    intro E _ _ _ g hg hgc
    have hgcont : Continuous g := hg.continuous
    obtain ⟨bound, hbi, hb⟩ := exists_integrable_bound_comp_add A hAB (μ := μ) hgcont hgc
    refine contDiff_zero.2 (continuous_of_dominated (fun ρ => ?_) (fun ρ => ae_of_all _ (hb ρ)) hbi (ae_of_all _ ?_))
    · exact (hgcont.comp (continuous_const.add hB)).aestronglyMeasurable
    · intro w
      exact hgcont.comp (A.continuous.add continuous_const)
  | succ n ih =>
    intro E _ _ _ g hg hgc
    rw [Nat.cast_succ] at hg ⊢

    obtain ⟨g', hg'⟩ : ∃ g' : V' → (V →L[ℝ] E), ∀ y, g' y = (fderiv ℝ g y).comp A := ⟨_, fun _ => rfl⟩
    have hg'fun : g' = fun y => (fderiv ℝ g y).comp A := funext hg'
    have hfd : ContDiff ℝ n (fderiv ℝ g) := hg.fderiv_right le_rfl
    have hg'smooth : ContDiff ℝ n g' := by
      rw [hg'fun]
      exact hfd.clm_comp contDiff_const
    have hg'c : HasCompactSupport g' := (hgc.fderiv ℝ).mono fun y hy => Function.mem_support.2 fun h0 =>
      Function.mem_support.1 hy (by rw [hg', h0, ContinuousLinearMap.zero_comp])
    have hgcont : Continuous g := hg.continuous
    obtain ⟨bound, hbi, hb⟩ := exists_integrable_bound_comp_add A hAB (μ := μ) hgcont hgc
    obtain ⟨bound', hbi', hb'⟩ := exists_integrable_bound_comp_add A hAB (μ := μ) hg'smooth.continuous hg'c
    have hmeas : ∀ ρ : V, AEStronglyMeasurable (fun w => g (A ρ + B w)) μ := fun ρ =>
      (hgcont.comp (continuous_const.add hB)).aestronglyMeasurable
    have hderiv : ∀ ρ : V, HasFDerivAt (fun ρ : V => ∫ w, g (A ρ + B w) ∂μ) (∫ w, g' (A ρ + B w) ∂μ) ρ := by
      intro ρ₀
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun ρ w => g (A ρ + B w))
        (F' := fun ρ w => g' (A ρ + B w)) (bound := bound') (s := univ) Filter.univ_mem
        (Filter.Eventually.of_forall hmeas) ?_ ?_ (ae_of_all _ fun w ρ _ => hb' ρ w) hbi' (ae_of_all _ fun w ρ _ => ?_)
      · exact Integrable.mono' hbi (hmeas ρ₀) (ae_of_all _ (hb ρ₀))
      · exact (hg'smooth.continuous.comp (continuous_const.add hB)).aestronglyMeasurable
      · have hgd : DifferentiableAt ℝ g (A ρ + B w) :=
          (hg.differentiable (lt_of_lt_of_le zero_lt_one le_add_self).ne') _
        show HasFDerivAt (fun ρ => g (A ρ + B w)) (g' (A ρ + B w)) ρ
        rw [hg']
        exact hgd.hasFDerivAt.comp ρ (A.hasFDerivAt.add_const (B w))
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (V →L[ℝ] E) g' hg'smooth hg'c, fun ρ => hderiv ρ⟩

include hB hAB in

private theorem contDiff_integral_comp_add {g : V' → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) fun ρ : V => ∫ w, g (A ρ + B w) ∂μ :=
  contDiff_infty.2 fun n =>
    contDiff_integral_comp_add_aux A hB hAB (μ := μ) n ℂ g (hg.of_le (by exact_mod_cast le_top)) hgc

omit [T2Space W] [SecondCountableTopology W] [OpensMeasurableSpace W] [IsFiniteMeasureOnCompacts μ] in
include hAB in

private theorem hasCompactSupport_integral_comp_add {g : V' → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport fun ρ : V => ∫ w, g (A ρ + B w) ∂μ := by
  have hS : IsCompact {p : V × W | A p.1 + B p.2 ∈ tsupport g} := hAB _ hgc
  refine HasCompactSupport.intro (hS.image continuous_fst) fun ρ hρ => ?_
  have hzero : ∀ w, g (A ρ + B w) = 0 := fun w =>
    image_eq_zero_of_notMem_tsupport fun h => hρ ⟨(ρ, w), h, rfl⟩
  simp only [hzero, integral_zero]

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

private theorem continuous_adeleSnd : Continuous fun x : AdeleRing (𝓞 F) F => x.2 :=
  continuous_snd

private theorem continuous_adeleOfInf : Continuous fun ρ : InfiniteAdeleRing F => ((ρ, 0) : AdeleRing (𝓞 F) F) :=
  continuous_id.prodMk continuous_const

private theorem continuous_adeleOfFin :
    Continuous fun ρ : FiniteAdeleRing (𝓞 F) F => ((0, ρ) : AdeleRing (𝓞 F) F) :=
  continuous_const.prodMk continuous_id

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

private theorem traceFibre_add (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r r' : AdeleRing (𝓞 K) K)
    (w w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    traceFibre K L (r + r') (w + w') = traceFibre K L r w + traceFibre K L r' w' := by
  obtain ⟨e, htr, -⟩ := exists_traceCoords K L
  rw [← htr, ← htr, ← htr, ← cons_add_cons, map_add]

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

private theorem traceFibreInf_add (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ρ ρ' : InfiniteAdeleRing K)
    (u u' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) :
    traceFibreInf K L (ρ + ρ') (u + u') = traceFibreInf K L ρ u + traceFibreInf K L ρ' u' := by
  have h := congrArg Prod.fst
    (traceFibre_add K L (ρ, 0) (ρ', 0) (fun j => (u j, 0)) fun j => (u' j, 0))
  simp only [traceFibre_eq_components] at h
  exact h

private theorem traceFibreInf_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ρ : InfiniteAdeleRing K) (u : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) :
    traceFibreInf K L ρ u = traceFibreInf K L ρ 0 + traceFibreInf K L 0 u := by
  simpa only [add_zero, zero_add] using traceFibreInf_add K L ρ 0 0 u

private theorem traceFibreInf_add_left (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ρ ρ' : InfiniteAdeleRing K) :
    traceFibreInf K L (ρ + ρ') 0 = traceFibreInf K L ρ 0 + traceFibreInf K L ρ' 0 := by
  simpa only [add_zero] using traceFibreInf_add K L ρ ρ' 0 0

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

private theorem continuous_traceFibreFin (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    Continuous fun p : FiniteAdeleRing (𝓞 K) K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      FiniteAdeleRing (𝓞 K) K) => traceFibreFin K L p.1 p.2 := by
  have hpair : Continuous fun p : FiniteAdeleRing (𝓞 K) K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → FiniteAdeleRing (𝓞 K) K) =>
      (((0, p.1) : AdeleRing (𝓞 K) K), fun j => ((0, p.2 j) : AdeleRing (𝓞 K) K)) :=
    (continuous_adeleOfFin.comp continuous_fst).prodMk
      (continuous_pi fun j => continuous_adeleOfFin.comp ((continuous_apply j).comp continuous_snd))
  have h := (continuous_traceFibre_uncurry K L).comp hpair
  exact continuous_adeleSnd.comp h

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

private theorem isCompact_preimage_traceFibreFin (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {C : Set (FiniteAdeleRing (𝓞 L) L)} (hC : IsCompact C) :
    IsCompact {p : FiniteAdeleRing (𝓞 K) K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) →
      FiniteAdeleRing (𝓞 K) K) | traceFibreFin K L p.1 p.2 ∈ C} := by
  obtain ⟨e, htr, -⟩ := exists_traceCoords K L
  set y₀ : InfiniteAdeleRing L := traceFibreInf K L 0 fun _ => 0
  have hT : IsCompact (e ⁻¹' ({y₀} ×ˢ C)) :=
    e.toHomeomorph.isCompact_preimage.2 (isCompact_singleton.prod hC)
  have hπ : Continuous fun x : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K =>
      ((x 0).2, fun j => (x (Fin.succ j)).2) :=
    (continuous_apply (0 : Fin _)).snd.prodMk (continuous_pi fun j => (continuous_apply (Fin.succ j)).snd)
  refine (hT.image hπ).of_isClosed_subset (hC.isClosed.preimage (continuous_traceFibreFin K L)) ?_
  rintro ⟨ρ, v⟩ hp
  refine ⟨Fin.cons (0, ρ) fun j => (0, v j), ?_, ?_⟩
  · show e _ ∈ {y₀} ×ˢ C
    rw [htr, traceFibre_eq_components]
    exact ⟨rfl, hp⟩
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

private theorem hasCompactSupport_tensor (K : Type) [Field K] [NumberField K] {G : mixedEmbedding.mixedSpace K → ℂ}
    (hG : HasCompactSupport G) {H : FiniteAdeleRing (𝓞 K) K → ℂ} (hH : HasCompactSupport H) :
    HasCompactSupport fun x : AdeleRing (𝓞 K) K => G (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * H x.2 := by
  obtain ⟨φ, hφ, -⟩ := exists_mixedHomeomorph K
  have hS : IsCompact (φ ⁻¹' tsupport G) := φ.isCompact_preimage.2 hG
  refine HasCompactSupport.intro (hS.prod hH) fun x hx => ?_
  rcases not_and_or.1 (fun h' => hx (Set.mem_prod.2 h')) with h1 | h1
  · rw [← hφ, image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

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

open scoped Classical in

private theorem tracePushforward_mem_schwartzBruhat
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} (s : Finset ι) (g : ι → mixedEmbedding.mixedSpace L → ℂ)
    (hg : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i))
    (h : ι → FiniteAdeleRing (𝓞 L) L → ℂ)
    (hh : ∀ i ∈ s, IsLocallyConstant (h i)) (hhc : ∀ i ∈ s, HasCompactSupport (h i))
    (F : AdeleRing (𝓞 L) L → ℂ)
    (hF : ∀ x, F x = ∑ i ∈ s, g i (InfiniteAdeleRing.ringEquiv_mixedSpace L x.1) * h i x.2) :
    tracePushforward K L F ∈ NumberField.AdelicFourier.schwartzBruhat K ∧
      HasCompactSupport (tracePushforward K L F) ∧ Continuous (tracePushforward K L F) := by

  obtain ⟨φK, hφK, hφKs⟩ := exists_mixedHomeomorph K
  obtain ⟨φL, hφL, -⟩ := exists_mixedHomeomorph L

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
  obtain ⟨μ₁, μ₂, a, hμ₁, hμ₂, ha, hsplit⟩ :=
    exists_integral_pi_eq_mul_integral_prod (ι := Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))))
      (mP := adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K)
  haveI := hμ₁
  haveI := hμ₂

  obtain ⟨A, hA⟩ : ∃ A : mixedEmbedding.mixedSpace K →L[ℝ] mixedEmbedding.mixedSpace L,
      ∀ ρ, A ρ = φL (traceFibreInf K L (φK.symm ρ) 0) := by
    refine ⟨AddMonoidHom.toRealLinearMap
      (AddMonoidHom.mk' (fun ρ => φL (traceFibreInf K L (φK.symm ρ) 0)) fun ρ ρ' => ?_) ?_, fun ρ => rfl⟩
    · simp only [hφKs, map_add, traceFibreInf_add_left, hφL]
    · have h1 := (continuous_traceFibreInf K L).comp
        (φK.symm.continuous.prodMk (continuous_const
          (y := (0 : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K))))
      exact φL.continuous.comp h1
  obtain ⟨B, hBc, hB⟩ : ∃ B : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) →
      mixedEmbedding.mixedSpace L, Continuous B ∧ ∀ u, B u = φL (traceFibreInf K L 0 u) :=
    ⟨fun u => φL (traceFibreInf K L 0 u), by
      have h1 := (continuous_traceFibreInf K L).comp
        ((continuous_const (y := (0 : InfiniteAdeleRing K))).prodMk continuous_id)
      exact φL.continuous.comp h1, fun u => rfl⟩
  have hdec : ∀ (ρ : InfiniteAdeleRing K)
      (u : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K),
      φL (traceFibreInf K L ρ u) = A (φK ρ) + B u := by
    intro ρ u
    rw [hA, hB, φK.symm_apply_apply, traceFibreInf_split K L ρ u, hφL, hφL, hφL, map_add]
  have hAB : ∀ C : Set (mixedEmbedding.mixedSpace L), IsCompact C → IsCompact {p : mixedEmbedding.mixedSpace K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) | A p.1 + B p.2 ∈ C} := by
    intro C hC
    have hS := isCompact_preimage_traceFibreInf K L (φL.isCompact_preimage.2 hC)
    have himg := hS.image (φK.continuous.comp continuous_fst |>.prodMk continuous_snd)
    refine himg.of_isClosed_subset (hC.isClosed.preimage (A.continuous.comp continuous_fst |>.add
      (hBc.comp continuous_snd))) ?_
    rintro ⟨ρ, u⟩ hp
    refine ⟨(φK.symm ρ, u), ?_, ?_⟩
    · show φL (traceFibreInf K L (φK.symm ρ) u) ∈ C
      rwa [hdec, φK.apply_symm_apply]
    · show (φK (φK.symm ρ), u) = (ρ, u)
      rw [Homeomorph.apply_symm_apply]
  have hPsiArch : Continuous fun p : mixedEmbedding.mixedSpace K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → InfiniteAdeleRing K) => A p.1 + B p.2 :=
    (A.continuous.comp continuous_fst).add (hBc.comp continuous_snd)

  obtain ⟨𝒢, h𝒢⟩ : ∃ 𝒢 : ι → SchwartzMap (mixedEmbedding.mixedSpace K) ℂ, ∀ i ∈ s, ∀ ρ,
      𝒢 i ρ = ∫ u, g i (A ρ + B u) ∂(Measure.pi fun _ => μ₁) := by
    refine ⟨fun i => if hi : i ∈ s then
      (hasCompactSupport_integral_comp_add A hAB (μ := Measure.pi fun _ => μ₁) (hgc i hi)).toSchwartzMap
        (contDiff_integral_comp_add A hBc hAB (hg i hi) (hgc i hi)) else 0, fun i hi ρ => ?_⟩
    simp only [dif_pos hi]
    rfl

  obtain ⟨H, hH⟩ : ∃ H : ι → FiniteAdeleRing (𝓞 K) K → ℂ, ∀ i ρ,
      H i ρ = ∫ v, h i (traceFibreFin K L ρ v) ∂(Measure.pi fun _ => μ₂) := ⟨_, fun _ _ => rfl⟩
  have hHfun : ∀ i, H i = fun ρ => ∫ v, h i (traceFibreFin K L ρ v) ∂(Measure.pi fun _ => μ₂) := fun i =>
    funext (hH i)
  have hΘc : ∀ i ∈ s, HasCompactSupport fun p : FiniteAdeleRing (𝓞 K) K ×
      (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → FiniteAdeleRing (𝓞 K) K) =>
        h i (traceFibreFin K L p.1 p.2) := fun i hi =>
    hasCompactSupport_comp_of_isCompact_preimage (Ψ := fun p => traceFibreFin K L p.1 p.2)
      (fun C hC => isCompact_preimage_traceFibreFin K L hC) (hhc i hi)
  have hHlc : ∀ i ∈ s, IsLocallyConstant (H i) := fun i hi => by
    have hlc := isLocallyConstant_integral_of_hasCompactSupport (Measure.pi fun _ => μ₂)
      ((hh i hi).comp_continuous (continuous_traceFibreFin K L)) (hΘc i hi)
    rw [hHfun]
    exact hlc
  have hHc : ∀ i ∈ s, HasCompactSupport (H i) := fun i hi => by
    have hcs := hasCompactSupport_integral_of_hasCompactSupport (Measure.pi fun _ => μ₂) (hΘc i hi)
    rw [hHfun]
    exact hcs
  have h𝒢c : ∀ i ∈ s, HasCompactSupport ((a : ℝ) • 𝒢 i : mixedEmbedding.mixedSpace K → ℂ) := by
    intro i hi
    refine (hasCompactSupport_integral_comp_add A hAB (μ := Measure.pi fun _ => μ₁) (hgc i hi)).mono fun ρ hρ => ?_
    refine Function.mem_support.2 fun h0 => Function.mem_support.1 hρ ?_
    have h0' : (∫ u, g i (A ρ + B u) ∂(Measure.pi fun _ => μ₁)) = 0 := h0
    rw [Pi.smul_apply, h𝒢 i hi, h0', smul_zero]

  have hsum : ∀ r : AdeleRing (𝓞 K) K, tracePushforward K L F r =
      ∑ i ∈ s, ((a : ℝ) • 𝒢 i) (InfiniteAdeleRing.ringEquiv_mixedSpace K r.1) * H i r.2 := by
    intro r
    have hintArch : ∀ i ∈ s, Integrable (fun u => g i (A (φK r.1) + B u)) (Measure.pi fun _ => μ₁) := fun i hi =>
      integrable_comp_slice hPsiArch hAB (hg i hi).continuous (hgc i hi) (φK r.1)
    have hintf : ∀ i ∈ s, Integrable (fun v => h i (traceFibreFin K L r.2 v)) (Measure.pi fun _ => μ₂) := fun i hi =>
      integrable_comp_slice (continuous_traceFibreFin K L) (fun C hC => isCompact_preimage_traceFibreFin K L hC)
        (hh i hi).continuous (hhc i hi) r.2
    calc tracePushforward K L F r
        = a * ∫ p, F (traceFibre K L r fun j => (p.1 j, p.2 j))
            ∂((Measure.pi fun _ => μ₁).prod (Measure.pi fun _ => μ₂)) := hsplit _
      _ = a * ∫ p, ∑ i ∈ s, g i (A (φK r.1) + B p.1) * h i (traceFibreFin K L r.2 p.2)
            ∂((Measure.pi fun _ => μ₁).prod (Measure.pi fun _ => μ₂)) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          dsimp only
          rw [hF, traceFibre_eq_components]
          simp only [← hφL, hdec]
      _ = a * ∑ i ∈ s, ∫ p, g i (A (φK r.1) + B p.1) * h i (traceFibreFin K L r.2 p.2)
            ∂((Measure.pi fun _ => μ₁).prod (Measure.pi fun _ => μ₂)) := by
          congr 1
          exact integral_finsetSum s fun i hi => (hintArch i hi).mul_prod (hintf i hi)
      _ = ∑ i ∈ s, ((a : ℝ) • 𝒢 i) (InfiniteAdeleRing.ringEquiv_mixedSpace K r.1) * H i r.2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [integral_prod_mul (fun u => g i (A (φK r.1) + B u)) fun v => h i (traceFibreFin K L r.2 v),
            SchwartzMap.smul_apply, ← hφK, h𝒢 i hi, hH, Complex.real_smul, mul_assoc]
  have hfun : tracePushforward K L F = fun r =>
      ∑ i ∈ s, ((a : ℝ) • 𝒢 i) (InfiniteAdeleRing.ringEquiv_mixedSpace K r.1) * H i r.2 := funext hsum
  have hpi : tracePushforward K L F = ∑ i ∈ s, fun r : AdeleRing (𝓞 K) K =>
      ((a : ℝ) • 𝒢 i) (InfiniteAdeleRing.ringEquiv_mixedSpace K r.1) * H i r.2 :=
    hfun.trans (Finset.sum_fn s _).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hpi]
    exact Submodule.sum_mem _ fun i hi => AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet
      (AdelicFourier.tensor_mem_pureTensorSet ((a : ℝ) • 𝒢 i) (H i) (hHlc i hi) (hHc i hi))
  · rw [hfun]
    exact hasCompactSupport_finset_sum s fun i hi => hasCompactSupport_tensor K (h𝒢c i hi) (hHc i hi)
  · rw [hfun]
    exact continuous_finsetSum s fun i hi => (((a : ℝ) • 𝒢 i).continuous.comp
      ((AdelicBox.continuous_ringEquiv_mixedSpace K).comp continuous_fst)).mul
        ((hHlc i hi).continuous.comp continuous_snd)

end

end AdelicTracePushforward

open NumberField IsDedekindDomain
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} (s : Finset ι) (g : ι → mixedEmbedding.mixedSpace L → ℂ)
    (hg : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i))
    (h : ι → FiniteAdeleRing (𝓞 L) L → ℂ)
    (hh : ∀ i ∈ s, IsLocallyConstant (h i)) (hhc : ∀ i ∈ s, HasCompactSupport (h i))
    (F : AdeleRing (𝓞 L) L → ℂ)
    (hF : ∀ x, F x = ∑ i ∈ s, g i (InfiniteAdeleRing.ringEquiv_mixedSpace L x.1) * h i x.2) :
    tracePushforward K L F ∈ NumberField.AdelicFourier.schwartzBruhat K ∧
      HasCompactSupport (tracePushforward K L F) ∧ Continuous (tracePushforward K L F) :=
  AdelicTracePushforward.tracePushforward_mem_schwartzBruhat K L s g hg hgc h hh hhc F hF

#print axioms solution

end S_TraceFibrePushforward_tracePushforward_mem_schwartzBruhat
end P2MW
export P2MW.S_TraceFibrePushforward_tracePushforward_mem_schwartzBruhat (solution)
