-- Prove2me | solution 1 for UpperTheory.V.Base.galEmbTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:40:56.379305+00:00
-- url     : https://prove2.me/submissions/90c5c624-8f44-4059-b6ea-b74e4167bbd0

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_GalEmbTop
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base
private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm
    rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base
namespace UpperTheory.V.Base
theorem _root_.solution :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω
  intros
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _
    constructor
    · rintro h y ⟨x, rfl⟩
      simpa using h x
    · intro h x
      simpa using h _ ⟨x, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩,
        fun σ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩
  · intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  · rw [hset]
    exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm
end UpperTheory.V.Base
