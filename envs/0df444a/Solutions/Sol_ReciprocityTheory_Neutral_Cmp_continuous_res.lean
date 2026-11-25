-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.continuous_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:46.445952+00:00
-- url     : https://prove2.me/submissions/e8e75729-4ec1-4a85-b3de-b8da38a98479

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : Continuous (res (F := F) ι) := by
  letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra
  letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra
  haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : F →+* Kloc F ι := (ι.comp (algebraMap F Ω)).codRestrict (Kloc F ι)
    fun c => IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
  letI : Algebra F (Kloc F ι) := φ.toAlgebra
  haveI : IsScalarTower F (Kloc F ι) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : Ω, IsIntegral (Kloc F ι) (ι x) := fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral.map
      (IsScalarTower.toAlgHom F Ω (PadicAlgCl p))).tower_top
  apply continuous_of_continuousAt_one (res (F := F) ι)
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hEfin, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  haveI := hEfin
  let b := Module.finBasis F E
  let E' : IntermediateField (Kloc F ι) (PadicAlgCl p) :=
    IntermediateField.adjoin (Kloc F ι) (Set.range fun i => ι (b i))
  haveI : FiniteDimensional (Kloc F ι) E' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact hint _)
  have hE' : (E'.fixingSubgroup : Set (GK F ι)) ∈ nhds (1 : GK F ι) :=
    (krullTopology_mem_nhds_one_iff (Kloc F ι) (PadicAlgCl p) _).2 ⟨E', inferInstance, le_rfl⟩
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hE' fun σ hσ => hEs ?_
  have hb : ∀ i, res ι σ (b i : Ω) = b i := fun i => by
    apply ι.injective
    rw [res_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hL := b.ext (f₁ := (res ι σ).toLinearMap ∘ₗ E.val.toLinearMap)
    (f₂ := E.val.toLinearMap) fun i => hb i
  exact LinearMap.congr_fun hL ⟨x, hx⟩
end ReciprocityTheory.Neutral.Cmp
