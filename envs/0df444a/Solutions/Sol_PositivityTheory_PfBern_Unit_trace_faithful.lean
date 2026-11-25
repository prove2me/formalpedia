-- Prove2me | solution 1 for PositivityTheory.PfBern.Unit.trace_faithful
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:42.551948+00:00
-- url     : https://prove2.me/submissions/39883047-74e8-4de5-a138-b4c406b3f533

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul
import Theorems.Thm_PositivityTheory_PfBern_Unit_level_density
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_idem_eq_fixedProj
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Unit
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace PositivityTheory.PfBern.Unit
theorem _root_.solution (hρ : IsAdmissible ρ) [ρ.IsIrreducible] (S : Module.End ℂ V)
    (h : ∀ f : locallyConstantCompactSupport G ℂ ℂ, finTrace (heckeLin μ hρ.1 f ∘ₗ S) = 0) : S = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ (S v) : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 (S v)).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  haveI := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have hSvW : S v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  let M : Module.End ℂ (fixedVectors ρ (K : Subgroup G)) :=
    fixedProj ρ hρ.1 hKc hKo ∘ₗ S ∘ₗ (fixedVectors ρ (K : Subgroup G)).subtype
  have htr : ∀ r : HeckeAlgebraLevel μ (K : Subgroup G) hKc hKo,
      LinearMap.trace ℂ (fixedVectors ρ (K : Subgroup G)) (levelLin hKc hKo ρ r ∘ₗ M) = 0 := by
    intro r
    have hle : LinearMap.range (heckeLin μ hρ.1 (r : HeckeAlgebra μ) ∘ₗ S) ≤ fixedVectors ρ (K : Subgroup G) := by
      rintro _ ⟨x, rfl⟩
      exact range_heckeLin_le μ hρ.1 (r : HeckeAlgebra μ) (K := (K : Subgroup G))
        (fun k hk y => HeckeAlgebraLevel.apply_mul_left hKc hKo r hk y) (LinearMap.mem_range_self _ (S x))
    have h0 := h (r : HeckeAlgebra μ)
    rw [← finTrace_eq_trace _ _ hle] at h0
    convert h0 using 2
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hri : idem μ hKc hKo * (r : HeckeAlgebra μ) = (r : HeckeAlgebra μ) ∧
        (r : HeckeAlgebra μ) * idem μ hKc hKo = (r : HeckeAlgebra μ) :=
      (mem_biInvariant_iff_idem hKc hKo).1 (HeckeAlgebraLevel.val_mem hKc hKo r)
    change heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (fixedProj ρ hρ.1 hKc hKo (S w) : V) =
      heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (S w)
    rw [← heckeAct_idem_eq_fixedProj (μ := μ) hKc hKo hρ.1,
      ← heckeAct_groupConv (r : HeckeAlgebra μ).mem (idem μ hKc hKo).mem (hρ.1 _), ← HeckeAlgebra.coe_mul, hri.2]
  have hM : M = 0 := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    by_contra hne
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors ρ (K : Subgroup G)), φ (M w) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ (M w)).1 hall)
    obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW (φ.smulRight w)
    have := htr r
    rw [hr] at this
    have e : φ.smulRight w ∘ₗ M = (φ ∘ₗ M).smulRight w := LinearMap.ext fun x => rfl
    rw [e, LinearMap.trace_smulRight] at this
    exact hφ this
  have h1 : (M ⟨v, hvW⟩ : V) = S v := fixedProj_apply_of_mem hρ.1 hKc hKo hSvW
  rw [← h1, hM, LinearMap.zero_apply, Submodule.coe_zero]
end PositivityTheory.PfBern.Unit
