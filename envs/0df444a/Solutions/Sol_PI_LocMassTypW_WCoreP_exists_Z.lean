-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.exists_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:18.275751+00:00
-- url     : https://prove2.me/submissions/d3f17fe9-b7bc-41b5-89a6-ab7634ccd454

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w) :
    ∃ Z : Submodule K V, Z ≤ LinearMap.ker b ∧ (∀ z ∈ Z, z ∈ LinearMap.range a → z = 0) ∧
      finrank K Z + finrank K (LinearMap.ker (b ∘ₗ a)) + finrank K W = finrank K V := by
  set S := LinearMap.range a ⊓ LinearMap.ker b with hSdef
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.comap (LinearMap.ker b).subtype S)
  refine ⟨C.map (LinearMap.ker b).subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · intro z hz hza
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hz
    have hcS : c ∈ Submodule.comap (LinearMap.ker b).subtype S := ⟨hza, c.2⟩
    have h0 : c = 0 := (Submodule.disjoint_def.mp hC.disjoint) c hcS hc
    rw [h0, map_zero]
  · have h1 := Submodule.finrank_add_eq_of_isCompl hC
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker b) (Submodule.comap _ S),
      Submodule.map_comap_subtype] at h1
    rw [Submodule.finrank_map_subtype_eq]
    have h2 : finrank K ↥(LinearMap.ker b ⊓ S) = finrank K (LinearMap.ker (b ∘ₗ a)) := by
      have hS : LinearMap.ker b ⊓ S = (LinearMap.ker (b ∘ₗ a)).map a := by
        rw [LinearMap.ker_comp, Submodule.map_comap_eq, hSdef, inf_comm, inf_assoc, inf_idem]
      rw [hS]
      exact (Submodule.equivMapOfInjective a ha _).finrank_eq.symm
    have h3 : finrank K (LinearMap.ker b) + finrank K W = finrank K V := by
      have h4 := LinearMap.finrank_range_add_finrank_ker b
      have hr : LinearMap.range b = ⊤ := LinearMap.range_eq_top.mpr fun w => ⟨s w, hbs w⟩
      rw [hr, finrank_top] at h4
      omega
    omega
end PI.LocMassTypW.WCoreP
