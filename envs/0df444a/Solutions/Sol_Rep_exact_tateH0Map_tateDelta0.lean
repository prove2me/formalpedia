-- Prove2me | solution 1 for Rep.exact_tateH0Map_tateDelta0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/843412fa-8c7c-55ac-a33d-d1ac033b002e

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exact_tateH0Map_tateDelta0

universe u

set_option autoImplicit false
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateH0Map X.g) (Rep.tateδ₀ hX) := by
  have h3 : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 0).hom =
      LinearMap.ker (groupCohomology.δ hX 0 1 rfl).hom :=
    (groupCohomology.mapShortComplex₃_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  have hnat : ∀ u, (groupCohomology.H0Iso X.X₃).hom ((groupCohomology.map (MonoidHom.id G) X.g 0) u) =
      Rep.invariantsMap X.g ((groupCohomology.H0Iso X.X₂).hom u) :=
    fun u => groupCohomology.map_id_comp_H0Iso_hom_apply X.g u
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Rep.tateδ₀_mk]
  constructor
  · intro hz
    have hz' : (groupCohomology.H0Iso X.X₃).inv z ∈
        LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 0).hom := by
      rw [h3]; exact hz
    obtain ⟨u, hu⟩ := hz'
    refine ⟨Submodule.Quotient.mk ((groupCohomology.H0Iso X.X₂).hom u), ?_⟩
    rw [Rep.tateH0Map_mk, ← hnat u]
    congr 1
    change (groupCohomology.H0Iso X.X₃).hom ((groupCohomology.map (MonoidHom.id G) X.g 0).hom u) = z
    rw [hu]
    exact CategoryTheory.Iso.inv_hom_id_apply _ _
  · rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [Rep.tateH0Map_mk] at hw

    have key : ∀ z' : X.X₃.ρ.invariants, Submodule.Quotient.mk z' = (Submodule.Quotient.mk (Rep.invariantsMap X.g v) : X.X₃.tateH0) →
        groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv z') = 0 := by
      intro z' hz'
      rw [← Rep.tateδ₀_mk hX, hz', Rep.tateδ₀_mk]
      have hv : Rep.invariantsMap X.g v = (groupCohomology.H0Iso X.X₃).hom
          ((groupCohomology.map (MonoidHom.id G) X.g 0) ((groupCohomology.H0Iso X.X₂).inv v)) := by
        rw [hnat]
        congr 1
        exact (CategoryTheory.Iso.inv_hom_id_apply (groupCohomology.H0Iso X.X₂) v).symm
      rw [hv, CategoryTheory.Iso.hom_inv_id_apply]
      have : (groupCohomology.map (MonoidHom.id G) X.g 0) ((groupCohomology.H0Iso X.X₂).inv v) ∈
          LinearMap.ker (groupCohomology.δ hX 0 1 rfl).hom := by
        rw [← h3]; exact LinearMap.mem_range_self _ _
      exact this
    exact key z hw.symm

end S_Rep_exact_tateH0Map_tateDelta0
end P2MW
export P2MW.S_Rep_exact_tateH0Map_tateDelta0 (solution)
