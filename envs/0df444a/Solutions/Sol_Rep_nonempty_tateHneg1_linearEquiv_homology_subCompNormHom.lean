-- Prove2me | solution 1 for Rep.nonempty_tateHneg1_linearEquiv_homology_subCompNormHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ace9dad4-7803-58e4-93a9-6218b3032875

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nonempty (A.tateHneg1 ≃ₗ[k] (FiniteCyclicGroup.subCompNormHom A g).homology) := by

  let φ : LinearMap.ker (FiniteCyclicGroup.subCompNormHom A g).g.hom →ₗ[k] A.tateHneg1 :=
    LinearMap.codRestrict _ (Representation.Coinvariants.mk A.ρ ∘ₗ (LinearMap.ker _).subtype) (fun v => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, Representation.normBar_mk]
      apply Subtype.ext
      rw [Representation.coe_normToInvariants_apply]
      exact v.2)

  have hφ : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, Representation.normBar_mk] at hc
    exact congrArg Subtype.val hc

  have hkerφ : LinearMap.range (FiniteCyclicGroup.subCompNormHom A g).moduleCatToCycles = LinearMap.ker φ := by
    ext x
    have hx' : x ∈ LinearMap.ker φ ↔ Representation.Coinvariants.mk A.ρ x.1 = 0 := by
      rw [LinearMap.mem_ker, Subtype.ext_iff]
      exact Iff.rfl
    rw [hx', Representation.Coinvariants.mk_eq_zero,
      Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv⟩
  exact ⟨((Submodule.quotEquivOfEq _ _ hkerφ).trans (LinearMap.quotKerEquivOfSurjective φ hφ)).symm.trans
    (FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso.toLinearEquiv.symm⟩

end S_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom
end P2MW
export P2MW.S_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom (solution)
