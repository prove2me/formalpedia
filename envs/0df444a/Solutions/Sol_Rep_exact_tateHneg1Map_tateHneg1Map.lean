-- Prove2me | solution 1 for Rep.exact_tateHneg1Map_tateHneg1Map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e0f1e9ab-0dd2-5dc0-afd1-e7f955ebb1cc

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exact_tateHneg1Map_tateHneg1Map

set_option autoImplicit false
universe u v w
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type*} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.f) (Rep.tateHneg1Map X.g) := by
  classical
  have hfinj : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hgsurj : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hker : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hgf : ∀ a : X.X₁, X.g.hom (X.f.hom a) = 0 := fun a => by
    rw [← Rep.comp_apply, X.zero]; rfl

  have hKer : Representation.Coinvariants.ker X.X₃.ρ ≤ (Representation.Coinvariants.ker X.X₂.ρ).map X.g.hom.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨h, c⟩, rfl⟩
    obtain ⟨b, rfl⟩ := hgsurj c
    refine ⟨X.X₂.ρ h b - b, Representation.Coinvariants.sub_mem_ker h b, ?_⟩
    show X.g.hom (X.X₂.ρ h b - b) = X.X₃.ρ h (X.g.hom b) - X.g.hom b
    rw [map_sub, Rep.hom_comm_apply]

  have hNker : ∀ (x : X.X₂), x ∈ Representation.Coinvariants.ker X.X₂.ρ → X.X₂.ρ.norm x = 0 := by
    intro x hx
    have h := X.X₂.ρ.normBar_mk x
    rw [(Representation.Coinvariants.mk_eq_zero (ρ := X.X₂.ρ)).2 hx, map_zero] at h
    exact (congrArg Subtype.val h).symm
  intro y
  constructor
  · intro hy

    have hy' : coinvariantsMap X.g (y : X.X₂.ρ.Coinvariants) = 0 := by
      have := congrArg Subtype.val hy
      rwa [Rep.coe_tateHneg1Map_apply] at this
    obtain ⟨x₂, hx₂⟩ := Representation.Coinvariants.mk_surjective _ (y : X.X₂.ρ.Coinvariants)
    rw [← hx₂, Rep.coinvariantsMap_mk, Representation.Coinvariants.mk_eq_zero] at hy'

    obtain ⟨w, hw, hgw⟩ := hKer hy'
    have hgw' : X.g.hom w = X.g.hom x₂ := hgw

    have hk : (x₂ - w) ∈ LinearMap.ker X.g.hom.toLinearMap := by
      show X.g.hom (x₂ - w) = 0
      rw [map_sub, hgw', sub_self]
    rw [← hker] at hk
    obtain ⟨a, ha⟩ := hk
    have ha' : X.f.hom a = x₂ - w := ha

    have hNy : X.X₂.ρ.norm x₂ = 0 := by
      have h := congrArg Subtype.val y.2
      rw [← hx₂, Representation.normBar_mk] at h
      exact h
    have hNa : Representation.Coinvariants.mk X.X₁.ρ a ∈ LinearMap.ker X.X₁.ρ.normBar := by
      rw [LinearMap.mem_ker, Representation.normBar_mk]
      apply Subtype.ext
      apply hfinj
      rw [Representation.coe_normToInvariants_apply, Rep.hom_norm_apply, ha', map_sub, hNy, hNker w hw, sub_self]
      show 0 = X.f.hom ((0 : X.X₁.ρ.invariants) : X.X₁)
      rw [Submodule.coe_zero, map_zero]
    refine ⟨⟨Representation.Coinvariants.mk X.X₁.ρ a, hNa⟩, ?_⟩
    apply Subtype.ext
    rw [Rep.coe_tateHneg1Map_apply]
    show coinvariantsMap X.f (Representation.Coinvariants.mk X.X₁.ρ a) = (y : X.X₂.ρ.Coinvariants)
    rw [Rep.coinvariantsMap_mk, ha', ← hx₂, map_sub, sub_eq_self]
    exact (Representation.Coinvariants.mk_eq_zero (ρ := X.X₂.ρ)).2 hw
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    rw [Rep.coe_tateHneg1Map_apply, Rep.coe_tateHneg1Map_apply]
    obtain ⟨x₁, hx₁⟩ := Representation.Coinvariants.mk_surjective _ (w : X.X₁.ρ.Coinvariants)
    show coinvariantsMap X.g (coinvariantsMap X.f (w : X.X₁.ρ.Coinvariants)) = 0
    rw [← hx₁, Rep.coinvariantsMap_mk, Rep.coinvariantsMap_mk, hgf, map_zero]

end S_Rep_exact_tateHneg1Map_tateHneg1Map
end P2MW
export P2MW.S_Rep_exact_tateHneg1Map_tateHneg1Map (solution)
