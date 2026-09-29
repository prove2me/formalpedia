-- Prove2me | solution 1 for Rep.exact_tateHneg1Map_tateDeltaNeg1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/baa82ddc-9a98-519c-bfbc-7e12bec5f39c

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exact_tateHneg1Map_tateDeltaNeg1

universe u v w

set_option autoImplicit false
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.g) (Rep.tateδneg1 hX) := by
  intro x
  obtain ⟨t, rfl⟩ := Rep.seamθ_surjective hX x
  have ht : Rep.tateδneg1 hX (Rep.seamθ X t) =
      Submodule.Quotient.mk ⟨Rep.seamψ hX t, Rep.seamψ_mem_invariants hX t⟩ :=
    Rep.tateδneg1_mk hX t.1 t.2 ⟨Rep.seamψ hX t, Rep.seamψ_mem_invariants hX t⟩ (Rep.f_seamψ hX t)
  rw [ht, Submodule.Quotient.mk_eq_zero]
  constructor
  ·
    rintro ⟨α, hα⟩
    obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective _ α
    have hα' : X.X₁.ρ.norm a₀ = Rep.seamψ hX t := congrArg Subtype.val hα
    have hb' : X.X₂.ρ.norm ((t : X.X₂) - X.f.hom a₀) = 0 := by
      rw [map_sub, ← Rep.hom_norm_apply, hα', Rep.f_seamψ, sub_self]
    refine ⟨⟨Representation.Coinvariants.mk _ ((t : X.X₂) - X.f.hom a₀), LinearMap.mem_ker.2 (Subtype.ext hb')⟩,
      Subtype.ext ?_⟩
    rw [Rep.coe_tateHneg1Map_apply, Rep.coe_seamθ_apply]
    change Rep.coinvariantsMap X.g (Representation.Coinvariants.mk _ ((t : X.X₂) - X.f.hom a₀)) = _
    rw [Rep.coinvariantsMap_mk, map_sub, Rep.seam_g_f_apply, sub_zero]
  ·
    rintro ⟨x', hx'⟩
    obtain ⟨b', hb'⟩ := Submodule.Quotient.mk_surjective _ (x' : X.X₂.ρ.Coinvariants)
    have hb'' : Representation.Coinvariants.mk X.X₂.ρ b' = (x' : X.X₂.ρ.Coinvariants) := hb'
    have hNb' : X.X₂.ρ.norm b' = 0 := by
      have := congrArg Subtype.val (LinearMap.mem_ker.1 x'.2)
      rw [← hb''] at this
      exact this
    have hgt : Representation.Coinvariants.mk X.X₃.ρ (X.g.hom b') =
        Representation.Coinvariants.mk X.X₃.ρ (X.g.hom t) := by
      have := congrArg Subtype.val hx'
      rw [Rep.coe_tateHneg1Map_apply, Rep.coe_seamθ_apply, ← hb'', Rep.coinvariantsMap_mk] at this
      exact this
    have hdiff : X.g.hom (b' - t) ∈ Representation.Coinvariants.ker X.X₃.ρ := by
      rw [map_sub]; exact (Submodule.Quotient.eq _).1 hgt
    obtain ⟨i, hi, hgi⟩ := Rep.coinvariantsKer_le_map hX hdiff
    have hrange : b' - (t : X.X₂) - i ∈ LinearMap.range X.f.hom.toLinearMap := by
      rw [Rep.seam_range_eq_ker hX, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hgi.symm
    obtain ⟨a₁, ha₁⟩ := hrange
    refine ⟨Representation.Coinvariants.mk _ (-a₁), Subtype.ext (Rep.seam_f_injective hX ?_)⟩
    change X.f.hom (X.X₁.ρ.norm (-a₁)) = X.f.hom (Rep.seamψ hX t)
    rw [Rep.hom_norm_apply, map_neg, show X.f.hom a₁ = b' - t - i from ha₁, Rep.f_seamψ, map_neg, map_sub, map_sub,
      hNb', Rep.norm_eq_zero_of_mem_coinvariantsKer _ hi]
    simp

end S_Rep_exact_tateHneg1Map_tateDeltaNeg1
end P2MW
export P2MW.S_Rep_exact_tateHneg1Map_tateDeltaNeg1 (solution)
