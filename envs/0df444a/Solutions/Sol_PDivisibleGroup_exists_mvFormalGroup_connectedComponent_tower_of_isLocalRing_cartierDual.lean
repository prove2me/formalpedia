-- Prove2me | solution 1 for PDivisibleGroup.exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fc042c02-a57c-5388-b050-12356da5f6e5

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual
import Theorems.Thm_PDivisibleGroup_exists_compatible_specialFibre_coordinates_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
import Theorems.Thm_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) :
    ∃ (d : ℕ) (F : MvFormalGroup d 𝓞) (_ : F.IsComm) (h₀ : ℕ) (_ : h₀ ≤ h)
      (R₀ : ℕ → Type v) (_ : ∀ v, CommRing (R₀ v)) (_ : ∀ v, HopfAlgebra 𝓞 (R₀ v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)) (_ : ∀ v, Module.Free 𝓞 (R₀ v))
      (_ : ∀ v, Module.Finite 𝓞 (R₀ v))
      (ρ : ∀ v, L v →ₐc[𝓞] R₀ v) (e : ∀ v, L v) (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v)
      (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v),
    (∀ v, Function.Surjective (t₀ v)) ∧
    (∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, (ρ v).comp (t v) = (t₀ v).comp (ρ (v + 1))) ∧
    (∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v) ∧
    ∀ v, IsIdempotentElem (e v) ∧ Coalgebra.counit (R := 𝓞) (e v) = 1 ∧
      Function.Surjective (ρ v) ∧ RingHom.ker (ρ v : L v →ₐ[𝓞] R₀ v) = Ideal.span {1 - e v} ∧
      IsLocalRing (R₀ v) ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) (R₀ v)) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (R₀ v))) ∧
      Function.Surjective (π v) ∧
      (∀ i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ G : MvPowerSeries (Fin d) 𝓞,
        π v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      RingHom.ker (π v) = Ideal.span (Set.range (F.nthSeries (p ^ v))) ∧
      (∀ i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
          (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
          (F.toPowerSeries i)) := by

  obtain ⟨h₀, hh₀, R₀, i₁, i₂, i₃, i₄, i₅, ρ, e, t₀, ht₀s, hrank, ht₀k, hρt, hlev⟩ :=
    PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual p hp hker h L t ht hrankL
      hkerL hunipL
  have hconn : ∀ v, IsLocalRing (R₀ v) := fun v => (hlev v).2.2.2.2.1

  obtain ⟨d, x, hxt, hxε, hxrad, hxsurj, hxker⟩ :=
    PDivisibleGroup.exists_compatible_specialFibre_coordinates_of_isLocalRing p hp hker h₀ R₀ t₀ ht₀s hrank
      ht₀k hconn

  obtain ⟨F, hF, π, -, hπs, hπt, hπrad, hπev, hπinj, hπsurjj, hπε, hπΔ⟩ :=
    PDivisibleGroup.exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates p hp hker R₀ t₀ d x
      hxt hxε hxrad hxsurj hxker

  have hkerπ := fun v =>
    PDivisibleGroup.ker_eq_span_range_nthSeries_of_comul_eq_adicEval p hp hker h₀ R₀ t₀ ht₀s hrank ht₀k
      hconn d π hπs hπt hπε hπrad hπinj hπsurjj F hπΔ v

  exact ⟨d, F, hF, h₀, hh₀, R₀, i₁, i₂, i₃, i₄, i₅, ρ, e, t₀, π, ht₀s, hrank, ht₀k, hρt, hπt, fun v =>
    ⟨(hlev v).1, (hlev v).2.1, (hlev v).2.2.1, (hlev v).2.2.2.1, (hlev v).2.2.2.2.1, (hlev v).2.2.2.2.2.1,
      (hlev v).2.2.2.2.2.2, hπs v, fun i => hπrad v i, hπev v, hkerπ v, fun i => hπΔ v i⟩⟩

end S_PDivisibleGroup_exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_PDivisibleGroup_exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual (solution)
