-- Prove2me | solution 1 for PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2cfacd81-7207-5fde-b95a-d7c991538862

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_PDivisibleGroup_exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
import Theorems.Thm_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq
import Theorems.Thm_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace C2SUB

def mkΓ {R : Type} [CommRing R] {p h' : ℕ}
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra R (L v)]
    [∀ v, Coalgebra.IsCocomm R (L v)] [∀ v, Module.Free R (L v)] [∀ v, Module.Finite R (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[R] L v) (hsurj : ∀ v, Function.Surjective (t' v))
    (hfin : ∀ v, Module.finrank R (L v) = p ^ (v * h'))
    (hker : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v)) :
    PDivisibleGroup R p h' :=
  { level := L, transition := t', transition_surjective := hsurj, finrank_level := hfin, ker_transition := hker }
end Ws47.C2SUB

namespace Ws47
namespace C2SUB

theorem tail
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    {h' : ℕ} (Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] Γ.level v)
    (hφt : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (hφinj : ∀ v, ∀ γ γ' : Γ.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
        γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] Γ.level v) = γ'.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] Γ.level v) → γ = γ')
    (hφimg : ∀ (v : ℕ) (y : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p),
        (∃ γ : Γ.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p, γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] Γ.level v) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom y)) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    ∃ Tφ : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)),
      (∀ (x : TateModule p (Γ.Points (PadicAlgCl p))) (n w : ℕ) (g : Γ.Point (PadicAlgCl p) w),
        Γ.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → Γ.Points (PadicAlgCl p)) n →
        ((Tφ x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) n =
          G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[(PadicAlgCl.ringOfIntegers p K)] Γ.level w))))) ∧
      (∀ (τ : PadicAlgCl p ≃ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) (x : TateModule p (Γ.Points (PadicAlgCl p))),
        Tφ (Γ.tateModuleRep (PadicAlgCl p) τ x) = G.tateModuleRep (PadicAlgCl p) τ (Tφ x)) ∧
      Function.Injective Tφ ∧ LinearMap.range Tφ = M := by
  classical
  obtain ⟨Tφ, hTφ, hTφeq⟩ :=
    PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq p (PadicAlgCl p) G Γ φ hφt
  obtain ⟨hinj, hrange⟩ :=
    PDivisibleGroup.injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem p (PadicAlgCl p) G Γ φ hφt
      Tφ hTφ M hMsat
      (fun v g g' hgg' => by
        have := hφinj v (PDivisibleGroup.Point.toAlgHom g) (PDivisibleGroup.Point.toAlgHom g')
          (congrArg PDivisibleGroup.Point.toAlgHom hgg')
        exact congrArg PDivisibleGroup.Point.ofAlgHom this)
      (fun v y => by
        have hoy : PDivisibleGroup.Point.ofAlgHom (PDivisibleGroup.Point.toAlgHom y) = y := rfl
        have key := hφimg v (PDivisibleGroup.Point.toAlgHom y)
        rw [hoy] at key
        refine ⟨fun hg => key.1 ?_, fun hx => ?_⟩
        · obtain ⟨g, hg⟩ := hg
          exact ⟨PDivisibleGroup.Point.toAlgHom g, congrArg PDivisibleGroup.Point.toAlgHom hg⟩
        · obtain ⟨γ, hγ⟩ := key.2 hx
          exact ⟨PDivisibleGroup.Point.ofAlgHom γ, congrArg PDivisibleGroup.Point.ofAlgHom hγ⟩)
  exact ⟨Tφ, hTφ, hTφeq, hinj, hrange⟩
end Ws47.C2SUB

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    ∃ (h' : ℕ) (Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
      (φ : ∀ v : ℕ, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v)
      (Tφ : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p))),
      (∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) ∧
      (∀ (x : TateModule p (Γ.Points (PadicAlgCl p))) (n w : ℕ) (g : Γ.Point (PadicAlgCl p) w),
        Γ.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → Γ.Points (PadicAlgCl p)) n →
        ((Tφ x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) n =
          G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level w))))) ∧
      (∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (Γ.Points (PadicAlgCl p))),
        Tφ (Γ.tateModuleRep (PadicAlgCl p) τ x) = G.tateModuleRep (PadicAlgCl p) τ (Tφ x)) ∧
      Function.Injective Tφ ∧ LinearMap.range Tφ = M := by
  classical

  obtain ⟨m, hmt, htm, hkill, hmaps, i₀, hbij⟩ :=
    PDivisibleGroup.exists_bialgHom_comp_eq_nsmulBialgHom_and_bijOn_hopfKer_of_hopf_quotient_system_of_ringOfIntegers
      p K G M hMstab hMsat B π t hπ ht hπt hpts

  obtain ⟨-, hrankK⟩ := PDivisibleGroup.finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
      p K G M hMstab hMsat B π t hπ ht hπt hpts
  have hrank0 := hrankK i₀
  clear hrankK
  generalize hh' : Module.finrank ℤ_[p] ↥M = h' at hrank0
  have hrank : Module.finrank (PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h' := hrank0

  haveI : IsLocalRing (PadicAlgCl.ringOfIntegers p K) := by
    obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
    exact hdvr.toIsLocalRing
  haveI : IsPrincipalIdealRing (PadicAlgCl.ringOfIntegers p K) := by
    obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
    exact hdvr.toIsPrincipalIdealRing

  obtain ⟨L, iCR, iHA, iCC, iFree, iFin, t', ι, hsurj, hfin, hker, hιinj, hιrange, hιt⟩ :=
    PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer p h' i₀ B t ht m hmt htm hkill hmaps
      (fun w hw => hbij w hw) hrank

  let Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h' := Ws47.C2SUB.mkΓ L t' hsurj hfin hker

  obtain ⟨φ, hφt, hφinj, hφimg⟩ :=
    PDivisibleGroup.exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
      p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt
  obtain ⟨Tφ, h1, h2, h3, h4⟩ := Ws47.C2SUB.tail p K G M hMsat Γ φ hφt hφinj hφimg
  exact ⟨h', Γ, φ, Tφ, hφt, h1, h2, h3, h4⟩

end S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers (solution)
