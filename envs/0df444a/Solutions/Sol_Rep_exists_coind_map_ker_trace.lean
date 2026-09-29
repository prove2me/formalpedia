-- Prove2me | solution 1 for Rep.exists_coind_map_ker_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3e0eada7-d151-5e5e-b04d-2776a037ba98

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_coind_map_ker_trace

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

namespace P2mS26R5b

open CategoryTheory

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G)

noncomputable def post {X X' : Rep.{u} k G} (f : X ⟶ X') :
    Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U.subtype (Rep.res U.subtype X') :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (Representation.coind U.subtype (Rep.res U.subtype X).ρ) (Representation.coind U.subtype (Rep.res U.subtype X').ρ)
    { toFun := fun y => ⟨fun g => f.hom ((y : G → X) g), fun u g => by
        show f.hom ((y : G → X) (U.subtype u * g)) = X'.ρ (U.subtype u) (f.hom ((y : G → X) g))
        rw [y.2 u g]
        exact Rep.hom_comm_apply f _ _⟩
      map_add' := fun y y' => Subtype.ext (funext fun g => by
        show f.hom ((y : G → X) g + (y' : G → X) g) = f.hom ((y : G → X) g) + f.hom ((y' : G → X) g)
        rw [map_add])
      map_smul' := fun c y => Subtype.ext (funext fun g => by
        show f.hom (c • (y : G → X) g) = c • f.hom ((y : G → X) g)
        rw [map_smul]) }
    (fun h y => rfl))

lemma post_apply {X X' : Rep.{u} k G} (f : X ⟶ X') (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G) :
    ((post U f).hom y : G → X') g = f.hom ((y : G → X) g) := rfl

variable [U.FiniteIndex]

lemma trace_post {X X' : Rep.{u} k G} (f : X ⟶ X')
    (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X) (τ' : Rep.coind U.subtype (Rep.res U.subtype X') ⟶ X')
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹))
    (hτ' : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X'), τ'.hom y = ∑ᶠ c : G ⧸ U, X'.ρ c.out ((y : G → X') (c.out)⁻¹))
    (Yf : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U.subtype (Rep.res U.subtype X'))
    (hYf : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((Yf.hom y : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = f.hom ((y : G → X) g))
    (y : Rep.coind U.subtype (Rep.res U.subtype X)) :
    τ'.hom (Yf.hom y) = f.hom (τ.hom y) := by
  classical
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  rw [hτ', hτ, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hYf, Rep.hom_comm_apply]

omit [U.FiniteIndex] in

lemma trace_surjective (X : Rep.{u} k G) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹)) :
    Function.Surjective τ.hom := by
  classical
  intro x
  let y : Rep.coind U.subtype (Rep.res U.subtype X) :=
    ⟨fun g => if g ∈ U then X.ρ g x else 0, fun u g => by
      show (if U.subtype u * g ∈ U then X.ρ (U.subtype u * g) x else 0)
        = X.ρ (U.subtype u) (if g ∈ U then X.ρ g x else 0)
      by_cases hg : g ∈ U
      · have hug : U.subtype u * g ∈ U := U.mul_mem u.2 hg
        rw [if_pos hg, if_pos hug, map_mul, Module.End.mul_apply]
      · have hug : U.subtype u * g ∉ U := fun h => hg (by simpa using U.mul_mem (U.inv_mem u.2) h)
        rw [if_neg hg, if_neg hug, map_zero]⟩
  refine ⟨y, ?_⟩
  rw [hτ]
  have h1 : ∀ c : G ⧸ U, c ≠ (QuotientGroup.mk 1 : G ⧸ U) → X.ρ c.out ((y : G → X) (c.out)⁻¹) = 0 := by
    intro c hc
    have hout : c.out ∉ U := fun h => hc (by
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq]
      simpa using U.inv_mem h)
    have hout' : (c.out)⁻¹ ∉ U := fun h => hout (by simpa using U.inv_mem h)
    show X.ρ c.out (if (c.out)⁻¹ ∈ U then X.ρ (c.out)⁻¹ x else 0) = 0
    rw [if_neg hout', map_zero]
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ U) h1]
  have hone : ((QuotientGroup.mk 1 : G ⧸ U).out) ∈ U := by
    have h := QuotientGroup.out_eq' (QuotientGroup.mk (1 : G) : G ⧸ U)
    rw [QuotientGroup.eq, mul_one] at h
    simpa using U.inv_mem h
  have hone' : ((QuotientGroup.mk 1 : G ⧸ U).out)⁻¹ ∈ U := U.inv_mem hone
  show X.ρ (QuotientGroup.mk 1 : G ⧸ U).out
      (if ((QuotientGroup.mk 1 : G ⧸ U).out)⁻¹ ∈ U then X.ρ ((QuotientGroup.mk 1 : G ⧸ U).out)⁻¹ x else 0) = x
  rw [if_pos hone', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end P2mS26R5b

theorem solution {k G : Type u} [CommRing k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (φ : G)
    {X X' : Rep.{u} k G} (f : X ⟶ X')
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (ι' : X' ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (τ' : Rep.coind U.subtype (Rep.res U.subtype X') ⟶ X')
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹))
    (hι' : ∀ (x : X') (g : G), ((ι'.hom x : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = X'.ρ g x)
    (hτ' : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X'), τ'.hom y = ∑ᶠ c : G ⧸ U, X'.ρ c.out ((y : G → X') (c.out)⁻¹))
    {K K' : Rep.{u} k G} (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K) (i' : K' ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (E' : Rep.coind U.subtype (Rep.res U.subtype X') ⟶ K')
    (hi' : Function.Injective i'.hom) (hτi' : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X'), τ'.hom y = 0 ↔ ∃ κ : K', i'.hom κ = y)
    (hE : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g)
    (hE' : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X')) (g : G), ((i'.hom (E'.hom y) : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = X'.ρ φ ((y : G → X') (φ⁻¹ * g)) - (y : G → X') g)
    (hτi : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = 0 ↔ ∃ κ : K, i.hom κ = y) :
    ∃ (Yf : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (Kf : K ⟶ K'),
      (∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((Yf.hom y : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = f.hom ((y : G → X) g)) ∧
      Kf ≫ i' = i ≫ Yf ∧ ι ≫ Yf = f ≫ ι' ∧ E ≫ Kf = Yf ≫ E' ∧ τ ≫ f = Yf ≫ τ' := by
  classical
  let Yf := P2mS26R5b.post U f
  have hYf : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G),
      ((Yf.hom y : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = f.hom ((y : G → X) g) :=
    fun _ _ => rfl
  have hτnat : ∀ y, τ'.hom (Yf.hom y) = f.hom (τ.hom y) := P2mS26R5b.trace_post U f τ τ' hτ hτ' Yf hYf

  have hland : ∀ κ : K, Yf.hom (i.hom κ) ∈ LinearMap.range i'.hom.toLinearMap := by
    intro κ
    obtain ⟨κ', hκ'⟩ := (hτi' _).1 (by rw [hτnat, (hτi _).2 ⟨κ, rfl⟩, map_zero])
    exact ⟨κ', hκ'⟩
  let eI := LinearEquiv.ofInjective i'.hom.toLinearMap hi'
  let KfL : K →ₗ[k] K' :=
    eI.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range i'.hom.toLinearMap) (Yf.hom.toLinearMap ∘ₗ i.hom.toLinearMap) hland
  have hKfL : ∀ κ : K, i'.hom (KfL κ) = Yf.hom (i.hom κ) := by
    intro κ
    have := eI.apply_symm_apply ⟨Yf.hom (i.hom κ), hland κ⟩
    exact congrArg Subtype.val this
  let Kf : K ⟶ K' := Rep.ofHom (KfL.intertwiningMap_of_isIntertwiningMap K.ρ K'.ρ (fun g κ => hi' (by
      show i'.hom (KfL (K.ρ g κ)) = i'.hom (K'.ρ g (KfL κ))
      rw [hKfL, Rep.hom_comm_apply i g κ, Rep.hom_comm_apply Yf g, Rep.hom_comm_apply i' g, hKfL])))
  have hKf : ∀ κ : K, i'.hom (Kf.hom κ) = Yf.hom (i.hom κ) := hKfL
  refine ⟨Yf, Kf, hYf, ?_, ?_, ?_, ?_⟩
  · apply Rep.hom_ext
    exact DFunLike.ext _ _ fun κ => hKf κ
  · apply Rep.hom_ext
    refine DFunLike.ext _ _ fun x => Subtype.ext (funext fun g => ?_)
    show ((Yf.hom (ι.hom x) : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = ((ι'.hom (f.hom x) : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g
    rw [hYf, hι, hι', Rep.hom_comm_apply]
  · apply Rep.hom_ext
    refine DFunLike.ext _ _ fun y => ?_
    show Kf.hom (E.hom y) = E'.hom (Yf.hom y)
    apply hi'
    rw [hKf]
    apply Subtype.ext; funext g
    rw [hYf, hE, hE', map_sub, Rep.hom_comm_apply, hYf, hYf]
  · apply Rep.hom_ext
    exact DFunLike.ext _ _ fun y => (hτnat y).symm

end S_Rep_exists_coind_map_ker_trace
end P2MW
export P2MW.S_Rep_exists_coind_map_ker_trace (solution)
