-- Prove2me | solution 1 for Rep.exists_hom_coind_res_comp_eq_index_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/38f5abd1-aa43-57b0-b8a7-304a7bca025f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_hom_coind_res_comp_eq_index_smul

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

theorem solution {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.FiniteIndex] (N : Rep.{u} k G) :
    ∃ (ι : N ⟶ Rep.coind S.subtype (Rep.res S.subtype N)) (τ : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N),
      (∀ (n : N) (g : G), ((ι.hom n : Rep.coind S.subtype (Rep.res S.subtype N)) : G → N) g = N.ρ g n) ∧
      (∀ f : Rep.coind S.subtype (Rep.res S.subtype N),
        τ.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹)) ∧
      Function.Surjective τ.hom ∧
      ∀ n : N, τ.hom (ι.hom n) = (S.index : k) • n := by
  classical
  haveI : Finite (G ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _

  set I := Rep.coind S.subtype (Rep.res S.subtype N) with hI
  have memI : ∀ (f : I) (s : S) (g : G), (f : G → N) ((s : G) * g) = N.ρ (s : G) ((f : G → N) g) :=
    fun f s g => f.2 s g
  have actI : ∀ (h : G) (f : I) (g : G), ((I.ρ h f : I) : G → N) g = (f : G → N) (g * h) := fun _ _ _ => rfl

  let Lι : N →ₗ[k] I :=
    { toFun := fun n => ⟨fun g => N.ρ g n, fun s g => by
        show N.ρ ((s : G) * g) n = N.ρ (s : G) (N.ρ g n)
        rw [map_mul]; rfl⟩
      map_add' := fun n n' => by
        apply Subtype.ext; funext g
        show N.ρ g (n + n') = N.ρ g n + N.ρ g n'
        rw [map_add]
      map_smul' := fun c n => by
        apply Subtype.ext; funext g
        show N.ρ g (c • n) = c • N.ρ g n
        rw [map_smul] }
  have hLι : ∀ (n : N) (g : G), ((Lι n : I) : G → N) g = N.ρ g n := fun _ _ => rfl
  let ι : N ⟶ I := Rep.ofHom (Lι.intertwiningMap_of_isIntertwiningMap N.ρ I.ρ (fun h n => by
      apply Subtype.ext; funext g
      show N.ρ g (N.ρ h n) = ((I.ρ h (Lι n) : I) : G → N) g
      rw [actI, hLι, map_mul]; rfl))
  have hι : ∀ n : N, ι.hom n = Lι n := fun _ => rfl

  let Lτ : I →ₗ[k] N :=
    { toFun := fun f => ∑ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹)
      map_add' := fun f f' => by
        show ∑ q, _ = (∑ q, _) + ∑ q, _
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← map_add]; rfl
      map_smul' := fun c f => by
        show ∑ q, _ = c • ∑ q, _
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← map_smul]; rfl }
  have hLτ : ∀ f : I, Lτ f = ∑ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹) := fun _ => rfl

  have hterm : ∀ (f : I) (g : G) (s : S), N.ρ (g * s) ((f : G → N) (g * s)⁻¹) = N.ρ g ((f : G → N) g⁻¹) := by
    intro f g s
    rw [mul_inv_rev, ← Subgroup.coe_inv, memI, map_mul, Module.End.mul_apply]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]

  have hequiv : ∀ (h : G) (f : I), Lτ (I.ρ h f) = N.ρ h (Lτ f) := by
    intro h f
    rw [hLτ, hLτ, map_sum]
    symm
    refine Fintype.sum_bijective (fun q : G ⧸ S => h • q) (MulAction.bijective h) _ _ fun q => ?_

    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (h * q.out)
    have hq : h • q = ((h * q.out : G) : G ⧸ S) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    show N.ρ h (N.ρ q.out ((f : G → N) (q.out)⁻¹)) = N.ρ (h • q).out (((I.ρ h f : I) : G → N) ((h • q).out)⁻¹)
    rw [actI, hq, hs, mul_assoc h, mul_inv_rev, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hterm]
  let τ : I ⟶ N := Rep.ofHom (Lτ.intertwiningMap_of_isIntertwiningMap I.ρ N.ρ hequiv)
  have hτ : ∀ f : I, τ.hom f = Lτ f := fun _ => rfl

  have hsupp : ∀ f : I, (∀ g : G, g ∉ S → (f : G → N) g = 0) → τ.hom f = (f : G → N) 1 := by
    intro f hf
    rw [hτ, hLτ, Finset.sum_eq_single (((1 : G)) : G ⧸ S)]
    · obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (1 : G)
      rw [hs, one_mul, ← mul_one ((s : G))⁻¹, ← Subgroup.coe_inv, memI, ← Module.End.mul_apply, ← map_mul,
        Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro q _ hq
      have hout : q.out ∉ S := fun hmem => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using S.inv_mem hmem))
      rw [hf _ (fun h' => hout (by simpa using S.inv_mem h')), map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨ι, τ, fun n g => rfl, fun f => by rw [hτ, hLτ, finsum_eq_sum_of_fintype], ?_, ?_⟩
  ·
    intro n
    let fn : I := ⟨fun g => if g ∈ S then N.ρ g n else 0, fun s g => by
      show (if (s : G) * g ∈ S then N.ρ ((s : G) * g) n else 0) = N.ρ (s : G) (if g ∈ S then N.ρ g n else 0)
      by_cases hg : g ∈ S
      · rw [if_pos (S.mul_mem s.2 hg), if_pos hg, map_mul]; rfl
      · have hsg : (s : G) * g ∉ S := fun h' => hg (by simpa using S.mul_mem (S.inv_mem s.2) h')
        rw [if_neg hsg, if_neg hg, map_zero]⟩
    refine ⟨fn, ?_⟩
    rw [hsupp fn (fun g hg => if_neg hg)]
    show (if (1 : G) ∈ S then N.ρ 1 n else 0) = n
    rw [if_pos S.one_mem, map_one, Module.End.one_apply]
  ·
    intro n
    rw [hτ, hLτ]
    have : ∀ q : G ⧸ S, N.ρ q.out (((ι.hom n : I) : G → N) (q.out)⁻¹) = n := by
      intro q
      rw [hι, hLι, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, Subgroup.index, Nat.card_eq_fintype_card]

end S_Rep_exists_hom_coind_res_comp_eq_index_smul
end P2MW
export P2MW.S_Rep_exists_hom_coind_res_comp_eq_index_smul (solution)
