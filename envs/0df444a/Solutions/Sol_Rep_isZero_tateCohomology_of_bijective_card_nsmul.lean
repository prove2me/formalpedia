-- Prove2me | solution 1 for Rep.isZero_tateCohomology_of_bijective_card_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/36657dca-451d-50c1-875a-653e7816266f

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_tateMap_add
import Theorems.Thm_Rep_tateMap_id
import Theorems.Thm_Rep_tateMap_comp
import Theorems.Thm_Rep_card_smul_eq_zero_of_tateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_of_bijective_card_nsmul

set_option autoImplicit false
universe u
open CategoryTheory Rep

namespace P2mS26Acyc

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateMap_zero_hom {A B : Rep.{u} k G} (n : ℤ) : Rep.tateMap (0 : A ⟶ B) n = 0 := by
  have h := Rep.tateMap_add (0 : A ⟶ B) 0 n
  rw [add_zero] at h
  calc Rep.tateMap (0 : A ⟶ B) n
      = (Rep.tateMap (0 : A ⟶ B) n + Rep.tateMap (0 : A ⟶ B) n) - Rep.tateMap (0 : A ⟶ B) n := by
        rw [add_sub_cancel_right]
    _ = Rep.tateMap (0 : A ⟶ B) n - Rep.tateMap (0 : A ⟶ B) n := by rw [← h]
    _ = 0 := sub_self _

theorem tateMap_nsmul_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (m : ℕ) (n : ℤ) (x : A.tateCohomology n) :
    (Rep.tateMap (m • φ) n).hom x = m • (Rep.tateMap φ n).hom x := by
  induction m with
  | zero =>
    rw [zero_nsmul, zero_nsmul, tateMap_zero_hom]
    rfl
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, Rep.tateMap_add, ModuleCat.hom_add, LinearMap.add_apply, ih]

end P2mS26Acyc

open P2mS26Acyc in
theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : Function.Bijective (fun a : A => Fintype.card G • a)) (q : ℤ) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by

  let L : (A : Type u) →ₗ[k] A := Fintype.card G • LinearMap.id
  have hL : ∀ a : A, L a = Fintype.card G • a := fun a => rfl
  have hLbij : Function.Bijective L := hA
  let E : (A : Type u) ≃ₗ[k] A := LinearEquiv.ofBijective L hLbij
  have hE : ∀ a : A, E a = Fintype.card G • a := fun a => rfl
  have hLρ : ∀ (g : G) (a : A), L (A.ρ g a) = A.ρ g (L a) := fun g a => by
    rw [hL, hL, map_nsmul]

  have hequiv : ∀ g : G, E.symm.toLinearMap ∘ₗ A.ρ g = A.ρ g ∘ₗ E.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro a
    change E.symm (A.ρ g a) = A.ρ g (E.symm a)
    apply E.injective
    rw [E.apply_symm_apply]
    change A.ρ g a = L (A.ρ g (E.symm a))
    rw [hLρ]
    exact congrArg (A.ρ g) (E.apply_symm_apply a).symm
  let ν : A ⟶ A := Rep.ofHom ⟨E.symm.toLinearMap, hequiv⟩
  let μ : A ⟶ A := Fintype.card G • 𝟙 A
  have hνμ : ν ≫ μ = 𝟙 A := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => ?_))
    change μ.hom (E.symm a) = a
    rw [show μ.hom (E.symm a) = Fintype.card G • (𝟙 A : A ⟶ A).hom (E.symm a) from by
      rw [Rep.nsmul_hom]; rfl]
    change Fintype.card G • E.symm a = a
    rw [← hE]
    exact E.apply_symm_apply a

  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  have key : ∀ x : A.tateCohomology q, x = 0 := fun x => by
    have h1 : (Rep.tateMap (ν ≫ μ) q).hom x = x := by
      rw [hνμ, Rep.tateMap_id]; rfl
    rw [Rep.tateMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, tateMap_nsmul_apply,
      Rep.tateMap_id] at h1
    rw [← h1, ← Nat.cast_smul_eq_nsmul k]
    exact Rep.card_smul_eq_zero_of_tateCohomology A q _
  rw [key x, key y]

end S_Rep_isZero_tateCohomology_of_bijective_card_nsmul
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_of_bijective_card_nsmul (solution)
