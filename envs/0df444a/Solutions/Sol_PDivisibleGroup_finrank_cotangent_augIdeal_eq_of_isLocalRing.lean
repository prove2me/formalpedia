-- Prove2me | solution 1 for PDivisibleGroup.finrank_cotangent_augIdeal_eq_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/27ae89fb-eb75-5412-b8dc-c3a6e2993bc1

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing

set_option autoImplicit false

universe v

namespace COTConstBody

open PDivisibleGroup.Hopf Function

section Step

variable {p : ℕ}
variable {A B : Type*} [CommRing A] [CommRing B] [Bialgebra (ZMod p) A] [Bialgebra (ZMod p) B]

theorem natCast_p_eq_zero : (p : A) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) A) p, ZMod.natCast_self, map_zero]

theorem torsionIdeal_le_sq {v : ℕ} (hv : 1 ≤ v) :
    torsionIdeal (ZMod p) A (p ^ v) ≤ augIdeal (ZMod p) A ^ 2 := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  have h1 := PDivisibleGroup.Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq (R := ZMod p) (A := A) (p ^ v) ha
  have h2 : (p ^ v : ℕ) • a = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow, natCast_p_eq_zero (p := p) (A := A), zero_pow (by omega), zero_mul]
  rw [h2, sub_zero] at h1
  exact h1

variable (s : A →ₐc[ZMod p] B)

theorem augIdeal_le_comap :
    augIdeal (ZMod p) A ≤ (augIdeal (ZMod p) B).comap (s : A →ₐ[ZMod p] B) := by
  intro a ha
  rw [mem_augIdeal_iff] at ha
  rw [Ideal.mem_comap, mem_augIdeal_iff]
  change Coalgebra.counit (R := ZMod p) (s a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha]

theorem augIdeal_map_eq (hs : Surjective s) :
    (augIdeal (ZMod p) A).map (s : A →ₐ[ZMod p] B) = augIdeal (ZMod p) B := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (augIdeal_le_comap s)) ?_
  intro b hb
  obtain ⟨a, rfl⟩ := hs b
  have ha : a - algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) a) ∈ augIdeal (ZMod p) A :=
    sub_algebraMap_counit_mem_augIdeal (ZMod p) A a
  have hb' : Coalgebra.counit (R := ZMod p) a = 0 := by
    rw [mem_augIdeal_iff] at hb
    rwa [CoalgHomClass.counit_comp_apply] at hb
  have hsa : (s : A →ₐ[ZMod p] B) (a - algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) a)) = s a := by
    rw [hb', map_zero, sub_zero]
    rfl
  rw [← hsa]
  exact Ideal.mem_map_of_mem _ ha

theorem finrank_cotangent_eq (hs : Surjective s) {v : ℕ} (hv : 1 ≤ v)
    (hker : RingHom.ker s = torsionIdeal (ZMod p) A (p ^ v)) :
    Module.finrank (ZMod p) (augIdeal (ZMod p) A).Cotangent =
      Module.finrank (ZMod p) (augIdeal (ZMod p) B).Cotangent := by
  have hsurj : Surjective (Ideal.mapCotangent (augIdeal (ZMod p) A) (augIdeal (ZMod p) B)
      (s : A →ₐ[ZMod p] B) (augIdeal_le_comap s)) := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := (augIdeal (ZMod p) B).toCotangent_surjective y
    have hb' : b ∈ (augIdeal (ZMod p) A).map (s : A →ₐ[ZMod p] B) := by
      rw [augIdeal_map_eq s hs]
      exact hb
    obtain ⟨a, ha, hab⟩ := (Ideal.mem_map_iff_of_surjective (s : A →ₐ[ZMod p] B) hs).1 hb'
    refine ⟨(augIdeal (ZMod p) A).toCotangent ⟨a, ha⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    congr 1
    exact Subtype.ext hab
  have hinj : Injective (Ideal.mapCotangent (augIdeal (ZMod p) A) (augIdeal (ZMod p) B)
      (s : A →ₐ[ZMod p] B) (augIdeal_le_comap s)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, ha⟩, rfl⟩ := (augIdeal (ZMod p) A).toCotangent_surjective x
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hx
    rw [Ideal.toCotangent_eq_zero]
    change a ∈ augIdeal (ZMod p) A ^ 2
    have hx' : (s : A →ₐ[ZMod p] B) a ∈ ((augIdeal (ZMod p) A) ^ 2).map (s : A →ₐ[ZMod p] B) := by
      rw [Ideal.map_pow, augIdeal_map_eq s hs]
      exact hx
    obtain ⟨y, hy, hya⟩ := (Ideal.mem_map_iff_of_surjective (s : A →ₐ[ZMod p] B) hs).1 hx'
    have hay : a - y ∈ RingHom.ker s := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hya.symm
    rw [hker] at hay
    have h := Ideal.add_mem _ (torsionIdeal_le_sq (A := A) hv hay) hy
    rwa [sub_add_cancel] at h
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

end Step

end COTConstBody

open COTConstBody in
theorem solution
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (w : ℕ) (hw : 1 ≤ w) :
    Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)).Cotangent =
      Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent := by
  induction w, hw using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    exact finrank_cotangent_eq (s n) (hs n) hn (hkerH n)

end S_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing
end P2MW
export P2MW.S_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing (solution)
