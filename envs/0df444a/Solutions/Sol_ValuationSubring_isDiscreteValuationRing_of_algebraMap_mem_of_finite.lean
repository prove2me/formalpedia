-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/71cf4a6f-6cd9-5133-b700-c36250e960e1

import Mathlib
import Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite

set_option autoImplicit false

namespace KrullAkizukiDVR

theorem main {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by

  let B : Subalgebra A L :=
    { carrier := O
      mul_mem' := fun ha hb => O.mul_mem _ _ ha hb
      one_mem' := O.one_mem
      add_mem' := fun ha hb => O.add_mem _ _ ha hb
      zero_mem' := O.zero_mem
      algebraMap_mem' := hA }
  have hB := Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  haveI : IsNoetherianRing B := hB.1

  let e : B ≃+* O :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsNoetherianRing O := isNoetherianRing_of_ringEquiv B e

  have hnf : ¬ IsField O := by
    intro hF
    apply hO
    rw [eq_top_iff]
    intro x _
    by_contra hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx O.zero_mem
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
    have hne : (⟨x⁻¹, hxinv⟩ : O) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg Subtype.val h
      simpa using this
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    have hy' : x⁻¹ * (y : L) = 1 := by
      have := congrArg Subtype.val hy
      simpa using this
    have hyx : (y : L) = x := by
      have h1 : x * (x⁻¹ * (y : L)) = x := by rw [hy', mul_one]
      rwa [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact hx (hyx ▸ y.2)
  haveI : IsLocalRing O := inferInstance
  haveI : ValuationRing O := inferInstance
  have htfae := IsDiscreteValuationRing.TFAE O hnf
  exact (htfae.out 0 1).mpr ‹ValuationRing O›

end KrullAkizukiDVR

theorem solution
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O :=
  KrullAkizukiDVR.main (K := K) O hA hO

end S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite (solution)
