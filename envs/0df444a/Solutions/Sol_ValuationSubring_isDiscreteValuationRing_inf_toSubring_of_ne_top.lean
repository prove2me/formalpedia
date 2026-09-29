-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_inf_toSubring_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9c2a99f5-0c99-5fc1-82fb-9228233bc96d

import Mathlib
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top

set_option autoImplicit false

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (hO : O ≠ ⊤)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    IsDiscreteValuationRing ↥(O.toSubring ⊓ K.toSubring) ∧
      ∀ x : AlgebraicClosure ℚ, x ∈ K →
        ∃ a b : AlgebraicClosure ℚ, a ∈ O.toSubring ⊓ K.toSubring ∧ b ∈ O.toSubring ⊓ K.toSubring ∧
          b ≠ 0 ∧ x * b = a := by
  classical
  set L := AlgebraicClosure ℚ with hL

  let O' : ValuationSubring ↥K := O.comap (algebraMap ↥K (AlgebraicClosure ℚ))
  have hmemO' : ∀ y : ↥K, y ∈ O' ↔ (y : AlgebraicClosure ℚ) ∈ O := fun y => ValuationSubring.mem_comap

  have hO' : O' ≠ ⊤ := by
    intro htop
    apply hO
    have hq : ∀ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q ∈ O := by
      intro q
      have : (algebraMap ℚ ↥K q : ↥K) ∈ O' := htop ▸ ValuationSubring.mem_top _
      rw [hmemO'] at this
      simpa [← IsScalarTower.algebraMap_apply] using this

    let S : Subring (AlgebraicClosure ℚ) := O.valuation.integer
    have hS : ∀ x, x ∈ S ↔ x ∈ O := fun x => by
      show x ∈ O.valuation.integer ↔ x ∈ O
      rw [ValuationSubring.integer_valuation]; rfl
    let i : ℚ →+* ↥S := (algebraMap ℚ (AlgebraicClosure ℚ)).codRestrict S (fun q => (hS _).mpr (hq q))
    letI : Algebra ℚ ↥S := i.toAlgebra
    haveI : IsScalarTower ℚ ↥S (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq (fun q => rfl)
    apply top_unique
    intro x _
    have hint : IsIntegral ↥S x := (((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral).tower_top
    have := (Valuation.integer.integers O.valuation).mem_of_integral hint
    exact (hS x).mp this

  have hZ : ∀ a : ℤ, algebraMap ℤ ↥K a ∈ O' := fun a => by
    rw [hmemO']
    have : ((algebraMap ℤ ↥K a : ↥K) : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ) := by simp
    rw [this]; exact intCast_mem O a
  haveI hDVR' : IsDiscreteValuationRing ↥O' :=
    ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (A := ℤ) (K := ℚ) (L := ↥K) O' hZ hO'

  let R : Subring (AlgebraicClosure ℚ) := O.toSubring ⊓ K.toSubring
  have hmemR : ∀ x, x ∈ R ↔ x ∈ O ∧ x ∈ K := fun x => Subring.mem_inf
  let e : ↥R ≃+* ↥O' :=
    { toFun := fun x => ⟨⟨x.1, ((hmemR _).mp x.2).2⟩, (hmemO' _).mpr ((hmemR _).mp x.2).1⟩
      invFun := fun y => ⟨((y : ↥K) : AlgebraicClosure ℚ), (hmemR _).mpr ⟨(hmemO' _).mp y.2, (y : ↥K).2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl
      map_add' := fun x y => rfl }
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm, ?_⟩

  intro x hxK
  by_cases hxO : x ∈ O
  · exact ⟨x, 1, (hmemR _).mpr ⟨hxO, hxK⟩, (hmemR _).mpr ⟨one_mem O, one_mem K.toSubring⟩, one_ne_zero, mul_one x⟩
  · have hx0 : x ≠ 0 := fun h => hxO (h ▸ zero_mem O)
    have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    refine ⟨1, x⁻¹, (hmemR _).mpr ⟨one_mem O, one_mem K.toSubring⟩, (hmemR _).mpr ⟨hinv, ?_⟩, inv_ne_zero hx0, mul_inv_cancel₀ hx0⟩
    exact K.inv_mem hxK

end S_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top (solution)
