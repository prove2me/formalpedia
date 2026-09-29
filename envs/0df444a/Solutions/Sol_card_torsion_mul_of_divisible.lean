-- Prove2me | solution 1 for card_torsion_mul_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9162918b-d17f-51b4-a8ea-37f9af7446cf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_card_torsion_mul_of_divisible

open Function

theorem solution
    {A : Type*} [AddCommGroup A]
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ x : A, ∃ y : A, m • y = x)
    (a b : ℕ) (ha : a ≠ 0)
    (hfa : Finite {x : A // a • x = 0}) (hfb : Finite {x : A // b • x = 0}) :
    Finite {x : A // (a * b) • x = 0} ∧
      Nat.card {x : A // (a * b) • x = 0} =
        Nat.card {x : A // a • x = 0} * Nat.card {x : A // b • x = 0} := by

  let T : ℕ → AddSubgroup A := fun n => (zsmulAddGroupHom (n : ℤ)).ker
  have hT : ∀ n (x : A), x ∈ T n ↔ n • x = 0 := fun n x => by
    simp only [T, AddMonoidHom.mem_ker, zsmulAddGroupHom_apply, natCast_zsmul]
  have eT : ∀ n, {x : A // n • x = 0} ≃ T n := fun n =>
    Equiv.subtypeEquivRight fun x => (hT n x).symm

  let φ : T (a * b) →+ T b :=
    { toFun := fun x => ⟨a • (x : A), by
        rw [hT, ← mul_smul, mul_comm]; exact (hT (a*b) _).mp x.2⟩
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [AddSubgroup.coe_add, smul_add]; rfl }

  have hφsurj : Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hdiv a ha y
    refine ⟨⟨z, ?_⟩, ?_⟩
    · rw [hT, mul_comm, mul_smul, hz]; exact (hT b y).mp hy
    · exact Subtype.ext hz

  have hmem_ker : ∀ x : T (a * b), x ∈ φ.ker ↔ a • (x : A) = 0 := fun x => by
    simp only [AddMonoidHom.mem_ker, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddSubgroup.mk_eq_zero]
  let hker : (φ.ker : Type _) ≃ T a :=
    { toFun := fun x => ⟨(x : T (a * b)), (hT a _).mpr ((hmem_ker _).mp x.2)⟩
      invFun := fun y => ⟨⟨(y : A), (hT (a*b) _).mpr (by
          rw [mul_comm, mul_smul, (hT a _).mp y.2, smul_zero])⟩,
        (hmem_ker _).mpr ((hT a _).mp y.2)⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

  have hcard : Nat.card (T (a * b)) = Nat.card (T a) * Nat.card (T b) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv,
      Nat.card_congr hker, mul_comm]

  have hfa' : Finite (T a) := (eT a).finite_iff.mp hfa
  have hfb' : Finite (T b) := (eT b).finite_iff.mp hfb
  have : (0 : A) ∈ T a := (hT a 0).mpr (smul_zero a)
  have : (0 : A) ∈ T b := (hT b 0).mpr (smul_zero b)
  have hpos : 0 < Nat.card (T (a * b)) := by
    rw [hcard]
    exact Nat.mul_pos Nat.card_pos Nat.card_pos
  have hfab' : Finite (T (a * b)) := (Nat.card_pos_iff.mp hpos).2
  refine ⟨(eT (a*b)).finite_iff.mpr hfab', ?_⟩
  rw [Nat.card_congr (eT (a*b)), Nat.card_congr (eT a), Nat.card_congr (eT b), hcard]

end S_card_torsion_mul_of_divisible
end P2MW
export P2MW.S_card_torsion_mul_of_divisible (solution)
