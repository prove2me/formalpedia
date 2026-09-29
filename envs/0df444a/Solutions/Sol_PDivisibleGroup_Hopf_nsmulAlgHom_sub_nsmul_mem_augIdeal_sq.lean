-- Prove2me | solution 1 for PDivisibleGroup.Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/08d70860-6604-53d5-a4b2-e20e6d90b30d

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv Finset

universe u v

namespace PDivTower

section NSMul

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]

open PDivisibleGroup.Hopf

noncomputable def projLin : A →ₗ[R] A :=
  LinearMap.id - (Algebra.linearMap R A) ∘ₗ Coalgebra.counit

theorem projLin_apply (a : A) : projLin (R := R) a = a - algebraMap R A (counit (R := R) a) := rfl

theorem projLin_mem (a : A) : projLin (R := R) a ∈ augIdeal R A :=
  sub_algebraMap_counit_mem_augIdeal R A a

theorem projLin_of_mem {a : A} (ha : a ∈ augIdeal R A) : projLin (R := R) a = a := by
  rw [projLin_apply, (mem_augIdeal_iff R A a).1 ha, map_zero, sub_zero]

noncomputable def P : WithConv (A →ₗ[R] A) := toConv (projLin (R := R) (A := A))

theorem P_apply (a : A) : (P (R := R) (A := A)) a = projLin (R := R) a := rfl

theorem toConv_id_eq : toConv (LinearMap.id : A →ₗ[R] A) = P + 1 := by
  rw [LinearMap.convOne_def, P, ← toConv_add, projLin, sub_add_cancel]

theorem P_pow_succ_apply_mem (k : ℕ) (a : A) :
    ((P (R := R) (A := A)) ^ (k + 1)) a ∈ augIdeal R A ^ (k + 1) := by
  induction k generalizing a with
  | zero =>
    rw [zero_add, pow_one, pow_one]
    exact projLin_mem a
  | succ k ih =>
    rw [pow_succ (P (R := R) (A := A)) (k + 1), (Coalgebra.Repr.arbitrary R a).convMul_apply,
      pow_succ (augIdeal R A) (k + 1)]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_mul (ih _) (projLin_mem _)

theorem P_pow_apply_mem_sq {k : ℕ} (hk : 2 ≤ k) (a : A) :
    ((P (R := R) (A := A)) ^ k) a ∈ augIdeal R A ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h := P_pow_succ_apply_mem (R := R) (j + 1) a
  exact Ideal.pow_le_pow_right hk h

theorem nsmulAlgHom_apply_eq (n : ℕ) (a : A) :
    nsmulAlgHom R A n a = ((P (R := R) (A := A) + 1) ^ n) a := by
  have h := toConv_toLinearMap_nsmulAlgHom R A n
  rw [toConv_id_eq] at h
  have h' := congrArg (fun f : WithConv (A →ₗ[R] A) => f a) h
  exact h'

private theorem _root_.PDivTower.sum_apply (s : Finset ℕ) (f : ℕ → WithConv (A →ₗ[R] A)) (a : A) :
    (∑ m ∈ s, f m) a = ∑ m ∈ s, (f m) a := by
  have : (∑ m ∈ s, f m).ofConv = ∑ m ∈ s, (f m).ofConv :=
    map_sum (WithConv.addEquiv (A →ₗ[R] A)) f s
  change (∑ m ∈ s, f m).ofConv a = _
  rw [this, LinearMap.sum_apply]

p2m_export "PDivTower" "sum_apply"

theorem nsmulAlgHom_sub_nsmul_mem_sq (n : ℕ) {x : A} (hx : x ∈ augIdeal R A) :
    nsmulAlgHom R A n x - n • x ∈ augIdeal R A ^ 2 := by
  rw [nsmulAlgHom_apply_eq, (Commute.one_right (P (R := R) (A := A))).add_pow, sum_apply]

  have hterm : ∀ m ∈ range (n + 1),
      ((P ^ m * 1 ^ (n - m) * (n.choose m : WithConv (A →ₗ[R] A)) : WithConv (A →ₗ[R] A))) x =
        (n.choose m : A) * ((P (R := R) (A := A)) ^ m) x := by
    intro m _
    rw [one_pow, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul]
    change (n.choose m • ((P (R := R) (A := A)) ^ m)).ofConv x = _
    rw [ofConv_smul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hterm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    rw [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero,
      zero_smul, sub_zero, LinearMap.convOne_apply, (mem_augIdeal_iff R A x).1 hx, map_zero]
    exact Ideal.zero_mem _
  · have h1 : 1 ∈ range (n + 1) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ h1, Nat.choose_one_right, pow_one, P_apply, projLin_of_mem hx,
      ← nsmul_eq_mul, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm1 : m ≠ 1 := (Finset.mem_erase.1 hm).1
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · rw [pow_zero, LinearMap.convOne_apply, (mem_augIdeal_iff R A x).1 hx, map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (P_pow_apply_mem_sq (by omega) x)

theorem toCotangent_nsmulAlgHom (n : ℕ) (x : augIdeal R A) :
    (augIdeal R A).toCotangent ⟨nsmulAlgHom R A n x, nsmulAlgHom_mem_augIdeal R A x.2 n⟩ =
      n • (augIdeal R A).toCotangent x := by
  rw [← map_nsmul, Ideal.toCotangent_eq]
  exact nsmulAlgHom_sub_nsmul_mem_sq n x.2

end NSMul

end PDivTower

open PDivTower in
theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    (n : ℕ) {x : A} (hx : x ∈ PDivisibleGroup.Hopf.augIdeal R A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A n x - n • x ∈ PDivisibleGroup.Hopf.augIdeal R A ^ 2 :=
  nsmulAlgHom_sub_nsmul_mem_sq n hx

end S_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
end P2MW
export P2MW.S_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq (solution)
