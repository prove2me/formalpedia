-- Prove2me | solution 1 for PDivisibleGroup.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ea336680-4627-58f8-946c-5521df805c98

import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv Finset Pointwise

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

theorem torsionIdeal_le (n : ℕ) :
    torsionIdeal R A n ≤ Ideal.span {(n : A)} * augIdeal R A ⊔ augIdeal R A ^ 2 := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  have hdec : nsmulAlgHom R A n a = (n : A) * a + (nsmulAlgHom R A n a - n • a) := by
    rw [nsmul_eq_mul]; abel
  rw [hdec]
  exact Submodule.add_mem_sup (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ha)
    (nsmulAlgHom_sub_nsmul_mem_sq n ha)

end NSMul

section Tower

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

open PDivisibleGroup PDivisibleGroup.Hopf

theorem pow_smul_toCotangent_eq_zero (v : ℕ) (x : G.augIdeal v) :
    ((p : R) ^ v) • (G.augIdeal v).toCotangent x = 0 := by
  have h := toCotangent_nsmulAlgHom (R := R) (A := G.level v) (p ^ v) x
  have hzero : (⟨nsmulAlgHom R (G.level v) (p ^ v) x,
      nsmulAlgHom_mem_augIdeal R (G.level v) x.2 (p ^ v)⟩ : G.augIdeal v) = 0 := by
    ext
    change nsmulAlgHom R (G.level v) (p ^ v) x = 0
    rw [G.nsmulAlgHom_pow_level_apply v, (G.mem_augIdeal_iff v _).1 x.2, map_zero]
  rw [hzero, map_zero] at h
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact h.symm

theorem pow_smul_cotangent_eq_zero (v : ℕ) (y : G.Cotangent v) : ((p : R) ^ v) • y = 0 := by
  obtain ⟨x, rfl⟩ := (G.augIdeal v).toCotangent_surjective y
  exact pow_smul_toCotangent_eq_zero G v x

theorem span_pow_smul_top_eq_bot (v : ℕ) :
    Ideal.span {(p : R) ^ v} • (⊤ : Submodule R (G.Cotangent v)) = ⊥ := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  exact pow_smul_cotangent_eq_zero G v z

theorem map_augIdeal_transition (v : ℕ) :
    (G.augIdeal (v + 1)).map (G.transitionAlgHom v) = G.augIdeal v := by
  refine le_antisymm ((Ideal.map_le_iff_le_comap).2 (G.augIdeal_le_comap_transition v)) ?_
  intro b hb
  obtain ⟨a, rfl⟩ := G.transition_surjective v b
  have hb' : counit (R := R) a = 0 := by
    have := (G.mem_augIdeal_iff v _).1 hb
    rwa [G.counit_transition] at this
  have ha : a ∈ G.augIdeal (v + 1) := (G.mem_augIdeal_iff (v + 1) a).2 hb'
  exact Ideal.mem_map_of_mem _ ha

theorem ker_transition_le (v : ℕ) :
    RingHom.ker (G.transitionAlgHom v) ≤
      Ideal.span {((p : G.level (v + 1)) ^ v)} * G.augIdeal (v + 1) ⊔ G.augIdeal (v + 1) ^ 2 := by
  intro a ha
  have ha' : a ∈ torsionIdeal R (G.level (v + 1)) (p ^ v) := by
    rw [← G.ker_transition v]; exact ha
  have := torsionIdeal_le (R := R) (A := G.level (v + 1)) (p ^ v) ha'
  rwa [Nat.cast_pow] at this

theorem ker_cotangentMap (v : ℕ) :
    LinearMap.ker (G.cotangentMap v) = Ideal.span {(p : R) ^ v} • ⊤ := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨x, rfl⟩ := (G.augIdeal (v + 1)).toCotangent_surjective y
    rw [cotangentMap_toCotangent, Ideal.toCotangent_eq_zero] at hy
    change G.transitionAlgHom v x ∈ G.augIdeal v ^ 2 at hy

    rw [← map_augIdeal_transition G v, ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective (G.transitionAlgHom v) (G.transitionAlgHom_surjective v)] at hy
    obtain ⟨x', hx', hxx'⟩ := hy

    have hdiff : (x : G.level (v + 1)) - x' ∈ RingHom.ker (G.transitionAlgHom v) := by
      rw [RingHom.mem_ker, map_sub, hxx', sub_self]
    have hx : (x : G.level (v + 1)) ∈
        Ideal.span {((p : G.level (v + 1)) ^ v)} * G.augIdeal (v + 1) ⊔ G.augIdeal (v + 1) ^ 2 := by
      have := Submodule.add_mem_sup (ker_transition_le G v hdiff)
        (show x' ∈ G.augIdeal (v + 1) ^ 2 from hx')
      rwa [sub_add_cancel, sup_assoc, sup_idem] at this
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hx
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu

    have hw1 : w ∈ G.augIdeal (v + 1) := Ideal.pow_le_self two_ne_zero hw
    have hxeq : x = ((p : R) ^ v) • (⟨z, hz⟩ : G.augIdeal (v + 1)) + ⟨w, hw1⟩ := by
      ext
      change (x : G.level (v + 1)) = ((p : R) ^ v) • z + w
      rw [← huw, Algebra.smul_def, map_pow, map_natCast]
    rw [hxeq, map_add, LinearMap.map_smul_of_tower,
      (Ideal.toCotangent_eq_zero _ (⟨w, hw1⟩ : G.augIdeal (v + 1))).2 hw, add_zero,
      Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    rw [LinearMap.mem_ker, LinearMap.map_smul_of_tower]
    exact pow_smul_cotangent_eq_zero G v _

end Tower

end PDivTower

open PDivTower in
theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ) :
    LinearMap.ker (G.cotangentMap v) = Ideal.span {(p : R) ^ v} • ⊤ ∧
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R (G.Cotangent v)) = ⊥ :=
  ⟨ker_cotangentMap G v, span_pow_smul_top_eq_bot G v⟩

end S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
end P2MW
export P2MW.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot (solution)
