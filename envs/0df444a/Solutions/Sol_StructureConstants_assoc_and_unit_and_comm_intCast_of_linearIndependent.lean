-- Prove2me | solution 1 for StructureConstants.assoc_and_unit_and_comm_intCast_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a628bdb8-3b89-5878-a811-c0f21e383d81

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace StructureConstantsSol

variable {A : Type*} [Ring A] {K : ℕ} (u : Fin K → A) (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ)

section AnyRing

variable (R : Type*) [CommRing R]

def cst (a b : Fin K → R) : Fin K → R := fun m => ∑ k, ∑ l, a k * b l * (c k l m : R)

theorem cst_apply (a b : Fin K → R) (m : Fin K) : cst c R a b m = ∑ k, ∑ l, a k * b l * (c k l m : R) := rfl

theorem sum4_rot (f : Fin K → Fin K → Fin K → Fin K → R) :
    ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l := by
  calc ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ q, ∑ k, ∑ t, ∑ l, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ k, ∑ l, ∑ t, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ q, ∑ l, ∑ t, f q t k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ q, ∑ t, f q t k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem sum3_rot (f : Fin K → Fin K → Fin K → R) :
    ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ t, ∑ q, f q l t := by
  calc ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ q, ∑ t, f q l t := Finset.sum_comm
    _ = ∑ l, ∑ t, ∑ q, f q l t := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem cst_cst_left (a b d : Fin K → R) (s : Fin K) :
    cst c R (cst c R a b) d s = ∑ k, ∑ l, ∑ t, a k * b l * d t * ∑ q, (c k l q : R) * (c q t s : R) := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_cst_right (a b d : Fin K → R) (s : Fin K) :
    cst c R a (cst c R b d) s = ∑ k, ∑ l, ∑ t, a k * b l * d t * ∑ q, (c l t q : R) * (c k q s : R) := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_eq_sum_right (a b : Fin K → R) (s : Fin K) :
    cst c R a b s = ∑ l, b l * ∑ k, a k * (c k l s : R) := by
  rw [cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cst_eq_sum_left (a b : Fin K → R) (s : Fin K) :
    cst c R a b s = ∑ k, a k * ∑ l, b l * (c k l s : R) := by
  rw [cst_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem cst_single_single (k l : Fin K) : cst c R (Pi.single k 1) (Pi.single l 1) = fun m => (c k l m : R) := by
  funext m
  rw [cst_apply, Finset.sum_eq_single k, Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, Pi.single_eq_same, one_mul, one_mul]
  · intro l' _ h; rw [Pi.single_eq_of_ne h, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ l) h
  · intro k' _ h
    exact Finset.sum_eq_zero fun l' _ => by rw [Pi.single_eq_of_ne h, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem cst_single_right (x : Fin K → R) (t s : Fin K) : cst c R x (Pi.single t 1) s = ∑ q, x q * (c q t s : R) := by
  rw [cst_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single t]
  · rw [Pi.single_eq_same, mul_one]
  · intro t' _ h; rw [Pi.single_eq_of_ne h, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem cst_single_left (x : Fin K → R) (k s : Fin K) : cst c R (Pi.single k 1) x s = ∑ q, x q * (c k q s : R) := by
  rw [cst_apply, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.single_eq_same, one_mul]
  · intro k' _ h
    exact Finset.sum_eq_zero fun q _ => by rw [Pi.single_eq_of_ne h, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

end AnyRing

def elem (a : Fin K → ℤ) : A := ∑ k, a k • u k

theorem elem_single (k : Fin K) : elem u (Pi.single k 1) = u k := by
  rw [elem, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_smul]
  · intro l _ hl; rw [Pi.single_eq_of_ne hl, zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem elem_sub (a b : Fin K → ℤ) : elem u (a - b) = elem u a - elem u b := by
  simp only [elem, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

variable (hu : LinearIndependent ℤ u)
  (hu_mul : ∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) (hu_one : ∑ m, c₁ m • u m = 1)

include hu in
theorem elem_injective : Function.Injective (elem u) := by
  intro a b h
  have h0 : elem u (a - b) = 0 := by rw [elem_sub, h, sub_self]
  have := (Fintype.linearIndependent_iff.mp hu) (a - b) h0
  funext k
  exact sub_eq_zero.mp (this k)

include hu_mul in

theorem elem_cst (a b : Fin K → ℤ) : elem u (cst c ℤ a b) = elem u a * elem u b := by
  have hR : elem u a * elem u b = ∑ k, ∑ l, ∑ m, (a k * b l * c k l m) • u m := by
    rw [elem, elem, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, hu_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hL : elem u (cst c ℤ a b) = ∑ m, ∑ k, ∑ l, (a k * b l * c k l m) • u m := by
    simp only [elem, cst, Int.cast_id]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

include hu_one in
theorem elem_c₁ : elem u c₁ = 1 := hu_one

include hu hu_mul in

theorem cst_assoc_int (a b d : Fin K → ℤ) : cst c ℤ (cst c ℤ a b) d = cst c ℤ a (cst c ℤ b d) := by
  apply elem_injective u hu
  rw [elem_cst u c hu_mul, elem_cst u c hu_mul, elem_cst u c hu_mul, elem_cst u c hu_mul, mul_assoc]

include hu hu_mul hu_one in
theorem cst_c₁_int (a : Fin K → ℤ) : cst c ℤ c₁ a = a := by
  apply elem_injective u hu
  rw [elem_cst u c hu_mul, elem_c₁ u c₁ hu_one, one_mul]

include hu hu_mul hu_one in
theorem cst_c₁_int' (a : Fin K → ℤ) : cst c ℤ a c₁ = a := by
  apply elem_injective u hu
  rw [elem_cst u c hu_mul, elem_c₁ u c₁ hu_one, mul_one]

include hu hu_mul in
theorem cst_comm_int (hcomm : ∀ k l : Fin K, u k * u l = u l * u k) (a b : Fin K → ℤ) :
    cst c ℤ a b = cst c ℤ b a := by
  apply elem_injective u hu
  rw [elem_cst u c hu_mul, elem_cst u c hu_mul]
  refine (Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_).eq
  have hc : Commute (u k) (u l) := hcomm k l
  exact (hc.smul_left (a k)).smul_right (b l)

include hu hu_mul in
theorem c_assoc (k l t s : Fin K) : ∑ q, c k l q * c q t s = ∑ q, c l t q * c k q s := by
  have h := congrFun (cst_assoc_int u c hu hu_mul (Pi.single k 1) (Pi.single l 1) (Pi.single t 1)) s
  rw [cst_single_single, cst_single_single, cst_single_right, cst_single_left] at h
  simpa only [Int.cast_id] using h

include hu hu_mul hu_one in
theorem c_unit_left (l s : Fin K) : ∑ k, c₁ k * c k l s = (Pi.single l (1 : ℤ) : Fin K → ℤ) s := by
  have h := congrFun (cst_c₁_int u c c₁ hu hu_mul hu_one (Pi.single l 1)) s
  rw [cst_single_right] at h
  simpa only [Int.cast_id] using h

include hu hu_mul hu_one in
theorem c_unit_right (k s : Fin K) : ∑ l, c₁ l * c k l s = (Pi.single k (1 : ℤ) : Fin K → ℤ) s := by
  have h := congrFun (cst_c₁_int' u c c₁ hu hu_mul hu_one (Pi.single k 1)) s
  rw [cst_single_left] at h
  simpa only [Int.cast_id] using h

include hu hu_mul in
theorem c_comm (hcomm : ∀ k l : Fin K, u k * u l = u l * u k) (k l s : Fin K) : c k l s = c l k s := by
  have h := congrFun (cst_comm_int u c hu hu_mul hcomm (Pi.single k 1) (Pi.single l 1)) s
  rw [cst_single_single, cst_single_single] at h
  simpa only [Int.cast_id] using h

section Cast

variable (R : Type*) [CommRing R]

include hu hu_mul in
theorem c_assoc_cast (k l t s : Fin K) :
    ∑ q, (c k l q : R) * (c q t s : R) = ∑ q, (c l t q : R) * (c k q s : R) := by
  have h := congrArg (fun z : ℤ => (z : R)) (c_assoc u c hu hu_mul k l t s)
  simpa only [Int.cast_sum, Int.cast_mul] using h

theorem single_cast (l s : Fin K) :
    (((Pi.single l (1 : ℤ) : Fin K → ℤ) s : ℤ) : R) = (Pi.single l (1 : R) : Fin K → R) s := by
  by_cases h : s = l
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, Int.cast_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Int.cast_zero]

include hu hu_mul hu_one in
theorem c_unit_left_cast (l s : Fin K) :
    ∑ k, (c₁ k : R) * (c k l s : R) = (Pi.single l (1 : R) : Fin K → R) s := by
  have h := congrArg (fun z : ℤ => (z : R)) (c_unit_left u c c₁ hu hu_mul hu_one l s)
  simpa only [Int.cast_sum, Int.cast_mul, single_cast] using h

include hu hu_mul hu_one in
theorem c_unit_right_cast (k s : Fin K) :
    ∑ l, (c₁ l : R) * (c k l s : R) = (Pi.single k (1 : R) : Fin K → R) s := by
  have h := congrArg (fun z : ℤ => (z : R)) (c_unit_right u c c₁ hu hu_mul hu_one k s)
  simpa only [Int.cast_sum, Int.cast_mul, single_cast] using h

theorem sum_mul_single (a : Fin K → R) (s : Fin K) : ∑ l, a l * (Pi.single l (1 : R) : Fin K → R) s = a s := by
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same, mul_one]
  · intro l _ hl; rw [Pi.single_eq_of_ne' hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ s) h

include hu hu_mul in
theorem cst_assoc (a b d : Fin K → R) (s : Fin K) : cst c R (cst c R a b) d s = cst c R a (cst c R b d) s := by
  rw [cst_cst_left, cst_cst_right]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun t _ => ?_
  rw [c_assoc_cast u c hu hu_mul R]

include hu hu_mul hu_one in
theorem cst_unit_left (a : Fin K → R) (s : Fin K) : cst c R (fun k => (c₁ k : R)) a s = a s := by
  rw [cst_eq_sum_right]
  conv_rhs => rw [← sum_mul_single R a s]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [c_unit_left_cast u c c₁ hu hu_mul hu_one R]

include hu hu_mul hu_one in
theorem cst_unit_right (a : Fin K → R) (s : Fin K) : cst c R a (fun l => (c₁ l : R)) s = a s := by
  rw [cst_eq_sum_left]
  conv_rhs => rw [← sum_mul_single R a s]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [c_unit_right_cast u c c₁ hu hu_mul hu_one R]

include hu hu_mul in
theorem cst_comm (hcomm : ∀ k l : Fin K, u k * u l = u l * u k) (a b : Fin K → R) (s : Fin K) :
    cst c R a b s = cst c R b a s := by
  rw [cst_apply, cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [c_comm u c hu hu_mul hcomm k l s, mul_comm (a k) (b l)]

end Cast

end StructureConstantsSol

open StructureConstantsSol in
theorem solution
    {A : Type} [Ring A] {K : ℕ} (u : Fin K → A) (hu : LinearIndependent ℤ u)
    (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ)
    (hu_mul : ∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) (hu_one : ∑ m, c₁ m • u m = 1)
    (R : Type) [CommRing R] :
    (∀ (a b d : Fin K → R) (s : Fin K),
      ∑ q, ∑ t, (∑ k, ∑ l, a k * b l * (c k l q : R)) * d t * (c q t s : R) =
        ∑ k, ∑ q, a k * (∑ l, ∑ t, b l * d t * (c l t q : R)) * (c k q s : R)) ∧
    (∀ (a : Fin K → R) (s : Fin K), ∑ k, ∑ l, (c₁ k : R) * a l * (c k l s : R) = a s) ∧
    (∀ (a : Fin K → R) (s : Fin K), ∑ k, ∑ l, a k * (c₁ l : R) * (c k l s : R) = a s) ∧
    ((∀ k l : Fin K, u k * u l = u l * u k) →
      ∀ (a b : Fin K → R) (s : Fin K),
        ∑ k, ∑ l, a k * b l * (c k l s : R) = ∑ k, ∑ l, b k * a l * (c k l s : R)) :=
  ⟨fun a b d s => cst_assoc u c hu hu_mul R a b d s,
   fun a s => cst_unit_left u c c₁ hu hu_mul hu_one R a s,
   fun a s => cst_unit_right u c c₁ hu hu_mul hu_one R a s,
   fun hcomm a b s => cst_comm u c hu hu_mul R hcomm a b s⟩

end

end S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent
end P2MW
export P2MW.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent (solution)
