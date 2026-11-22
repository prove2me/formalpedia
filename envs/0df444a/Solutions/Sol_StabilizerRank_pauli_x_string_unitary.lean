-- Prove2me | solution 1 for StabilizerRank.pauli_x_string_unitary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-08T01:28:57.444403+00:00
-- url     : https://prove2.me/submissions/07726994-d5b3-4f01-a4fd-9d16d8d840a6

import Definitions.Def_StabilizerRank

open StabilizerRank

theorem solution {n : ℕ} (x : Bits n) :
    pauliMatrix x 0 ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  have f_inv : Function.Involutive (fun x' : Bits n => (fun i => xor (x i) (x' i))) := by
    intro x'
    funext i
    show xor (x i) (xor (x i) (x' i)) = x' i
    cases h1 : x i <;> cases h2 : x' i <;> rfl
  have f_inj : Function.Injective (fun x' : Bits n => (fun i => xor (x i) (x' i))) :=
    f_inv.injective
  have hconv : ∀ {a c : Bits n}, a = (fun i => xor (x i) (c i)) →
      c = (fun i => xor (x i) (a i)) := by
    intro a c ha
    funext i
    have hai : a i = xor (x i) (c i) := congrArg (fun y : Bits n => y i) ha
    show c i = xor (x i) (a i)
    rw [show a i = xor (x i) (c i) from hai]
    cases hx : x i <;> cases hc : c i <;> rfl
  have hU : ∀ y x' : Bits n, pauliMatrix x 0 y x' =
      (if y = (fun i => xor (x i) (x' i)) then (1 : ℂ) else 0) := by
    intro y x'
    simp [pauliMatrix, Matrix.of_apply]
  have hstar : ∀ c b : Bits n, star (pauliMatrix x 0) c b =
      (if b = (fun i => xor (x i) (c i)) then (1 : ℂ) else 0) := by
    intro c b
    rw [Matrix.star_apply, hU]
    by_cases h : b = (fun i => xor (x i) (c i)) <;> simp [h]
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply]
  have hsum : ∀ c : Bits n, pauliMatrix x 0 a c * star (pauliMatrix x 0) c b =
      ((if c = (fun i => xor (x i) (a i)) then (1 : ℂ) else 0) *
        (if c = (fun i => xor (x i) (b i)) then (1 : ℂ) else 0)) := by
    intro c
    rw [hU, hstar]
    by_cases ha : a = (fun i => xor (x i) (c i)) <;> by_cases hb : b = (fun i => xor (x i) (c i))
    · rw [if_pos ha, if_pos hb, if_pos (hconv ha), if_pos (hconv hb)]
    · rw [if_pos ha, if_neg hb, if_pos (hconv ha),
        if_neg (fun hcb => hb (hconv hcb))]
    · rw [if_neg ha, if_pos hb, if_neg (fun hca => ha (hconv hca)),
        if_pos (hconv hb)]
    · rw [if_neg ha, if_neg (fun hca => ha (hconv hca)), zero_mul, zero_mul]
  simp_rw [hsum]
  by_cases hab : a = b
  · subst hab
    have hone : ∀ c : Bits n, ((if c = (fun i => xor (x i) (a i)) then (1 : ℂ) else 0) *
        (if c = (fun i => xor (x i) (a i)) then (1 : ℂ) else 0)) =
        (if c = (fun i => xor (x i) (a i)) then (1 : ℂ) else 0) := by
      intro c
      by_cases h : c = (fun i => xor (x i) (a i)) <;> simp [h]
    simp_rw [hone]
    rw [Matrix.one_apply, if_pos rfl]
    rw [Finset.sum_ite_eq']
    simp
  · have hRHS : (1 : Matrix (Bits n) (Bits n) ℂ) a b = 0 := by
      simp [hab]
    rw [hRHS]
    apply Finset.sum_eq_zero
    intro c hc
    by_cases ha : c = (fun i => xor (x i) (a i)) <;>
      by_cases hb : c = (fun i => xor (x i) (b i))
    · exfalso
      exact hab (f_inj (ha.symm.trans hb))
    · rw [if_neg hb, mul_zero]
    · rw [if_neg ha, zero_mul]
    · rw [if_neg ha, zero_mul]


