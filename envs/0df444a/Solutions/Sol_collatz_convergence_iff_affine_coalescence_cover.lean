-- Prove2me | solution 1 for collatz_convergence_iff_affine_coalescence_cover
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T01:00:08.469517+00:00
-- url     : https://prove2.me/submissions/fff401dc-a7e4-491c-b2b7-03afabdbd159

import Theorems.Thm_syracuse_smaller_predecessor_iff_affine_interval
import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

open Nat

private theorem halvePow (a z : ℕ) : collatzStep^[a] (2^a*z)=z := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, pow_succ' (2:ℕ)]
    simpa [Nat.mul_assoc, collatzStep] using ih

private theorem oddPartStep (x : ℕ) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] x) = ordCompl[2] (collatzStep x) := by
  by_cases h : Even x
  · use 0
    have hd : 2 ∣ x := by rw [Nat.even_iff] at h; omega
    simpa only [Function.iterate_zero, id_eq, collatzStep, if_pos h] using
      (Nat.ordCompl_div_of_dvd Nat.prime_two hd).symm
  · use 1
    have hd : ¬ 2 ∣ x := by rw [Nat.not_even_iff] at h; omega
    have he := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x Nat.prime_two).mpr (Or.inr hd)
    rw [Function.iterate_one, he, collatzStep, if_neg h, syracuseStep]

private theorem project (x a : ℕ) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] x) = ordCompl[2] (collatzStep^[a] x) := by
  induction a with
  | zero => exact ⟨0,rfl⟩
  | succ a ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨u,hu⟩ := oddPartStep (collatzStep^[a] x)
    exact ⟨u+t, by rw [Function.iterate_add_apply, ht, Function.iterate_succ_apply', hu]⟩

private theorem liftOdd (x t : ℕ) (hx : ¬ 2 ∣ x) :
    ∃ a : ℕ, collatzStep^[a] x = syracuseStep^[t] x := by
  induction t generalizing x with
  | zero => exact ⟨0,rfl⟩
  | succ t ih =>
    let y := syracuseStep x
    let e := (3*x+1).factorization 2
    have hyo : ¬ 2 ∣ y := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
    have eqn : 2^e*y=3*x+1 := Nat.ordProj_mul_ordCompl_eq_self (3*x+1) 2
    have hn : ¬ Even x := by rw [Nat.not_even_iff]; omega
    have first : collatzStep^[e+1] x=y := by
      rw [Function.iterate_succ_apply, collatzStep, if_neg hn, ← eqn]
      exact halvePow e y
    obtain ⟨a,ha⟩ := ih y hyo
    exact ⟨a+(e+1), by rw [Function.iterate_add_apply, first, ha, Function.iterate_succ_apply]⟩

private theorem oddIterate (x t : ℕ) (hx : ¬ 2 ∣ x) :
    ¬ 2 ∣ syracuseStep^[t] x := by
  cases t with
  | zero => exact hx
  | succ t =>
    rw [Function.iterate_succ_apply', syracuseStep]
    exact Nat.not_dvd_ordCompl Nat.prime_two (by omega)

theorem solution :
    (∀ n : ℕ, 0 < n → ∃ a : ℕ, collatzStep^[a] n = 1) ↔
    (∀ n : ℕ, 1 < n → ¬ 2 ∣ n →
      ∃ (t : ℕ) (w : List ℕ), (∀ a : ℕ, a ∈ w → 0 < a) ∧
        let F := 2^w.sum * syracuseStep^[t] n
        let C := syracuseAffineConstant w
        let M := 3^w.length
        F % M = C % M ∧ C + M ≤ F ∧ F < C + M*n) := by
  constructor
  · intro all n hn ho
    obtain ⟨a,ha⟩ := all n (by omega)
    obtain ⟨t,ht⟩ := project n a
    have ee := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr ho)
    rw [ee,ha] at ht
    have ht' : syracuseStep^[t] n=1 := ht.trans (by simp [Nat.factorization_one])
    exact ⟨t,[],by simp, by simpa [syracuseAffineConstant, ht'] using hn⟩
  · intro cover
    have fixed : syracuseStep 1=1 := by decide +kernel
    have allOdd (n : ℕ) (hp : 0 < n) (ho : ¬ 2 ∣ n) :
        ∃ j : ℕ, syracuseStep^[j] n=1 := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n=1
        · exact ⟨0,hn⟩
        obtain ⟨t,w,hw,hcert⟩ := cover n (by omega) ho
        let y := syracuseStep^[t] n
        obtain ⟨k,hkp,hklt,hmeet,_,hko⟩ :=
          (syracuse_smaller_predecessor_iff_affine_interval w y n (oddIterate n t ho) hw).mp hcert
        obtain ⟨j,hj⟩ := ih k hklt hkp hko
        have hconst (l : ℕ) : syracuseStep^[l] 1=1 := Function.iterate_fixed fixed l
        refine ⟨j+t,?_⟩
        rw [Function.iterate_add_apply]
        change syracuseStep^[j] y=1
        rw [← hmeet, ← Function.iterate_add_apply, Nat.add_comm j w.length,
          Function.iterate_add_apply, hj, hconst]
    intro n hn
    let x := ordCompl[2] n
    have hx : 0 < x := Nat.ordCompl_pos 2 hn.ne'
    have ho : ¬ 2 ∣ x := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
    obtain ⟨j,hj⟩ := allOdd x hx ho
    obtain ⟨a,ha⟩ := liftOdd x j ho
    let e := n.factorization 2
    have he : 2^e*x=n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have hx' : collatzStep^[e] n=x := by rw [← he]; exact halvePow e x
    exact ⟨a+e, by rw [Function.iterate_add_apply, hx', ha, hj]⟩
