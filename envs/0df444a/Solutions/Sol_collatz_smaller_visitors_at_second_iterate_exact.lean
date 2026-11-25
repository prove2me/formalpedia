-- Prove2me | solution 1 for collatz_smaller_visitors_at_second_iterate_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:23:33.93203+00:00
-- url     : https://prove2.me/submissions/3acac065-0eea-45c1-bcb1-3749cf5dc5a3

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorization.Basic

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]


private theorem powerHalvings (s k : ℕ) : collatzStep^[s] (2^s*k) = k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hf : 2^(s+1)*k = 2*(2^s*k) := by rw [pow_succ]; ring
    rw [Function.iterate_succ_apply, hf, stepEven _ (by omega)]
    simpa using ih


private theorem oddStepThenHalves (x y a : ℕ) (ha : 0<a)
    (h : 3*x+1=2^a*y) : collatzStep^[a+1] x=y := by
  have he : (3*x+1)%2=0 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    have heq : 2^(j+1)*y=2*(2^j*y) := by rw [pow_succ]; ring
    rw [h,heq]
    omega
  have ho : x%2=1 := by omega
  rw [Function.iterate_add_apply,Function.iterate_one,stepOdd _ ho,h,powerHalvings]


/-- Additive numerator of a sequence of ordinary odd steps with the
prescribed numbers of following halvings. The first exponent is first
in forward time. -/
private def collatzHalvingWordOffset : List ℕ → ℕ
  | [] => 0
  | e::w => 3^w.length+2^e*collatzHalvingWordOffset w

/-- The integer affine identity forces every intermediate division and
every parity required by a positive halving word. -/
private theorem collatz_halving_word_of_affine_identity
    (w : List ℕ) (x y : ℕ)
    (hword : ∀ e∈w, 0<e)
    (h : 3^w.length*x+collatzHalvingWordOffset w=2^w.sum*y) :
    collatzStep^[w.sum+w.length] x=y := by
  induction w generalizing x with
  | nil => simpa [collatzHalvingWordOffset] using h
  | cons e w ih =>
    have he : 0<e := hword e (List.mem_cons_self)
    have hcoef : 3^w.length*(3*x+1)+2^e*collatzHalvingWordOffset w =
        2^e*(2^w.sum*y) := calc
      _ = 3^(e::w).length*x+collatzHalvingWordOffset (e::w) := by
        simp only [List.length_cons,collatzHalvingWordOffset,pow_succ]
        ring
      _ = 2^(e::w).sum*y := h
      _ = _ := by rw [List.sum_cons,pow_add,Nat.mul_assoc]
    have hprod : 2^e ∣ 3^w.length*(3*x+1) :=
      (Nat.dvd_add_iff_left (Nat.dvd_mul_right _ _)).mpr ⟨_,hcoef⟩
    have hcop : (2^e).Coprime (3^w.length) :=
      ((by decide : Nat.Coprime 2 3).pow_left e).pow_right _
    obtain ⟨z,hz⟩ := hcop.dvd_of_dvd_mul_left hprod
    have hfirst : collatzStep^[e+1] x=z := oddStepThenHalves x z e he hz
    have hrest : 3^w.length*z+collatzHalvingWordOffset w=2^w.sum*y := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos e)
      calc
        _ = 3^w.length*(2^e*z)+2^e*collatzHalvingWordOffset w := by ring
        _ = _ := by rw [←hz]; exact hcoef
    have hend := ih z (fun a ha => hword a (List.mem_cons_of_mem _ ha)) hrest
    rw [show (e::w).sum+(e::w).length=(w.sum+w.length)+(e+1) by simp; omega,
      Function.iterate_add_apply,hfirst,hend]


/-- The pair of length and affine offset can be evaluated with an
ordinary list fold. -/
private theorem collatz_halving_word_offset_fold (w : List ℕ) :
    w.foldr (fun e (p : ℕ × ℕ) => (p.1+1,3^p.1+2^e*p.2)) (0,0) =
      (w.length,collatzHalvingWordOffset w) := by
  induction w with
  | nil => rfl
  | cons e w ih => simp [collatzHalvingWordOffset,ih]


private theorem oddTarget_halving_word (t x y : ℕ) (hy : y%2=1)
    (h : collatzStep^[t] x=y) :
    ∃ (s u : ℕ) (w : List ℕ), x=2^s*u ∧ u%2=1 ∧
      (∀ a∈w, 0<a) ∧ t=s+(w.sum+w.length) ∧
      3^w.length*u+collatzHalvingWordOffset w=2^w.sum*y := by
  induction t generalizing x with
  | zero =>
    change x=y at h
    subst x
    exact ⟨0,y,[],by simp,hy,by simp,by simp,by simp [collatzHalvingWordOffset]⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    obtain ⟨s,u,w,hstart,hu,hword,ht,hend⟩ := ih _ h
    by_cases he : x%2=0
    · rw [stepEven _ he] at hstart
      have hx : x=2^(s+1)*u := calc
        _ = 2*(x/2) := by omega
        _ = _ := by rw [hstart,pow_succ]; ring
      exact ⟨s+1,u,w,hx,hu,hword,by omega,hend⟩
    · have ho : x%2=1 := by omega
      rw [stepOdd _ ho] at hstart
      have hs : 0<s := by
        by_contra! hzero
        rw [Nat.eq_zero_of_le_zero hzero,pow_zero,one_mul] at hstart
        omega
      refine ⟨0,x,s::w,by simp,ho,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hs
        · exact hword a ha'
      · simp only [zero_add,List.length_cons,List.sum_cons]
        omega
      · calc
          3^(s::w).length*x+collatzHalvingWordOffset (s::w) =
              3^w.length*(3*x+1)+2^s*collatzHalvingWordOffset w := by
            simp only [List.length_cons,pow_succ,collatzHalvingWordOffset]
            ring
          _ = 2^s*(3^w.length*u+collatzHalvingWordOffset w) := by
            rw [hstart]
            ring
          _ = 2^(s::w).sum*y := by rw [hend,List.sum_cons,pow_add,Nat.mul_assoc]

/-- This characterizes every smaller visitor to the second iterate
when that iterate is odd. The offset and source-size checks are exact. -/
private theorem collatz_second_iterate_smaller_visitor_iff_word (n : ℕ) (hclass : n%16=15) :
    (∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[2] n) ↔
      ∃ w : List ℕ, (∀ a∈w, 0<a) ∧
        let y := (3*n+1)/2
        let B := collatzHalvingWordOffset w
        let z := 2^w.sum*y-B
        0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n := by
  let y := (3*n+1)/2
  have hny : collatzStep^[2] n=y := oddStepThenHalves n y 1 (by decide)
    (by dsimp [y]; omega)
  have hy : y%2=1 := by dsimp [y]; omega
  rw [hny]
  constructor
  · rintro ⟨k,t,hk,hl,hkt⟩
    obtain ⟨s,u,w,hstart,hu,hword,_,hend⟩ := oddTarget_halving_word t k y hy hkt
    have hu0 : 0<u := by omega
    have hlu : u<n := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)).trans_lt (hstart ▸ hl)
    have hz : 2^w.sum*y-collatzHalvingWordOffset w=3^w.length*u := by omega
    refine ⟨w,hword,?_⟩
    dsimp only
    rw [hz]
    have hp : 0<(3:ℕ)^w.length := Nat.pow_pos (by decide)
    exact ⟨Nat.mul_pos hp hu0,⟨u,rfl⟩,Nat.mul_lt_mul_of_pos_left hlu hp⟩
  · rintro ⟨w,hword,hdata⟩
    let z := 2^w.sum*y-collatzHalvingWordOffset w
    change 0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n at hdata
    obtain ⟨hz,⟨k,hfac⟩,hlt⟩ := hdata
    have hk : 0<k := by
      by_contra! he
      rw [Nat.eq_zero_of_le_zero he,mul_zero] at hfac
      omega
    have hkn : k<n := (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0<(3:ℕ)))).mp
      (by rwa [hfac] at hlt)
    have ha : 3^w.length*k+collatzHalvingWordOffset w=2^w.sum*y := by dsimp [z] at *; omega
    exact ⟨k,w.sum+w.length,hk,hkn,collatz_halving_word_of_affine_identity w k y hword ha⟩

theorem solution (n : ℕ) (hclass : n%16=15) :
    (∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[2] n) ↔
    (∃ w : List ℕ, (∀ a∈w, 0<a) ∧
      let y := (3*n+1)/2
      let B := (w.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^w.sum*y-B
      0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n) := by
  simpa only [collatz_halving_word_offset_fold] using
    collatz_second_iterate_smaller_visitor_iff_word n hclass
