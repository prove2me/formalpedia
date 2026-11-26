-- Prove2me | solution 1 for collatz_repeat_gap_and_band_escape_above_frontier
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:43:18.567215+00:00
-- url     : https://prove2.me/submissions/dcf775c1-d1c7-4245-98a7-1992a2f3fcc2

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Card

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

/-- Counts of halving and odd steps on an ordinary Collatz segment. -/
private def collatzOrdinaryStepCounts : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0,0)
  | t+1, x =>
    let p := collatzOrdinaryStepCounts t (collatzStep x)
    if x%2=0 then (p.1+1,p.2) else (p.1,p.2+1)

/-- Multiplying the step inequalities gives exact integer bounds for a
segment that stays above a fixed floor. -/
private theorem collatz_ordinary_segment_product_bounds (N t x : ℕ)
    (hfloor : ∀ i : ℕ, i≤t → N≤collatzStep^[i] x) :
    let p := collatzOrdinaryStepCounts t x
    p.1+p.2=t ∧
    3^p.2*x≤2^p.1*collatzStep^[t] x ∧
    (0<p.2 → 3^p.2*x<2^p.1*collatzStep^[t] x) ∧
    2^p.1*(N^p.2*collatzStep^[t] x)≤(3*N+1)^p.2*x := by
  induction t generalizing x with
  | zero => simp [collatzOrdinaryStepCounts]
  | succ t ih =>
    let y := collatzStep x
    let z := collatzStep^[t] y
    let p := collatzOrdinaryStepCounts t y
    have hy : ∀ i : ℕ, i≤t → N≤collatzStep^[i] y := by
      intro i hi
      rw [←Function.iterate_succ_apply]
      exact hfloor (i+1) (by omega)
    obtain ⟨hc,hlo,hstrict,hup⟩ := ih y hy
    change p.1+p.2=t at hc
    change 3^p.2*y≤2^p.1*z at hlo
    change 0<p.2 → 3^p.2*y<2^p.1*z at hstrict
    change 2^p.1*(N^p.2*z)≤(3*N+1)^p.2*y at hup
    simp only [collatzOrdinaryStepCounts,Function.iterate_succ_apply]
    by_cases hx : x%2=0
    · rw [if_pos hx]
      change (p.1+1)+p.2=t+1 ∧ 3^p.2*x≤2^(p.1+1)*z ∧
        (0<p.2 → 3^p.2*x<2^(p.1+1)*z) ∧
        2^(p.1+1)*(N^p.2*z)≤(3*N+1)^p.2*x
      have hx2 : x=2*y := by dsimp [y]; rw [stepEven _ hx]; omega
      have hl : 3^p.2*x=2*(3^p.2*y) := by rw [hx2]; ring
      have hright : 2^(p.1+1)*z=2*(2^p.1*z) := by rw [pow_succ]; ring
      have hlast : 2^(p.1+1)*(N^p.2*z)=2*(2^p.1*(N^p.2*z)) := by rw [pow_succ]; ring
      have hxlast : (3*N+1)^p.2*x=2*((3*N+1)^p.2*y) := by rw [hx2]; ring
      rw [hl,hright,hlast,hxlast]
      exact ⟨by omega,Nat.mul_le_mul_left 2 hlo,
        fun h => Nat.mul_lt_mul_of_pos_left (hstrict h) (by decide),Nat.mul_le_mul_left 2 hup⟩
    · rw [if_neg hx]
      change p.1+(p.2+1)=t+1 ∧ 3^(p.2+1)*x≤2^p.1*z ∧
        (0<p.2+1 → 3^(p.2+1)*x<2^p.1*z) ∧
        2^p.1*(N^(p.2+1)*z)≤(3*N+1)^(p.2+1)*x
      have ho : y=3*x+1 := stepOdd x (by omega)
      have hlt : 3^(p.2+1)*x<2^p.1*z := calc
        _ = 3^p.2*(3*x) := by rw [pow_succ]; ring
        _ < 3^p.2*y := by rw [ho]; exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by decide))
        _ ≤ _ := hlo
      have hxN : N≤x := hfloor 0 (Nat.zero_le _)
      have hlocal : N*y≤(3*N+1)*x := by
        rw [ho]
        calc
          N*(3*x+1) = 3*N*x+N := by ring
          _ ≤ 3*N*x+x := Nat.add_le_add_left hxN _
          _ = (3*N+1)*x := by ring
      refine ⟨by omega,hlt.le,fun _ => hlt,?_⟩
      calc
        2^p.1*(N^(p.2+1)*z) = N*(2^p.1*(N^p.2*z)) := by rw [pow_succ]; ring
        _ ≤ N*((3*N+1)^p.2*y) := Nat.mul_le_mul_left N hup
        _ = (3*N+1)^p.2*(N*y) := by ring
        _ ≤ (3*N+1)^p.2*((3*N+1)*x) := Nat.mul_le_mul_left _ hlocal
        _ = (3*N+1)^(p.2+1)*x := by rw [pow_succ]; ring

set_option maxHeartbeats 0 in
private theorem collatz_cycle_upper_power_bound :
    (3*2310000+1 : ℕ)^4961 < 2^7863*(2310000 : ℕ)^4961 := by decide +kernel

/-- The two fractions 1054/665 and 7863/4961 have determinant one.
Their exact power comparisons exclude all smaller step counts. -/
private theorem collatz_cycle_counts_at_floor_bound (e o : ℕ) (ho : 0<o)
    (hlo : 3^o<2^e) (hup : 2^e*(2310000 : ℕ)^o≤(3*2310000+1 : ℕ)^o) :
    5626≤o ∧ 8917≤e := by
  have hc : (2:ℕ)^1054 < 3^665 := by decide +kernel
  have hleft : (2:ℕ)^(1054*o)<2^(e*665) := calc
    _ = ((2:ℕ)^1054)^o := by rw [pow_mul]
    _ ≤ ((3:ℕ)^665)^o := Nat.pow_le_pow_left hc.le _
    _ = ((3:ℕ)^o)^665 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ < ((2:ℕ)^e)^665 := Nat.pow_lt_pow_left hlo (by decide : (665:ℕ)≠0)
    _ = 2^(e*665) := by rw [pow_mul]
  have hlow : 1054*o<665*e := by
    by_contra! h
    have h' := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show e*665≤1054*o by omega)
    exact (not_lt_of_ge h') hleft
  have hu : 2^(e*4961)*(2310000 : ℕ)^(o*4961)≤(3*2310000+1 : ℕ)^(o*4961) := by
    simpa only [mul_pow,pow_mul] using Nat.pow_le_pow_left hup 4961
  have hh : (3*2310000+1 : ℕ)^(4961*o)<2^(7863*o)*(2310000 : ℕ)^(4961*o) := by
    simpa only [mul_pow,pow_mul] using
      Nat.pow_lt_pow_left collatz_cycle_upper_power_bound (Nat.ne_of_gt ho)
  rw [Nat.mul_comm o 4961] at hu
  have hright : (2:ℕ)^(e*4961)<2^(7863*o) := Nat.lt_of_mul_lt_mul_right (hu.trans_lt hh)
  have hhigh : 4961*e<7863*o := by
    by_contra! h
    have h' := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 7863*o≤e*4961 by omega)
    exact (not_lt_of_ge h') hright
  have hdet : o=665*(7863*o-4961*e)+4961*(665*e-1054*o) := by omega
  have hb1 : 0<7863*o-4961*e := by omega
  have hb2 : 0<665*e-1054*o := by omega
  constructor <;> omega

/-- Every positive return segment wholly above the frontier floor has
at least 5626 odd steps and at least 8917 halvings. -/
private theorem collatz_return_segment_minimum_length_above_frontier (x t : ℕ)
    (ht : 0<t) (hreturn : collatzStep^[t] x=x)
    (hfloor : ∀ i : ℕ, i≤t → 2310000≤collatzStep^[i] x) :
    14543≤t := by
  let p := collatzOrdinaryStepCounts t x
  obtain ⟨hc,hle,hstrict,hup⟩ := collatz_ordinary_segment_product_bounds 2310000 t x hfloor
  change p.1+p.2=t at hc
  change 3^p.2*x≤2^p.1*collatzStep^[t] x at hle
  change 0<p.2 → 3^p.2*x<2^p.1*collatzStep^[t] x at hstrict
  change 2^p.1*((2310000:ℕ)^p.2*collatzStep^[t] x)≤(3*2310000+1 : ℕ)^p.2*x at hup
  have hx : 0<x := (by decide : 0<2310000).trans_le (hfloor 0 (Nat.zero_le _))
  rw [hreturn] at hle hstrict hup
  have hupper := Nat.le_of_mul_le_mul_right (by rwa [Nat.mul_assoc] :
    (2^p.1*(2310000:ℕ)^p.2)*x≤(3*2310000+1 : ℕ)^p.2*x) hx
  have hp : 0<p.2 := by
    by_contra! hzero
    have hz : p.2=0 := by omega
    rw [hz,pow_zero,pow_zero,mul_one] at hupper
    have he : 0<p.1 := by omega
    have hbig : (2:ℕ)^1≤2^p.1 := Nat.pow_le_pow_right (by decide) he
    omega
  have hlow := Nat.lt_of_mul_lt_mul_right (hstrict hp)
  obtain ⟨ho,he⟩ := collatz_cycle_counts_at_floor_bound p.1 p.2 hp hlow hupper
  omega

private theorem collatz_non_descending_repeat_gap (n a b : ℕ)
    (hlarge : 2310000≤n) (hstay : ∀ j : ℕ, n≤collatzStep^[j] n)
    (hab : a<b) (heq : collatzStep^[a] n=collatzStep^[b] n) : 14543≤b-a := by
  have hclock (i : ℕ) : collatzStep^[i] (collatzStep^[a] n)=collatzStep^[i+a] n :=
    (Function.iterate_add_apply collatzStep i a n).symm
  apply collatz_return_segment_minimum_length_above_frontier (collatzStep^[a] n) (b-a) (by omega)
  · rw [hclock,show b-a+a=b by omega]
    exact heq.symm
  · intro i _
    rw [hclock]
    exact hlarge.trans (hstay (i+a))

/-- A block of 14543 consecutive states has distinct values. Consequently
every such block leaves the band from n to n+14541. -/
private theorem collatz_non_descending_escapes_short_band (n t : ℕ)
    (hlarge : 2310000≤n) (hstay : ∀ j : ℕ, n≤collatzStep^[j] n) :
    ∃ j : ℕ, j≤14542 ∧ n+14542≤collatzStep^[t+j] n := by
  by_contra! h
  let f : Fin 14543 → Fin 14542 := fun i =>
    ⟨collatzStep^[t+i.val] n-n,by have hb := h i (by omega); omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have he := congrArg Fin.val hij
    change collatzStep^[t+i.val] n-n=collatzStep^[t+j.val] n-n at he
    have hb (x : Fin 14543) : n≤collatzStep^[t+x.val] n := hstay _
    have heq : collatzStep^[t+i.val] n=collatzStep^[t+j.val] n := by
      have := hb i
      have := hb j
      omega
    apply Fin.ext
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hg := collatz_non_descending_repeat_gap n (t+i.val) (t+j.val)
        hlarge hstay (by omega) heq
      omega
    · have hg := collatz_non_descending_repeat_gap n (t+j.val) (t+i.val)
        hlarge hstay (by omega) heq.symm
      omega
  have hc : Fintype.card (Fin 14543)≤Fintype.card (Fin 14542) := Fintype.card_le_of_injective f hinj
  simp at hc

theorem solution (n : ℕ) (hlarge : 2310000≤n)
    (hstay : ∀ j : ℕ, n≤collatzStep^[j] n) :
    (∀ a b : ℕ, a<b → collatzStep^[a] n=collatzStep^[b] n → 14543≤b-a) ∧
    (∀ t : ℕ, ∃ j : ℕ, j≤14542 ∧ n+14542≤collatzStep^[t+j] n) := by
  exact ⟨fun a b => collatz_non_descending_repeat_gap n a b hlarge hstay,
    fun t => collatz_non_descending_escapes_short_band n t hlarge hstay⟩
