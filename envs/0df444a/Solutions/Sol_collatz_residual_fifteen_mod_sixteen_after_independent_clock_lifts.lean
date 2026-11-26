-- Prove2me | solution 1 for collatz_residual_fifteen_mod_sixteen_after_independent_clock_lifts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:08:26.027074+00:00
-- url     : https://prove2.me/submissions/3975176d-ebe0-46ad-a857-0ebcc0c13df6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_syracuse_descent_residual_fifteen_mod16_mod4096
import Theorems.Thm_collatz_descent_of_syracuse_descent

private def traceProgression : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | t + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then traceProgression t (a / 2) (b / 2)
      else traceProgression t (3 * a) (3 * b + 1)
    else none

private theorem traceProgression_sound (t a b u v : ℕ)
    (h : traceProgression t a b = some (u, v)) (q : ℕ) :
    collatzStep^[t] (a * q + b) = u * q + v := by
  induction t generalizing a b with
  | zero =>
    simp [traceProgression] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ t ih =>
    simp only [traceProgression] at h
    split at h
    · rename_i ha
      have ha' : a = 2 * (a / 2) := by omega
      rw [Function.iterate_succ_apply]
      split at h
      · rename_i hb
        have hb' : b = 2 * (b / 2) := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) := by
          calc
            a * q + b = (2 * (a / 2)) * q + 2 * (b / 2) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        rw [hx]
        simpa [collatzStep] using ih _ _ h
      · rename_i hb
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) + 1 := by
          calc
            a * q + b = (2 * (a / 2)) * q + (2 * (b / 2) + 1) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        have hodd : ¬ Even (a * q + b) := by simp [hx]
        rw [collatzStep, if_neg hodd]
        convert ih _ _ h using 2
        ring
    · contradiction

private theorem ordinaryStepPositive (x : ℕ) (hx : 0<x) : 0 < collatzStep x := by
  unfold collatzStep
  split
  · rename_i he
    have hm := Nat.even_iff.mp he
    omega
  · omega

private theorem ordinaryIteratePositive (t x : ℕ) (hx : 0<x) :
    0 < collatzStep^[t] x := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ordinaryStepPositive _ ih

private theorem certifiedClassDescent (n m r t a b : ℕ)
    (hc : n%m=r) (ht : traceProgression t m r=some (a,b))
    (ha : a ≤ m) (hb : b < r) : ∃ j : ℕ, collatzStep^[j] n<n := by
  let q := n/m
  have hn : n=m*q+r := by
    rw [Nat.add_comm,←hc]
    exact (Nat.mod_add_div _ _).symm
  refine ⟨t,?_⟩
  rw [hn,traceProgression_sound t m r a b ht]
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q ha) hb

private theorem allFifteenClassDescent (n : ℕ) (hclass : n%16=15) :
    ∃ t : ℕ, collatzStep^[t] n<n := by
  by_cases h128_15 : n%128=15
  · exact certifiedClassDescent n 128 15 11 81 10 h128_15 (by decide) (by decide) (by decide)
  by_cases h256_79 : n%256=79
  · exact certifiedClassDescent n 256 79 13 243 76 h256_79 (by decide) (by decide) (by decide)
  by_cases h256_95 : n%256=95
  · exact certifiedClassDescent n 256 95 13 243 91 h256_95 (by decide) (by decide) (by decide)
  by_cases h256_175 : n%256=175
  · exact certifiedClassDescent n 256 175 13 243 167 h256_175 (by decide) (by decide) (by decide)
  have h256 : n%256≠79 ∧ n%256≠95 ∧ n%256≠175 := ⟨h256_79,h256_95,h256_175⟩
  by_cases h1024_287 : n%1024=287
  · exact certifiedClassDescent n 1024 287 16 729 205 h1024_287 (by decide) (by decide) (by decide)
  by_cases h1024_367 : n%1024=367
  · exact certifiedClassDescent n 1024 367 16 729 262 h1024_367 (by decide) (by decide) (by decide)
  by_cases h1024_575 : n%1024=575
  · exact certifiedClassDescent n 1024 575 16 729 410 h1024_575 (by decide) (by decide) (by decide)
  by_cases h1024_735 : n%1024=735
  · exact certifiedClassDescent n 1024 735 16 729 524 h1024_735 (by decide) (by decide) (by decide)
  by_cases h1024_815 : n%1024=815
  · exact certifiedClassDescent n 1024 815 16 729 581 h1024_815 (by decide) (by decide) (by decide)
  by_cases h1024_975 : n%1024=975
  · exact certifiedClassDescent n 1024 975 16 729 695 h1024_975 (by decide) (by decide) (by decide)
  have h1024 : n%1024≠287 ∧ n%1024≠367 ∧ n%1024≠575 ∧ n%1024≠735 ∧ n%1024≠815 ∧ n%1024≠975 := ⟨h1024_287,h1024_367,h1024_575,h1024_735,h1024_815,h1024_975⟩
  by_cases h4096_383 : n%4096=383
  · exact certifiedClassDescent n 4096 383 19 2187 205 h4096_383 (by decide) (by decide) (by decide)
  by_cases h4096_463 : n%4096=463
  · exact certifiedClassDescent n 4096 463 19 2187 248 h4096_463 (by decide) (by decide) (by decide)
  by_cases h4096_879 : n%4096=879
  · exact certifiedClassDescent n 4096 879 19 2187 470 h4096_879 (by decide) (by decide) (by decide)
  by_cases h4096_1087 : n%4096=1087
  · exact certifiedClassDescent n 4096 1087 19 2187 581 h4096_1087 (by decide) (by decide) (by decide)
  by_cases h4096_1231 : n%4096=1231
  · exact certifiedClassDescent n 4096 1231 19 2187 658 h4096_1231 (by decide) (by decide) (by decide)
  by_cases h4096_1647 : n%4096=1647
  · exact certifiedClassDescent n 4096 1647 19 2187 880 h4096_1647 (by decide) (by decide) (by decide)
  by_cases h4096_1823 : n%4096=1823
  · exact certifiedClassDescent n 4096 1823 19 2187 974 h4096_1823 (by decide) (by decide) (by decide)
  by_cases h4096_1855 : n%4096=1855
  · exact certifiedClassDescent n 4096 1855 19 2187 991 h4096_1855 (by decide) (by decide) (by decide)
  by_cases h4096_2031 : n%4096=2031
  · exact certifiedClassDescent n 4096 2031 19 2187 1085 h4096_2031 (by decide) (by decide) (by decide)
  by_cases h4096_2239 : n%4096=2239
  · exact certifiedClassDescent n 4096 2239 19 2187 1196 h4096_2239 (by decide) (by decide) (by decide)
  by_cases h4096_2351 : n%4096=2351
  · exact certifiedClassDescent n 4096 2351 19 2187 1256 h4096_2351 (by decide) (by decide) (by decide)
  by_cases h4096_2591 : n%4096=2591
  · exact certifiedClassDescent n 4096 2591 19 2187 1384 h4096_2591 (by decide) (by decide) (by decide)
  by_cases h4096_2975 : n%4096=2975
  · exact certifiedClassDescent n 4096 2975 19 2187 1589 h4096_2975 (by decide) (by decide) (by decide)
  by_cases h4096_3119 : n%4096=3119
  · exact certifiedClassDescent n 4096 3119 19 2187 1666 h4096_3119 (by decide) (by decide) (by decide)
  by_cases h4096_3295 : n%4096=3295
  · exact certifiedClassDescent n 4096 3295 19 2187 1760 h4096_3295 (by decide) (by decide) (by decide)
  by_cases h4096_4063 : n%4096=4063
  · exact certifiedClassDescent n 4096 4063 19 2187 2170 h4096_4063 (by decide) (by decide) (by decide)
  have h4096 : n%4096≠383 ∧ n%4096≠463 ∧ n%4096≠879 ∧ n%4096≠1087 ∧ n%4096≠1231 ∧ n%4096≠1647 ∧ n%4096≠1823 ∧ n%4096≠1855 ∧ n%4096≠2031 ∧ n%4096≠2239 ∧ n%4096≠2351 ∧ n%4096≠2591 ∧ n%4096≠2975 ∧ n%4096≠3119 ∧ n%4096≠3295 ∧ n%4096≠4063 := ⟨h4096_383,h4096_463,h4096_879,h4096_1087,h4096_1231,h4096_1647,h4096_1823,h4096_1855,h4096_2031,h4096_2239,h4096_2351,h4096_2591,h4096_2975,h4096_3119,h4096_3295,h4096_4063⟩
  have ho : ¬Even n := by rw [Nat.even_iff]; omega
  exact collatz_descent_of_syracuse_descent n ho
    (syracuse_descent_residual_fifteen_mod16_mod4096 n hclass h128_15 h256 h1024 h4096)

set_option linter.unusedVariables false in
theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170])
    (h19683 : n % 19683 ∉ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ))
    (hfirst : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let P := 3^L*q
      ¬ (P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s))))
    (hsecond : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let X := (3^L*q-1)/2
      let H := (X+1).factorization 2
      let Q := (X+1)/2^H
      let W := 3^H*Q
      ¬ ((L ≤ 4 ∧ 3 ≤ H ∧
        (W % 256 ∈ ([43] : List ℕ) ∨
        W % 512 ∈ ([199, 363] : List ℕ) ∨
        W % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
        W % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
        W % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
        W % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ))) ∨
      (L ≤ 7 ∧ 5 ≤ H ∧
        (W % 16384 ∈ ([303, 2731, 6371] : List ℕ) ∨
        W % 32768 ∈ ([12715, 18659, 20783, 23211] : List ℕ) ∨
        W % 65536 ∈ ([1131, 8419, 15019, 25259, 26851, 30339, 37291, 39215, 45359, 47275, 60263] : List ℕ))) ∨
      (L ≤ 12 ∧ 7 ≤ H ∧
        (W % 262144 ∈ ([4551, 43691, 198427, 208743] : List ℕ))) ∨
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(n))))
    (hexit : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let X := (3^L*q-1)/2
      let H := (X+1).factorization 2
      let Q := (X+1)/2^H
      let W := 3^H*Q
      ¬ (∃ s r : ℕ, 1 ≤ s ∧ r ≤ H ∧ 2^s ∣ W-1 ∧
        2^(s-1)%3^r=1 ∧ 2^r*(W+2^(s-1)-1) ≤ 3^r*2^(s-1)*n))
    (hmacro : ¬ (let runEnd : ℕ → ℕ := fun x =>
        let r := (x+1).factorization 2
        3^r*((x+1)/2^r)-1
      let jump : ℕ → ℕ := fun x =>
        let w := runEnd x
        w/2^(w.factorization 2)
      ∃ j s e : ℕ,
        let w := runEnd (jump^[j] n)
        let y := w/2^s
        let z := 2^e*y+1
        let r := z.factorization 3
        2^s ∣ w ∧ (y < n ∨ 2^r*(z/3^r)-1 < n)))
    (hordinary : ¬ (∃ t e : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let r := z.factorization 3
      2^r*(z/3^r)-1<n))
    (htwo : ¬ (∃ t e h d : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let x := 2^h*(z/3^h)-1
      let w := 2^d*x+1
      let r := w.factorization 3
      3^h ∣ z ∧ 2^r*(w/3^r)-1<n))
    (hsix : ¬ (∃ a : ℕ × ℕ, a ∈
      ([(69984, 14335),
       (629856, 146527),
       (5668704, 3995647),
       (51018336, 37378015),
       (153055008, 109181599),
       (1377495072, 840444415),
       (12397455648, 3901544575),
       (37192366944, 6197369695),
       (334731302496, 208689145279),
       (3012581722464, 2737770097471),
       (27113235502176, 1064113584991),
       (81339706506528, 74370268831615),
       (732057358558752, 472031056196863),
       (6588516227028768, 2749542838379647),
       (19765548681086304, 6653848750692991),
       (177889938129776736, 169170582350735935),
       (1601009443167990624, 307529423118340063)] : List (ℕ × ℕ)) ∧ n%a.1=a.2))
    (hsearch : ¬ ((n%9=7 ∧
      let next : ℕ → ℕ := fun v =>
        if 0<v ∧ v<6*n+2 then
          if v<n then v
          else if v%3=2 then (2*v-1)/3
          else if v%3=1 ∧ 2*v<6*n+2 then (4*v-1)/3
          else 0
        else 0
      let u := next^[6*n+1] ((32*n+1)/9)
      0<u ∧ u<n) ∨ n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229))
    (hrelay : ¬ (∃ s r : ℕ, 0<s ∧ 0<r ∧ 2^r*(16*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 16*4^s*(3*n+1)-10))
    (hvariable : ¬ (∃ s r a b : ℕ, 0<r ∧ 2≤a ∧ 2≤b ∧
      2^r*(2^(a+b)*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b)))
    (hfirstRunVisitor : ¬ (let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    let s := w.factorization 2
    ∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*(w/2^s)-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n))
    (hLateResidue : ¬ (∃ p : ℕ × ℕ, p∈([(1224440064, 524071407), (11019960576, 2338056687), (11019960576, 2957834991),
      (11019960576, 3862823151), (11019960576, 6016620015), (11019960576, 6497574639),
      (11019960576, 6918369519), (11019960576, 7647666159), (11019960576, 8278858479),
      (11019960576, 8544237807), (11019960576, 8578203375), (11019960576, 9083530735),
      (11019960576, 10717660911), (11019960576, 10768609263), (22039921152, 15112762095),
      (99179645184, 57926895), (99179645184, 236993263), (99179645184, 818377455),
      (99179645184, 2643882991), (99179645184, 3611896815), (99179645184, 4273203183),
      (99179645184, 4278013167), (99179645184, 5557880559), (99179645184, 5635018479),
      (99179645184, 5765693679)] : List (ℕ × ℕ)) ∧ n%p.1=p.2))
    (hsecondRunVisitor : ¬ (let runEnd : ℕ → ℕ := fun x =>
      let r := (x+1).factorization 2
      3^r*((x+1)/2^r)-1
    let jump : ℕ → ℕ := fun x =>
      let w := runEnd x
      w/2^(w.factorization 2)
    ∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let y := jump (jump n)
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*y-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n))
    (hBinaryLift : ¬ (∃ d m : ℕ, 0<d ∧ d<n ∧
      (let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let r := n%2^m
    d≤r ∧ S^[m] r=S^[m] (r-d) ∧ S^[m] (2^m+r)=S^[m] (2^m+r-d))))
    (hIndependentLift : ¬ (∃ a b u v s : ℕ, 0<u ∧ 0<v ∧ a≠b ∧
      (let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let P := 2^a*u
    let Q := 2^b*v
    let r := n%P
    0<s ∧ s<r ∧ Q≤P ∧ S^[a] r=S^[b] s ∧ S^[a] (P+r)=S^[b] (Q+s)))) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  obtain ⟨t,ht⟩ := allFifteenClassDescent n hclass
  exact ⟨collatzStep^[t] n,t,0,ordinaryIteratePositive t n (by omega),ht,rfl⟩
