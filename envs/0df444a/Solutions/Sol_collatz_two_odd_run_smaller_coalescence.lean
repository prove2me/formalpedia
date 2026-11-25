-- Prove2me | solution 1 for collatz_two_odd_run_smaller_coalescence
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:28:52.016345+00:00
-- url     : https://prove2.me/submissions/16b14244-e261-4324-be7e-eb5588672fac

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

/- Progression verifier adapted from immiq's Prove2Me submission
   1843fe6d-cde2-4133-a4d5-fcfa32356e48 (Apache-2.0).
   Track the image of an entire arithmetic progression. An even coefficient
   makes parity independent of the parameter. -/
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

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

private theorem trailingOnesRun (L q : ℕ) (hq : 0 < q) :
    collatzStep^[2*L] (2^L*q-1) = 3^L*q-1 := by
  induction L generalizing q with
  | zero => simp
  | succ L ih =>
    have hp : 0 < 2^L*q := Nat.mul_pos (Nat.two_pow_pos _) hq
    have hh : 2^(L+1)*q = 2*(2^L*q) := by rw [pow_succ]; ring
    have odd : (2^(L+1)*q-1) % 2 = 1 := by rw [hh]; omega
    have second : (3*(2^(L+1)*q-1)+1) % 2 = 0 := by rw [hh]; omega
    have hx : 2^L*(3*q) = 3*(2^L*q) := by ring
    have firstPair : collatzStep^[2] (2^(L+1)*q-1) = 2^L*(3*q)-1 := by
      rw [Function.iterate_succ_apply, Function.iterate_one, stepOdd _ odd, stepEven _ second,
        hh, hx]
      omega
    have hpow : 3^L*(3*q) = 3^(L+1)*q := by rw [pow_succ]; ring
    rw [show 2*(L+1) = 2*L+2 by omega, Function.iterate_add_apply, firstPair,
      ih (3*q) (by omega), hpow]

private theorem powerHalvings (s k : ℕ) : collatzStep^[s] (2^s*k) = k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hf : 2^(s+1)*k = 2*(2^s*k) := by rw [pow_succ]; ring
    rw [Function.iterate_succ_apply, hf, stepEven _ (by omega)]
    simpa using ih

/-- Pull an anchor merger back to the original start when the size margin pays
for shortening the second odd run. All indices count ordinary Collatz steps. -/
private theorem collatz_lift_anchor_merger_with_power_margin
    (L q r u d : ℕ) (hq : q%2 = 1) (hu : u%2 = 1) (hd : 0 < d)
    (hk : 2 ≤ 2^r*u)
    (hshift : 2^d*(3^r*u+1) = 3^L*q+1)
    (hmargin : 2^r*3^L ≤ 3^r*2^(L+d))
    (hmerge : ∃ a b : ℕ, collatzStep^[a] ((3^L*q-1)/2) =
      collatzStep^[b] ((3^r*u-1)/2)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  let X := 3^L*q
  let Y := 3^r*u
  change 2^d*(Y+1) = X+1 at hshift
  have hd2 : 2 ≤ 2^d := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ d by omega)
  have hstrict : 2^d*Y < X := by
    rw [Nat.mul_add, mul_one] at hshift
    omega
  have hmid : 2^d*(3^r*(2^r*u)) < 2^d*(3^r*(2^L*q)) := calc
    _ = 2^r*(2^d*Y) := by dsimp [Y]; ring
    _ < 2^r*X := (Nat.mul_lt_mul_left (Nat.two_pow_pos r)).mpr hstrict
    _ = (2^r*3^L)*q := by dsimp [X]; ring
    _ ≤ (3^r*2^(L+d))*q := Nat.mul_le_mul_right q hmargin
    _ = _ := by rw [pow_add]; ring
  have hpairs : 2^r*u < 2^L*q :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < (3:ℕ)))).mp
      ((Nat.mul_lt_mul_left (Nat.two_pow_pos d)).mp hmid)
  have anchor (J v : ℕ) (hv : v%2 = 1) :
      collatzStep^[1+2*J] (2^J*v-1) = (3^J*v-1)/2 := by
    have hm : 3^J*v % 2 = 1 := by
      rw [Nat.mul_mod, Nat.pow_mod, hv]
      simp
    rw [Function.iterate_add_apply, trailingOnesRun J v (by omega),
      Function.iterate_one, stepEven _ (by omega)]
  obtain ⟨a,b,hm⟩ := hmerge
  refine ⟨2^r*u-1, a+(1+2*L), b+(1+2*r), by omega, by omega, ?_⟩
  rw [Function.iterate_add_apply _ a (1+2*L),
    Function.iterate_add_apply _ b (1+2*r), anchor L q hq, anchor r u hu]
  exact hm


private theorem exactSuffixPair
    (H Q d M residue s a b coefficient constant inverse : ℕ)
    (hH : d ≤ H) (hQ : 0 < Q) (hresidue : (3^H*Q) % M = residue)
    (hrow : (3^d*s) % M = residue) (hinv : (inverse*3^d) % M = 1)
    (hs : s < M) (hspos : 0 < s)
    (ha : traceProgression a (3^d*M) (3^d*s-1) = some (coefficient,constant))
    (hb : traceProgression b M (s-1) = some (coefficient,constant)) :
    ∃ j k : ℕ, collatzStep^[j] (2^H*Q-1) =
      collatzStep^[k] (2^(H-d)*Q-1) := by
  let A := 3^(H-d)*Q
  let G := (3:ℕ)^d
  have hP : 3^H*Q = G*A := calc
    _ = 3^((H-d)+d)*Q := by rw [Nat.sub_add_cancel hH]
    _ = _ := by rw [pow_add]; dsimp [A,G]; ring
  change (G*s)%M = residue at hrow
  change (inverse*G)%M = 1 at hinv
  have hAA : (G*A) % M = (G*s) % M := by rw [← hP, hresidue, hrow]
  have cancel (x : ℕ) : ((inverse*G)*x) % M = x % M := by
    rw [Nat.mul_mod, hinv, one_mul, Nat.mod_mod]
  have hA : A % M = s := calc
    A % M = ((inverse*G)*A) % M := (cancel A).symm
    _ = ((inverse*G)*s) % M := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_mod inverse (G*A),
        Nat.mul_mod inverse (G*s), hAA]
    _ = s := by rw [cancel, Nat.mod_eq_of_lt hs]
  let j := A/M
  have hquot : A = M*j+s := by
    simpa only [j, hA] using (Nat.mod_add_div A M).symm.trans (Nat.add_comm _ _)
  have hxlo : A-1 = M*j+(s-1) := by rw [hquot]; omega
  have hxhi : G*A-1 = (G*M)*j+(G*s-1) := by
    have heq : G*A = (G*M)*j+G*s := by rw [hquot]; ring
    have hp : 0 < G*s := Nat.mul_pos (Nat.pow_pos (by decide : 0 < (3:ℕ))) hspos
    omega
  refine ⟨a+2*H, b+2*(H-d), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, trailingOnesRun H Q hQ,
    trailingOnesRun (H-d) Q hQ, hP, hxhi]
  change collatzStep^[a] ((G*M)*j+(G*s-1)) = collatzStep^[b] (A-1)
  rw [hxlo, traceProgression_sound _ _ _ _ _ ha, traceProgression_sound _ _ _ _ _ hb]

private theorem boundedMargin (L upper r d : ℕ) (hL : L ≤ upper)
    (hbound : 2^r*3^upper ≤ 3^r*2^(upper+d)) :
    2^r*3^L ≤ 3^r*2^(L+d) := by
  let delta := upper-L
  have hsum : L+delta = upper := by dsimp [delta]; omega
  have hleft : 3^delta*(2^r*3^L) = 2^r*3^upper := calc
    _ = 2^r*3^(L+delta) := by rw [pow_add]; ring
    _ = _ := by rw [hsum]
  have hright : 2^delta*(3^r*2^(L+d)) = 3^r*2^(upper+d) := calc
    _ = 3^r*2^((L+delta)+d) := by
      rw [show L+delta+d = (L+d)+delta by omega, pow_add]
      ring
    _ = _ := by rw [hsum]
  by_contra! contra
  have hcmp : (2:ℕ)^delta ≤ 3^delta := Nat.pow_le_pow_left (by decide) delta
  have hlt := calc
    3^r*2^(upper+d) = 2^delta*(3^r*2^(L+d)) := hright.symm
    _ < 2^delta*(2^r*3^L) := (Nat.mul_lt_mul_left (Nat.two_pow_pos delta)).mpr contra
    _ ≤ 3^delta*(2^r*3^L) := Nat.mul_le_mul_right _ hcmp
    _ = 2^r*3^upper := hleft
  exact (Nat.not_lt_of_ge hbound) hlt

private theorem threePowerOdd (r u : ℕ) : (3^r*u) % 2 = u % 2 := by
  rw [Nat.mul_mod, Nat.pow_mod, show (3:ℕ)%2 = 1 by decide, one_pow]
  simp

private theorem liftShortening
    (L q H Q r d : ℕ) (hQ : 0 < Q) (hr : 0 < r) (hrL : r ≤ L)
    (hd : 0 < d) (hH : d+1 ≤ H) (h2mod : (2^d) % (3^r) = 1)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q)
    (hmargin : 2^r*3^L ≤ 3^r*2^(L+d))
    (hmerge : ∃ a b : ℕ, collatzStep^[a] (2^H*Q-1) =
      collatzStep^[b] (2^(H-d)*Q-1)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  let P := 3^L*q
  let A := 2^(H-d)*Q
  let Y := 2*A-1
  have hA : 0 < A := Nat.mul_pos (Nat.two_pow_pos _) hQ
  have hY : 0 < Y := by dsimp [Y]; omega
  have hadd : Y+1 = 2*A := by dsimp [Y]; omega
  have hpow : 2^d*(Y+1) = P+1 := calc
    _ = 2^(d+(H-d)+1)*Q := by rw [hadd, pow_succ, pow_add]; dsimp [A]; ring
    _ = 2^(H+1)*Q := by rw [show d+(H-d) = H by omega]
    _ = _ := hbetween.symm
  have hpdvd : (3:ℕ)^r ∣ P := by
    refine ⟨3^(L-r)*q, ?_⟩
    dsimp [P]
    conv_lhs => rw [show L = r+(L-r) by omega, pow_add]
    ring
  have hpmod : P%(3^r) = 0 := Nat.dvd_iff_mod_eq_zero.mp hpdvd
  have hY1 : (Y+1)%(3^r) = (0+1)%(3^r) := calc
    _ = (2^d*(Y+1))%(3^r) := by rw [Nat.mul_mod, h2mod, one_mul, Nat.mod_mod]
    _ = (P+1)%(3^r) := by rw [hpow]
    _ = _ := by rw [Nat.add_mod P 1, hpmod, zero_add, Nat.mod_mod, zero_add]
  have hYe : Y ≡ 0 [MOD 3^r] := Nat.ModEq.add_right_cancel' 1 hY1
  have hYdvd : (3:ℕ)^r ∣ Y := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    simpa [Nat.ModEq] using hYe
  obtain ⟨u,hu⟩ := hYdvd
  have hqOdd : q%2 = 1 := by
    have hb : (2^(H+1)*Q)%2 = 0 := by rw [pow_succ]; simp [Nat.mul_assoc, Nat.mul_left_comm]
    have hp : P%2 = q%2 := threePowerOdd _ _
    omega
  have huOdd : u%2 = 1 := by
    have hy2 : Y%2 = 1 := by dsimp [Y]; omega
    rw [hu, threePowerOdd] at hy2
    exact hy2
  have huPos : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero,mul_zero] at hu
    omega
  have hk : 2 ≤ 2^r*u := calc
    2 ≤ 2^r := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 1 ≤ r)
    _ ≤ _ := Nat.le_mul_of_pos_right _ huPos
  have hnx : (P-1)/2 = 2^H*Q-1 := by
    have hp : P+1=2*(2^H*Q) := by rw [hbetween,pow_succ]; ring
    omega
  have hny : (3^r*u-1)/2 = A-1 := by
    rw [← hu]
    dsimp [Y]
    omega
  apply collatz_lift_anchor_merger_with_power_margin L q r u d hqOdd huOdd hd hk
    (by rw [← hu]; exact hpow) hmargin
  change ∃ a b : ℕ, collatzStep^[a] ((P-1)/2) = collatzStep^[b] ((3^r*u-1)/2)
  rw [hnx,hny]
  exact hmerge

private theorem secondRunExit (L q H Q : ℕ) (hL : 4 ≤ L) (hq : 0 < q) (hQ : 0 < Q)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q)
    (h : ∃ s : ℕ, 2^s ∣ 3^H*Q-1 ∧ 3^H*Q ≤ 2^s*(2^L*q-1)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  obtain ⟨s, ⟨k,hk⟩, hbudget⟩ := h
  let P := 3^L*q
  have hnx : P+1=2*(2^H*Q) := by rw [hbetween,pow_succ]; ring
  have hfirst : collatzStep^[1+2*L] (2^L*q-1) = 2^H*Q-1 := by
    rw [Function.iterate_add_apply, trailingOnesRun L q hq, Function.iterate_one]
    change collatzStep (P-1) = 2^H*Q-1
    rw [stepEven _ (by omega)]
    omega
  have hgt : 1 < P := by
    have h3 : 3 ≤ 3^L := Nat.pow_le_pow_right (n := 3) (by decide) (by omega : 1 ≤ L)
    have hp : 3^L ≤ P := Nat.le_mul_of_pos_right _ hq
    omega
  have hW : 2^H*Q ≤ 3^H*Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
  have hkPos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,mul_zero] at hk
    omega
  have hlt : 2^s*k < 2^s*(2^L*q-1) := by omega
  refine ⟨k, s+(2*H+(1+2*L)), 0, hkPos, (Nat.mul_lt_mul_left (Nat.two_pow_pos s)).mp hlt, ?_⟩
  rw [Function.iterate_add_apply _ s (2*H+(1+2*L)),
    Function.iterate_add_apply _ (2*H) (1+2*L), hfirst, trailingOnesRun H Q hQ, hk,
    powerHalvings]
  rfl

theorem solution (L q H Q : ℕ) (hL : 4 ≤ L) (hq : 0 < q) (hQ : 0 < Q)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q)
    (hcase : let W := 3^H*Q
      (L ≤ 4 ∧ 3 ≤ H ∧
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
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(2^L*q-1))) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  rcases hcase with htwo | hfour | hsix | hexit
  · obtain ⟨hupper,hH,hrs⟩ := htwo
    apply liftShortening L q H Q 1 2 hQ (by decide) (by omega) (by decide)
      hH (by decide) hbetween (boundedMargin L 4 1 2 hupper (by decide))
    rcases hrs with h256 | h512 | h1024 | h2048 | h4096 | h8192
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h256
      exact exactSuffixPair H Q 2 256 43 147 10 12 81 47 57 (by omega) hQ h256
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h512
      rcases h512 with hr199 | hr363
      · exact exactSuffixPair H Q 2 512 199 79 12 14 243 38 57 (by omega) hQ hr199
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 512 363 211 12 14 243 101 57 (by omega) hQ hr363
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1024
      rcases h1024 with hr235 | hr395 | hr583
      · exact exactSuffixPair H Q 2 1024 235 595 14 16 729 425 569 (by omega) hQ hr235
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 1024 395 499 13 15 243 119 569 (by omega) hQ hr395
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 1024 583 975 14 16 729 695 569 (by omega) hQ hr583
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2048
      rcases h2048 with hr263 | hr795 | hr839 | hr1163 | hr1175 | hr1515
      · exact exactSuffixPair H Q 2 2048 263 1167 15 17 729 416 1593 (by omega) hQ hr263
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 2048 795 771 14 16 243 92 1593 (by omega) hQ hr795
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 2048 839 1231 16 18 2187 1316 1593 (by omega) hQ hr839
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 2048 1163 1267 15 17 729 452 1593 (by omega) hQ hr1163
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 2048 1175 1951 15 17 729 695 1593 (by omega) hQ hr1175
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 2048 1515 851 16 18 2187 911 1593 (by omega) hQ hr1515
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4096
      rcases h4096 with hr523 | hr631 | hr775 | hr1003 | hr1675 | hr1687 | hr1895 | hr2331 | hr2351 | hr2375
      · exact exactSuffixPair H Q 2 4096 523 3699 16 18 729 659 3641 (by omega) hQ hr523
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 631 3711 17 19 2187 1982 3641 (by omega) hQ hr631
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 775 3727 17 19 2187 1991 3641 (by omega) hQ hr775
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 1003 2387 18 20 6561 3827 3641 (by omega) hQ hr1003
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 1675 3827 17 19 2187 2045 3641 (by omega) hQ hr1675
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 1687 2463 17 19 2187 1316 3641 (by omega) hQ hr1687
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 1895 2031 16 18 729 362 3641 (by omega) hQ hr1895
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 2331 259 16 18 729 47 3641 (by omega) hQ hr2331
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 2351 3447 16 18 729 614 3641 (by omega) hQ hr2351
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 4096 2375 719 18 20 6561 1154 3641 (by omega) hQ hr2375
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h8192
      rcases h8192 with hr1051 | hr1263 | hr1547 | hr3079 | hr3355 | hr3375 | hr3399 | hr3787 | hr3847 | hr3991 | hr4699 | hr4747 | hr4759 | hr5207 | hr6123 | hr7015 | hr7799
      · exact exactSuffixPair H Q 2 8192 1051 1027 17 19 729 92 3641 (by omega) hQ hr1051
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 1263 2871 18 20 2187 767 3641 (by omega) hQ hr1263
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 1547 4723 18 20 2187 1262 3641 (by omega) hQ hr1547
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3079 3983 18 20 2187 1064 3641 (by omega) hQ hr3079
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3355 1283 18 20 2187 344 3641 (by omega) hQ hr3355
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3375 375 18 20 2187 101 3641 (by omega) hQ hr3375
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3399 5839 20 22 19683 14033 3641 (by omega) hQ hr3399
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3787 1331 17 19 729 119 3641 (by omega) hQ hr3787
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3847 6799 19 21 6561 5447 3641 (by omega) hQ hr3847
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 3991 6815 18 20 2187 1820 3641 (by omega) hQ hr3991
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 4699 4163 17 19 729 371 3641 (by omega) hQ hr4699
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 4747 6899 19 21 6561 5528 3641 (by omega) hQ hr4747
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 4759 1439 19 21 6561 1154 3641 (by omega) hQ hr4759
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 5207 2399 18 20 2187 641 3641 (by omega) hQ hr5207
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 6123 3411 20 22 19683 8201 3641 (by omega) hQ hr6123
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 7015 7151 18 20 2187 1910 3641 (by omega) hQ hr7015
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 2 8192 7799 2687 19 21 6561 2153 3641 (by omega) hQ hr7799
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨hupper,hH,hrs⟩ := hfour
    apply liftShortening L q H Q 1 4 hQ (by decide) (by omega) (by decide)
      hH (by decide) hbetween (boundedMargin L 7 1 4 hupper (by decide))
    rcases hrs with h16384 | h32768 | h65536
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h16384
      rcases h16384 with hr303 | hr2731 | hr6371
      · exact exactSuffixPair H Q 4 16384 303 2431 18 22 6561 974 2225 (by omega) hQ hr303
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 16384 2731 14395 16 20 729 641 2225 (by omega) hQ hr2731
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 16384 6371 3315 17 21 2187 443 2225 (by omega) hQ hr6371
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h32768
      rcases h32768 with hr12715 | hr18659 | hr20783 | hr23211
      · exact exactSuffixPair H Q 4 32768 12715 28475 18 22 2187 1901 18609 (by omega) hQ hr12715
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 32768 18659 15603 19 23 6561 3125 18609 (by omega) hQ hr18659
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 32768 20783 22911 20 24 19683 13763 18609 (by omega) hQ hr20783
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 32768 23211 18491 18 22 2187 1235 18609 (by omega) hQ hr23211
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h65536
      rcases h65536 with hr1131 | hr8419 | hr15019 | hr25259 | hr26851 | hr30339 | hr37291 | hr39215 | hr45359 | hr47275 | hr60263
      · exact exactSuffixPair H Q 4 65536 1131 9723 20 24 6561 974 18609 (by omega) hQ hr1131
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 8419 38131 20 24 6561 3818 18609 (by omega) hQ hr8419
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 15019 43067 20 24 6561 4313 18609 (by omega) hQ hr15019
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 25259 20539 19 23 2187 686 18609 (by omega) hQ hr25259
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 26851 23795 21 25 19683 7148 18609 (by omega) hQ hr26851
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 30339 51347 20 24 6561 5141 18609 (by omega) hQ hr30339
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 37291 53051 20 24 6561 5312 18609 (by omega) hQ hr37291
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 39215 8575 21 25 19683 2576 18609 (by omega) hQ hr39215
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 45359 47487 22 26 59049 42788 18609 (by omega) hQ hr45359
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 47275 50747 19 23 2187 1694 18609 (by omega) hQ hr47275
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact exactSuffixPair H Q 4 65536 60263 47671 21 25 19683 14318 18609 (by omega) hQ hr60263
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨hupper,hH,hrs⟩ := hsix
    apply liftShortening L q H Q 2 6 hQ (by decide) (by omega) (by decide)
      hH (by decide) hbetween (boundedMargin L 12 2 6 hupper (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrs
    rcases hrs with hr4551 | hr43691 | hr198427 | hr208743
    · exact exactSuffixPair H Q 6 262144 4551 169375 22 28 59049 38153 154985 (by omega) hQ hr4551
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exactSuffixPair H Q 6 262144 43691 7971 20 26 6561 200 154985 (by omega) hQ hr43691
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exactSuffixPair H Q 6 262144 198427 47379 22 28 59049 10673 154985 (by omega) hQ hr198427
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exactSuffixPair H Q 6 262144 208743 56383 22 28 59049 12701 154985 (by omega) hQ hr208743
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondRunExit L q H Q hL hq hQ hbetween hexit
