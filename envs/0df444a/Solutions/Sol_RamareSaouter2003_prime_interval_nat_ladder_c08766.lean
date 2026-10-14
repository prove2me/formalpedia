-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_c08766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:59:34.154918+00:00
-- url     : https://prove2.me/submissions/f210cef5-fa86-4e7c-bf02-cbd38a03e368

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith

/-! Ramare-Saouter finite range, ladder chunk 8766: every natural n with 99876372021712761067 < n <= 10 ^ (20 : Nat) has a prime p with
n * (1 - 1/28314000) < p < n. A ladder of 35523 primes q_0 < q_1 < ..., each step
q_{i+1} <= q_i + (q_i - 1) / 28313999, every q_i certified by Pocklington's criterion with a known prime
factor (or two) of q_i - 1, checked by the kernel (`decide +kernel`) through the frame `RAFrame`. -/

set_option autoImplicit false

namespace RAFrame

/-! ## Modular powering

`pw p a e n acc` is left-to-right base-256 powering over the digits `n - 1, ..., 0` of `e`; each
window is one GMP `pow`/`mul`/`mod` step in the kernel. `pw5` is the same with five windows written
out (no recursion, exponents below `2 ^ 40`); `pw5 p a e = pw p a e 5 1` holds by `rfl`. -/

def pw (p a e : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc => pw p a e i (Nat.mod (Nat.mul (Nat.pow acc 256)
      (Nat.pow a (Nat.land (Nat.shiftRight e (Nat.mul 8 i)) 255))) p)

def pw5 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul
    (Nat.pow (Nat.mod (Nat.mul (Nat.pow 1 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 32) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 24) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 16) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 8) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 0) 255))) p

theorem pw5_eq (p a e : ℕ) : pw5 p a e = pw p a e 5 1 := rfl

theorem digit_eq (e i : ℕ) :
    Nat.land (Nat.shiftRight e (Nat.mul 8 i)) 255 = e / 256 ^ i % 256 := by
  have h1 : Nat.shiftRight e (Nat.mul 8 i) = e / 256 ^ i := by
    have := Nat.shiftRight_eq_div_pow e (8 * i)
    rw [pow_mul] at this
    exact this
  rw [h1]
  exact Nat.and_two_pow_sub_one_eq_mod (e / 256 ^ i) 8

theorem pw_spec (p a e : ℕ) :
    ∀ n acc, pw p a e n acc ≡ acc ^ (256 ^ n) * a ^ (e % 256 ^ n) [MOD p] := by
  intro n
  induction n with
  | zero =>
    intro acc
    show acc ≡ acc ^ (256 ^ 0) * a ^ (e % 256 ^ 0) [MOD p]
    rw [pow_zero, pow_one, Nat.mod_one, pow_zero, mul_one]
  | succ n ih =>
    intro acc
    have hd := digit_eq e n
    have h := ih ((acc ^ 256 * a ^ (e / 256 ^ n % 256)) % p)
    show pw p a e n (Nat.mod (Nat.mul (Nat.pow acc 256)
      (Nat.pow a (Nat.land (Nat.shiftRight e (Nat.mul 8 n)) 255))) p) ≡ _ [MOD p]
    rw [hd]
    refine h.trans ?_
    have h2 : (acc ^ 256 * a ^ (e / 256 ^ n % 256)) % p ≡ acc ^ 256 * a ^ (e / 256 ^ n % 256) [MOD p] :=
      Nat.mod_modEq _ _
    refine (Nat.ModEq.mul_right _ (Nat.ModEq.pow _ h2)).trans ?_
    rw [Nat.mod_pow_succ]
    have e1 : (acc ^ 256 * a ^ (e / 256 ^ n % 256)) ^ 256 ^ n * a ^ (e % 256 ^ n) =
        acc ^ 256 ^ (n + 1) * a ^ (e % 256 ^ n + 256 ^ n * (e / 256 ^ n % 256)) := by
      ring
    exact congrArg (· % p) e1

theorem pw_pow (p a e n : ℕ) (he : e < 256 ^ n) : pw p a e n 1 ≡ a ^ e [MOD p] := by
  have h := pw_spec p a e n 1
  rw [one_pow, one_mul, Nat.mod_eq_of_lt he] at h
  exact h

theorem e40 : (256 : ℕ) ^ 5 = 1099511627776 := by norm_num

theorem pw5_pow (p a e : ℕ) (he : e < 1099511627776) : pw5 p a e ≡ a ^ e [MOD p] := by
  rw [pw5_eq]
  exact pw_pow p a e 5 (by rw [e40]; exact he)

/-! ## Pocklington's criterion with one large prime factor

If `N = R * L + 1` with `0 < R`, `L` prime, `N < (L + 1) ^ 2`, `y ^ L ≡ 1 (mod N)` and
`gcd(y - 1, N) = 1`, then `N` is prime: `y` has order exactly `L` modulo every prime factor `p` of
`N`, so `L ∣ p - 1`, `p > L` and `p ^ 2 > N`. -/

theorem pockY (N L R y : ℕ) (hR0 : 0 < R) (hR : R * L + 1 = N) (hlt : N < (L + 1) * (L + 1))
    (hL : L.Prime) (h1 : y ^ L ≡ 1 [MOD N]) (hc : Nat.Coprime (y + N - 1) N) : N.Prime := by
  have hL0 : 0 < L := hL.pos
  have hN1 : N ≠ 1 := by
    have : 0 < R * L := Nat.mul_pos hR0 hL0
    omega
  have hpp : N.minFac.Prime := Nat.minFac_prime hN1
  set p := N.minFac with hp
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact L.Prime := ⟨hL⟩
  have hpN : p ∣ N := Nat.minFac_dvd N
  have hyL : ((y : ℕ) : ZMod p) ^ L = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (h1.of_dvd hpN)
    push_cast at this
    exact this
  have hN0 : ((N : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpN
  have hy1 : ((y : ℕ) : ZMod p) ≠ 1 := by
    intro hb1
    have hle : 1 ≤ y + N := by omega
    have hzero : ((y + N - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hle]
      push_cast
      rw [hb1, hN0]
      ring
    have hpz : p ∣ y + N - 1 := (ZMod.natCast_eq_zero_iff _ _).1 hzero
    have hg := Nat.dvd_gcd hpz hpN
    rw [Nat.Coprime] at hc
    rw [hc] at hg
    exact hpp.one_lt.ne' (Nat.dvd_one.1 hg)
  have hord : orderOf ((y : ℕ) : ZMod p) = L := orderOf_eq_prime hyL hy1
  have hb0 : ((y : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hL0.ne'] at hyL
    exact zero_ne_one hyL
  have hdvd := ZMod.orderOf_dvd_card_sub_one hb0
  rw [hord] at hdvd
  have hp2 := hpp.two_le
  have hle : L ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  rw [← hp, pow_two] at hsq
  have : (L + 1) * (L + 1) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- three windows written out, for exponents below `2 ^ 24` -/
def pw3 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow 1 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 16) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 8) 255))) p) 256)
    (Nat.pow a (Nat.land (Nat.shiftRight e 0) 255))) p

theorem pw3_eq (p a e : ℕ) : pw3 p a e = pw p a e 3 1 := rfl

theorem e24 : (256 : ℕ) ^ 3 = 16777216 := by norm_num

theorem pw3_pow (p a e : ℕ) (he : e < 16777216) : pw3 p a e ≡ a ^ e [MOD p] := by
  rw [pw3_eq]
  exact pw_pow p a e 3 (by rw [e24]; exact he)

/-- the exponent bound of the powering selected by the size flag `s` -/
def ebound (s : ℕ) : ℕ := cond (Nat.beq s 1) 16777216 1099511627776

/-- `pw3` when the size flag `s` is `1`, else `pw5` -/
def pwk (s p a e : ℕ) : ℕ := cond (Nat.beq s 1) (pw3 p a e) (pw5 p a e)

theorem pwk_pow (s p a e : ℕ) (he : e < ebound s) : pwk s p a e ≡ a ^ e [MOD p] := by
  unfold pwk
  unfold ebound at he
  cases h : Nat.beq s 1
  · simp only [h, cond_false] at he ⊢
    exact pw5_pow p a e he
  · simp only [h, cond_true] at he ⊢
    exact pw3_pow p a e he

/-! ## Small primes: one gcd against the pool `PS`

`PS` is the product of the primes up to `4095`, as a literal. Nothing assumes what it is: `PS_ok`
checks in the kernel that every `i ∈ [2, 4095]` shares a factor with it. A number in
`[2, 16777216)` (`16777216 = 4096 ^ 2`) coprime to `PS` is then prime. -/

def PS : ℕ := 0x4fe43c99ab1d4b82fb62181608cdf254da35e2509ca1ed2c61a2bc632b4ab01e7665bdc31494e92728925dd7211e8f94b33cf972e2da39b982cb3198b48b74f444d48c40a4286b87bea0b342dd5b00cfd3fe713196fe1a8ef91bfdb256567e83d0f5e4ef8f6f9ff93a21acff3cb617353bc083f1ab635e8507d26ee4308e43ea5d24dde0b1c0b54c1ae384925f2bc1b4283dd5a1d6818e43ed2055fb92d7615f7aeeeb20453336aede273f9dbc43147355bed9561b3167d47f61365a5992721e1c3cd5e6b1b79446b05bc870771d736d4107df5b51059b9a3bff8319130832b54f6820037de9ea7b9cf653b6d1c0d9a37e82d299f2b2116364710c914889f6c5c434731116567cef6d762085c1ce7e7f208db9f843b93d4478594a76af1793d223c27d0702cd452d627568648bad61b1ef7ec587d8ee97c3ad83eef04dd264c0ea1dad1adea22ae802a68734da7e4a1312de6e133630b46620919769a561060cc0caedfd396a9ade2550c1603d29840d68d64c2926fe0d7d245f1819f8ec09ed98e718eb0c68415bd6dbcceb2ae3a354611db9601f72512100a679c9baadc7e2ef50684dae00f67df611174a37f0e0d4ab9828a78c8e5d7a07fd94fd92813231964f0475240b9a774bf08d679d0ff0f27ba0923366a8e3d56f04134f2f87b6acb0e79f4806136de2f7443a0a3d2f3a4716ec861f62dcfc63f58a181987d26ec1c05015a9223b822688cd18e8934197b55f94bd3fbbf956d93c74cb54193fa4235492be0371bac7c60c03b2d3ab16fac739a8b664739ac4334684779568f7ba8358664e5012ef9447d20db63182edebe75ec48aa62444146a198b25836d74d954225debb8bde3fd1fc702db92d856c497cf39a316cdb72d61f205a8eeffbbf4e1c08e4fdc500a6931ff93603bdb5302749b6faa6674a337c963c027a1af07146ea2a7db8fb555d5fc9a6c63def4697757c11e623c79733d1a9e1ed585af2fe3667580230c2bfdb9bb81938dbf0a7cbf93ef619c08baa76

/-- `allg P a n d`: every `i ∈ (a, a + n]` has `gcd i P ≠ 1` (binary split; `d` is fuel) -/
def allg (P a n : ℕ) : ℕ → Bool
  | 0 => false
  | d + 1 => cond (Nat.ble n 1) (cond (Nat.beq n 0) true (!(Nat.beq (Nat.gcd (a + 1) P) 1)))
      (allg P a (n / 2) d && allg P (a + n / 2) (n - n / 2) d)

theorem allg_sound : ∀ (d P a n : ℕ), allg P a n d = true →
    ∀ i, a < i → i ≤ a + n → Nat.gcd i P ≠ 1 := by
  intro d
  induction d with
  | zero => intro P a n h; simp [allg] at h
  | succ d ih =>
    intro P a n h i h1 h2
    simp only [allg] at h
    cases hb : Nat.ble n 1
    · rw [hb, cond_false, Bool.and_eq_true] at h
      by_cases hi : i ≤ a + n / 2
      · exact ih P a (n / 2) h.1 i h1 hi
      · exact ih P (a + n / 2) (n - n / 2) h.2 i (by omega) (by omega)
    · have hn := Nat.le_of_ble_eq_true hb
      rw [hb, cond_true] at h
      cases hz : Nat.beq n 0
      · rw [hz, cond_false] at h
        have hn0 : n ≠ 0 := by
          intro h0
          rw [h0] at hz
          exact absurd hz (by decide)
        have hi : i = a + 1 := by omega
        rw [hi]
        intro hg
        rw [hg] at h
        exact absurd h (by decide)
      · have := Nat.eq_of_beq_eq_true hz
        omega

/-- every `i ∈ [2, 4095]` shares a factor with `PS` -/
theorem PS_ok : allg PS 1 4094 16 = true := by decide +kernel

/-- a number in `[2, 16777216)` coprime to `PS` is prime -/
theorem prime_of_coprime_PS (q : ℕ) (h2 : 2 ≤ q) (hq : q < 16777216)
    (hc : Nat.gcd q PS = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hk : q.minFac ≤ 4095 := by
    by_contra hc'
    have h1 : 4096 ≤ q.minFac := by omega
    have h3 := le_trans (Nat.mul_le_mul h1 h1) hsq'
    omega
  have hm2 := hmp.two_le
  have hg := allg_sound 16 PS 1 4094 PS_ok q.minFac (by omega) (by omega)
  have hdF : q.minFac ∣ PS := by
    rcases Nat.coprime_or_dvd_of_prime hmp PS with h | h
    · exact absurd h hg
    · exact h
  have hd : q.minFac ∣ Nat.gcd q PS := Nat.dvd_gcd (Nat.minFac_dvd q) hdF
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  omega

/-- a number in `[2, B]` coprime to `k!` is prime when `B < (k + 1) ^ 2` -/
theorem prime_of_coprime_fact (k B q : ℕ) (hB : B < (k + 1) * (k + 1)) (h2 : 2 ≤ q) (hq : q ≤ B)
    (hc : Nat.gcd q (Nat.factorial k) = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hk : q.minFac ≤ k := by
    by_contra hc'
    have h1 : k + 1 ≤ q.minFac := by omega
    have h3 := le_trans (Nat.mul_le_mul h1 h1) hsq'
    omega
  have hdF : q.minFac ∣ Nat.factorial k := Nat.dvd_factorial hmp.pos hk
  have hd : q.minFac ∣ Nat.gcd q (Nat.factorial k) := Nat.dvd_gcd (Nat.minFac_dvd q) hdF
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

/-- the pool for `q`: `k!` for the tier with `k` below `q` and `(k + 1) ^ 2` above it, then `PS` -/
def fpool (q : ℕ) : ℕ :=
  cond (Nat.blt q 9) (Nat.factorial 2) (cond (Nat.blt q 81) (Nat.factorial 8)
    (cond (Nat.blt q 6561) (Nat.factorial 80) (cond (Nat.blt q 31684) (Nat.factorial 177) PS)))

/-- `q` is prime: `q = 2`, or `2 ≤ q < 2 ^ 24` and `q` is coprime to its tier's pool -/
def gOK (q : ℕ) : Bool :=
  Nat.beq q 2 || (Nat.ble 2 q && Nat.blt q 16777216 && Nat.beq (Nat.gcd q (fpool q)) 1)

theorem gOK_prime (q : ℕ) (h : gOK q = true) : q.Prime := by
  unfold gOK at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Nat.eq_of_beq_eq_true h]
    exact Nat.prime_two
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h1' := Nat.le_of_ble_eq_true h1
    have h2' := Nat.le_of_ble_eq_true h2
    have h3' := Nat.eq_of_beq_eq_true h3
    unfold fpool at h3'
    by_cases c1 : q < 9
    · rw [blt_t c1, cond_true] at h3'
      exact prime_of_coprime_fact 2 8 q (by norm_num) h1' (by omega) h3'
    rw [blt_f c1, cond_false] at h3'
    by_cases c2 : q < 81
    · rw [blt_t c2, cond_true] at h3'
      exact prime_of_coprime_fact 8 80 q (by norm_num) h1' (by omega) h3'
    rw [blt_f c2, cond_false] at h3'
    by_cases c3 : q < 6561
    · rw [blt_t c3, cond_true] at h3'
      exact prime_of_coprime_fact 80 6560 q (by norm_num) h1' (by omega) h3'
    rw [blt_f c3, cond_false] at h3'
    by_cases c4 : q < 31684
    · rw [blt_t c4, cond_true] at h3'
      exact prime_of_coprime_fact 177 31683 q (by norm_num) h1' (by omega) h3'
    rw [blt_f c4, cond_false] at h3'
    exact prime_of_coprime_PS q h1' h2' h3'

theorem gOK_lt (q : ℕ) (h : gOK q = true) : q < 16777216 := by
  unfold gOK at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Nat.eq_of_beq_eq_true h]; norm_num
  · simp only [Bool.and_eq_true] at h
    exact Nat.le_of_ble_eq_true h.1.2

/-! ## Pocklington with a known prime `L ∣ q - 1`

`kOK s q L a`: with `R = (q - 1) / L` and `y = a ^ R mod q` (computed by `pwk s`): `R ≥ 1`,
`R * L + 1 = q`, `q < (L + 1) ^ 2`, `R` and `L` below the powering bound, `y ^ L ≡ 1 (mod q)` and
`gcd(y + q - 1, q) = 1`. With `L` prime this proves `q` prime (`pockY`). -/

def kOK (s q L a : ℕ) : Bool :=
  Nat.ble 1 (Nat.div (Nat.sub q 1) L) &&
    Nat.beq (Nat.add (Nat.mul (Nat.div (Nat.sub q 1) L) L) 1) q &&
    Nat.blt q (Nat.mul (Nat.add L 1) (Nat.add L 1)) &&
    Nat.blt (Nat.div (Nat.sub q 1) L) (ebound s) && Nat.blt L (ebound s) &&
    Nat.beq (pwk s q (pwk s q a (Nat.div (Nat.sub q 1) L)) L) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (pwk s q a (Nat.div (Nat.sub q 1) L)) q) 1) q) 1

theorem kOK_prime (s q L a : ℕ) (hL : L.Prime) (h : kOK s q L a = true) : q.Prime := by
  simp only [kOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  set R := Nat.div (Nat.sub q 1) L with hR
  set y := pwk s q a R with hy
  have hyR : y ≡ a ^ R [MOD q] := pwk_pow s q a R (Nat.le_of_ble_eq_true h3)
  have hyL := pwk_pow s q y L (Nat.le_of_ble_eq_true h4)
  rw [Nat.eq_of_beq_eq_true h5] at hyL
  exact pockY q L R y (Nat.le_of_ble_eq_true h0) (Nat.eq_of_beq_eq_true h1)
    (Nat.le_of_ble_eq_true h2) hL hyL.symm (Nat.eq_of_beq_eq_true h6)

/-! ## Pocklington with two known primes `L1 L2 ∣ q - 1`

`pock` is the general criterion (`F` with all its prime factors checked); `k2OK` uses
`F = L1 * L2`: with `y = a ^ R`, `z1 = y ^ L1`, `z2 = y ^ L2` it checks `z1 ^ L2 ≡ 1` and that
`z1 - 1` and `z2 - 1` are units mod `q`. -/

theorem pock (N F R a : ℕ) (hR0 : 0 < R) (hR : R * F + 1 = N) (hlt : N < (F + 1) * (F + 1))
    (h1 : (a ^ R) ^ F ≡ 1 [MOD N])
    (h2 : ∀ f : ℕ, f.Prime → f ∣ F → ∃ z, z ≡ (a ^ R) ^ (F / f) [MOD N] ∧ Nat.Coprime (z + N - 1) N) :
    N.Prime := by
  have hF : 0 < F := by
    rcases Nat.eq_zero_or_pos F with h | h
    · subst h; simp at hR; omega
    · exact h
  have hN1 : N ≠ 1 := by
    have : 0 < R * F := Nat.mul_pos hR0 hF
    omega
  have hpp : N.minFac.Prime := Nat.minFac_prime hN1
  set p := N.minFac with hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpN : p ∣ N := Nat.minFac_dvd N
  have hcast : ∀ x y : ℕ, x ≡ y [MOD N] → ((x : ℕ) : ZMod p) = ((y : ℕ) : ZMod p) := by
    intro x y h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd hpN)
  have hbF : (((a ^ R : ℕ) : ZMod p)) ^ F = 1 := by
    have := hcast _ _ h1
    push_cast at this ⊢
    exact this
  have hN0 : ((N : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpN
  have hdiv : ∀ f : ℕ, f.Prime → f ∣ F → (((a ^ R : ℕ) : ZMod p)) ^ (F / f) ≠ 1 := by
    intro f hf hfF hb1
    obtain ⟨z, hz, hc⟩ := h2 f hf hfF
    have hz' : ((z : ℕ) : ZMod p) = (((a ^ R : ℕ) : ZMod p)) ^ (F / f) := by
      rw [hcast _ _ hz]
      push_cast
      rfl
    have hle : 1 ≤ z + N := by omega
    have hzero : ((z + N - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hle]
      push_cast
      rw [hz', hb1, hN0]
      ring
    have hpz : p ∣ z + N - 1 := (ZMod.natCast_eq_zero_iff _ _).1 hzero
    have hg := Nat.dvd_gcd hpz hpN
    rw [Nat.Coprime] at hc
    rw [hc] at hg
    exact hpp.one_lt.ne' (Nat.dvd_one.1 hg)
  have hord : orderOf (((a ^ R : ℕ) : ZMod p)) = F := orderOf_eq_of_pow_and_pow_div_prime hF hbF hdiv
  have hb0 : (((a ^ R : ℕ) : ZMod p)) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hF.ne'] at hbF
    exact zero_ne_one hbF
  have hdvd := ZMod.orderOf_dvd_card_sub_one hb0
  rw [hord] at hdvd
  have hp2 := hpp.two_le
  have hle : F ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  rw [← hp, pow_two] at hsq
  have : (F + 1) * (F + 1) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
  omega

def k2OK (s q L1 L2 a : ℕ) : Bool :=
  Nat.ble 1 (Nat.div (Nat.sub q 1) (Nat.mul L1 L2)) &&
    Nat.beq (Nat.add (Nat.mul (Nat.div (Nat.sub q 1) (Nat.mul L1 L2)) (Nat.mul L1 L2)) 1) q &&
    Nat.blt q (Nat.mul (Nat.add (Nat.mul L1 L2) 1) (Nat.add (Nat.mul L1 L2) 1)) &&
    Nat.blt (Nat.div (Nat.sub q 1) (Nat.mul L1 L2)) (ebound s) && Nat.blt L1 (ebound s) &&
    Nat.blt L2 (ebound s) &&
    Nat.beq (pwk s q (pwk s q (pwk s q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L1) L2) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (pwk s q (pwk s q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L1) q) 1) q) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (pwk s q (pwk s q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L2) q) 1) q) 1

theorem k2OK_prime (s q L1 L2 a : ℕ) (h1 : L1.Prime) (h2 : L2.Prime) (h : k2OK s q L1 L2 a = true) :
    q.Prime := by
  simp only [k2OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, hRF⟩, hlt⟩, hRb⟩, hL1b⟩, hL2b⟩, hpw⟩, hc1⟩, hc2⟩ := h
  set F := Nat.mul L1 L2 with hF
  set R := Nat.div (Nat.sub q 1) F with hR
  set y := pwk s q a R with hy
  have hyR : y ≡ a ^ R [MOD q] := pwk_pow s q a R (Nat.le_of_ble_eq_true hRb)
  have hz1 : pwk s q y L1 ≡ (a ^ R) ^ L1 [MOD q] :=
    (pwk_pow s q y L1 (Nat.le_of_ble_eq_true hL1b)).trans (Nat.ModEq.pow _ hyR)
  have hz2 : pwk s q y L2 ≡ (a ^ R) ^ L2 [MOD q] :=
    (pwk_pow s q y L2 (Nat.le_of_ble_eq_true hL2b)).trans (Nat.ModEq.pow _ hyR)
  have hFL1 : F / L1 = L2 := by
    show L1 * L2 / L1 = L2
    exact Nat.mul_div_cancel_left L2 h1.pos
  have hFL2 : F / L2 = L1 := by
    show L1 * L2 / L2 = L1
    exact Nat.mul_div_cancel L1 h2.pos
  apply pock q F R a (Nat.le_of_ble_eq_true h0) (Nat.eq_of_beq_eq_true hRF) (Nat.le_of_ble_eq_true hlt)
  · have h3 := (pwk_pow s q (pwk s q y L1) L2 (Nat.le_of_ble_eq_true hL2b)).trans (Nat.ModEq.pow _ hz1)
    rw [Nat.eq_of_beq_eq_true hpw, ← pow_mul] at h3
    exact h3.symm
  · intro f hf hfF
    rcases (Nat.Prime.dvd_mul hf).1 hfF with h' | h'
    · have hf1 : f = L1 := (Nat.prime_dvd_prime_iff_eq hf h1).1 h'
      subst hf1
      rw [hFL1]
      exact ⟨_, hz2, Nat.eq_of_beq_eq_true hc2⟩
    · have hf2 : f = L2 := (Nat.prime_dvd_prime_iff_eq hf h2).1 h'
      subst hf2
      rw [hFL2]
      exact ⟨_, hz1, Nat.eq_of_beq_eq_true hc1⟩

/-! ## The record checks with a direct base power

For the ladder records `y = a ^ R mod q` is one GMP `pow` and one `mod` when `R < 2 ^ 17`, else
`ytwo` (`yget`); the powers `y ^ L` use `pw3` (`L < 2 ^ 24`). `kOKr` takes
`R` and `L` and checks `q = R * L + 1` with the windowed powering (table records). -/

theorem dpow (q a R : ℕ) : Nat.mod (Nat.pow a R) q ≡ a ^ R [MOD q] := Nat.mod_modEq (a ^ R) q

/-- `a ^ R mod N` as `((a ^ (R / 2 ^ 16) mod N) ^ (2 ^ 16) mod N) * a ^ (R mod 2 ^ 16) mod N`: two GMP
powers with exponents below `2 ^ 17` (for `R < 2 ^ 33`) and two squaring windows -/
def ytwo (N a R : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.mod (Nat.pow (Nat.mod (Nat.pow (Nat.mod (Nat.pow a (Nat.shiftRight R 16)) N) 256) N)
    256) N) (Nat.pow a (Nat.land R 65535))) N

theorem ytwo_spec (N a R : ℕ) : ytwo N a R ≡ a ^ R [MOD N] := by
  have e1 : Nat.shiftRight R 16 = R / 65536 := by
    show R >>> 16 = R / 65536
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land R 65535 = R % 65536 := Nat.and_two_pow_sub_one_eq_mod R 16
  unfold ytwo
  rw [e1, e2]
  have h1 : Nat.mod (Nat.pow a (R / 65536)) N ≡ a ^ (R / 65536) [MOD N] := Nat.mod_modEq _ _
  have h2 : Nat.mod (Nat.pow (Nat.mod (Nat.pow a (R / 65536)) N) 256) N ≡ (a ^ (R / 65536)) ^ 256 [MOD N] :=
    (Nat.mod_modEq _ _).trans (h1.pow 256)
  have h3 : Nat.mod (Nat.pow (Nat.mod (Nat.pow (Nat.mod (Nat.pow a (R / 65536)) N) 256) N) 256) N ≡
      ((a ^ (R / 65536)) ^ 256) ^ 256 [MOD N] :=
    (Nat.mod_modEq _ _).trans (h2.pow 256)
  have h4 := (Nat.mod_modEq (Nat.mul (Nat.mod (Nat.pow (Nat.mod (Nat.pow (Nat.mod (Nat.pow a (R / 65536)) N) 256) N)
    256) N) (Nat.pow a (R % 65536))) N).trans (h3.mul_right (a ^ (R % 65536)))
  refine h4.trans ?_
  have e3 : ((a ^ (R / 65536)) ^ 256) ^ 256 * a ^ (R % 65536) = a ^ R := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e3]

/-- the base power `a ^ R mod q`: one GMP `pow` when `R < 2 ^ 17`, else `ytwo` -/
def yget (q a R : ℕ) : ℕ := cond (Nat.blt R 131072) (Nat.mod (Nat.pow a R) q) (ytwo q a R)

theorem yget_spec (q a R : ℕ) : yget q a R ≡ a ^ R [MOD q] := by
  unfold yget
  cases Nat.blt R 131072
  · exact ytwo_spec q a R
  · exact dpow q a R

def kOKd (q L a : ℕ) : Bool :=
  Nat.ble 1 (Nat.div (Nat.sub q 1) L) &&
    Nat.beq (Nat.add (Nat.mul (Nat.div (Nat.sub q 1) L) L) 1) q &&
    Nat.blt q (Nat.mul (Nat.add L 1) (Nat.add L 1)) &&
    Nat.blt L 16777216 &&
    Nat.beq (pw3 q (yget q a (Nat.div (Nat.sub q 1) L)) L) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (yget q a (Nat.div (Nat.sub q 1) L)) q) 1) q) 1

theorem kOKd_prime (q L a : ℕ) (hL : L.Prime) (h : kOKd q L a = true) : q.Prime := by
  simp only [kOKd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h4⟩, h5⟩, h6⟩ := h
  set R := Nat.div (Nat.sub q 1) L with hR
  set y := yget q a R with hy
  have hyL := pw3_pow q y L (Nat.le_of_ble_eq_true h4)
  rw [Nat.eq_of_beq_eq_true h5] at hyL
  exact pockY q L R y (Nat.le_of_ble_eq_true h0) (Nat.eq_of_beq_eq_true h1)
    (Nat.le_of_ble_eq_true h2) hL hyL.symm (Nat.eq_of_beq_eq_true h6)

def k2OKd (q L1 L2 a : ℕ) : Bool :=
  Nat.ble 1 (Nat.div (Nat.sub q 1) (Nat.mul L1 L2)) &&
    Nat.beq (Nat.add (Nat.mul (Nat.div (Nat.sub q 1) (Nat.mul L1 L2)) (Nat.mul L1 L2)) 1) q &&
    Nat.blt q (Nat.mul (Nat.add (Nat.mul L1 L2) 1) (Nat.add (Nat.mul L1 L2) 1)) &&
    Nat.blt L1 16777216 && Nat.blt L2 16777216 &&
    Nat.beq (pw3 q (pw3 q (yget q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L1) L2) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (pw3 q (yget q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L1) q) 1) q) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (pw3 q (yget q a (Nat.div (Nat.sub q 1) (Nat.mul L1 L2))) L2) q) 1) q) 1

theorem k2OKd_prime (q L1 L2 a : ℕ) (h1 : L1.Prime) (h2 : L2.Prime) (h : k2OKd q L1 L2 a = true) :
    q.Prime := by
  simp only [k2OKd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, hRF⟩, hlt⟩, hL1b⟩, hL2b⟩, hpw⟩, hc1⟩, hc2⟩ := h
  set F := Nat.mul L1 L2 with hF
  set R := Nat.div (Nat.sub q 1) F with hR
  set y := yget q a R with hy
  have hyR : y ≡ a ^ R [MOD q] := yget_spec q a R
  have hz1 : pw3 q y L1 ≡ (a ^ R) ^ L1 [MOD q] :=
    (pw3_pow q y L1 (Nat.le_of_ble_eq_true hL1b)).trans (Nat.ModEq.pow _ hyR)
  have hz2 : pw3 q y L2 ≡ (a ^ R) ^ L2 [MOD q] :=
    (pw3_pow q y L2 (Nat.le_of_ble_eq_true hL2b)).trans (Nat.ModEq.pow _ hyR)
  have hFL1 : F / L1 = L2 := by
    show L1 * L2 / L1 = L2
    exact Nat.mul_div_cancel_left L2 h1.pos
  have hFL2 : F / L2 = L1 := by
    show L1 * L2 / L2 = L1
    exact Nat.mul_div_cancel L1 h2.pos
  apply pock q F R a (Nat.le_of_ble_eq_true h0) (Nat.eq_of_beq_eq_true hRF) (Nat.le_of_ble_eq_true hlt)
  · have h3 := (pw3_pow q (pw3 q y L1) L2 (Nat.le_of_ble_eq_true hL2b)).trans (Nat.ModEq.pow _ hz1)
    rw [Nat.eq_of_beq_eq_true hpw, ← pow_mul] at h3
    exact h3.symm
  · intro f hf hfF
    rcases (Nat.Prime.dvd_mul hf).1 hfF with h' | h'
    · have hf1 : f = L1 := (Nat.prime_dvd_prime_iff_eq hf h1).1 h'
      subst hf1
      rw [hFL1]
      exact ⟨_, hz2, Nat.eq_of_beq_eq_true hc2⟩
    · have hf2 : f = L2 := (Nat.prime_dvd_prime_iff_eq hf h2).1 h'
      subst hf2
      rw [hFL2]
      exact ⟨_, hz1, Nat.eq_of_beq_eq_true hc1⟩

def kOKr (s R L a : ℕ) : Bool :=
  Nat.ble 1 R && Nat.blt (Nat.add (Nat.mul R L) 1) (Nat.mul (Nat.add L 1) (Nat.add L 1)) &&
    Nat.blt L (ebound s) &&
    Nat.beq (pwk s (Nat.add (Nat.mul R L) 1) (ytwo (Nat.add (Nat.mul R L) 1) a R) L) 1 &&
    Nat.beq (Nat.gcd (Nat.sub (Nat.add (ytwo (Nat.add (Nat.mul R L) 1) a R) (Nat.add (Nat.mul R L) 1)) 1)
      (Nat.add (Nat.mul R L) 1)) 1

theorem kOKr_prime (s R L a : ℕ) (hL : L.Prime) (h : kOKr s R L a = true) :
    (Nat.add (Nat.mul R L) 1).Prime := by
  simp only [kOKr, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h2⟩, h4⟩, h5⟩, h6⟩ := h
  set N := Nat.add (Nat.mul R L) 1 with hN
  set y := ytwo N a R with hy
  have hyL := pwk_pow s N y L (Nat.le_of_ble_eq_true h4)
  rw [Nat.eq_of_beq_eq_true h5] at hyL
  exact pockY N L R y (Nat.le_of_ble_eq_true h0) rfl (Nat.le_of_ble_eq_true h2) hL hyL.symm
    (Nat.eq_of_beq_eq_true h6)

/-! ## The table of large primes `L`

A table `T` packs `K` entries of 66 bits, entry `i` at bit `66 * i`: `L` (40 bits), `L2` (24 bits),
the base offset (1 bit) and the size flag (1 bit). `tOK T K` certifies every `L`: `L2` by `gOK` and
`L` by `kOK` with the prime `L2 ∣ L - 1`. -/

def tL (T i : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul 66 i)) 1099511627775

def tL2 (T i : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.add (Nat.mul 66 i) 40)) 16777215

def tA (T i : ℕ) : ℕ := Nat.add 2 (Nat.land (Nat.shiftRight T (Nat.add (Nat.mul 66 i) 64)) 1)

def tS (T i : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.add (Nat.mul 66 i) 65)) 1

def tOK (T : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => gOK (tL2 T k) && kOK (tS T k) (tL T k) (tL2 T k) (tA T k) && tOK T k

theorem tOK_sound (T : ℕ) : ∀ K, tOK T K = true → ∀ i, i < K → (tL T i).Prime := by
  intro K
  induction K with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    simp only [tOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    by_cases hik : i = k
    · subst hik
      exact kOK_prime _ _ _ _ (gOK_prime _ h1) h2
    · exact ih h3 i (by omega)

/-! ## The certificate of one ladder prime

For types `t ≠ 2` the prime `L ∣ q - 1` is given by the field `X`: for `t = 0`, `L = X` with
`gOK X`; otherwise `L` is table entry `X < K`. -/

def Lof (T t X : ℕ) : ℕ := cond (Nat.beq t 0) X (tL T X)

def lOK (T K t X : ℕ) : Bool := cond (Nat.beq t 0) (gOK X) (Nat.blt X K)

theorem lOK_prime (T K t X : ℕ) (hT : tOK T K = true) (h : lOK T K t X = true) :
    (Lof T t X).Prime := by
  unfold lOK at h
  unfold Lof
  cases ht : Nat.beq t 0
  · simp only [ht, cond_false] at h ⊢
    exact tOK_sound T K hT X (Nat.le_of_ble_eq_true h)
  · simp only [ht, cond_true] at h ⊢
    exact gOK_prime X h

/-- type `2`: `X = L1 + 2 ^ 24 * L2` with `gOK L1`, `gOK L2` and `k2OK`; types `0`, `1`: `lOK` and `kOK` -/
def cOK (T K q t s a X : ℕ) : Bool :=
  cond (Nat.beq t 2)
    (gOK (Nat.land X 16777215) && gOK (Nat.shiftRight X 24) &&
      k2OK s q (Nat.land X 16777215) (Nat.shiftRight X 24) a)
    (lOK T K t X && kOK s q (Lof T t X) a)

theorem cOK_prime (T K q t s a X : ℕ) (hT : tOK T K = true) (h : cOK T K q t s a X = true) :
    q.Prime := by
  unfold cOK at h
  cases ht : Nat.beq t 2
  · simp only [ht, cond_false, Bool.and_eq_true] at h
    exact kOK_prime s q _ a (lOK_prime T K t X hT h.1) h.2
  · simp only [ht, cond_true, Bool.and_eq_true] at h
    exact k2OK_prime s q _ _ a (gOK_prime _ h.1.1) (gOK_prime _ h.1.2) h.2

/-! ## The ladder

`Inv q0 q`: `q` is prime, and every `n` with `q0 < n ≤ q` has a prime `p < n` with
`n * 28313999 < 28314000 * p`. A step from the prime `q` to any prime `q' ≤ q + D`, where
`D = (q - 1) / 28313999`, keeps `Inv`: for `q < n ≤ q'` take `p = q`, since
`n * 28313999 ≤ (q + D) * 28313999 ≤ q * 28313999 + q - 1`. -/

def Inv (q0 q : ℕ) : Prop :=
  q.Prime ∧ ∀ n, q0 < n → n ≤ q → ∃ p : ℕ, p.Prime ∧ p < n ∧ n * 28313999 < 28314000 * p

theorem inv_init (q0 : ℕ) (h : q0.Prime) : Inv q0 q0 :=
  ⟨h, fun n h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)⟩

theorem inv_step (q0 q q' : ℕ) (hI : Inv q0 q) (hle : q' ≤ q + Nat.div (Nat.sub q 1) 28313999)
    (hp : q'.Prime) : Inv q0 q' := by
  obtain ⟨hq, hI⟩ := hI
  refine ⟨hp, ?_⟩
  intro n hn1 hn2
  have hq2 := hq.two_le
  set D := Nat.div (Nat.sub q 1) 28313999 with hD
  have hDm : D * 28313999 ≤ q - 1 := Nat.div_mul_le_self (q - 1) 28313999
  have hnq : n ≤ q + D := le_trans hn2 hle
  by_cases hn : n ≤ q
  · exact hI n hn1 hn
  · refine ⟨q, hq, by omega, ?_⟩
    have h3 : n * 28313999 ≤ (q + D) * 28313999 := Nat.mul_le_mul_right _ hnq
    rw [add_mul] at h3
    omega

/-- `q + D - δ` (records of types `0` and `2`) -/
def nextq (q δ : ℕ) : ℕ := Nat.sub (Nat.add q (Nat.div (Nat.sub q 1) 28313999)) δ

/-- `R = (q + D - 1) / L - k` (records of type `1`: `q' = R * L + 1`) -/
def rT (q L k : ℕ) : ℕ := Nat.sub (Nat.div (Nat.sub (Nat.add q (Nat.div (Nat.sub q 1) 28313999)) 1) L) k

/-- the next ladder prime of a record -/
def qnext (T q t k X : ℕ) : ℕ :=
  cond (Nat.beq t 1) (Nat.add (Nat.mul (rT q (tL T X) k) (tL T X)) 1) (nextq q k)

theorem qnext_le (T q t k X : ℕ) (hq : 1 ≤ q) :
    qnext T q t k X ≤ q + Nat.div (Nat.sub q 1) 28313999 := by
  unfold qnext
  cases ht : Nat.beq t 1
  · simp only [cond_false, nextq]
    show q + (q - 1) / 28313999 - k ≤ q + (q - 1) / 28313999
    omega
  · simp only [cond_true, rT]
    set L := tL T X
    set U := Nat.sub (Nat.add q (Nat.div (Nat.sub q 1) 28313999)) 1 with hU
    have h1 : (Nat.div U L - k) * L ≤ U := by
      calc (Nat.div U L - k) * L ≤ Nat.div U L * L := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ ≤ U := Nat.div_mul_le_self U L
    show (Nat.div U L - k) * L + 1 ≤ q + (q - 1) / 28313999
    have : U = q + (q - 1) / 28313999 - 1 := rfl
    omega

/-- one record: type `1`: table entry `X < K`, `kOKr` with `R = rT q L k`; type `2`:
`X = L1 + 2 ^ 24 * L2`, `gOK L1`, `gOK L2`, `k2OKd`; otherwise `gOK X` and `kOKd` (`L = X`) -/
def stepOK (T K q t a k X : ℕ) (s : ℕ) : Bool :=
  cond (Nat.beq t 1) (Nat.blt X K && kOKr s (rT q (tL T X) k) (tL T X) a)
    (cond (Nat.beq t 2)
      (gOK (Nat.land X 16777215) && gOK (Nat.shiftRight X 24) &&
        k2OKd (nextq q k) (Nat.land X 16777215) (Nat.shiftRight X 24) a)
      (gOK X && kOKd (nextq q k) X a))

theorem step_prime (T K q t a k X s : ℕ) (hT : tOK T K = true) (h : stepOK T K q t a k X s = true) :
    (qnext T q t k X).Prime := by
  unfold stepOK at h
  unfold qnext
  cases h1 : Nat.beq t 1
  · simp only [h1, cond_false] at h ⊢
    cases h2 : Nat.beq t 2
    · simp only [h2, cond_false, Bool.and_eq_true] at h
      exact kOKd_prime _ _ _ (gOK_prime _ h.1) h.2
    · simp only [h2, cond_true, Bool.and_eq_true] at h
      exact k2OKd_prime _ _ _ _ (gOK_prime _ h.1.1) (gOK_prime _ h.1.2) h.2
  · simp only [h1, cond_true, Bool.and_eq_true] at h ⊢
    exact kOKr_prime s _ _ a (tOK_sound T K hT X (Nat.le_of_ble_eq_true h.1)) h.2

theorem step_sound (T K q0 q t a k X s : ℕ) (hT : tOK T K = true) (h : stepOK T K q t a k X s = true)
    (hI : Inv q0 q) : Inv q0 (qnext T q t k X) :=
  inv_step q0 q _ hI (qnext_le T q t k X hI.1.one_lt.le) (step_prime T K q t a k X s hT h)

/-- the walk over packed record groups. A group `G` holds records of `w` bits, low record first,
ended by a leading sentinel bit (`G ≤ 1` ends the group). A record is, from the low bit: `t` (2 bits),
the base offset (1 bit, base `2 + bit`), the size flag `s` (1 bit), `k` (from bit 4, mask `md`) and
`X` (from bit `s1`, mask `mx`). Every check is `&&`-ed, so one failed record makes the value `false`.
The empty list requires `q = qe` exactly. `f` is fuel. -/
def seg (T K qe md s1 mx w : ℕ) : ℕ → List ℕ → ℕ → Bool
  | _, _, 0 => false
  | q, [], _ + 1 => Nat.beq q qe
  | q, G :: l, f + 1 =>
    cond (Nat.ble G 1) (seg T K qe md s1 mx w q l f)
      (stepOK T K q (Nat.land G 3) (Nat.add 2 (Nat.land (Nat.shiftRight G 2) 1))
          (Nat.land (Nat.shiftRight G 4) md) (Nat.land (Nat.shiftRight G s1) mx)
          (Nat.land (Nat.shiftRight G 3) 1) &&
        seg T K qe md s1 mx w
          (qnext T q (Nat.land G 3) (Nat.land (Nat.shiftRight G 4) md) (Nat.land (Nat.shiftRight G s1) mx))
          (Nat.shiftRight G w :: l) f)

theorem seg_sound (T K q0 qe md s1 mx w : ℕ) (hT : tOK T K = true) :
    ∀ (f q : ℕ) (l : List ℕ), seg T K qe md s1 mx w q l f = true → Inv q0 q → Inv q0 qe := by
  intro f
  induction f with
  | zero => intro q l h; simp [seg] at h
  | succ f ih =>
    intro q l h hI
    cases l with
    | nil =>
      simp only [seg] at h
      rw [← Nat.eq_of_beq_eq_true h]
      exact hI
    | cons G l =>
      simp only [seg] at h
      cases hG : Nat.ble G 1
      · rw [hG, cond_false, Bool.and_eq_true] at h
        exact ih _ _ h.2 (step_sound T K q0 q _ _ _ _ _ hT h.1 hI)
      · rw [hG, cond_true] at h
        exact ih q l h hI

/-! ## From the ladder to the statement -/

theorem real_of_nat (n p : ℕ) (h1 : p < n) (h2 : n * 28313999 < 28314000 * p) :
    (n : ℝ) * (1 - 1 / 28314000) < (p : ℝ) ∧ (p : ℝ) < (n : ℝ) := by
  have h3 : ((n * 28313999 : ℕ) : ℝ) < ((28314000 * p : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  refine ⟨?_, by exact_mod_cast h1⟩
  have e : (n : ℝ) * (1 - 1 / 28314000) = (n : ℝ) * 28313999 / 28314000 := by ring
  rw [e, div_lt_iff₀ (by norm_num)]
  linarith

theorem finish (q0 qe A B : ℕ) (hI : Inv q0 qe) (hA : q0 ≤ A) (hB : B ≤ qe) (n : ℕ)
    (hn : A < n) (hu : n ≤ B) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  obtain ⟨p, hp, h1, h2⟩ := hI.2 n (by omega) (by omega)
  exact ⟨p, hp, real_of_nat n p h1 h2⟩

end RAFrame

namespace RAData

/-- the table of large primes (10 entries of 66 bits) -/
def TB : ℕ := 0x2e6852c09502f9b4c715d2d02540be69b020df0409502f9a240227a702540be677006372409502f996403d75902540be64d03a20f409502f97d4027ed702540be51700e6434095160ab046a8b0b0253f9c589

theorem TOK : RAFrame.tOK TB 10 = true := by decide +kernel

theorem P0 : RAFrame.cOK TB 10 99876372021712761067 1 0 2 0 = true := by decide +kernel

def D0 : List ℕ := [
  0x1008642190054010004c01410584182060013086471208588110c4c216305031110581101058214104c110204841210501120864513004c312004c413284c218185c21820403121064416084c5120044313044801000600140840018105821804484132860110085421418541110040e1000540193c406122064310145c6151050417284c819005021610604181854512084c61810582151c48a14104421300504170858017105c31210606131040416085c013105021908447126048810005421718582131050018584c0110440010085001710503110440115004c512284c219006451208646140c48012085c0100040319105c81300608150444716005d01,
  0x14085871208580191448214105c418005c21900611110c5c214004c4181060813286401408544160449a12105c018104c219044ca15085c4180044010046441828640150860013004431238600140c48014144841608581124058312084011210580153840615206011238402102049019044021710542154854312004c4150440718044001218582190448216304c5110458617105041408556150050213006421710581110854512284ca10004c2131c488141c48210105c6150850a15144801608504160054418085451000482131c48414086421108588191854217006031044603111064112084c0150860417005421418608180050e161044e11005481,
  0x140858014084c5121848214005c2170448a1220440140844414004cc112450818184c219305421648502180050415106491200495110c480160c4861814442171854512106021600645122444314105c0141448a15004521604488140444f13284c010005c712084c018285c41908646170c484122840012106441520606110858019144c214104c017244921218446130058818004091210500190c4c0150858413084461200482147054419144c413044491020645111058c170c4801850640160c48a16106001410542153055015105041614401150054910184431000483102c58312284c01940544131064e191850e14004c2191840b130860017144841,
  0x1710582140064e154054010084c1120858d120848612084c31104642170054312304841508506171844113144831114606131054a192060110044c0132050019505801800402110c5c511004c21300545120850014144811104504160864311185c014084441538441140050414085011208500160864418005c214005c0110c642191448a18004c4110860615105c41308586131051413104c417186081110441120860415484c414504c415105c61308648110448012106081000404191054a14084c1100840012084c6140861216204c01308605120048815004c3100c64113205c11100447132c484140864618084ca1304491101c500162444012085c01,
  0x14044821218404160444211084c211006471028589121840214004c81818642141044513005c8160440319085801920600150864513004c2150050818004cf1218641111854613086021110441150054415404d112004001028640190c4841900502101c487111044612104401964400141054310185001310584191c44212105091200644150c406120858112085c71208500135058011085c4190050217006071114480172c4821110480141040218006451350584171060a14004c3121848011044801310540110c4041410609100060219005c214185041308441133c4861338601120864311086021100502163840113044821730501110848217105801,
  0x120048211305441410502112c580130864a19044c216005c4140c48012285021500504142064d111040417104c418104441920644111c58213004c3121044811004c618206401750582100c58312005501500403162064113084c11210584181050214006411000416170058214185431010640150440818405c310304821510584181850011046001610604191c446195444215106021900542160058418084c1112858512285021510504140044316005c41708592142040811084ce1608441173064b116c602191440413105881108442180050312144441100449160c440130850112085c018084c019044401210480120c40314005c41820500150c4841,
  0x17004011208401121060615104c8180448217286001518443120850014085501910603110848410104421700588181059614006021800603120440113044821100608130448e15005441534446171065014044821700540110460a16004c2150c440130044011044c41818540100064619285831218444190440816084c01820543100050618084c31100442110c4821204440100848412084c1111044217105811208585120058e150050312004031510644170040214185c21400502140448111145411220604190060912105c411046431210644181440211004c5100c58416106001614409150c44b170c485100c60615085441718500100454a17044821,
  0x1610644151c484172050013286401000440161058415085c3110848a18144021130482183058218005c312105c0152058415044011940544160c401132064014044141008440123860013086001908500140c48311346421018643111060014085c419104001908640171060f1000602181854216005841548442111450110184c1120858a180448214106401804400102840314006451308505121048a15005c31218642160c44518104c018204c211004c11238480120858a152864713085071208400131448e191064611146441910549100040217106001638641100460015085c0190854111104441608644141864818005441520504170054413086401,
  0x13305c21904442121060018084c419285c1121048417086061428442180448411244ca170c44117044021710545120860416004c214044821900505100c50312044021218582101c48414206451200648141050712105c6100c582190058214244411400409123848a141448210085c813204001510606190c4c0161050a19105c4130c4041418642151448017084c511004c91008401130c41114084c6140854b120048215004c2131448a12006441724489110048311305d0130448215185c21308441130064a18085861514402141060110084c1121054510105091024584170058414084c41108441141858312006021804480110854214005c413184011,
  0x170c48a14005001028443120858711104c215004c41310504100c48010144411500502181058614085c0191448815285c4133440010004c0160860b1118644184844915106441420504102844310244c3120054010045c01638540150c44316005051210645130840c161064313006441954400180864113084c0151050216404c5120058414085001310542161850a13085c01308642110c5881918544180858013104c215005c210145c41910405140060218306021900603121060410104c01020501123848010085d0180064510105491228484131060a150440214044041208600110c4c613084c51024540150850512184c41508641120848419005c81,
  0x1528445102448617084c31100504111448418105061414482124864214184c01020484170854613085801508553120854018285c814184c21704403180c4801520504190058813285c2100c48a16084c019405841408604180064e182854211005851208408110c487110460014084061908640140c400140860512005021804480100044a14006021130504161c40311104411900543121848411284c3120c401132064417104c4150058814006041310411142c48a100854c10105c210004c2160448216105021100601102048013144021228507100858016284c6110c602154050c162054112084c01628582171064b124850311244c01608584160c4421,
  0x12085cb11004c2130044e1610500116c4c0142c4841228642190064214105001408541101048213105d0161850512084901528580110c48c121444118004cb111440115185821604401130440919085051228484150c440141860419205c418004c416104c2160840016186041710500112448a132040711044c11218402141044418205041818584160c404100844114204c11210484161050710045891200484190c4841900514161064d120848618085041418585110c504130864112105c2111060017385c418004c2150c440110064217105c112085041314484151c44714304c21700549102c5c2171860813144861608500150854419005c215105c01,
  0x100458211004c0131448815184c217044821504482154c48813004c2141050416004c2131058112104ca1908507120854310085c21304449140c4861208482110c40119005ca170c4801514442120060414084c0180860c16084c4150840719044c81748542111060018086021104500160040218205c014284ce18104c01450640163c48013104c41320581110c403162864414104c6130864311144c31118580142c48814044841208501110c508150c44214104c8160064512105c3120040219144c112104d0180c4561500543101060a1810500150c44411305041904442141844216004431900447144854a16084c0130850417104c014104c218005851,
  0x190040315285c618104c21400604100c58018004001710600160850016105c2150050a151440416104c81318542130050214044881108440140c4001314480170c481101048510045c0180860013105cb120440811044861310650152054711204c0180c48a1028581120850015085861600400150844213105021510600142850710204441704410100858217004c213005c3102460511004811000486150850416105041410645110c5cc160444612285c614086061908542111c484190c4401500582141054017085c013105041514482120060511085c011106021548445140850013085461610645100c50219144c014206471208480151448215005401,
  0x140840112104c614144821118603120c445140c44b152040c190054512085d21318447150044b1308581100c455181058511284c418005811000507121060818005cb1208604191c4011500544151c40211045841728645120440312104c8160064e1008402191058219005c814005041510644150850618105831208400120050214004c6110448012206411304442123848c14106421900542140058216004c311304851108580140c48018286021410401180860a1000403141854418084481100402110c582100444118006011118506132c40e120050213285c617084c110285c216006141800542180064f131050619104041118490141040b12286421,
  0x14084c418005431200484150040112305021408402162860611085021434482140840618105061714482151854214006041508647102840214105801508506130440b1500443151844317005431104403170c48416005021628580160860810044c112285c219305441310602183060512084c01410549111864912105441440604143050414044441018604140c44c1418585121064a180c409130050d1008481104458112084c112206421104504102c580103c50616085c413105441604482141050a15105c7120855214086011210482120c441190c48614084c1102848b1008580131440812105c014085041510544181c482152c400120c40b15444881,
  0x11105031200643131860417085c210104031828402170840312284c41508596140c44810285001124484180854a16005c711084801000482100064011204c0151050511045811004585120058216044881800443120440316085c0160850015085c112104c2162040219086401710602100c44612005051200442180854616085401908504180050e1810512161044b12105c215004c5120850112106081900600110448418084471300602181850413086021118640100c58013104c814305831200502160040b121060a1008400151058214044801100480190c4001408644182c40419005c510205411010444150c40515004411318509112848417005041,
  0x150050512085c11210482123050214184431918502191860417106401008402114448210184411414484100858016085001408540191054217104c4161c488151060016085c9110051014044031614409171444119005441324480181054216184431428605110c60a130054010305c016384ca191050112105541914406162449013004c310104c419004491914400130c486152850216105411204400122860a14406461010480174448212305c21728580170c4901528504160054b12084801310646110060410084431038601111060311004421500444182c4021848583103040215404c4132c48a14004c3101048016144011504442130c442141050a1,
  0x1418504141050c11085841608581120854016085c0151058512304061900582130448218004c415144821704484142448016084c01908640140c48018084c0160854110104c811045c21704401171448017104ca111060215004cc113c5421604482171448011084821004544141448013085c014105c11130484141044211184c0180044115004c3120048010006001614480110448310004ca1810584190c4011928543122c4021030403181860418084c013105821034482111060018085c6181058a102c449190860010104d01710644170c4051114402150444918084c5100045a1800648162c480172054a140064b101c5801308444180440113006421,
  0x1910640180850017204c5110c5c013084c211006481110441120c447150858016204c0141058219044c8130040415385471020590192c4c618205041300444190864a18044821600588163c440140060011004c910144c0192860214384071200540101c480191050215004ca18086411108484180444215004c41608400131051617405c41320604180060a15084c618205c014084c01408644140c4501100640180c480190850017084c4160064311104c0142448016104c21400544140c484190054711084841718440143054a170c48413004c21618505112844011084c01104544150444d1404442100060b121064816105c61608584110450b10204031,
  0x1414410100c6021700502170040512105c2112c5011210642151058b11304c416004461508442170864a1400645110454110385041900543120048219044c51040482131864216144801310541100840717004ce1600588140064010046041600502131054a13006421518502154064414005ca1128602192850417005421308400151060414004c2151050310005041418507111044812086411208480192058211044c0160c4851028486120850015105c4110c5c0100044317085071110608140448a121064414205001928610160858416004c01100604111064512104061834441192054111206001408600171050218044831030441171054015144011,
  0x16044841600403130c4031604484140040318105421810640100c4ca14104c419044c41008441140c489110050511006011000589100060d1210582171858216004c2130844510305411208501120865017284c0140858112086451210500130c4801708544172858413304c21528417171054015085c1110c5c512104c2181050014084c013104c4150858111104c311005c416286031010640110c5401408506150c48013205c61308592170850a190448e19586041810401133850018105841600443151060e10005c4150c4401308440150864416006451208541122840413284c31228600180044113044021710506180854015205c4130050213144861,
  0x100c64313105001800401121060112084c0131c44218404421714480101458218284c4140448219006401000504111c54214005c4161054110006071208540160c483101444112084c111044c41504444132c48413105c213184c41320604101450111204c112084c013084c01308545120048813004c111004801908606140c480140854616084c414004c4113044616104c01700443180c400120858418185821900582171c484120444d130850013084c0141040312006441408540190844716084c1120848c100c500130854413005021700545120850112205c6141440a19144c21304402171850e140c44016104c61508540191050011044c015144011,
  0x110c547101c5011004540132c4821820442135050014004031910642160840314084c0150044c19084471300649122c4431500505120040019105441304402130440415285871008484191c40012185c41934401161064511344c1100c5431210580160044616144841904441161c444162c44211006421004482151c480100864311084401500504140858017104c2181060019106071100505120044413085c61608540180c40316005c41504400100c4c0170c48a172844714084c112084cc15044401004604190850610086441114540132850512085861008504100040212004821200484121040812285c71238500180c40416044851008442110c4041,
  0x141448111045c013085c0100c606190c4c0181448219105c01910582130050213105001318401120048412204c6182064d1208580180864a1418584170850017205c1111050215185c417284c3120440119285c4191c4841808504160054419085001500407160840115005041818401182c480141054b1200401110c4c2100060018084c013104c2142854415106061724444110060418104c21700545122064014404c218006021810506170c480140c40314004c21410546180860018084c0152448018205441104405160858a160050414084451210404160040a151c444112c5051000402122858c15085c4160440215006051108481100844015084cc1,
  0x10104401100645130440f193854d110c540103c6001004586182058016086001838646180040316104c41724486150044112005041428503120040e13105c4172864513284cc1308501101840c18344821100584182c48216044841908641130c4431410580190c484180050011104431208480131050213185c0100c44a191058a190840c14084c5120444e161440018084ca1310546181064710144461114503100054216106051210640150854b1210500130858a170448216006051210543120058f111464313144521808581120854c14444881218542141c48412106041320507120848614084c615106021604442150058216005c4170858018184411,
  0x1820642113459c161054019105041808644180054817185821418542181c482121841117286021120402190c4c0160850112105421604486100858213044821800540111c6011028481100048013105d3100850214005811020484130c44a15105011208580164060217184c2180c44118144801120588160064216184c813105861640643121050a150064f134448a19005821924400140c40011005841420440140440016104c014084c0170c4441200583100c580150860019105c5113c581110058512105c0142050a18304001134401152444518105c311004821400645130c480130854112085c61410502171064510105c615084c112084c017085811,
  0x1144580160858512804481208507120858018085c0142864415184071204403150c4861220480190860712105c512085801708540131060410204c0192860110204c311005451018406151c4821200485110450112086411110643130448218186021600504133c447100c48211005c414084401310582191050a13185021904482180064215105811210502130448217184c41810505120040019005011038602132c40210085831200585120854013284c819305c21628541120c4401300440180448214004c410004411918502181058418044821604482161448c120c4491014440140858a16105c112104021000554114c4c214004c2130441013244801,
  0x150444214186031200543100c4c31134610160854016084c414184c21608402100c60018085811208501121048216005821700449170448219185431208400151448c1350580151c408160854013084c3110848819305021400542151860414205801414402120050815404c112086401500401181060019085401514482151040017084411708444111844012285441620640140044015005c41414444110451912206401708600162855419106401904408110c601100848811104801508444191854e1910504130060416085921908640140c48018084c01404442112050c19205811220500110c4c11208480180864512006421430545121044315005c21,
  0x100444e190860013144081210580190864a1410580141054214004c31210540160c44c14105ca1720642100c482120050711144c415105801508580131448e170c40c192860a15185831124584130060a1308640160c48413005c710004c5120050110304801908610161044113104c610045471110540100460015084c013105c21930582190054414085861410542103055414105061308545100c442182448015106011018583100050112105441404440171844813004c611044861420541112048018105c41008401160864419044c21500601110450216285d014005c2130448813006021604408100c442100860a132c4921308601102050415044411,
  0x1200556131054213004c4190c4c11210509101048d110c500100844f1530610181058a1720500140c48016084c51200503121044017084c01300408140c4801308644180448818006051100446160064b1304400125854415104c61714402131044017084c615085c0140858019206001508602100c487101c4c813104c2100c48210005c418106421408400130044b195c485110c603103058415085c11220500180860a131854413105c415284c2130050216305021310580150444714144421904482131064414304c4132c484120858712085441810500110844b12004c1110464a141064910004c81500503121048415005421904441145444015005c31,
  0x154440418104c9102458a1614480191054414085c7111044212304ca171040512104c21630582141c441170444812005041728510180860c112464112084c0181064219305c41314482180064b122064111104c41804442142c488191c48215304c110145c1100c5c31210644190060010044ca170044a11145881600508160844613005421104502191c4c2140448216004c81910600161c402122050418004c2131440410106471228583100840812084ca1928504182c40b130858013085c413005421704481102c48415005c312184c0110840514004411430609112c5021304482150054a17205c11210602116044a110c58a1504490150c40418006031,
  0x12104c3121060019085041800582130060b121440e1200504130854411044881520401160050213104cc142448e11045401308581110c54010005811200403123040019006081304489110c5c41910581120044814204c4141448014144821604484190c48a160064512044001228600130860112085801308401190c48414286441418588141c482160050c1000580160844618105c3120054912105c11208640181058710005c2110c54110184c112085061608580130858016084ca141050014084c41504482170064b13244801510400110c5c4131c441174051111085c41340540112c5421018583121054614084c013085c11208480130c44410105801,
  0x13105c3120050214044021024500190844415105c414144921308541120c406100c5021600403150040517004411710541124054b1240446101854013104031200484121444a140c48011104c2141860416104d01604400130c44013304c912005451004506140864417304c510044c4141060015205841300643121850312004c5123840114085c419084001110640180840418005c3110840217084c3101849017004d416184c110185ca130c4021610541100048017205c0140c409171444a131050c141064211045081518503120058312006011120604130864018104021900584132c484150c48618204c0100848014184431028588150440813104c11,
  0x120048a16106041834442160c48418005031000403160858016204c0190c4401608586100c5461128443190448215006411100480140850013205ca171c44119044801108585120860310184801908604130440816004c2131c4841810508161044519105801304440130c440150058414084c0190c480190c4c9110048a16305ca1310544112c54312005c818185821728400150860614384041310506180854614044401010440121048211004c415104c215044411510580130c405181060414044001024541120850c1724440120850a1600544140860015104c216004c3120050417085061910600110454010084c5120040213005441310584150c4801,
  0x13006041608542110c40213285c11220644181064018085011010486110c582141c447130040315005c4190c4c0130040117185c41510544141064f1300402180840112304801008404182858413084c016384d21408540180864019284401104646162058711206471208640151060211045c213004c4130850c14205c6180c480130864414005ce180444214044881404484160854c17085041900508160054215144001808505103058710084c3124064b11084401544409111058d120855112106431104502170c4401518600110050a15004451910405190c4c5110048218305481510504161864218105c7120854511006431304404130844110105831,
  0x14004c4180c4001424449180064310004031708540181440116305c310246011104646100c5801800440160064512084c413405841800608171448012105c512085c0110c484120058417084cc19144041504400182440216105821704402161850216184c01104601120848012084ca18104c018085ca194054011146441818402110c4021034600160858210044ce10005c013285821708402170864416005d211005c0161c4001404449130c4001104400130448413085c11208484161060c132448014084481118444100460417284c414144841304442110848017084c0170c481111c506182858418205c511104001508644181440613084ca17144441,
  0x1124601120848017104c3121064617084c112085861108442120864b13105c9112050e191860216404c112104c21604442161448618004421408582102040a190c480193850415005d11208604192c4801320640151060419144c21900544150c480160c48019086011030400130440113105441604482120444315085c111104c213044901228482151058616084c01808406151c440180064418085011208404140058310005881718542181050015085041300604150c440120850615105021404484141064a150c4801510643120c442160c4801510542140054512084c01628504141c44012304031304484100864113084c414004c2131440013085041,
  0x110844218005c2180050312444001308581110c50218185c9127c403130860712105c51208540130c481100c5c21378582170060011044c0140854111084c512006081330500113c50218306411000540173850013104c21604482122444113204c110105c2192c483104454110104c2140c4011908541111c544191050a14004c21418545120c44319005ce180448217184c3121050014104c5121048419144c2140c4421508546181c40019005431214400132054311084421900447101840013104c3112c4c213006051228602161054b120058413385401838600141054311184c4150044019005c419104021324441190c4c0130c492140864512106001,
  0x120048e11045421610601110458614706561914442170448213006441508640140c480182058a1718502181844517085061710403180c44e1310502161448015184001810581121054a16084c210205041300402140044116004c4150c440102060a190060217005c41308546134054a16105c2131054a14104421100504162854014105481400642104c50a13084c4160054210004401140488180448413404c41908581121064312005c71118445172440a1900544190c4c1121058216005421414400130850013106051208580180044317405c2180444412085c4100454312285c0110c480161058410085c416005c214004c21400648142858413044071,
  0x1600448114c64310105811208645131060414005c312105c0181440319205c01608546171060414004011500604181040410184011300510171060215284c4143065210005c419044c21814480181c4021708501101048213304c213105c013406041720501100850016885c3120440010044c41358542141858a142448c1208505121044013085cc1608405170844113005441420600170c480150840410185021038443191c40213084c1111064911104c31000580140860615244841914440161050310004c3100c440100c4c1121050410145c410084011210642191054d12085c417285501500642161860216004c418104081500507110044012105c31,
  0x16085c017084ca19285001408501120864614106441520501121048214106001708540181054b110c4c4191064e1618502150050217105c0180854016085c711084401714482170040010186041104642151060014285ca17104c5102048412005c213104d01810601100044213085431004501101c5841408646150c440140c4961228445120058415285081910405130448214105c5120050b1208481110c5821404446110040c140440012185431018508171860312004c2132441816286001508500130c44410244c417004c4170c48c1420582110c4c214284c7120444018105441828546140859616004dc152064511004821200583120050310005c21,
  0x1900644110854416005441510502181444016084c013285c4170c40915185c216285041600582160064215185c2144058413104c0100040918085c41900642160840318084c71208480181060413105c4190c4801210542190054415084c61808586160850a1918542160058218285011004604160444510084861800405110454011004411004542131064a14005491218589121050112085061320540182040511185031228401121c44b12105831000603100854219144c5125858310084c1101040b170054213185821514406121c44a100454e100044614084c014084c016104c416085801014502160040218004c2174864b13085811208540141448a1,
  0x10104061708500190c48a14106411200448161448812305c2192c4c6170854419044c813006421904485100c5441908500194050a170c4441610642101c4d11210506190854d110858618085441310641120854e110454a15005841614442130059419005091200482122440410046441508503100c442142c4841608541121064e10045021318604110044814085841810552140864111204901110580110c48016104ca1610504180c402100050511104401520580140440015005cf10006031000508191448416004c4130c4801708540192040611186431200642181040718084cb120048415104c41620440170c4861528580110c4c2150064815005421,
  0x150c4841500543120040417085cc14104c2131c48310005c4190c40014205461320546162844316184c2141444616084c61620640161054214184c21904487110044016205c0102c482151c48416084c014204c311084801130543100858011044c51204441134054013044021020480140858a16185c2151c403161058214285c5120050214005841918443170858112205cc14086441900502173050214144841404456150c44611084c613105c31000501101840015085001808606141058417085ca173c40814044411908600191444213304cf100840311044c0100c5c417044421300444191044215004091318403132840418104c4110058213305891,
  0x1318448153448212105841710546190858b1130601113050a150054512206401808601100848013104c21618644190c4c61918409140041313344821800649110448219044c8170045118105c214006011100486181058815186021710506150854112104c111004c6190854c160440013006491300503113058512085c01308500162060a1408401130c44014006441410602170050512385cc14085011220544151854216004431210540160c480190c48111104cf120044417085001920612172444918184c2160448e12144031104484130c480131058213004c21610401131054210045021004644180858111084c418186021800542131060011245401,
  0x19185d2110c50214184c81600543111064017085841704484123854110286041620600192440413005101420540162860a1520541122064111104cb120854015104c21610540180c441100c582160058219005c410104c6100060419244001700602160064218006021400582150444410104c219244021408580180045011044ca19144d018004c21710580111450a1310585120860418005c3110050a140c48412004c4151840818084ca16184c2170054414084c41800643132c400191058414085c111084c0170858c1708506160c480120c4501118502140058e15006421500602181c4491310582161050a102c5401014544103858619105c215305421,
  0x19206401704440131860216185c2151065014004ca162440410305041708500170c4801810502170064814305441508642100c485102454814284c4190064313006021810540191448415104c4130864a151050014004031118402132050c161050a1114604161c406120064a1420641122048c1210504179858614085131214401152c48011205c0140c48613085001308580150c44a141860414106041608640190840414104c416285c61608500132c481113464f1200502191c4c21824442171060b120854413104c51120402112854216184c312544011708540130864c19085891100580161040210446001928602144054414105c0140850415044821,
  0x170864b10104c6160c490173050512085c712144421010485100058215105c413104c71010441141c4821100484135844418106021300602181840315104c014085c4150448212006421618544150858013205401100440150050a150044114005ca170c4861420501100844416005c5100850416006411020582131c48417085461600449150040d18004c3120c401130c48a14104c014086001308501110850018184031210584130858410185c41508503110044414105c112104c0110455016004c110004c01908603100058112084c01428504150c486150c4051820541110850014084c014084c4160064e1400544190c4841200484142c48415084001,
  0x10144821210580190c4c0180c400120844612084c019105051028505124049015084cb10004c213185481510610151858214186041620641124050216286411320592100c643111044119086001010402111050e110464010105021600502131448612106451228608170448a190440210086501700504160440e13105041508641100450413144401308600140040d12005881648542191850213044421610402101c58413084021714488131c488111860f120048a111c4021408546191058217004c111004d2163854a14005021700645110458419005c4193850b100c50112285021860550132c44412084cc14084c013104c219044c2130054410044421,
  0x11046401420606172854b103854417005421928580192058110084c51210601120044c140440a10204c5120048711004801200446134050417606021510544181444413185c0100c54a101454b120848a18006411104501110064712085c014106021810448110c60f12004c81400644182448017085c01400443143c480141440314204c41304403162044115084c4190060419244c419005c8111044113084051504447130444213285001940602140054215104c7110c4c2160060a16085c11208604143044319005c413084c9101844012085c0160844112205401404442114844013005841608500151040913285841710540140854018205c410044841,
  0x121040313005441008400140854014084c71028402101860311004c31200503100054a182050617105c819144c7100454013105431204407191864512104821558586134040312004841208540102460b12004c5120854a111840a1428540100050110384c018086411030443102848814044001020587100840216044881900454140844118005c512104c51000401131064010344401114604110c64a1510647132c482131448615106041908602100040b121064112084901228400190044115005031010541120c404130058213105c1120440519144c510145c912005c91128446190c4c01608600191058414085c614084ca150064417085c014285801,
  0x102058112206041604488100448217004c219186431000582161054615144421100490130858418044c3101040012085d312105441608500100c54616585031218504160858417105441910502100c48219006451200400151854216185ca191c4001330448151058014085c01120407110844817084ce113058512405c7121058215305821504484180858a140448413244811124482120054418085c4101040d111050010245cb120860418005471100611130064414144881908441191440418144c416005d512305421900609120064110384c312004c710084841108441131058213005021500585120c44419044c4100c4c01510403180054213044441,
  0x12005c8132c48014085cb11185c512084861500447141858815044821918604182440a131c4021430443130448219144811108480150c487100c440103c640100c503111048013105c312184c21308401180448a15084c0140444410004c0182448010104c8160060818044c312184821710601100040213084c41514440100858018285c81910509102c44211044811110401160058213006411104480150858015204011500403113840112204511210406113c50015184061014444111850217006041800443120848014084c016085c11120504170449612104c11000404121c45314044421210580111064214106011228544102844014104c312006161,
  0x191850214005021410601120844013085c61620646183040115004c21544480130858112084c41400649120058b110848015044421010402121054616084c011245031008482154058c18085c0190c4c019105021510600190854017004001038413110448111045031200602100450213084401800588191448c17205401408504132c44017105021318451131c400160058e130c44e1508501120848411044c5120854112084c01614448150060414104441320584141c4821600585121444a1608640142448c15105c31]

theorem S0 : RAFrame.seg TB 10 99904221663074704013 63 10 15 14 99876372021712761067 D0 1000000 = true := by decide +kernel

def D1 : List ℕ := [
  0x121048612085401324400100c64011384001008405132840318044421700506101c506140864e1000515110058415004c214005431248543120040214104c311005c013206061114484190864811044801808606152c44213286001708602100450512005481730583120064513084c416004c2191050415004c51208500190864019184411300648185c4c1110c4c218005811000607131448418206041928600140c486162054015205401304401170840410145011240608160064e140065513185c41014602190448410145c2140444211306421000542160440f122c4431500508170060310105c0180044110104c1110c4c2191c442121850a13085ca1,
  0x143844614206411208640160c48016144821210480120044014006021900443192850415184c6102064912705ca1618588140044b1328504190440017144401310502153054214004c21500642171c40216004c4170858014085c4151054013204c41634482152858018206021004480190040211405001908640190040017005c21410441120848018044041008604142060a1708453170044912005c21918588130060416105c41908540140c48012085171140506152064b12104c41000403183064313044821800500110c4861108443180058512084c4101c496180c4c019144c81600502160058310004d1120850417285451018408120c44512185891,
  0x130060f13004c41624404102c582131c482140050219105041504485111c5471108600151058e191065014004c010085ce17004031100440100850d102044919105c41404488182850110105821500543122844a10045811114640184c401130c4801608506112464018086461724440120858016084c01610584182448a191040112084c4190c440140060811144ca151058112084c31108504192854413284c310005031200648161440f14006091210440182854a131448d100448216005421900503114050014084c112085c7122848418086041940400190864110205d0150044312005c3121040017084c7120850014104c2140448215004c111006001,
  0x13405031210540190858413104c416004001004582101c60511186451250584131058016105c217104c0161444212004841228544130040817086401104406131064113084c41918502140050211145d6140060111085441410506110064210045821004500190854014105c217044801100504191854213185031104403115860814006481000504150c48a13284ca142c4401208610170844c14006431000502180444717006011100504131060b1240504140065111044001110540171050512104821700502182c4851100489110048217185021718502101840511045411100440182c4c0142060a14005ca14085dd1204408180060f111054013104c21,
  0x171060014084c0171054216004c81908403140854c1714482120064417444821600604170c480130444217106081100402180040814004c0100c444183858712204cc1344480113458310004841200647103054018085411220441160850310004801308580130864415185c31200544130860014104c21700544153041f121054c130c48c16084c2100060014084c0140850019144c413104c213004c31200644140440010284c61708644140060414084c4150064513285401108444112c58213184ca130854413004c31218543120048415285c81928440120040213044821720442150854a182c480100864911084421810640160044015104c013206411,
  0x14004c214105041404441131c482131c4821508443121844a101040115204011728559122064712084c01810602150448218005491100583111864510084c61800447180054218005c21514480141060218004431710644190060510104011310546130864c1720506190040115105c112284ca190040114004d01718449120860a10144c61510507110050413004c81514480170c4491914448100040410005c4180c48c1708504190054214004c111004801910591120854013144811008447190050a130c48416185ce15005c2191058a1314440131054215185421000508180044319044101614482190060f1018482150448310004ce1310541110c6421,
  0x1430503110050711005c01428540110c58813184c21618603133c44017105c211204c413105c312004881328607124840210086001608540102840a14085451124645122042412185c215004c0110c54215104c310004c51200648191c40315105c21618584140854a1410580140c44a1114484151050015105c81744484190c440150058216105c414285c4103050312005441604442111048815285c4190448215344841314484121064b13084c712085d61810540110c60010244c3100460217106071308644140448417386001410502170064011184c01420640180c4ca13144861010582162c48414006481400449186440a150c444194058a16005021,
  0x13184ce18005421504403180864810044c61528540100c60419144c011044c01900407121860913105001314484121058219305d01400400194c48213004c91230442140044218104441104503121064414105011008480192850a141054011044c0132050617085c4150044413104c3121c406100458a190864419005c219305c2101064b130064210044821514440151060310004841810584140c400161448214004c710004041200494151440012085ca18005811004504140864a1600443191854218044821810640140c44019144c4132c484170044316105ca1510402140448215005841614402140448218105001808601120c406190c4c112104c21,
  0x1904404140858b12005cb100450d10044c0180844710045001508593120c44319044c2190060a1518441121048012086041800505121840712484841220606150855f12085cc130851c130440e181c40412085071208480160440b11045c4131448215044821330542151448012206011208500140850417084421540502191c4c01010445100454413044421400502132864512005c41410543121860111086031200482150064216106041504444130444014106041910601130c483101450512184831110640182050c113c504190448a1910543112850017086401908405123048213104d1120c44715406451000442140c40c120854d102050111084441,
  0x19044021504482130444218185c3100040412085c512305421704488191854e14285c416005021300502110454311284401300403142c48811044c21900544140850112105841820506190440c15106111304404144060313186081900544195c48b1004580140c44315005c417085c619086011208490130064512084c7123850111104cb12084c4150448e160841414104c218044c216005c21318503101064512305831010584161054016384c01410602140060312005c215305ca100844015004c415104451600442100840112085401314448140064a1010445150864014205cd1208480160c48a151854910105c0163c401110c544190c4c112184401,
  0x100840018105821704401181050414044821224451160041115085c0101464b12284c512385001328411140040317085011208540170040017185c2143040010144461310653101054217005841708504190444215005c510106491200603120c4061404401151c4841808644141040119105031210480162064016204c018085001808441140c48111044051258640140444010104c712085431000480130c480122050017084c01904406131448b1000643111454312004c31008405190058216184c81328580150850c100c546100c640181064a15004471500602181448012104c41008441120844c1114649120054213285c018044421908642110c4c21,
  0x10084061924406142440417004c415284ce1558580130844b14006081800504100c5401514448161840316084491608540191064f13185001054446100054016085cc17104c2150448214185421518500110064112106411038402170c4481308540140859014104ca131060614085821004600180860113084401110583123048e18285401714481110045c141060015085c41904482150c4421220487110864c1408640164044514084c7111044d1804490110844a1900508153054215184c3101848711004421108650190044f16205481104584101c4811108588100450e143040218106451300648161440016706081818543120064310185c312005051,
  0x1518443182c442111054015084c61708541100c5c91200544150c480150040113004c31200542171054112085c0140850614105831200482171448418005c2140058214004c413085c01310604185058a1400582183c44115084c110084ca1810441102854e18044011530542151060018004031810640100040114004091420504132c480113854c150c486131448111045c010085c1101c48414004c21404482171050019085c5121058111106031210644144060512144001208541110860416005851210604181058312004c31110442110850415104c312005051234441130858013085401738500161448a1318441101c443170c486141064313144471,
  0x15105451200442131044a18144c8151050110045861710645120848415285c6180c4c413005031230584190444611004dd12084471500443172c4c2130058610004c610205c01800441171c482191860511046411310643120c40210184081308501121064b12386461510502141c4821618500101c548101c6401408540191c446120844114284051400542190060513084c210005481000500141c402180858013084c112085c413004c310204081538617100444318085c41900503120050816006421818502165c480120850413004c2130064415085c6173860112104c11108504160858014085c6192854a1010643130054414204c112104ca18205061,
  0x10105c512085011038480183c40a180444f10104c112084c015505401920584140840715204011210440125048a12004431814480102c4c312106441728641120850a140058213044801000583102c442140c48019105071018645131064c140850110206041400504150c481100450011244c0160840011004821300500113458d120848616085001620543111850016084c616085c4191449017144c7123854416144801110642170448215004c21518542140c4001200483100c5c414005c312004c213005c816004c312006441510504110c604100040411004c4180c44015084461808407121051613285c5130c48612086001810609120054a17085cc1,
  0x100064a154064312105c0154054312005541914481100c6441414402120050312005021534480111040718186041608646172444619205101710640190c48613004001518583125444219286021518544191844312205c018205801314442133064312004c419085c01420512150440114086021004441122860010345c112085031100546130444e190858017144c2193054213044841200400161448a16004c213184c218044cb111c646180c416101064614085c614104cb120850614085cb100048216105c1123848012084d1120c442110854417005441608640100c4801220405137040113105021300502130448818105871208540190444c18144cd1,
  0x1110402130058413084c41700608191440019284431904483113440716184c215185c41608508100450014085401514482120844e18004151620601121064817005c2151050015105c110005c51200549110040419085001310550140844b18144c4171c4c21840607130c48416004c41408540130045b1424443161860210044821528585120840315084c6180c4861220406180c4c418044c810204081724408100850310005011000404120060e171448017205411208540190c4c6190c44013085801708447130c48418144841600403170064b13504c016085ca192864311005d019286001928548170060415085c018144c3120040218005c214106051,
  0x140c4811008640140850510005421718602170444218006031218650170c48f1104583120c4421610409150058011104411708407150050415085801338504142040a1020404110c600141064a1408545111854710104001300604160858015085cb1218642140060e170054a163854013084c110004401410407120848616085c1136860617004031700401121064017286021810580130854112084c0160c40616144821230504182860a160c48012085001510542151844f1018544182c48e132c48418606421930403110050215305421814486154058a1920640182050013085c01838405132860a1800542180444210104c013105421320443100850d1,
  0x140054214104c112104c21418581110844011104431838546172050c13084c112105c815004091630409170050216105401620600181448213185041408586160858d1200414102860214144801208484173050217185c21534482180054511084411010482134854512084c9111c542144858110084021210645120c401130854419005c414144401130544190058a152060415044421304444170040c180448815104c0191448210284c51110440160c4841518541100060618085c41600541103040a100048212005c0110c5841544484181040f131840b1414482121060a101c544130858014384c015044461310608110044517444c4151860415085401,
  0x1608501120444615144041810602110460416006041914402161850218005431200443121060016285831200600104c58413005031200549120048a17144c312105c7131058011084c31210586192850215044411700542192444013344881604408130054511104021618582134050619105021134548150840410044c017004011928407131058214305c41408604180058111384d015084c413104c5120060b13084c614405c4140c44013104c2172c40a19005891000504150c48617085801528542170064814305c51104645121854210045c5121050215004c512285831100584140850a1510504141040c10086461144515121051618044c416705421,
  0x14085841440445124048012085401504444110048412005821610513101048219084091900403140858014105c41808642110c4c2150058a1310502170058213105001308580180040017485041720604151448a12185c8141c4821410644142864016285c41508546170c48613086041418642174054417005c0100458416104c01410544140c488100c48217144c2100c50416284c213005d01408641121050312485021918644112c64910185c3120444210005c511105cb1308585100840014004c215185821600595111058a101848415284c211044861314449100c646160044019044c2161448012084c0141058312004c214104c0170844512004041,
  0x150c400120840415005451220640182c4ca140c40613084c016085c419185091108442162054512106011210508143444916205011208496161064c1108582100c60219186421728600150864c19244ca151058413104c013144821418502160064913004cf1210442110c64218044431904440190060215106401408506111044519105c21014580162844a140850c154051411044821304488171c4841500440130054010005001610582181c4421730582153844217085041528540131059b101844215185841308500170c480171054214005c312105c11328405160850416004c2190050214044461100606150044712185421900645131448a130c4061,
  0x170050310006431310500132c41615085c0180044410085cc1714401190448310004c4195860a180c4c016104c41824484170064c1004504113448414084c112285c11118504140448818084411530506103c482140061111084801410604111460a14085c617205401408500130c48014105441320507121c400120048214104cc16004011218608191448013084c414104c410144861508600110854017085c4171040016104c21610641120860112204471314484170c4c910004c4151440a1718443141c4841520640150854112104c213005021710586100c48415184c21410607130850b1210480190858a1104403130c4481240502101858213006101,
  0x1024440132054a180058218044c51104480141c44014106401510444190c40415104c1120c4061208547120848011105c512085c010144c214006491200502141044c1508582111c54019285821600401111044214144041108604140064417085d113044841404402142c484151054e190448a14085c511005c51310500100c504143844b140058a130850d1108480150040610144c01714488121054017144421208400173044010044801528502161858e1848502162c404163c40214285881300604161054a1314442190448213105401608600100c646171050813105c0180c4c61314488130050e1618603130448311106001608400142064617144ce1,
  0x113448a1210542133440216185c9130448417085c21118586150c48412044411810506150860512004c510084821104491100c54013105c312004c21800646100c5c215444841400503111858415086061914482161858110005001708601113040014005561510542150c406141064113084c41700544170850019104431500605122060619085461808640140040119144c017105d112084c1121058e101c44416085001300402130040017005881410546131c40011144c4130054211146441600543121854216005c211044821308443175054616084c013085c71234401160850013085411210482180054512085861910502160040f121050b12006051,
  0x1808580140c484170058413084c014084c416004c4140858018144c310084401318610170c4001008480190044114006421600582190040b192c50215105821108480101448a1308540190c4861518401120048e19186421604402191c402121060016204411408506190440012004cb1114400101848c14084cc18205811210584131060815185c218044c213304451304443100c48218044821210500151064211044c4190c4c0130040010006411008583100044315106411324444173c402130858310205c31200601100848814184c91258546160850e1100442113c6441510403150054414104c214006421500602152044913085c1131050213185c21,
  0x111060814005c2181860418444081210601132c4421318644161064314184c219005441308540161054e1928607130858010144c0111c540190045012105ca1610502160060010045c810046041618544181444010004c71200400131060417044081400509110058214106011000441151050310005c014085011004600150c48012105421014642100448111104c2150444217084031710504191450214104c0140c48618184011228501120850510005821300642161448614285091200441100850a15384c111045811108584151064112205441304488140c445140064218006031300502133844314084c018144821410640100c50a130064215305d01,
  0x160864419144c413585c113106451328502170c447100048e140058011045461324481101050414144421410610191450013085861510643131444012204cc102460615284d2111c50c170040e100c4841514480120858016085cd1220601120850014085871008500151c400120050510205c712085861720580184c407170861019185861004500150040713006021404482101450015085c614084c0170c4c0150844414084021618409121060a1704454120864c17085041344484181850310004c81800503100044910185c411145c912185c214004c217106041804482140054a13084c1121048711184861810644180044712184c418085c1121058b1,
  0x121060313005c3131058a180064417085c51200488140064211045c2150c44013044441508587100c64314584c6140854111085401814482170050610044411308600190864a16005c218144c0181054213284c0170864513105861940544160858c19085c017085041804402150440a14105451000406133440215185ca18044411910640100c5401100544140050e14485421510640151c44211085821004500160c4c4103454911004441910602143c40617044c5121064a1608606140858713104c611084d11208480124050217144061208547110c405142058014204c41600548150060313104c0140854015104c4180840519005421400502172c4461,
  0x101054512106001510602180051a1700609120048212005021910647140c480150c412163850415105811310643100044e1200444180864010244c415005801004446140850a1800502140054217005111208484192c4cc1508441122060d121064b1308603111c602171065310285c2152850417285071208580162c4441308544171064017085c0140858418005841408504181c486110054613084c61420440120050816204001010642110448c1414484160c481111c601130864015244861240642180064217144431414404141060112284c4150044317085c6140858d110858311006051240600103c54d1210642160060215104cc16085c112206411,
  0x15084c010144821310544191c48e141448415184ce1404402184044b10184c3122444010104c0180c446180c4c01910603131050112085c0170444211004421014504100c540170864415004c8130058216005841708580171058313004c711046011008402132855112104471944502152858310005cc192c504170c4c1100848413004c2151858b111044110045881818596110c4861538644171c48417085c2100448a141448013085401420647110454413144841200488140c408160850418005ca160c440130c4801310502130060312104cd120848016244801208540100c54613086011208480165c456131060216105c01014502140844117005021,
  0x12184c41820451151c4441308400161c442162c402121861710085471120440131060219005ce19005c41510444111044f18044011610582100454112084411820502100c4c1110850f12005501308580100c58010206411320500163c452100864419105c418144901618503121054110284c215244001810441130854110104c5100c64111086041508401190040112006451408400110044218044c6100c482101454014084451218608160c442191c442171060219044c31018644192c48511104cb113044312085c11324481113460511004831010443101c54310004811004503110c5c0172054615085c616105c913105811210602150064514084c01,
  0x130054215005c512085441004482171c4c310185c31248643130050910184ce130844112186001124502161060014085001320540110c500130c48012585c21418587110054015104c4100c601121840a110c600100c5c2170054011085831300443141c48212006441710548150054417444c213005c5121064b130444619145001904440181050018286481804440112844217085841410540160c48014304411744484172c48111084401610585120040019105c0161c4081310554160c4401100642161044113084c0151054312004c3120048a12104c2130448215006041508584193040911006441108441160c4c418184091904490140c44019105c31,
  0x1934549111c48216186611200611120c44211004401934440140050b10084001020480181448511086401708500132c40a141044314105051214444131448a15084011900642161060018085c014085c311004841210600142050417005c512085c111105c11060640190c4c41300508190440812105c112104c414105081600585100854c190c48616085401810543121045610045c21520440111464410044c7110054a1918648191060017144c21510401120858017105441408600181044314004c5122048b11304861148446140850014244001220584171050619105ca141044312304c2150060912185c5130854413005041808506191044312184821,
  0x180860b130448413085c113104c3111044010084c4192c5001610503100040711006451100643122850413285401338585120440413084c110046051308401151064113084c512005c3130064311104c1122850a10244c01908640100040112184841428544150864a170844118605c2180064510084c4151850a151c4001600608180444218005481410604161864f1200484170850b11104c01408404101448a1610500133040116144801810640100c5011124480110c5441308581120840a101064111104c910104c4111c544110844b1410605120064311384401800643134448612285c5121060219045421408442130c4801318441150064511085841,
  0x1304482171854312185041620646110c540132058c17285441410643111864312584811008580181044010084801208581120c400140c4811004442111c4811000440121060512004051710642162858a18044c813005091218488110054215044841218400161c4081318645140440019104401838546181c400152c48019085c6150858110105c312005c312006461004505110054214144401810443181c4821700440121054311005c311004c0100044112685441400585111841711084441904408112c50a11146451310502180444210304821110600112c4ce17044c218185cb1308500130044614185891228584160050414084c018085c5130044a1,
  0x140c44c1508540140c48013184411200502151c488121c44218005c510084811008584191c4021730608180448211004c4165c4ca1728602184c49013085441504482121048613004031810502140054418004031320540103c584170058912004041408540151054311006031314484180054218106011308606191c4401400504142044b14005451000400133448e15104c6170850011144ce130448412285031130602171c442141058210044c017144c91118541110864313005c0111c50a14144801644488134054510304c11018601120848015104c814004c311105871220505105455614005021440405191c5101808505110048212185c2101c6031,
  0x1804482130050312004021900402160060111085c2171c4c81610445121064115205871208641150858014084c014384c110105c313284c41600502184858313005421504482130058417105821410500180c4c2110c582150064511244151504444160c4c010086401124547100c4421020406100058512185051028502190c4021310584171440a143864113285451210486112454b12085001510602100444215104c01408540154054214005421310540170c480170040c181858a173c40112044401834482180054110384881414403111848111085001414441100058510004c81500605121c40115584c21710500180864a1114498101448a131c4421,
  0x1744484180444910145c9120048419204041000643100050815044881300508140c4401814404102444519144c11110448170444a130c48211045c019685c0100c4c41448405171064216044c51208586180844119086001448401190064b13204c1122048012084c1120864710085ca150050215105cc18085001508581131c4001400604161050e18044041054604112448014084c0192060311104401604482160840115005c21418502150448417085c016085441000650160c4841800501100850312004c2160c402170854311004841418643150844014004c312004c512244051508580190c5001800442180c48614086041714480152858912005021,
  0x120444819145051200544151055018086081104500130850415344441308581122850214006031114644180c4ca192c5471208587100840010205841804490150864113586091300642191058c140c4811128442191c5041408580170858712284841310583130448e16306021818594180448214005451120486180860014085c8110c402195c486160850414006051308546190c4c617085c01508582100044011104411004440120848015104c81114486140444510045c219044c413085011210608170c400121858b121c40014005ca141044319005c11018480170c44b10084001128580140850013084cc140864616106431318608160040210045c21,
  0x191454a143044112006051210584142050111286421704482140050214006441608500150854c1520545100048a1208500131c44011004021410546182c4c211044c213005cc114c641140854419145461814488161050b121054112285431128448100c5c41820580110c54416186431348591121c4461810540180c4c112105021620449131440219044811020484171844118005021700449181c4c5112c4011628440140860113086001608546190c44017285c216084411200645130854111104821328606170c48c1220606160c406170c48015204c616385431018646170860a1910600170c4c4132c40012086001024600144058214185c313044481,
  0x15085c0190c4841630544170c4c41700500110c5041318441100448214044401118404100040e190454213005c6110c4c31244450130444212104c0151448813144491400642181c484130850013084c016004011300580100044014184c010045421004542100454c131058b134840017044c1101848014144021610600190c4c311086051008601120860419185c21414481112464912004c21600642162c48018144c61004541120854018105081410407172c4c21808403180c44b14084c01840500111840410005021518648110040a100050216586001808600191c402130860b12005c5121c4001228480140850015085ca1000455130c44011104801,
  0x15004051714442140064315286051358544191c483110054312105c61508500180844119244c51000643120440e140440419184421708600160c48d1008500190c48013104c213186431400586100044115105021630403112044016185c312005c216344941510540101c4401200540110c40219185c5122444c130850310205021400608150c40212085441418644191450219006451308580180861112404ae131c44a11084c0180854c190c506130850112085c1110c64314044421710506170c4c0173440912205c41810500181c4401818504160850a15004c2144864511105c21500544130c48413105cc101048a16005c4184444413084c416044841,
  0x17485c419105c219185c51308644100458214005431210440171058211344ca170860a14005c219286001608441130844b1010481101444212005041328645151060510284c21820402121c40313084c613105421304486100450614084c0100c540160850413044841810508161044718144c312104801414484112065312084c013204c61620540181c40212585c215185c2161060710045471004586170c4801810540100458016144821518502134850216244461300584180c48418005c2172c4c013284c813005c110085c215605081418585120c40c13044401518542160050215104471508606150850a160040210004961300403121064017004411,
  0x150448215185c2141860a191058513085cc10445401104545120048417285c2151c484180c40412185c41508441100c44b18105031110643110044c190844211045041900584180040f1404442140854013105c2160050a18144c41808580170c44413106001414480100c60312004c2130064f1100642111448013084c1101c44116085c014086001804400120050512104c81418603121c44110004c712085c01800409190c480120040717005421500642101450210004071208482100448210004011300441121844611245821500589121058017144c4140440215085c016105821618582140c400120050110045081410604110464211044c217185c21,
  0x1410401140c44614105c2151064512105c417005c3121858210044ce140444213144901628646110c4c0150c48a18044c9111058017084411508506163c4c61708546131064911186431228480165c4c4141050a140c480100c48614084c01820547122848212004c81300503110050a112044117244c414004c4160440b110050015084c4144060411044811000580180860111084861608540161058214004c2131448013105c3123054312005c418085c210044c11208542100c5c4182448419144881000604114460510185c1112050512084801338601120c404100840817244401108440111054b12085c11320641130c48016205c5111850312005821,
  0x180058313005c417205c112085501400645131050213005821700402191044515004c8150c4411714442101054013405c81504404143c400100848018144c5121050215004c21104643130c4401218585131040319006021608401173840317004091820544180050312284c41910647150c48012105c5131054a1610603132858c110c544140058416086011010485100044215144001008544180864311004c0141840114004441500443120850013086451508401130060419206451418542150448212005821024440132c44016144821914500190c4841414480181449017244c017004471214400160c480171054215005c4100c4c017144c312004881,
  0x1800600110c488190040b1914502160060a1538401170c48615244c41000402182c48415044c21500542141c4041920445141c4841208641110c40417005c51308580140854018106421600642190448217084011164604192c4821728504170050410bc4901408600152c4d11210582180448216044c2130064512084c61808580160c48012284c11000641150c480110c54112085cd130c446151448212005c5130c4801200441151860414085c11210480100c502150058411004431708405120048414085cb113048216144001120441160858d130850616144c31200488110844113005c414105421700549131850a11105031210500151044a101448e1,
  0x12284c312004cd111848015144c214005c313186421608441100448a1220604180051a15286401620441190c4c01808640190858113385c6150c4901230600110c5c31300545120c40c101048214104c015184491408600101458216005c31230502151c4821910445181050712284c21304482130840611046011014447141448a141c44211105c8161054019105c81518543120050a17106441708540150854310045d4152040118044c21410600162c48010045021110441151c4c0100449612184821210501120850416005091204440100058c1810643101058019105831300504141c40010004ca16085c51000544165050617205c0150c48111105821,
  0x11086431328580191060215144c015204471210582171064311204a212086001710584192440013085011220644181c4ce1800505100848414444841414444171064c190c400150c40013084c4152c4c0150c4c11108486152864b1310645122054615144421700504170858c180c48613284091300502161858311004c21804482190448814044941900649121064a19244401534402161c48710004c21108484120444a13144011400442161060014405c312005c4170c4821004504192c4c0171448a1314482170444e1600643120048414105011000486130c48017085c3100848415044021308540162060112085c0170854a1840604150844010184801,
  0x130449417044c814305c313404001014504150c4c0150860410145c0160c4cc130864417285c6170854713104c213004491410647130c40711084c7110c40415185441850600140c480190c4c01804440111044112004421014603120050e1804485110860016106001034480130854019145041410602167054c17144c0100050c180c48419045471000580170c48416006021904404151058b132050b121c44011184c018004411300640100c4c51208644182c484130448a122050613385c6160c48a123048413205c1130c484151c4d017144c110085c5120850a14184c8161c4c41408580150854512005051208501120854a191c4821900405190c4831,
  0x110c5541020442110050b1208406100c48012084c417044c3110c4c4180c44012284c416006051208404112c403111c5d0180c4c4191c4c214186041114402171058016244c01424404161060a17144c512004821310640101040010104011100542151858312185c313104c014104c6100458c10145821800402160050415105c8154449214104c2110c4021008480190c581121058711085851000444111c544170c4001400588181c4c21908403171840d16144c21104604142c484171444012084c614085d017044c2151040513004c4130864a181054016144c21418502113040012084c71210644180850015004411804482160444211104c112085451,
  0x152060a14304c214005021630584150c484190844116285801914544100c5c112105c2150058819006451020400170c484182c4041814400170c409113048111084041230548180440212285c512004cf1218584151440113104c011144c8141860814186441808641130858617105c81800405191844112104c111206411120585130844115105c110105421500502161854b10384801710542161058d12084c61604400110c405143064417086421004594100c60b1250500134c440140448417085801700401131444110044841720400170054e111464112085c113205c513144041200581100050811004471824480190c40a17006451420601130c4011,
  0x13005851308540171058f1200555134058112206041428405181054018004471300604141050313005c9112860a1710641151050216044c41408606171064316105811308580160044212044421310589110050a18204031410643160044412104c712086101704484110c484191c4c21314445150040115044c417004431338580162860417105c5111844013106011210440111c6461728584150c484130c40017485821800644190c5061810443170c442180854c140858e100464418044ca141060419444421318501110058512005d018484021428542153444211284401110642190060b1208484122c40418144001608581121060a1810540110c50a1,
  0x1208404192c4801210511130858616105431314400176c4441500545130c404142c48012205c015085421014442130c48a15105011308544151060b1110440141040319105c6143850a1714480101064a18085811308585132858a110440219044821400502152440e170c4c71208481100850014085c7120c44c160c483101c5c215005851208646170c4c3110054112084c41648604155044119086411330400171c44813005c2191c50310005021404482130050512106021400502160060217144c4130c44611004881]

theorem S1 : RAFrame.seg TB 10 99932062828104475117 63 10 15 14 99904221663074704013 D1 1000000 = true := by decide +kernel

def D2 : List ℕ := [
  0x140c4ca1614484181444a14044c41608540140860b1200484170c40015144c41524444111050a16004051348401181c484131444215285451200405150044118105811300407120058814044c4162054015144ce130c40212284c8182c4c01434400141c4c21308449140854a1848542140c440130448a17244c2110460416044cb11084801410643131860217185c2191044115144c11128440130448812104c4153054a160440c181448418044821728546171058216305821848544160c4c31020643113060811044c21304494130060414105431300585132044013384011920441162054712105841528503121058017085441810600171058219144401,
  0x130854a1624440122c400120858d13084c0150c48413105811208481100849c1910441121064211045c3120048412204ca1730502162044f18184061114606100c4c01700401152c480110c5c71310406100840b120848616144d6150c480151440216005441708601130c440120854a1700649130844d1348542152860113206401814442133054312005c21914500150c44415005db1100580100c4821914580190c4c0190c440130c4041010648110c5c81514400130440010005c111006411208582110460016585c219005c21500544141448212185431210400110c506180858019144c218144c01608580101844913084c0102064017105c8151858a1,
  0x1010600180c4c112104d11208546181060310005451000440163050215044c0110840c140854018085451218444152c484150040d160040b1308546140c4411004440180c4821004600190c50112205c4191c4401020448130448215185c0111c4801708505131060a160054510085831000581100854b1218604190c48015085811308544111448c1508500150c48c140860112004011800502140844117005851110502141864514286421800444110c50712084801224400151c40011044ca13085441120442140c446140064514184491508582110454112085cc190c5461508604150058218004451408540100c6471204440151c482190448418086011,
  0x1410645161054417005d01808640170c400190c506150c4801708442110c5c81710509111c408111858211045131208500180c500160c4cc100c540171040312004c2134840317084011200484123848014105c2155c4c1120848013085c71008541130858019105ca110c547100848c16085c710104c21718602160c401140854014144c8190c456110c4011100580102c440101464211045c11308542100c503131060a1400643121054017144c41610583120044216105c0170440013304c110005431104404161064411145c0162448616205cc1708641110858311004c415044821210480141448217144801608604150050312105c419044ca13105031,
  0x18105c31200645150c49015044c4160c4801208480141448213005c911186031210440180c484141050c160c40915185c2150050312104c41828647140864018145041408541110858c160c4c41914540140c4c01400409121c442184450818105c01914542141c402121c401110860913006041510606111c480160850417006421904442181c443120058414085c2101c4c018145091200505120844210045041610604101c482151c44214044c4131050912184c418184411718548180c40216206011408540190844010406411210505121048e19285c0160c4c0140854016106451320607120444213085c015085c01908401172c483110054217144841,
  0x14044c810005411104400190c40a18144041310604192c4841904505103860a192c4801310445160c40811004ca191c50217006431548503120054e16185c4191458b1208645140840917105c0110c4d61414442111854217044c2130050e180c402123c44017144c312004c81910641130c48310085c5111044c11205c417644401510500173c4c5120440112005c4142854312005021730658100c4c3121848213004c512085c015084411308546150850014244c414044c4160850417005831218642171060416144cd122060113085001710502141c48215185081928600170c48419144c61510403143448213004c2131c44418206411210502161858a1,
  0x100444c161054a172864a190844411084c1120850311005001508580180864112085c0140c4c1100854510105cd1208647150c480191454010044c0162060415105c0155850819045421800603130840719045c81400641101c4e216186051408641100c44210006411210548141c403110040217005831300502190440a180c500150c4801314401140050312004c4140c486130860b14144841904503110058f13186431630542141c484140c4c01410651170c44019044001510580142858a190c48310006011208606190c5401114484110c58416044c217005c2171851410045831310580110c60713285441404440121048a180064011044c015086451,
  0x110844112204c0130c444121048014444c3103048812005031204447171058710106511408541121048218005c0110844417044c4140858111085001014503130060e1910641122444018145041800401130050219106011108501121444010006001710647100840214044c510085011328605100864018405da14044c4140860911184ca150050215105c4170060417085871308581110864515144d912105c3130448212104901804442112850410105431000441180860017085c0163c446183c48411304c417085851300604181c4021404400130058111186001524480181058214344851110489110044211105c414304051808601140c4d511184c01,
  0x16044c4130858418045081400442112844116105c1110854217044121100581100848014405421710603112040e160c442170855312084881104480160c4c01310544160c440160c4801010443160064515205c018144c213585c2111c4c5120054313004d418044401108543120c4021308604191c4c2161c4401018600171064b170858411044821610601121064b1508586140040a100c5481914581121058a190c48617285c913185041400441130448e19044c5110840c1520640190c5c310086431600542141440419044c4192c5c3120054513284c2181450113284c51108484182c4c11208504182c4c0100044119004061108486122050014205001,
  0x1300542161860a180c4ce110440015144561724406160c444191448413005021710541120848614144021630580110c484150c40a1200643133448219045c216084031500442110c60211045441900403181444613085801920641130c4851104405110840a15285c41408500170c484111044513006011130484190c408160c48013104c31230542160444213005421430542171c48418084011704445170840114044c0100c640102448a15085051300542141c440110054017385c416044c512085c1131449510105011210603140059112084c4180058218044c8161040114105441714482121060113085c016144c216005421800443131054414044821,
  0x150858b13005881120484130860416344481200484170c4c71008586160c446142060110105c51210445190c4c018106421800584192c4c21410500160044313085c4151050418044c2183058218186451208541130c480183040715405c511104c2101850512005081400449151058619086411020505121864819044c215204431420580180c4c0152064715386021124502171058112085c419044c511385441404484190c4c8100c48213285821024603150448e17005031000504160861e16105051308641170850a1600604191c407110044610084c310184841108400120050e1710640180c5441428401170854a1520443170c48c140854016144821,
  0x10384401240401160858010085c712105c312005c3130050416105431300605155c400111c6411008544191c40e17145001508584174c40412104c213184c813005071100646190c4c019286421910601150850a162858019444841720581130040113005c51228404180440111105c11028488131044b120c403101c448140c44c140850018105c31218605121440d101c542152860418144c019144c216044c011044921508540170860512184c218005841908607130c4431700502191448019004561104486171448217005c2171064112105821914500151c40013104cc170c48a160444219145011310504190c4c4101c4841704442140c486130840d1,
  0x1110546100c54b120064819045481504482174450a1904482164858b12204801850600160c4c416005c21710583110440012104431508444110c543121c40319145841508544180840116344ca150c44017085c01710544180c48418006021104503120040510085c114105421504482130060512105c4150c48419344421300504142c4c2150044918005c21610641140854018085c1140c48c1610600100450713144881904542194c506103c4c0100c64513084c017106431100588111c4c91228492191450e17105c018144891008441130c408120848615085061710602190c4411210647120848617285ca161064f111044012105c4191448216405801,
  0x1200403161054010244011820400172c442101858b1308600111440213144491914501102044a12005821408443131058a151050e1804402140444417004411610500150855112004c2131060113144821610500141060211044c218044811108484191454211446011300449100858a18005c314185041414408195c48018144021300651151c408132060113086021008480110c58f1114401150c48418044c01054504150850211044c41308401120058818005c41500400150054817044881744511111048510184c2142c4841728600191458a1508506171060913144841804543131864011084c712085c311185ca151054b12184841808645162c4441,
  0x11045801408500171444417145021804484170c480140c400130854113084c710105c211344821618443171450019244c510105c4190064918286051410445161c44412204c414044841618443181040314106411620611120840f1510502150058e11044c21510581120848612085411308500140c4c1120860513285011100400120048213005c51320600170c4c1120858410084831100643152c4c21004405190064e1100486130858a19045891220400110c407103c4081914503101c442140065116085cc16086011304406130448a15085c310004c510006041628542161440012084c417185c217005c4190864518105871328584161064111006451,
  0x15286451210582141c4c21500605122054c1620580190c609110850217005c21500544140c4c01414448181c544170c40613105ce17005431000505100c540101c58418005c218044c4130040116044c61004542100c5cb1108500102c542161060417305821400643110060510404c2140060510104c813006451408500190c44113085011010590170440017005c5120850015085461800443180c4ca13044801044401190460f1104482102c6101630510180c5061904454142444414106071410508192c4c01410501100048c120440710005871008643120048415085011108440161448213004481004403150c44613306431314440132058c15084021,
  0x1210580150840d1608581120864b18006071100641120840710104c312404c017244891100604160050b100c400110c6051000544160c4d219145821900400121054313185c3141c4c3110054313004c010045801814542151858611044c01408587111054816044821704405120854711045c5123440419144c41114504185c54312106411408601130860418106411408501122850214344c2171060512004c21334484160c4801408500150854112286431118482191c510190c50018144c8180c402180c4c3100860011044801210502152864111105441520601131060310185c0111044f13285041814543120048412085c419044c21004484140c4801,
  0x13305461104412110064914044c216005021410500151054a150c484120050913004c011504c415585ca190c503110840415086471000440141c482160050216004441110580150858c160c4c0140c4821000445161064116206471714542191c4c213004c4100c50016206411008641150860311006011510504180c50113105c312005051020580150c490133c402120c443181c54216285c61808580140c48416006561900441190c44510145c113004401904580101c616101c5cb130c48b1110640192c48213044841420641182448c170444110005821600603100444011045071020448166064511086021104645133054312105871310502142c4841,
  0x19144c112085801610545121054b132058d13384c6140c4c1121054214044821200482110454219145011208544151058112085ca191454a190440218005c2161440011086411708600170c541130858111405451128549114848a166858015105c31218546100454c16145021840641131060218286421110482180448413044081108502111c4c1125c40e1600588180440110005011320445181454414044c0100449610146011200413121048413286411708645141c44011005c7110850c150c484101448a180450214044c51224400161044316005421514400130440110005841508540181058011304531508445141c4c813106011310542180448e1,
  0x13005c312104c411045821804507110850e18005c81600603120064f1720441180058311104401410504180844b100064313104c419045081804404130864510184c8131c407111448412044031504442171840112004821400651160860114144c4100c64112084501710641161054710005c4192c58513044821810584180c4031004403102c402120054215005081440640192458112105081608401100454c10045c011145861004541130c4801208480160c4441220440191c50513085871230403130850113104ca171450312005c31210644191c543122c44310004441814505131054d12085c01724500100c641140c4801208441120844113105421,
  0x13104031804584110c60116244c112105c2100448215405441804484101445011105c3130440819044c011046451204403111864915044021314487102058b13305c4170c480140c481100c401100c64318005c315044841624480160444613005c3120840d181c502140044313185431210641150440c140044b1020601135c416141064911185c21710601120864d180858016244c310204c41800404121060610046041618643171c4c3114858419244d21710582190458216105c51400503110048219144801820644110844113004c413084cc160c403100848310004c512085031000540170c44012085d312205c0190c50416285c0181448414085451,
  0x1710600186c4c51230514153054513086451630584160c50018144c9120048814344821440580193c541111050f10005431018544180044312144041900448111854313104cc1408644191c4841318400113454216186031418602171448013085c1150c4c0161444a1404444110854216345021600443191864511104cb122850414144421430542141c482151858417044401318542161c50312104c6180c58015105c31230642192c582100c484190c4c014105421904502160058911284c61308605120048415085c9100060c190c446160c48412004c3101050016245061414482121048415044821300502170058312104841700643161444013084c61,
  0x160c5011210643180450f120844117044c41710643141064516445011308580160c54417044c5120c44411105c01600441170440417144c312004c417206011624480170c40419204421100441171064115085c112085c6190c54411645c4190c58112044461414480161058b1420600102450417105cb13105461440503123048217044c41610643130448412144011000480192c585130c480151440214105441804482170840115005c0111c48c140850113104c4170c4c419045041500409162860512086471108601160c4801610542110c4001400603100054215005c3111048c150c48013084c016206011510602181040510345cb133858114004411,
  0x190844118386461014484140c4d016305c9151064713084c0110044117006031004482101440414044041508581131448a15044461110607121054011085c2111c5021404488130c4421308606170444014144c11228610193c480120850c142444c192c5831200584170c48a151864b160c500180c4c4182c484151864011045431000540141050a140850019244c01314482191c48e130c402170c44019004011710600170040115344841320546162065112006431614480170c4c016144421510543110058112085c6162c4c91000583150c402150c4c41804589102854019145021800442110861b120064310004c219384491510549120064312105c61,
  0x101454815185021710640100c4841200482120049a18044c21600643130c440191c5041900443150044710184881310600180c50015144821418440100854614105431030483112860b1000549132c482111c5401400407151054111105481400544170c5401600401130058e1600403152c4c0182458112105c312005041508500142858513085c4161c4821318502160c44013006031410506152c4c51210443181451016045021404442181064514285811210482121050414044c217144c6180c54712084c4181060112084ca18045031228505120c402190c4c0130c480192c58f10006031010601160c544181c4c21900405190c484160448a13085c01,
  0x13084c0190c5c712085011324480190845119444c31130547121048c110c5c31200582171c4c510084c01308580170c501130864514144c11008504142c4c0161440a1308611160064b12104c214105c0170444c1400409181044518044ce18044801004541131054a16145021604503130064b1520641160c484130448815044c51204402121c40e15205071008486153c48419045d112084c019145801108480160860115144c213004c2151c48813005c515004031724486151840510044821034401140c4ca15105011318401132044113185431210500171450312105c91028440121850215006431804485110040216406451210543120054416085c01,
  0x1438541132060c180044313084c111285431228647130850017085c01908641130c44a18344051308541122058a19044c310005441404442150444016105c5131058112105831414444124c442161064512004431914540102c544100440211105851100502170450211145011308584170c4401200645180c48417106451530508161c48412206491014402140c4c4181c58315005011000581102051310085001450508100848616206411508542100c60f14344421508403180c4c211045c514084091218407130840912084d0151850417084481264446181c4c219145041600591140c406170c4841318507100060310044001308541131448415085411,
  0x1300449150854d130854c15085841904509131c480110458b1470407120840512305c312184841810443161058112105c2192c4c4161c548151858315044c4150c4c110284c21904603130064915144cb120049a1410645174458112105ca1708447180c5811328642192444019084051100646191458f130054214005c5140c48413104c0130c480110c4c418184401128401102c40612004c417244401508547120440111144c213144461408546170c492120844114144d112104c512084c016405c2170454312004821600643180c4021914483111848217004411018540180860310084c21704504180c4801508586162044116105c3121c44011005001,
  0x144054f14044ce151c482121050a151c488120060b131040512085c5120054611044c0160c4861208500161060818144841704408181c5c31500643110041a1400543130440a13004411304405100c406160040213044881300400122050211045401510502150448a12085001808441180c58418045c4181448a184458313044021600643181448f10005431108482191c4c3123048e16344c110085481700603111048018004041208647141064610044841504488191444c16105c3131044411044c21608443180c580160c484192c50a140c406151c482170064515085051310504150051713085c513285051010601170c4431000484182c54a16044c41,
  0x151844415144c4180c50a16044841714583141040715084411308582116c5831400405161060218044c3120048210104cd121440816005831100444160c485101860e11004461010484170c54a16105871238645170840316085d313106021914500190444018345051208642100c603150448215105c11458405190c5c112104041944515111850710004c014285061108645180441a1800441130050d101440012005c316044c414144c3121064d150c440182060d14244ca16044c4140c48c130c48013105801004500184448e1200582101448410006091234442141448016085801124584190450512084831008448191c6021104508163450512085411,
  0x191064517085c01908401192c4c21704488103460410145c312004031918403132c446182c54b1308605143064518044401400583121048a151c50313285001508541132050511285411208480160c407100850014085c4181c5c51208642100c4ce15106011228643150448416085c51300643160448410184411808401150840113105c511005cf13004c4163860d1404402130860116144c1100854514105831204404150440015006431420401100c4411308405113c482160450810004401720407180c480120854713004031310500100c5011000543110850419146031508441191440619086411208580170c58419084411400445141058219344c21,
  0x10005841014643153058219044c81914540172448c12084c61320580100c500173c4801208500170c506160444213085c1102060112084c110084c6160c480132050510304c21304488171c4c2191c603120064b180c5c51210582100450c163040119145c1160c4401808601122050418044c211044c414285c010244c216044461020445122060a1918640110c5831148444191458f14044c91210600110040a1410547110850419044471200600110c4c2112c601111054711005c311005c5141854210145001700441191c5031270500161450210044c41308580160c504190c4001200589102858018106401100401100048817144c0140440110005441,
  0x110058314044c313005041614484160840718546051700641111c48010244c112084c0180c484151c4421118483121c484140c480150c500150c48710106031814581100c403111464512005481800643120444214044c41818441180448215005c01004601180c442100460113144821704482151444417045c31300503131044112085c7160c4841814480183444019346441114589160c406120440e141c4c4160c51113144c11210581102058810204c91128607180c4c0142865712105c5141058b1308581121050b120864117085c4170044110044c0144c402150c4c01914502164058019544ca1818643102850310205c9121850219045c3161454b1,
  0x1508641180c480130c4861640405150c50113086011800443135854313005021604442150c448192c6431904542100458316344021534543153454315105811020641172044210085441604543103048415144c217044c2161448014144c216044c512004421014505130864112686011800409170c4901800446100c4c21504545150c540101440215005841808647171448f1228544180458510104c110005411208542110c58011084831008643130050f13044c5130860113085451408409120c44012085c512006491604504160040f1724584100464511105431504502160458f1510601141448217045831010587141c400171440a140c44018106511,
  0x1400441171c581100044014144c313005c91210640100c4801410543130c442150c48c181844316184411600603182c6051810647100860d170c581142058018244c016085c11314402111c4831028601120c403113054911005c1120860115085c0190c5401914583150c442130c4c6150044112104c7130c4821004504150448a130c480140c48810244ca150c49213205c1100444611186431608443120044719045c3120440411086411804443120440615105c2100c5081528645121c483120058516106051220401121c44011186451314484151844b101c5471208647182440c1510643180458011044801410643160458911305031310600193c4401,
  0x183c5d3150c54d13044021800447130844317106431800409130050315004031004582171c50f1228546181450312184c41408581150858019244811140643130050912584c018086411524541130c44a181c503141c4c91318443160458315144801414542170c442150c440151450219045cb142c48219144871108500150c4c0140858b1230446113450416044c2162c5451404402171c5171204411100444010004401300602192c584112c64211044841704484140c4d0190444011044c11220601120040315244c51110440111050210045c21914580173c4c418046031604504151448817104411700441190c44010005431504544161060312004c41,
  0x140454312005031410451161c504100c580180c500192c4c218345021604582100448a170c50111105c512084c018144821404488151c40a1814402133440216105c510005c21120442181c404190c64514144821104481121050310005021634484150c541152861419145c715144c9132858018144c818045031204482130064313006091834442150440d100c48a113c5411208586111450b1008485120054816305c31600602191c5881100501130c49112044831210602110c5c31708443162c444120840113105401004540180c4c617086051304482153840113105841814486150c50b12005441914503130054111305081104480160c58112086411,
  0x170458a19145c51508586190c607170044010046031704502171c44217044c4160444a110450515185831300509151c48217145c1170c5811320453101050f1010587130c4cc18145431300504190c6011410583130444810106451000551120854017104051814551140858b161c5c91100484160864513044c2172c5511204480101c5811338581140c5011508641192c48a140c48a17045c9160c403100860619244c0170c4ca17044a01328605110064f191448a190460211084c11160581140040116006431908447120058711004c61408580180c581140c48a16145c515105871100402191c400151c544190c500171448a160c58d131060111084c21,
  0x1308540190440219344001704585170c58c11144ca160c5c1150858117145c3131054113144c214145011410583172c4c6100c6451210581150858511105011444483110440310104c1130c4c512005c5130854114044411018603121050211045421104546180c541151450217044d01814548181460112284031404540100c551140c54d150c484110454e17344821714601100c48110084c1101054c110454710084801404440122864113044021314488161c4cb120860516044c815405c4103448216045821100500180c600190c60115105c3140840317004071814540190c641142860314005c0110460019044001414541120850417045ca11084451,
  0x13044c110085c8192c400180c5c51504482130050511144841814583150044f18006421000444160060b1208641140c54019544c0143c4ca171c442100064914044cc111c4c21104541111048415085c1120c487120850619145421634587110c402162c5041900404121440d100448c1910401100c50314306031534502161c5c3150065514044831100511110848c13044181510641140c481120c440173c4c311004461924641100864517044851108501120c48c19144c5122c4851208605171c5431308401180458316406111704583132040712006491100484150c440134060219045c314044ce1514404170c40217144431218503130844317245011,
  0x151c4831200643120444110044001138500110c541140858116004421200608101c488171448614085c1161044913005431600649161064112284c312105011210502160c44218145821934440110c50315044c2151c54b150c54115144421314404190454819044c21414482101440115244401550409121064515004411814587121040b180040114185841124500170864b180064f114050112084c31008502171c5c81914604190458f11004831200504170c5c1160c582110c6431400605140c4c6180044918145c3140448512084c6160c58b130444413144841900401130840011384981004410192c5cb160448413086421108406122850819045c31,
  0x130c485120c4411018603110c40014045451408601144060b120444c15044c313144801918443160c5861014508181c48e180064314006051208500180c504170c442160c547120c48c140c4c1130860512005cb15044441108545121448312184c4162c5c51710400170c48414044c4140c4c61808641120444012104c0171064311005431428441140c5011308545130050313044441320645171c4c215045451510645180c58d113850112084c41504585140c541130c485111c4051004605141c4c6111844112084cc140c54711084c016444c214084011204482142c50515144c0160040d12105871220587130c4c0150860114144c312005c312004c21,
  0x1710645142c58112385411208557160c440110064210085c312005c3170458210084411804442171c4c2100444a1814600111c5811808641140860711104c2151c488131448112084c0151448a1524440130850512106411208641100848015085c116244c1131064b12244861714583180844313285051220540190c44a1804543150448a100c64114405851308500172c4c2192c545130058316144c310004ca18044421310605151c484110c4c0151450216144471020641150c4861310443121854316045451220541163c4c512105d31318441120058f13044c215044421804451121050f15044c8150061113144c1100060a19044c3120050310005051,
  0x101854418044e2150c48112084c014086451404545140860112085c513005831318583120c442190c4c112004411914581131448511204c0180864114085c118145d113085411010545110864510004c5100c40014444cb1020484160450111005c1150c4c01518443130c48013105c219044c3130840917144c2165c58113144c4140c58113144801004547131060314045091310581181448413044401814446140c480180c605150060317044401000601170c6011728443121c482160460513205471108581182c5c210045431600445150c44414145411414545130850210044841004484180c48a1400645122054019144821700443191844019146031,
  0x16144c4160c58311085c315345c3103054315044c313044c3131444a142c48a18044ce11045421800402112c4c0140c4c019245451608447174c5491604589161064111084811110402142c480150c5851704489110050218044021804504180c587183c49310085031108583180c4401510607170c48415045c5160c507152c5cb1310505161064917044c3132040117146051608401191c6451534408151448214044c512104ca151458b170c4801900441181460112205c7142c583140458516104431714605150064210045c3120444a1128543121850516244c015085cc190c645110840710044c6111c6481104581150c541162c4c9122858b120448d1,
  0x113844613244401404543171458310086411100540180c5001904443132040b10504881300545130c4c0160c58111204c41404504170c504190458314344c1110050515144ca172c4c01414411100444015145851330509120051811344ca1404402190460313285c51218542111c583142c541150c4c0102460f1100440102c5c0100464112105491210585172c557150c44014005c313105811504402190c601140c501130c4c0110440018044c1100050511004c513506451600645152864b151448110184c0141c44015145c5182c4871210591160c4c11208601131058f1204484130864114105c31734549142c484160460310185c0110448414145011,
  0x170064f1614501150c58510005c31704501100048017244c211046471530444112844011005c116144c0110c482101460b160040514244441118483122c480111458314144c7121c4401714501132444110106031804503142c541150c547150c543110860312004ce1404583130440818144c0181444814084091708447150c581140c4c513044c51308501140c5411208647150c501150c4c4141060118744c0110c480110458110104c21904408153c40310144041308607180c5071320547130444215444831210441130c4cc170041919345c91614581150864117204011308601140c4cc140c440120c44011104c312006051208580191450f13186431,
  0x132864514144c5101c442191c643190c4001300605150c5001814583121064911005c01014643151864011044c0101454511105891334443121040114104571920401150c54410045031358641180c586111464912186431404482140448e18046431604543121054112106431904644101054010104c41904542190044012104c3114848a100c4c4140450219046401004605140c452150840511005411220551150c40910085411208557150064313144811058445180c4c1120c48a130440417044001704509151c484134840812005c31610641160c4801414549171c543130058314044c417144c218144c016144c21434483110c601110040c13005431,
  0x1240601120c4811104402121060f19004431604543130050312186031210441181454317184021100544100044412004c512204c418145c112105071110446171c44011185811220501170c601140c4851110501170c481101044314044c21414541140c400150c5c1102054117145c3121c404131064513144c91208403102c44413004431514511150c48111104c51128503171c484160c580190c5051318403151c501110064d1020540192454110085851604404130858117144c21814601130c4801814643120050c1004407143c444172c601120c496131060514006431814500180040913144c312006451838401130c48013144c2160844314586091,
  0x140c504112c6411400443140c486150c60113544c41510647170c5c512186441100485110440213085041834509120058318046091714501132c4841310583121c4881108443150c580101440316045031014402111c502110440a141064515046091110486180c5c41104605172c5441110486150c4c112406491604543141450b165c59a100c4c215044881914480160c519161448413106031908401131444014386051230503151c60b12085c0190c545130054312185c3130059712044051114501111440b100850112084c01424581140c54514045c318045511108446180c482100464518145851200597172c60311105c1180c6451218543120c4401,
  0x14044c5130c4801804448180c601190c5031018504111c4c21404549101048015245c1132c482130058913104011308501112048c172040d190c64b120050515544c0190c6071414483111840914045c5101064211045c315044c71100481121448419244d0192c601120c440120c48112084c41704550100064410104c5131055316144c416245c119145031200609180450418244c418145c9110064717144ca157460512385c517146411100409102050116044021124601170c5911714585141060d190c501160c501130864811044c2100c54511004401310500180c50019246021110600100c54316344c816044c4150c4c0150c40910044c014244401,
  0x1108587182c4c31300509170448217045031604484160c501160c60311044041514501120c40a182c4d2160c5c517045411108500111c5811614490150c5411128489110040f181450011245051704505121064319044c4182c4c21404584190c641120c400120854d10506011140645135058517044d110085071250647160c5c7140040912386401120446110c5c01024541140444c161c5c811444c618145db1400405120444017244421414408140c412155c5c7111044010005411404414160c58d12106471000505141864210085031234484160c581160844310045c11310503121054113085451804540110c5051208501171450f120058314104451,
  0x12044481624587120440e1200447191c5cf11006011008505130440216084451914641160c58112085851110641162458712104051414503161c60111085d5140458316344c011045001100505160c4841714547161454312004481134583151c50912044021110480170c4c510005891714505152c541152450718145c6100c503180450316044c31204444135c4421100585140c547152c5451624485120040b13205411424607180440017144c4181450b1204444140c484180c4001804404160c54b151c482162c4c4160460316145c715144c3121060d170c506190444015084011514601190c481120858517045c01004584190044312005c513106461,
  0x1514583100054512004c914144801404400160044312005c9181c5431214480170c5c5180465b1404543150448417084051404505130c4521208587162040911045ca10045031714607192c5031230640110c403140450219145c1140c4c11120487120860d15086411024443180448312285431100505150460912004c218145c11814482182c505150460010044c01818403120c4851118448141448018145831200503140458316144c1134450d1108482130441414044d017004411614507130c50910004831018585161c60314104021620408120c446151460317044821414484182c5c11404442190c440172044715145c5181458c110850711004421,
  0x1414541180c587140c49e150864117144821404502191450113145491804583121064111204c7131064516144851010603131c503141450b110060915045c315004451310585180c44c190c5c311005851908403120854d180c480170c48112206401004403100c480160c5001024580100c44a14044841308581180c645150440212105c11704446113064517144c3141044a10005c71314404180c486170040213344c2174c4891200605160c485111054210244431210607191460319046031804549151c60316044821]

theorem S2 : RAFrame.seg TB 10 99959916367638727273 63 10 15 14 99932062828104475117 D2 1000000 = true := by decide +kernel

def D3 : List ℕ := [
  0x120c481111050210046051414584110c4c1152840512084c1142c5891914605134c4c0110c585152c50318145071324493110848311085091004408170450f1304482151c4c2160440a120c40a1908401170454313106411208505131c4801004501162c6451420647172c545170c5c51934543150454110044ca1904503182c44210205c316144cb120440413105c5171c4001310641131c4021404400172840e14004021200647110048c19145031214481120c4861900442121850318084011304484160c48a141458116204401100503151460b151c4c21704605180c4c0171464313286011308647120854310184cd1208505171c5c31404545180c5911,
  0x150c4c1111054316044c914145451514587170c64d13085c119144c51320441140c4c0181440310044cf1014446140c511161044b191c6431610447190c64110104c418044471414406140c50b18144c419044c511205c1190c641121064312105c51800405100c507143c5c311045c51504546110458d190c5c1180c5c111204c113105c110005cb190460314045c314044c315046031904401110450314044821340641120c44017144c2181c5061004540190c4c019445421914501150c48018444c8100c4031514444150c58112084c1140c40616245c51904482130064513405c5160c58112184411804483100c40016044c21624440130064611044c11,
  0x12006451344543122864514145c712104c313186091914482110c403120050516145c31804585162c444160c581101058915046031210581150c607161449a130064514245411600440110048619144c11100641150044317144c31504503130454b185c444140040317144c51200403170c64112144821604605130c5411214402151448619145811100480181448312044841600441121448112206051814480140c58119144c4170c54019245c518045c0101c401193c645153454912006031210501150c4851200605170c581122864b160c545100448414145c5130c501160c50d130c4841704505150c480161460311106401018604100c40013044c51,
  0x140c50512105c513044c11130501120c4841704482182c608110c5c51338641190c58111084c5130450f120054611045c510004821310641150c4c419044c31504543170440415144c21904408130064c110044112004011420404110850111105031308401171464d12684c0192c54312084011400643131c509171c5831704482140448215145c1121c408142c40214145021100440132c501130864b170c40612005c314044c311105c51604586100c4821418642112c641160c501151458319045c318144c617245411630401130c45a1310603192c605100058011044841704543143064512104c312005c5191464211104451704649192c581120858b1,
  0x15145c7120860b12305031210405111c591142c4c9111048013144c313044d11410409141044513044421214412150c541131450819044001110449154448b111048910005c31434603153455113144d71514645171450911004c31404505130c481121040313184091914601120850713085811800443120c440180c48415045c3111060110105831804405102848512205c5160c404110c50219046051824587141440a142458d13144ce171c4ca1900403180c5c7180c4801900409125040712105c41120447193c5451904589181c482150c400181454714145491604543104854312006071104400110c5411914488130c4001904543120050211284411,
  0x11104401318403140458f171c488191c54513105c9181c6031814641170c484132860116204051128601130c58d100044114045031200605180c505151c4891200505140c4c0110c501182c6431414601170040215004001200401140458316345c3151c481111044113044c0100454519045091504505140c50516145c1142448512005c91218643171c5411018547161464317144801514589121054310005c11010484150c4c112205d114084431914482141460b14145c1140c5861100441191c5831210641180c5011410644113c4c7150c541192c48e140064312144061208641128858317045831404483121854313005c110304c1121448011104411,
  0x111c50b13145451814607190c647190c6411824607121058b13385cb14045031404483121c484170c580110c501130c501150c581180c64510186021104643140464318144c4180458312144021100547100850d120864010044071804545131064517144c818044831200543172c50d122850010346011820441190040715144c11514589131450b171c6031204408180450313045051220507132458112085c11914645190c541120c484170450f1118541110c54314044c211145c514104071220401147c448111458b170c60512105c111084901604583150450f130450211144c514044c31214440120c480172c6001100441152c484180c4c514046011,
  0x1030611130c4841714440160844112104c4100c641120c480151460b170c4841304484100c40b1304484192c4831118444100c4041904609131c585190c64112084d71110444171444112105451824641183c4c7130c503112058b19145c31600409120064b143c446160c44c122058010044011404484131060211084c3120448217044c211046031714641121050512144811100581190c6411020581140c4811004400181c489120448215044c3151844316045831504645183c48a105c4c5111044117004411218540113854b1404484152c643152c601131064b14044061804442163454312006081114501160c486162044813105c3140454317044801,
  0x1110540101858313045031304543140448a1908401180c64b121064715146431304540110464717144c3132c5411100443150c50714144c5161448216045c5140c54110104c4190c641120844010104c115444c2190c4471508404150c5c211104851100443100448018144d0110044116145cd150c4441604489110058519004031208501130c505180c446190460111184c01900441131864211044c710444481514442130448312006421000581131840e11184421110647150c5c519146451410401140840712084c1153c641140c4841908401142c48711004021824507172454516044c71038643190460315144841804541100844f10005c5140c5c51,
  0x1304557150c54117245411108581150c4cc190c545160464314144c1130c4841410401140c4c1141448b120864716244c7120840b120058511084801500447140454a1100402131c5c319044481404443101048112204471424601140c58112284c31704484140c4c0180c50714244c71310605190c64711084c81104507190c4c71418401114044413044c3171c4021214480140c4c6182c482190c40013045c110385031200505130c5d112005c312104c712105cb1414505140c48a1504542101440517045c513084411514583152c4c1150c64d19144851210511131064315044c3161c585160c4c31008503131c5c31200649150844810004c310304d51,
  0x13144c1120858112044001904545132c506110458b1314601150c50513045111120585172c585190460317045431704605150c4c512106531008641190c4c51010581112060b160450513245c7180c58716144831200503161c4c3131454712105431500400120040317144841818401141c505170c5cb160448413145c31320403130c4c8100c6451208548110c48816045c51008541160c55112305c91314586110c58b14046431304484170c4c61908402130c58112085011320405181c541110848818146011714651130c4c1122060711504401814605121044312285011910440140c40418045cb145c48418146071018588111054314044c310185c31,
  0x130c581130c5071430441170450210045c81120485120c48016044401418403121860a110c50515145c1152c503130460913344c3130449411044c31514641130c5c515244531204403100050f191c603130c441100440216044c5130c400150c5411914488170444216145c519144c1180c60c112c503120060313044c51714543181c603131840914044111414603131064113145431804400110c50315044841424641160c48c190c5cd1824541140c4ca112048810005051910401192c4c91508443150c545120050914044c313045c3150458011044c117145431404603150450f11004c312344811020544112c581102048311185891208443190c4841,
  0x150c58114145c1100050b1930400152454511004ce1014601163c6411308445140460316145811370643151450513044c51618441150444a140c541110864519144c11314503141448014145d710086451914505150448310106411914547110c400110064512044821944505191c58315445ce100458114244901404643130454313004031904505190c6051128641180c4c11228585170c54516044cb160c587150c54114145c312005c51900444151c4001404605130c484110454010045c61100580101c601160c484130454f131450112105801108581133c480170c647130c4031000505160044412144001714505150c541140c4c1132460011004841,
  0x1000483101440b10484d51514545120448b12105091900443160448419044401614601170c4c5130844919145431404442141c60517044401004643141c545140c4c111284831200551120c4001614585150c5441114507152c4c516146031304408120060011045c5172040319444441108640102c484150c511163450519144c4100c440171444312004051524585163454211184c110085011714404130c4c1132c580110c5cd11185c111004501100540112040216245051304515181c64b1108581180c640110c48411046041118509180c44012004c21904488160460313146011504442151c440174c505162c5c5140c54113004421118585160c5871,
  0x1108485100c4001404443100444f12085c113145c319145011314584100c5cb12005431404509131c50810044c31314446160c601181454312006451414583121c442140460513004431210543180454512204d31110603121c404190c601170c58519444c0192c5011100581181450312144811208581140c5051544484192c4c115145c312185491600405100c48d1204403121444312044021704642112c54118144c7110058d190c4c1180440617044881904488131454210084cd180c641180c602103c543173844211286411614605110040117044c31514480170c60515046051210607111c4d3160c404132c5c512005c11014401100060b130c6051,
  0x10004841510441151464319144831100601120444012004c5130c505151c600110450113144421514501130c5411208587120c486140c4851204484190c480150c54515045c5150c54d190c400181465711385411428443124448413106411008501182c48312185c312005881114580111464c100c545162c50516245071330441121060515146411500403130c601151440313044cb102448419044c3180440710004c118145c3131c5031210645170448416245051304605140c6471900401141c5c313045c0100c4c219045001100401170c5c1122c484190c4c712084031024486101c486111044e11205c51814597160c406130044b10204c312144811,
  0x160c50d150c500111058b1504543171c4831000651192458b1558400121858517445c210046031414486171464315046451608405130450312005431004643191c4c314045c51008541141455b10185c2115c4c51704503166c44015044c3181c44213045c315144c112285c51210403161454b17045051114543180044b172c48416145c0100c4031318643161464712085c2110458119044461834583190444519145c611346011008501170c541151448510085831014441170840214144c31808404120854714304011804482160450316044461120643141c483120044f18444c6110c60114144c31210501122c484110c4c1160c5401128480163c4c31,
  0x14045c31614440140c4c310005cd130c501130c5451414484181c601110048410046001104547180c480154444e121c4c31604444171044314045021004484180c4441344585191c483122c400170c486180c507126c4c119146091018484160c400172440412005c01008501180c4851234482195c50210084431408401173840114144c1143c5411200407182c58112086411414643140448611044c31000545141c5431704505170c4811108608110c505160c4cb124c4c51914505141448912104051444601120040110144011260403140c502106448419146051200585140c5cb1210585170c447181c505130c40112144441414603190450316045451,
  0x100858312004431404585121448312044c5121064911104c1150c54512005891218583123058111084c5140c4c116144c3162c647180c4c5180454319044821014484190844112005c314044c317144041714446121061514045941104545190c61110004c5130c400130c58512005831200651150c4c7150c4c111105031334646103c48312044851208507190c481130c58517044031404643171c549131460b133c402160c4c3102c40614045831404585143c48017145c31904449141448014146431304503144c64312005c5160c5c1151458312305c31810401190c482100c5051908405141c505151464512106431000505140c480152450713004411,
  0x11045851714406170c61011084c512044421204441180451712104161604583130450511105831614441130c581160c601161c440170c440110058111044c1160c5051008442121448c140c60b1444641130c4c1130c54211045411120581120c4c71924445161c606100854d13144c91128444161c58317044821104586100c503130454111084c0100c4011104480160c4c7121040b130c50114144cb112050715144c11030581161c4001634483120064710185031030491130464810185c410204c51104400130458314045c315344cc11204c1130c4c1170c5c118144c9170450912144c51814643100c54311005c5172454513044c3190458315046411,
  0x17445cb131c44016044891000482140c4061604605140c4c5193464317046451108484150464210044c611045811344504100c5011120501190840b17044c3120040314045891514406160c54110144021404414181c48310005051314484142450d140c5cd140c6451814400170c5451714442100458519045c3180450b160c541141840511004c1140c541140040716146051514601130c541110c480140440019045c6113864516045011000501121044915044c31228645141c402120c440132c5c21004441190c5811308401190c4c1180c4c513046431314581150c585122c480183c64e101c401172c54515246011904400131450d131c40019044c01,
  0x150c4cb1118645130c645130451510284c51904490140c44c18244481104505121448010044441208585121864111204831200649140464512144c3181c4c3125850d133c501121448216144c51304404140c4d11604645180c5c51610444111c645170444019045491200641110464611244c1133c50113145031744581191454314144cd170c5011208505120064316144c11724482101c5cb1904401100c501101c481102054119044031010445160c48d13244421000581150c446160440b10084851008480170c58511005c91120401152044116104451844582100c50914046031814582100c58314284051304609145c401122064b14045c5130c4061,
  0x120c48b1304605181464316145051028501131458310305821110400121844c120444011104c1160c48018004431208651161c4c5130c4c117146031304463170c5071200441160440318046431704505190c5cb152c601142c505150c40012285831604503140844119045c314044c914046001010482190456319245061100444110454b120054312006051324582100450119004061100480102c49417044cf11004cb190044119045061108486142458b1204404131450f181c5871008597140c5c4100858610285c31200545175448417044c5150c545180464317146041014504110454e11045c312104051244480190c6011208541140c5c516045451,
  0x10504c918044c3132c4c91138501110050715044001704503131448016204021910400120c4c118145831804505132464512044c711085c317045c314044c811045831904485120858518046051800441124c406110454112385811314503161440c171460312005441128440160c44411304c518544c7122054d14145c010104421614580100c501150c64011004481124641170c48112004031314541100c5431304543121c48a17144c5160c641152c5431304643180c406182c4c118245c910084c5111458318345c01134545191444a1210601180c507110c50411045831404642100450911004c010044411404401121858512106031000503182c4001,
  0x1304503160464515244421104585121858317144c1141448513146491304482172c645160040111084401708402110844a18044821804505170c64112144c4102448a190460316046451208501190c60715144c310005c11118581130c64114245911520448121850b150c4c7135c5031618400130c4c71814543191c54317346031600409122864515144c712244c1112064d1240543120064916044821714501160c4c1150c444122c4471208541173c4c512305491504543172c440160c60211245c512144c9172c485130458314204031400441191c482141c585130c5451314481120c4c5180454b130c5c515144861704401160c440131454d12244c31,
  0x1210581100848310004821704502111864510005411004406136c400161464b1200442130040b10004d1160c60d140c487133840b1404602101450716545c1180c60517144c11208641180c64d140c645120440310185c9131448211084011008641160c5c71110503120064916046091314641141464311104c1130040319146451314589190040211204c5130c581140c501120c484171448114244c7141c401151c605191454317044821504545120c440140c50515045c31504402192c64110044021404402160c4441408405101444712105c71800444180c4c1133c4851304545170c647142454011105071944483110058317145471808447180c4c51,
  0x140c404121c483141450d17144841804401100058519145831604485140c4c1142c54210004cb131458811045921008448171454319045cb190c6011300441121c503150448313344cb1314489120064318144c7151440e1804583120c4421554501100858113144c5101058b1008501100c4041214480180c4c115004491714643180840114044c313144c0100c601152464b123454313044851304442120c501192c5011004541106864118146091504410152c4c61104480161464011105c516444451020445174c40a182c585160c50b1714585191c483120060010044851200605120c48112106451800403142c5831504545130c5c11914485150c6011,
  0x1100484160c44018045851110603130450314045471008503101864710085c3161464113145451828403100048713544851100505140c5071500441160460915145411120601120840112285c31804605150044211004831304483131c603100048314045c91000603142c5c1190c507192c585130c4cd1530404150444310104c11130601140c4c51830445150c482101c50513045431234443150840119044c4111454312144c1184c44016044c3150c40012105d9131450312285811524601120c50b15045c3151c402131464b110044411084c518045091404482100460318045c317045431304483120450315046451600409121444010045c115145451,
  0x1304603132440112045031000543190464111085c91644501140c501150c400120c547160c481131448315044421214480190c48113145831204505120c5811224440173c5c1130c5051504603181460d15146451514405130c607180c6451814541182458d190c50b150464b151448910005031614446160c5c1130c48617245021100445131c4c010104481818405111054312045831304545140044415144421614581160c581130c54b161464112105c51314643130448313044021408441121c58314045831634543151c40215104021300410130c4811614442151c512100c542105c54717245041100453101c60714145031210601150c48417144041,
  0x141044319046431300446130c4001814605140c58510004c319046431504645172464b171450b131040213246451700443141454410045051814503151c549120450316045831404485152464115146011100441132c54915146411274442141c5031904557150c400120c5c1160c5071228649100048917044891404583161448715244801814543130448b140c501190c581180040011005021004641180c4c010044411514487170c481101464317044c31204482191c4c31904583181464d130c6011804440172440017144c11524504110460f1314581140c581170c6451214485167450611005c311104c116146031310403101c64b1944501180c6051,
  0x1800443150455b10105c1185450116145471004400190c507190c501133c487160c605152c40416144c512184041504603191454713144881004540110440211104c3152c581120c4851314481180c605172c5cb1404603151448112144c1110c402181448110205011604440121c483130444011046411008481120c5c51804489143460319004031104503132c5c51700444160c442180c48b11145c1140c48512104471914511160c481130c481101440415445831808444130c481101058511085051604511163c601130c4d1141c4c5170c5d610085c5141460011045c1150840515045c9182c5471814524110c5c31408402110045415145c714245811,
  0x12044821904655101c50110184c113344011028641110848d180c5c1110c501192c58917344c31804505162450511104c11214603120448b12145c5120c4c1150c601110850010044411004584112c4c5150c48b14145c713245c519045cb10144011100487170c400152454513044831414400140c4001824505133458310185c010205c7120c481150c60513044c5120c58113104031400445140c4c1141460915144c51704485150c64714044011204405150c481130c541150c4871604403102058110105831214440150c5011010509140458314145451800440150c4431014501130c582101c6021004581130844012006431804503151c640110440b1,
  0x1104483171458b1304605130c6451604545150c605163450915044c91534489155c54111204c51100603132c59312144c51614489130448e191c4c314345431514601132464b1314481152448311004c115144cf140454514146511224440140c5011514549111c483160448f151c5c3171450117244401314583111c609141c58516004491944603181c5451188445122458d140c541130c5451304603121460b1604482192c585151c5051808440111864318045c319044831404485130c5c11214450182458d111064314045031404585120c4cd160c48517044c5170c4811620405144454d16384001110647130c5111414441180c501160c55118044831,
  0x12146411214605160c5c512145c11624441165454d142c5431604605160c4c5161448d161460b130c481170c541140c4c1180c54119144421918445120c487130c60511004c9141c605131450316044c21114501130c581192455113044421904583191c649145c541150c541153c505181c545162c543151c58f1904605120c4c1122c483142c485121c483171c5451918446110064113144c31224442110c4c1132c6491704483111844a1414611190c54718544c6110c5c11714543140448315145c117246411900441150454f1204591110850d1110609172c4c1150c50119144891504603141448b131450519044c3160460f151c545160c44414044cf1,
  0x17044831130609191464118245451804543151450f1108603181c50312145811614480111c541130444018045411108485190c5cb12044c5150c541120c64513045831704543161c4c5130844115104441118609170454111305c512045951214481140c593180c54b170450313044c3130460b15246401100645190c440180c54b14045c3161c602111c5c5142460b12146011804441150458516145c313084481944641170c48516144c1120c54716146031804503190448f1100485130c54115244cd1420447190c5c7130c5051304483122c501180c4c7121454316045451108481132c54312046031214481180c6011138481192c509191449118004431,
  0x1304485150c481140c485172c54112145c3120448313044c91604515141c5091214440190c481180c5c511146051214645125c5851414501111044216046491804600110c500110c50314045c3151444015144d5151c48f152c6071808442140c547140c4c11814485172460116084411214643142c6071934446121c4c0113454512044c315044c314145451704483140464516145031300445160c5cd170c5011804441191044d13445c3121460111084cb130448317045c3147460d1224502111c60118144c91614581165c5cb151450f14044c313044c31214641150c5c7171464313044c3120464512244c5131454b141c4421604603151454715146431,
  0x180c4cd1924541143c54111104831304445120c481151458314004441704450120c5cd130c60713245441104511172c60f151454b1504603110844114044c5175458411085031604583132c485140460011244861104501152460514046431804611130c5851304504110c5011744509191c4c5192c6001154485170c58d1214442140454b194c446191c4831714641130c4c811084851604483131450b1600449150458f13044c5142c50711084c312345431614645131464517045c3121c5c316044831204484110c581146c54611245011614583161c64f1604503180460319146051504643141454113245431104545151c483171c605170c50118545511,
  0x16044c3151c4c3191c503121c603122c4c1140c4811824501140c64d120c501142450112245451234442142c59114045c31614481120844d123c5401140481130c481120c4441404503141c54315146411524547121458d11205431204543152c645142c641130c481150c48d141450312044c31604643191c5c31594605140c487120c64b141450211044c1130c4c11224501180c581146c5c1130c54513044c312046431944493142c645142c4c31414500110c4c1192c48316044cf13045881114485160454919084421604489141458113044411818443141c5c41110541142c5c5111060b1408440110c54117244811814507110850917045cb160c5011,
  0x120c48d170c4c11928443130450314045051614485192c4c3132c481130c4c7160c581130c481160c507120c4c1122458515044cf1204505142c442161c4c9111454a11145871714645140444816145031118609150450316145011514543191c645151461516044c5141448312045cc113458512144c1141455115144c3131c6031504605120c5411214503170c44616346051208445130450211085451324647120c4811314651120c4c2111044211285851110647131454f154c483152c64b19045c1110854316145cd13044411214485161c5031314501120c60111205cd170c54114004431524501182c54911104c1113854d110c64411145c113145831,
  0x112460115144c31304483130454f1914605150454514084411210440140c481150444619145051904486110458d1524647140c54311084831714651120450919346431904543121460b171c44a160c64113244d118044c211085c5120c5811614505180044a1104601140c481182448516045c91304445121460b140c547150c4851904603182c641170c5451804603152c4c11608442130c4c514044831514507140c5111644601150c5c1171448312144c11300447162c4c1190c4811814483165c5051914481160c5811310449191c50b120c64513044891204585170c4871814545120c5c51604545150c487130c485130844115145071444585170c4401,
  0x140c5c51904485160c4c1131458313045031504545152c50312044d716245011814543151c6091374581150c5451404509190c443130c4cb1804583191c4831204585191464b140c5cd16445031204603180044015144c5120c48d150c481180c505151c4c3170c446151448b160450b150c6071214609161c503182c4cd170c481140c50b140044f13145851704591130c501180c545130448318046431614501120c507180c641160c601130c481180044112146041100601111844616044831620447131464811045c1120c581133c440112060512346031304603181c505150c5411524601140c5011724545191c50318044c5120c58d190c4c115246401,
  0x1754440195c6511314603181458518045071128440130448b150c485150448516244c5141450113145c91634643131458b191c4d5121c5c91704485170c5c11444485180c5c714144d81124545132c585111060317045831204485140c587170c541120c5411150541191464912104471608445160450312044c512145851600443121460e111c503151c545180c645161c6031404489181c583121c58314044cf11285c5121c5c317146411514551170c641181450b12144c312445c51204545170c50717245c518044c31504551163c60b1404505152c48515145491304503131c58b1314505140c501150c58311005871624440166c501140c48112244c11,
  0x120464914044831304483163454d11004811924485183460915044c915044c3180464f1204483150460313046451440440140c60714145431128581160c5851714481120c581140c647190c641182c5c91804603191c5c3181c485130c547160c59112045091914645171c4921120581140c48119144cf125c6011224607170c5c1134448b140c440140c4851604503172c4c5160458512145c31404547111858b192c4c114004411314587170c481150c5851304505180c481162451d1234483144c483121c6491614496110844113144c1150c6411108645140448916044c313044c513004501108481150c50d1614609141448518145c1160c481122c5451,
  0x1500446150c48b18044c5112450518044c51810445171c4401304589182c48511044831404645150c50d120c5c5171c5051534441151c58b125c50b190c4c11824481120c501190c54d1910451130c5411514643120448b190c581140c5511204585180c485160460315645c313045c5150c4c7120c5cd1914505130c545182c481142c4831614641180c5d71734585192465117044831834603130464f161c503140448314144c111085c11324581130c605121c483121c444132c44817044481504503140448211046041110545130460d1108649141c54312145c11714543171c543121c585140c481141454b14004411730440120c641183c541120c5051,
  0x160444217045051214583150044312044c5162c645161460315044821104643150454316344c3131c583120464f15144c7130c482110c649120c454182c44216044851300449130c50114144c31944647170c541140c581130c4d3130c4c1130c541170c501130c507180c44113084451814613140c5071224541191444a16245411424482110844416144c7150c505182c647140c4cd1724641180c4c11904442151451b121c603131448112144c31204545150c541121c4401504605131458317144c0110058918044421704444180c485180448b172044018144c1130c485120458f131c4d1140c4ce110c6031214641190c48d120c507190c50513044831,
  0x1764582113454f1604645120c5411118440150448512245051304485162c4c5142c605140c5811114591181464211045c31224442150c50d140c448111c4c51404645120844411004c718244c1140c6011810446110450b1220448134c58314345c91204505152c543171465f120c547160c54117144831304485181460315404441100641160444015046491414641190c54117144831704442181460b1804583120464f12045c5170c5c5140450313046051504443191454513245c517084441110444120c4c1141450314044c5170044718045c5191454312444c1120c581130c48515046431244501122c4c91614641150c605181c58315144cb17144c51,
  0x1704503161c48316044c31204503121c503131c5091714601130c60118144c31814647130c54117444dd152450d130c4c118145431704485122454d150c5811504446141c50b140c501130c647122454b137464411085431514641174460318144c1152455117145cb15145811414444161448315045c5190844d190c50d190c50114144c313345c317044c31508444123c58518145d116045431514480110c4c1140c48515045c9152c481160c4c1130c4c5131c483170448914046451224507170c60b18044c9170450b19144c318046051724501141044312044c31304545180c601170c481112048113145c312345491304487115058b121c440120c4411,
  0x182458118145891704555190459712144c311004c315945431814442112448211044c317344c3134460d120c501131c44313304441104581180c541142c5c915046031214541130c481130c50518345c9181445818146431904583143458011044c51614581190c4c1110044115045051200441130448312346031814581140c48715244811924481130c5c5140c442180c4cb191c505192044512044c91234549180c44c121c501110c64318044cc11044851534442180460514244851214641120c4c1140c4c5151c611130c4401514503130458b191844d1514541170c481140444e120044114084411614641181444816045031734483151464118444c31,
  0x16145c4112c48a111450311185491304505150c5c1143c4cb1614501131464b132c5831604585193c441120c481170c553181465513044c3120c442130c541150c501191465b1734503162c601120c4501904543121044113145c211184441204643180460b170c505194c583130464513144d111104c5110c597121c5831704585160c4c111104c916045c3121c50b17145021104483171448516044c5160c4c1140c48114446031914641150c64d16444421314481160c4cd1224617130448f171c44a111058313344c3130460b182c605160c4851108440110055512144c1121448313144c7120c4851404605150c547160c4c51904483140458313145011,
  0x131c4851110444150c48513045c3172c480113c5871814483161c5c31704643192c581120c60611145021118641131450b1814585140c5c1120c641130c4c512145c516045831514507180c54d18245c1123044216045051138505161c482110464a115c5031404585133c440120c48511105851714485171c505192c483181448711085811654507180c4c114244c11914605120c501112064511144d71400442110464211186011224585164c4851314489150464318044c11118641120c60b1714547170c5c5191c50919145411654545150444219745411824641190c601120c54712244c5191c643144c605143c50117144c315044c3171464513044851,
  0x1274643110860313044c513245c71214611160c4871110601112054918044c317045031504485130c4c7182c583111460113084411824517120c442155c503131444617245c1140c4811830449140c54112444c3131c505160c481150c6471518442162c5c51100444170c4c5180454312146411524541190c581180c601126c481190044113045c31708444150c64516145cb12004451200447120454514244c117245571904445190c5131414543150044c120c607161c440140460516244c2111c4c1180c58b15144c11524601180c640112c64313045491204583122c64d125c58312344c5150844114145c31504483151c48f1804609192c54717145091,
  0x12045851308441191458313344c5141450913045061118441152c5cb12144cb15044401804491181448314045111200443133c605131c5091704545181444318144c718084411614483121458117245c519104411624602111c58515045071108454130c4411304543141844514146031100509121c483140460313045c5130c5011520442180c48712146431304543181464b121c489121448512045031544581131450318045c3121448118144c3164c4c31234657170c587130c6011614503164c489181448513144441104583180448b160c64513044831414547152c485132458b1414585171460b1814440172c4451214643180454919444c513045491,
  0x1618448131c6091234483170454317004491604585120c541120c4c11304440141c645132465116044c517084421454641170c581141464316146411744645140c4c516144c71414442150464914044c3121458115145891604609110050b150c541160c585172c481194454511084cf11085031404545160c58114304421128581111054511144891314487160c541132c505150c5c1122c515190448b18144831634603133460313044c51404443161458011044c11324641162c651120c54511184831534543151c503151c58f1404503180460514144c9190460912145841108505110850d120c4c714145c919045c317345491414444190454316045431,
  0x140c501160c60518044c313045431614481160c440170c5cd150c58515045431444585190454b142444a14044831804505121844f120c505151c543141460115245071444649150448c114c4c11944483191c483145c4c1122c65b1414601140c501160c5d11904603151c585120c5c51404645142c48316244461714541111448914046491604505173c60b12144851128641170c481140c48b14144cb1700446130c4c5131c4c3151c5c314444851304505150c481151448b14144c11104485130464f13044c3171c4c312044831314601170c541142c50316145c116144831404505140c547160c4871514580110864119245c9110054b141454114244871,
  0x140c481122458519044c5166c5911504605140c48d17146451424483111c5c1122c50513145c3151c4481314601152c54517144831704489191c60f150460516744c51214483131c485150c487130c61716044831714581110c48513345c0110c58f160460911104d1150454312584401114505180c581150c44014145c311005c3134464518204431414583140450b170c4811100443180c60011545011728440142458112144c9182c60117144c3180448f120448515044461110645121c48f19144851904585130c5c71]

theorem S3 : RAFrame.seg TB 10 99987756629278518587 63 10 15 14 99959916367638727273 D3 1000000 = true := by decide +kernel

def D4 : List ℕ := [
  0x13051905150315051501120b120317051205161d1219120515111104130311121809110117021105120115031401180313051605170b130f11001901140317051405180b13011503170911021203190118051703160b12011309180118051102110a14011405130b1715160b140515051705160b1605120112051703120511011403130211011301150211081503170719031701190111021115150117031301130f151114071503110c1303170514011505140313051405120113051705190b1403170115051903170b1201130514051805110417051705120511031907170011011807190513051205160b1703120514071509170519071705130b120312071,
  0x1401120911061203191313171203151d17011709190115051303160b150112031201151d120c110117021103150317071905140513051409130712091507150518031606110f14001100130314011403170b1705120517121105140518111601110613011803160119051327180118031201140312011801110017011102150113051703120116041105140312011403110414051911132b1603170514011903190b1705120b1106130518031901180318051411131315031501120316051801180b13031301140314071515120118031307140911041407150312011805190211051807190312011205170518051603170712051605140b17031207130315071,
  0x180512091707160312011403180516031103120312011205150316071209190718071102150f18011505190b130b12051606110411081505130d130f18011803150117051503120d18041100120b1203110018051905170315011403130516011503130713151301130f120b15011709141314111504110014051102180114031501130512051603180b1701160515091205150113091601160f130118051303120b1405180b17051501140519031201170f130d180315011503140112051603140115091805110611021101120515091604110119051703110013051211170315011703180b170117031707180316011305140316011511130319011503170b1,
  0x15071203160b19011611110a11041203130d1403130d19031300110913051601140f11001503151915031305190117151605140611001203170113091307180b17031301120f1311180114051703170519011405190318051405190b12001105150318001106110818011611190b1903110011051303130113051909140712031407180516031408110114051901170312011509120713031701150b11031601180611011705130b14131303150112051303110112031801170f12011503160611041605110a16131703110117031605130518011902110214031707110e18011609130519011403150d170318071703160517051811140714091207170318011,
  0x1805120312051201120312011303110c1605170b15031611160513011205160b1205140111021505160316091107140113061107150d16031201160517051405140317031101150116061119180112031701160512031106110313051301170516031401170315051104150511001305190311041101130913071703140d13091301140915011803160517011605140314071605140f1601120f160b140111051703150011031907140a11041102110212031707160f190b1601140f14071403150d1509120b120518011705130b1503150b14011405120f1401120f1201130b17031601190318071905170914071205170d11081407110c13111605130716031,
  0x180119091301130513031201160312051601140313011805150b1905120319051304110014051505170b17051501150315011203170519051605140111041403140b12011403160118031305160115051609190511041505180115051621180b1605120112001107150311021703180115051303130d160517111703190118051403180d1203120519051105160112031601140312011205150314071503110614051703150716031601170f15011315150111041203150b160513011603130519071803120713031104160117051903120114091601150518031301180519091507130b150312041107120312051208110812011503140119091801160315011,
  0x11081409130713031201121d191113051108190311021102120111091701130f140113041100190319051100150316051401130919011203140519041100140117111703120116051203150114031505180d1403160111041209170516011903160518011203150d1305180f13071803141116011503110112051203170b1805171611181707141516011903130116051303120518011705140312051901130f13071303130b18081103160512001114170d1305160b150f140117031204110411011917150b12091907140513051203130b130b180512111301130919071807110614071403140b14011709190715051603170115061102130113031207132d1,
  0x1203160311031705120316061103160b19071203160b160716031301130516031401150512041100130314011403140b1801190317011709120b190118031504110018051207170317071505191515071811160317051801130b1104190314011909190112051803160d150312131903150518011205120f1905190114051905160316071505120915011709160713051503190113091201150011081501120312051505180115021101120313011705150b120518031104190712091705190b130118031505130d120f190118031201120f1401110313011203140117051603140114091507160512031205130d1703170b14051705120518071703120115011,
  0x110c110412031100120514031616110d190314011605120313011403170715031505160113021101190516031401190312051201110a1903150d1400110112011605190912011102110417011109190d160317051905122811001100160517031501120514051403180114031605180112011100160711001106180115051909160b1301180411001203140111081110180119021101140316011805180312131603190113051203120d160316071403140118051303160516111603110015011305140b19031907180317051901180b180515051102190116031607130314171601180b170111021705120916051504110112091707170f18011405180111021,
  0x17011203110014091901131118031405140713031201120912071317110a1203140114031701190f120512011203120119031907170513051803120b1706110b130318251505150516031301130b1209190114031401160317011200110216071505130315011905150317011403120718091607160b1403160514011405150b15031204110011041104120b150511001403170712111505190315051305150b170515071209170114031705130011031801120b17051603130b1607130519171203131113011903190716091807130f170119011102120311001902110b1701140611091705160b11021801140f1701140315011809130713051503190112031,
  0x180011041503160711001100130b1801140315081101190b130c11121803110011041104170313051901160915011217160516031803110619031107130b19011605190315051401150513031301110011021200110113071803160513051301130b1403150119051509150d1808110d1703140518051401150d110016051305150112081101180b19031301180b12051303180514031103121116051703190512051901130517031307120315051301160514051402110b120114051903110618031601150f140b1801170317051201121512051301150317071305110b12051505190b1904110a11001205150f1110131114011903120119031400110517091,
  0x180116001104120b120b13031205130512071809170516011403140112051703140511061303170d16051503120115031205120118031611170112051205190b150315011603150b1405160b11061209110413011105150313051801120f170b19071303140712051203170d120316051817120113031902110414031305180119031201120514091901120313011609171318051905130313051207160316011203150c1100170916011209160712031305120411051805140114051902110817011104110014011706110317031411120512051201170315051201120b1311180b1203120512051705180116031603110012051201140918011905140318011,
  0x120211051905160517071503170512011605160317051501150317111307130011081401130511021201110514051318110317031901130511021601140313051301130515041109130113031301120312071605120919031101160d1300110915031417180311121801180b1509130716031901120514051905180912011403120b11001705121717031405120114031507170315031100150b150b140712001109180011011604110016011203180111081201160316011605120315011400110418031100170b18031201160f17011503130d13031904110014051106150313011405190916011303150713031209110815031201150512011103140c11071,
  0x11031705120f17051805121d150d140b120318051505180b13011203120b12071203170114091205140514011609180115031301140916041100110416071405170313011709160519051401160314011309130519031100150f110917031602110113011905140514031401130514051703120b1701170b13051608110214031100140311001703140115031402111315011803160211021207130511081501130514051306110d1605160114091807110211101301140513051303150b1305160113051603160114031601190b1609150b130119001103140513051403130519071203180118031801150313051801160011021701110212051701160914071,
  0x1501160b13051809130714051809130119031201190f12131103120719051603161117011603120113031605170113011103170b1809171317031207120514031301110a1403130118001107190d120c11011706110012031104190513051201160314001109180c11041903110218051603120118051505190514051403120716051405140912011805170f160b1601190516001101120211081607120f1100110218011703120411011605130b120515051703170115031205140112091405170b120a110618071703150117111805110f1805160b170517011603140b190111021601140512091217170a11001105130913011309130119031907140518011,
  0x120115051703150d1403140114031606110419051301180318011203150717051305120f19011203150518071509150d150915111905190116031701130519031100170511021711160118091501140f1505160118031201151119031311160517071600110318031305140118031301130919071505120313071805140519051600110215131305110a19031100170b1203160713031205190519051609110019051805130d13031307140611011301170515011100150116051705120315001105140515031605180113031301160314011505120312071805140314001100180315011903131114011605160b140f141713021102170b150b1405130514051,
  0x1901140319071205160514151305180114051400110814011301110613011605120518091805151a11021106170514031207180318011302110b17011303160b12061104120f110016051100160711011404111f1303160113011100130119071102190511031301150316071217190b1405140b140316011104130318051601120312011509190113031901180317011403150513051207140319021104141d110213011203140514011503120b150011101104170512191803180714031601130512051505190315071603180b190514011801110214031101130318021101160113051703170516051505180114031405180712031201150a1104180114031,
  0x190113031201180515031501130b19051803160116051603110618051603140b18011803120b120113051203180514111505190113051501110f14051709190d120f190a110211021801110214011105150312011303160c11051800110a171117031201170312011504110811051205170b18051100140316051104170117031605150116031211140713051303170714031201140312011303150211011905161714011405110e18011403190119051305170a11031605160d150f1201140f13051801131115031201190e110017071605120513031501110312011503140119091201140c1104170f12171805120716031705120515011503130b120119031,
  0x1405180b19051100140319011503130115031205180513041102120319011303180112031701130514031201130f1305180b1405140117051205180912021107170112051809160718031207140911001703120d13051804110b1903180712091217180519031106130115051305120312011317140b1305150312051205120111031301120b12031505150114031901190913011305130915011909140d120318011203150712031509110618071303180714031401120313011617140917051905131117011203170115001101140712051405120516031501170f1804111315051903160719031907140513031607140515051303120114091901130316051,
  0x1403150b1507180315011209160514011300110114011505170312011603140114051403160114051509180515011806110a12031401190b11021201180316011203122f1312110b191118031409110812031905190b1201170315011900110a1803130712031907170511031411130515011905160312111701140f1100180b13051405120316071603140b180b1901160514031307150913011805140317011805120c110e170716051104180518031901160011031303120117031323140b130512051705120711091307190917051901140518011102150b180f170712011101120114051903150d120914011905120315011809180b17011605120517031,
  0x13051511120b180b13111903180119031803110112021108110f180515021102180517071309150518011505190b130315071603160911001605180717031207130b16051305120318011205130b17031201140b1407110314051403150811021104130715031501160b1104140317011305120314011503130117031605190714031801120b160f16011503130d120011041106110e19031513140313011605170319071703140b1301170514031205160112051903120118031201130918011211160916011603120b140512131305130f150119001104120517031705120115051505120011011505170011041601170917131605140912011909130117051,
  0x1709180112031401170912051401160913011509110512051405130d1711120e11021509150d15031407150513051205130e110b15071905120512051503181116131603170117051300110f1810110013031801131b11001303180011091611120516041102150518151201140b1401110913031801180318021102170114031707130b190316051707180514051203170011061110110a15051211160312011803190114031404111212071603160d120311101105140b12071515160717031202110417031201120312011103160d1205130317051901180b151115031201170317051201130312011603160518011203150b170516011405130f170114051,
  0x15011905150319011505140513031104110018051209160b14171405120719021102110216011505120f150115051904110b13031201130318051501120b1203140518011703170114031805140114051603120d1403160b160118051409180a1108110714011305120915051301170513071101140115031407120519061104140f180511001605110914051807180913011209181c110e17031505170d1209120114031810110117031901170517051205140318071103180118051405190314011705141113031401130317051101130315011504110918051305150514051905140512071515140d130514031202110216011703120518011703130516011,
  0x161511051607190318011205170211021503120111021511150113051203150b140112151305110c1603110414011903190518051301150b1703130113031305140118071100110115091501130516001102190111081501120314011105130a111b18051807120f1601130f1605140b1201120315051401170315011709160b17011411120111121705190511051405181011051605160d140711021605170315011803160211011805160811081801180f180513011205120512051803150b160518051907130f15051110190b110013031602110115051711190d1203170512071811130317011815170112031505190b12051605190119031907180316051,
  0x180511011107150119051503190811021605140d1503110111021201190312011803160b1801140211021503180515011605160b14031205140716111306110111021203140117031701120314071403130518011303170115051603110413071805170918011305180f1201180514051405180515031411160712031705190713031301181119051707110c1801160914001103161a110315051603150116031701150314071503170114031701150315071203120d19031507150711011907120518051603170d15051511120312011503180117031401190f160114041101110a14031405180514051511150714031301180519041106170b1403190514011,
  0x11081811120b11011803141112001103110111041501180311041401180918051105110113031401150011021401180f1705170111051505170316051601170f1507160f16051313121518011803150411011603120d14031607140519031311140116031201130518031301120315071601110218031701170512051303140b14001103150d1703110d1104160516031705110515001105190b1905160211001601130517031401120f120113091201180b1809150713011100120716031601140411031601120316011603130716031301150312051801110f14011603150515011505140312011703110414011509160517071503140518011303130112051,
  0x120114031301150517151505160513051701160516001104140111031102170119071103140011031403160119091207190314011811130b14051605150b1603190113051203120d170516031100140315041105130112051800111c180914011303150d12051403120119031501160011031106140512051203110019091805121313021101120b17101100160911001309110514011203120b1905150b1505190911001301160318011301110119011404110b140519001102150513071421160d1409140b140116031407190b17031100120512031603110718011803140112021101171211041903190111021807110919011704110313011303130114051,
  0x11d2120311011305160b180519071600110111001901140316031100170112031218110514031307160b180311001703140b12011903130011031207150314051201140317011605160b1609110114031301120315111901180915071703140117051203190d1403140114031402110a1609120d13091905170511011503150b13071603190b1]

theorem S4 : RAFrame.seg TB 10 100000000014000798851 255 12 15 16 99987756629278518587 D4 1000000 = true := by decide +kernel

theorem cover : RAFrame.Inv 99876372021712761067 100000000014000798851 := by
  have h0 := RAFrame.inv_init 99876372021712761067 (RAFrame.cOK_prime _ _ _ _ _ _ _ TOK P0)
  have h1 := RAFrame.seg_sound TB 10 99876372021712761067 _ _ _ _ _ TOK _ _ _ S0 h0
  have h2 := RAFrame.seg_sound TB 10 99876372021712761067 _ _ _ _ _ TOK _ _ _ S1 h1
  have h3 := RAFrame.seg_sound TB 10 99876372021712761067 _ _ _ _ _ TOK _ _ _ S2 h2
  have h4 := RAFrame.seg_sound TB 10 99876372021712761067 _ _ _ _ _ TOK _ _ _ S3 h3
  have h5 := RAFrame.seg_sound TB 10 99876372021712761067 _ _ _ _ _ TOK _ _ _ S4 h4
  exact h5

end RAData

theorem solution (n : Nat)
    (hn : 99876372021712761067 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  exact RAFrame.finish 99876372021712761067 100000000014000798851 99876372021712761067 (10 ^ (20 : Nat)) RAData.cover (by norm_num) (by norm_num) n hn hupper
