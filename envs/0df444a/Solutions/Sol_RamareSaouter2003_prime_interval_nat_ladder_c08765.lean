-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_c08765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:59:13.627755+00:00
-- url     : https://prove2.me/submissions/c4b59239-4853-40ad-99a7-1fcb46b84216

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith

/-! Ramare-Saouter finite range, ladder chunk 8765: every natural n with 99752898761777419393 < n <= 99876372021712761067 has a prime p with
n * (1 - 1/28314000) < p < n. A ladder of 35509 primes q_0 < q_1 < ..., each step
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
def TB : ℕ := 0x14e9f4094eb634dc025e730253ad8d1d3564e3c094eb6335c2faf1d0253ad8c471bd3c94094eb6300c3912290253ad8bf101582e4094eb62e944f6c790253ad8b811aa2c2c094fe7162422536b02539b6e9f

theorem TOK : RAFrame.tOK TB 10 = true := by decide +kernel

theorem P0 : RAFrame.cOK TB 10 99752898761777419393 1 0 2 0 = true := by decide +kernel

def D0 : List ℕ := [
  0x100464b131060a17005821900544142444315044001814440162050014085801650506132444313285001408540171054214005c41708481110044115084841418402160c4021514441151064016044011408540190c4c017085c01410602110840915084c4190064913305421500604153854711044c616105021200504150854019084041510551110c6101310586142058417184481410597100c645124854e1500548160844013204481608604171064017086061708641111050011005c01958589112c642182840014286021000642190050416385c01208580120854014085c41518542170048415104ca120840916105001520544150048216106111,
  0x100458015085c2113c588170440719005441520580131044219005c813285801410512100064c10085461208608100840214104c210085c214004881610644170064110004c6190c48017085c3110858a15105c212185c2120c40114084c71100407190c4861320440140854012105c217006421410440142058a190064210005c8140048212004821510480160840017085c415104c01208600150c40319144801508444130050415084c4151060112285441700440122c40b173044916085c013084c016086001410502150048215184841210504171040210184501208500131060215184811900502161441215105d6140860019085061608640190c4811,
  0x12084871004484151440317186421604403151064216004811108401160444310085c011104831920550192c480151050217004041008500172048012104811900549111840212005041920444150c401182854815104c4121058a18006021300507101c4c21218585100c582192840115204c0160858017104c213104c31104648151044211005c01400406181c4881528586190440615004c8192440215405031114544130848413104801708506160858614105ce18106001520480130848018085c017085c018084c619144c213106501000402131048418004021210484121841413044411600482181054015204c413004c214104c6121844c14104471,
  0x15105c015085c41814480130c4051244403181058311244c0144060011005c01310482190040513085c6141048e1910604130050215186421810500192064513005d01610542162848810004c0141440715044011710482113048211085041210544160444119085401108480121064010044c01308506131048a151044117005c010304d0180055a1510504131048410005421400604191058210005881448547113844117185c2150048418404c2140048f110044713006021400542140054412086161918443181054a151048a181854215004001108582181864a190850412004461104602131840414085001610485110c4c410084c4121060614086071,
  0x150850413044011400545100c6421500542120048214184821200502151054018085c2100c48214105441600402120840012186401008544182c44611084021428480152050414005c51004600130858616105c418385041700507101c60815104c0190c44b1820401160860c1540482130440e190850c1108540160858417084001300644160c443190840011005c2151058018385841700544170864b1300502140844212085c01410642160048412044051500647100450413084c012104c815405c1110c4ce140044a11085841110640180860512005c4160854018085001208580151048214104c7111c60617104ce120054816004c418085c0132c4011,
  0x1110441160050a170850a16186051008401110c40117284c4120061414105c415305021830542191c480102044e11044c4122048413004881710641120864f1000486140848e1114500192448a160058e16004491418582153051018105081210541100c54212185421610584150060818106051218642190840019186001000581111c601110858410104821020608171c44314084d0172858014285481928584141058b1114550150848013084c4160060815005471004602191c4ca182448418005401100540141844010204411310601111c4c0181060a13205401208480120858018106421600502131048419144ca1728480132c44112184c218305041,
  0x190064a171054815005021300481111c4c4150854017105c2121844d17004c217284c018104c21300542150048211004ca1308484130040219105c019085041400648140064312004c2181448416005c110004c41700502190c40210045c016106021828640192850415084801308480142849c123864d131048710044c0100444612085801808506160858416106411208542110040011105421718540100058c1208500180c48a110c64011085c61608486150854013105c417044421420500121064218106441600582104c482120844510005ca12205cc100864113084d21008544140060216104401510582144048414106001804440101460214105821,
  0x110c64417385c013285c219044c111145c1100c48418084c411184c219005451018601110c54419244c0195841112284c412204c0120848015104c4150850a190448217005c4141040213604c2141050616085c61628484152c40212005c41310582131c403110854f10046431300543113c5441800640100c58419086411308400192044411344c214004c8190054a120040611005421300608162848014204841400442160048611044c015084c0171054511045041700448170058a112058019144ca160850015085c610205c414084401130403121840b110450412184121100586140848012084c4121858419244001108400161440117004c911085d01,
  0x15086011210482151864217044031708540133844018106421610544190840115005c9110054818185441808580126040c162444612004c212005c4133858015104021500404180440518406411220600131054418085c41410543112844215085481100584151060418105841200488130054411044041850402110c5041600608191040015205c01708504140840013185021900544170c44013084441000504190c48017106421400643100c5c0170044016105c8110064617406441524405160850616086001328482161054a12104801408480151050210005c2181058412104801210648101040416005421000482191c4841810544100850711084401,
  0x170050413044421308500150854014085041600582170058412206001610442184050d10245421400604140854017085c015085c21118484122848419185c2150054213184001110402174048a14205c0191060213106001308600111064211304c2130054a1708540150858c1308602112054e13004821400484170840c17205c111085421110442190c480160c443141850511084c410285c0170848c121c44117085841500604150c405180c40a120050215106401520506162858a1810604180858015285ca1610608190040311146431300643120054817284001308486130850615086001808644140054e15006021410609110040016105c417086001,
  0x1018582172850016084801210609121054014086441500500110854a1708518160c4021818502190040f1500648141848417205831110644180054218005421300504130044210085011134500152850a15105ca1714401180844015004c215044431320480141054213004c2130048213004c818005c417084c4150c4071410508104060211044c711245441200406190448a19205ca160044314104c0182c48219044c218005021300648161848213005c216004c01100491101458219005421500484161054e130054415084c617085c4160054219044c2101c48214005421010586140854013104831108600130850418105041500402151054015085ca1,
  0x10004821210540190c48014204c415105c01410642152844110045001308600133860013084ca17004421910500160850014104c41600402181050214005021500410142840812104c0150c44210004ca192c4c416004c51104480121048212005c4190c484130044b1214440170060a173440512105801608504110048e15304c4140445011044c21318643122854410005421810580141050212006021510504100054212104c01408509100048015084c0120864a19044ce1400508191058c1204441193c4c6160044012004c416084c0150858014085c016205c2110040410105c8113440019085c018105821900604180858a1400502130054216305831,
  0x110448010084031700544110850a1300503103040114005841414403120c4051520540182050a150444618104c61504442112850a182058c1900440170050b11044c2100c443182c448160050416106421128600182054a19005ce160440814105801414403195060013044011908580192c40d1600580110c48219005c610044c4171064a151864a161048010206041508540121844011284841100582141040111045441628480130040211104c214185c413084c01808540150848417484c417105821200484180c4841500482140054216285c41410580140844a1000502120054412084c01510444172848219304491200404180858015084c412004081,
  0x101048410284c012686041418443140444917085c110044c4170044a11105481110584150054412104ce13004ca150040f130858a1210489110460010084c212084001718502160048218484d1110c58217004c2120040813104c0132050412104c4190064111046021900544140854110045441604401161848a120858613106101938586181044512085001408480181058411104c010005041500502131064c15304011968586181050e12005c214005c212106061720640162440210044c413044011408504180448811104401108540161058a1408500170840113104c4161054216004821320440161064016b054015084ca142864616105c814186401,
  0x14004081600584160850019105c21900642150050217406001110642182c484151848418084c01810448120055013084841700603111044315004021700582151840611245421500602140048217104c017085461808643100464912104c013205c018085c1100c48818044101034544160050510045001430440132858616206451300494160060312005c2141058012084861900402140860e10005ca1310400121060217185081600643121048c1914484120040d17104ca1414448170850417285401220580110c6041108600141060217285c0102860218004d612044061014484151c44114105c21000482122864112284c818184c2171858212044421,
  0x191c4021000584180864b13105c0132858811004c2130048213104c31100480171054414184401300489111064418105831100442141050014384c4161054a14184c3110c50311005441100482141855210005441900590100040015005c21900542130050a150864112105421610501100c608150050413085401228482181854110104071210582141860215105c013105c2181040419185c21318502160844219085c014085ca1510405180864a15305411008504170c457140864018105c711004401608510150058e12285411104490180448215005821500502101058412105c0132040017105841008400100860017084c01210608191054c12084c41,
  0x1600544152058014084c01438584150058819044941600584120850016085821108602180050417205461208584160060f1200602190050413104821914485112848416304441808600183040613004ca16084c013284041308480100848c15204c413484c8151048016044011620604144054413005541610600131044116004c2180840113004c216104c016286471104602181050211006041108404100848818286001508580190c4041010480160848419044ca18104c412105c31018482120058213105c5110c58615105c81800502133050e1700400110044114084041610580120848416004441900441121048a141c447161054a121054014085841,
  0x10084c0161064815005c2170054b1008480161065c16105041208484141050016105ca150c445100c4c013105051000646100c546171064419285041128484196860019085041300604140c446110464015284c413104801008482190c4511704404100848417084421410582190050418105871120442151064d13104941204446180050213284cc12084841200482152844614085c410005c0100040a17485c417004021600402120040212205c4143840718204c0121844c194844a16085001310482161054419105c417004c2140048412085841740546122440316105401210590190840416006081310600142060112105081000584170840a102c4431,
  0x123854618205411104540151058510105001100480140850b11145541418583100c485102c4c41710556121058816105c01918403131060312284c0121054111145041310500134060512085861310489112c40410284c81200544170848411084001628586161c4001340600180440512006021300643120049a1700550180860419444c0190c4c0151064417084c01908580120860014084c013284c210106041300600102054010084c819144041500602180c40615285001810502141058310045c1100444213004c4172058016285c218405061808544150050a131058216105041600584132850817105461208580100864a1610641123850015105c51,
  0x16004c2180c4401000482121848419085411004600131c44517184821430604111048816004c2170054218286441700400100c5801034505113c540100858018085c810085d01808440121840c160048a1920510141048012204c0150044017006021800583110040316084c417005881400442191854816004c218004c21604403131440917084c019244841400488160c44213084821108492110058111245441440588130064815004c813104c810005c017205401608645102854018105881410645130060511545821900540110850219044c8131064c1828544140c4491200448110048a19244801404441160858c18084c0130840418105c615384401,
  0x191440a17004ca180850c12104c813005441208640160850012205c01910602150054812106041300483102c44011005001210509100c541110c5441010600100044a150054a131049617085c0140850414005441718448146044510004c019285041528444110854614284c4120850110284011500502170440f12206041400600100454f11045021500641110464611084821510506180040010005421538406120054219044c218004c2190c40012044401008502150060418105c21500544170c44916184ca12044011208604190448212105801908507110c5c21800584143850017205c013205041814484161048015086061508540121050215104101,
  0x142040012405021300645120854015384441310486160c40517385041728504150844012184ce15104401900441140048213005c2142c4091610484141850a1310502180444116005c010004c4186060a180c485110c4c0180860d101c6401508502110850011085c0110c4c51128441131858110045081200542190054218006511214401114460217004c8120058212005c214004c3110c60112205841000548101040111385c21748484130840210005061208486160858017106051104500180c444120054211005ca12085cc1404407140c40512104881518640112050813104c412105ca12004d414405c0174044411104431204441131860a102054a1,
  0x171854219006041500440130040214284801624405161050417085c0182c4841650484170054a160c41d17104821500485100448b1030440170050217005021200580101854011105821300406111860017205c5110c5851100582150050e19044c414084c41528547100c64311105c0161c40519005811038401149440117004801110440140064313104831000602150048217005c816106061310484121064313104c01708604182850012184001418582191064713105c4184c40015184c2141048416005411014587110448417105461310604140850017085c4140058815285cc120044017185c21310484151040016105021300590175048012205c01,
  0x1520504190440818105c2113c582160051613404c816185881310584132858618105021300482191444414005c2110044213105c61740485100c4c212104441500510120044019005ca18004001228480120858011105041700402102058711084431500486100058419604441110605120858615085831128411161050a123054819044821210543102c58417185c21410540121054418084c01208581110c4c415085801208490141048a1804484142058014085cb1120402125064a16005c213006081904483100c484151060618085431000403142864014085001408540150854417004ca19085c51144403132c44012085401208640142044114284081,
  0x15004041008485110c5d111444c215105c1100854016204c1112440213004c41220580120850416284801720644190064a17085801210442110044a140844016085c414005c0100060017084c615084c01420504190040a14084861208603101044214085c0140858412144401104580151064219044c2181054419006491300582130058a160c44a160440619106011210502130048a15085441028401111050215004c81708400191054a10105c413106031008602190060b1208544170c44a1100444140058211184c41500441141c441142860a161848219104051600546111864113085c01808601120c40418105021310404161064411045c210144401,
  0x12004c210005ca1208404140054215006021114484123050212004c819044c2130048f1000401120064217004c417085cc17204ca1600542160048216004c4141058415004001814480170040815286021400503110c5ca17004d015085c618085461410542160054a14105c21740640170850419044821600484151054416144011100442134850412044401828508120c440112c542130058214005c011284431508540190c4c01508546152844213005001018642110450c142060310004c01110482170044a160854019085ca182864b13105c01300442150850014105021518482151850212006021310540130851215144431420480160844013104021,
  0x171050a12104441608400170848012106431210580190854018084c4191c40e100c5861910543100c50211145c019105421910440170044713185c416105ca1520642100864b1320640112c504140860013085801500400130840212086441400484160864c160848c14085c013385901718484120850a150c44e12285441208484190064419106481920407192864419005451000600180850e100864415104c8161848211184c21000500111844b10104c014084c0140040017004c6101c5c212005d0120c40014204c0120844918005411014584110044318104cb112440516185c418286481700502151058a133040816004821310600112854412104c21,
  0x150854a11005c2161048015085401704440122044613004c21600646110448a1200583101048413005c21418582160048111146001308484150844e17206401640403120054a14086421030644190040218084061300484140854b110c4ca12006421500502141060016085c4180440414086041910540160440119086051210580131058816185021418547103448414205401810541102860c15085c01408480111064217404801504441191064210105401410544190858a120048210084001210480121064913005841408500120440112105501620484181444319144c510084011608640161049015085981808640180c4801410484170854a15004041,
  0x151040412085ca1000482100844218144021010544130054219044821600549100040d14005421700645121440113004c417085c71004480180860c150c44314105401628489102c4851024540100058810005c311045421804490111c640151058e140064215005831110443150c40212084801208644161060014085c01310582121c40115105801318450100450110245c4133854013084801100402170858017104941010642100050019086001628548130c441130c44910004c31114500110858217405c6160440118085c6160848614205001120480111060312306001104540120c443184064410186431300544134048e19144d2190c48017084001,
  0x10085011120540190840411005821200542170050213105441000402120050217004c816005851004580151048218004441708580121440116284c014205411108541101c5441128600151050215005441320542101850c1708440130848415004c4190c4c418044881700584120860712084d014044431308480130844615085c01110588130060216185441508546130440517004c2180448e131850111144801708484160049013086401100400180044310185051108484191448c150848615085c4173c441190c48c1330444100454214004c418086001910542150c44812004401300544131048e170044313105c6170c44c13084801308480150850c1,
  0x12085061210482170051a160054817184041910582191854e10005c4161064211144001004641120844018284c4190854c1924480160848012085c11120481100448414005421640601110844611205061120580130854417004c4154058217105881008504180c480141054a1320544140c4411408502111044e121060416084c11004540191058814285401908544193064313005811100443180050311004c010044801508540131060312004c218004c218185c216004821210640110c4c41428400111c64014085c0151054217005481510604180c4051200502163058211105801608504150060a15084841418542130844216205061608604131444b1,
  0x1700608180448213305c213105861708540130854018304411440486132c443140860616105421600602184059813084c0180864b100444614004861104403151864010245141500542191050013004031508485110044718006441708605122860013104041310404162050010084c6140860310004c6120040015105c018084c0141050818006421604401151064b120c40517305c0100448a13004c413204c015104c214104c4131064b13106461400446130048212284c016085801420500160040010084461200640110c4c415284841708480120854616085401838544151860218284c019085c01304407140044217205c01014484161050212005841,
  0x190c48c18085c01210488172044016185c2180444714005c2130060217104c0170864417004c9112c5821900502151844a120850413005831010403161854311044011700603121050015104c217004c21318542180444415184001508442164061018484021808641120040615304861020401111044017104c31114608174064112204841700482130444312084c6152048a160044217105801640580100064111045c4141848212004821500608140060e1300484141050812104c41228440160854019086401508500121054419144c11008484140044d1304447181050111344c5103c4c310044c9100844114205061538640182850213184c812004c21,
  0x1810540160848a1318548160040e15004c214006431210404145854a173844d1510586131040a100460112104501410502171c404100c608140048418085461608545101840d18105c6150848015085c014105421200482121050c1918443141c4411808582100060a18004c21300582171850817004821714440104c5c01808541100c5ce131064018105041508480162044619244c0123849012104841900642170054217004c217004c21418582180444113004c21210606170864618085c41310512180c4901210500131054216005421304442182c4431220581110848413105051008412101844714304c2140c401130844015084cf100448212284c01,
  0x162850e1200542150040218185421600502191c4821500487110060a1408480130864510204401410500142048c150860911046081404402101454a141048213105c0122058b110c4c01108582100450415005801008644104060312006441908584131848218004041430402181c445140c446130060512104421704405111c58613105041808583103448216105441800443160058a15085c018085c01408580130854015085c012085c6190c4c0171444419084001608400180860a16005c21800542180c40211104c01000580140854a183058816104c614085c6170c4031814486160858311045821934482137064113105c81228540190860112084431,
  0x150050a1814482100054217184c8121058013105ca120850415105841500444142060415005c218144841904485102040012086401700446160060414086001310482181058110044c41708403171040a180c44517685071128502170058412084801808583111c40111004821130500132048616085c4172849013005041220643110844510545821814480122c447135864113385c0161440716005881410604111c58817004ca16084c417006431228441120854012204c0122c449160861010006041108640110c4841200508130840012006431348582191854215005021200584190c44b1808546190c480150848a12005821224405131058613084c01,
  0x150050215185441008604184058c1320580171040415104c2194050410105c01820601110458015084801620585102c5c419085c017085c01608486150c442114c4111458485100c5821834481110448417086461900440142854016084801728608150444117084021408584150060a1914484121040817004c4180860b12005c2131048018085c01444407150054215006021400482170044210145c4161c409111c5c013105481800544130850614085c41610542100048210005001320640190c40012385c614085c0120848413006411008502181850215404d016005c214105401608540180c404100c48418104c0190840d1200440161854215006421,
  0x140045413185c21300508120c4411250496140054a130840418105c010104821600584180860017085441914401110844313005c9110044318105021204408100c6401980640170444113085c416184821808442131050218004c414085c016105c4150860018085001408584170058010005821000504120054215105401920646150864f11144801508580173848019084401908501110044b17004c21900602180060214004c4120848111044c418105001208504190448414084841208400140064216004c412105821900588111060413284c4140c441160440f110064113084c0142048617085c6180850014104c213105801308500142850212004c21,
  0x111c4841410584180060215304ce160060217005c214004021418543110040217004c214084401910645103051110505051040404130058218006421600582181058018085c419105841318489100c5801440482181c48b100c4c21500484130850013184001330544141444315104021608400171058413044471604441132858a161060418004c21210504160c402100458018085c61408506180850012285c21800582121058210085c217004441508500181844017004c213104861220540192448012105c2150048e16105c5113c484151848412204001610506110454c12106021500605121064215105801610582161848215005c311004c814004821,
  0x19044461100480152864a17105c216005851104407110c5c416084c014084c012206411020592141054417084c0130844412105c413105c2110c60711145c415005021800503100c4861210484182c482131060014085c6192054616105c214004c4160858012084c415006441928648171044115105c21310646191054217184421228507100850014144021200544141064313105871004440181050815304881518602163048215904c81528480150854615085c414105061600400121050012105c217185c21620402141064311005821100502130050e1810580170c446123c40a12105c310144c4140c40514004c818106401928403170040111006421,
  0x16405c013084c019085861910542101058a14405c414186421028606151055c1510545110c502141058510004c4192c48415104c21900542190050212105c5100c60112104c214004c81410600160864419105841830404102c483100c4c419005c0101040810084461710503110c5d01300644152050415005c813004821600544140858413284c4181060615105c011006061104400111454812184c21500582160050413084841510604190050a154048216004ca14085c21008482121850a14204c412004821000444162064d1210649130050213185c11004602180044217105c01808500193c4c414304c0110440111005441100608181c48818005821,
  0x16184c110044c212104c012085441010500104844114304c2135850c172054010086451000542192044915106041510483111040014106421100505101040a100458413044031824447100450510245001320501110460014044451804482151860817184c2121848215144451810408132858411285401200400181844316005c31124504180050611205c4151844113005421700482121058a15104801508484181860010245c417085041310506162058617184001900542120050416085101600582121058014085c0130040218085c311004cc12084801608480120c4041200582191c440100458411085441700514122854012205ca15185c217004031,
  0x1708506122440314005c219006421910606190c4861310502161050019085c010384801900447121060a1628400100848017104881708440161858412104841638600142044015084c0110c4c510145841904447140c40312184c011205441408582100c48216284c0182058015085c0121054a10104821210580122444412005c217005c21400482120048e120c40012004801100544181044f1014643101464711044c0151844117085ca130440115104c0150865614004c6100448011105421828580170040c10105c5110c50013084401808601120854a1950441121060419105c31110405141054017105821200502191448015085c511105c414106441,
  0x19104041004584120854014205c615085c7112440818005c210105c4112860416144431400482110058a190864414185161718449121050a15144101208504131048012205821104501110448015104821710500190c4c4144064010104491310540141048213184c81400608190448212004c5111c5c01208510151058010085801424443150c408110c4c216006421110540151440318086061808641131059a131050013004401230482141848814105c41210607121048611104401700482160050216044411000442170048c101844510004c21324441142058b1010500180440012105c6140c40913184881410484120048413204c310144c419106001,
  0x15406001820444102044910085c01708484171864312305c2171c442114450311004c4100850a18005c217005c3110c4c3110044211104401618542191050a1604441141048417184c815184ca1108540150864419005c413104c21430640100458614004001938400190058010185ca180840212084841728443103049016304c2132445115004c411105041120502110448412044041208481101c54018085c0130858016205c310045c215004c214105c4120054011085c01000641123848410105041210506162864011044c41610400160040211084c01814484191448010184c0130c40318584c0130044016005c2135844514105d0160054f10146421,
  0x1500509111848814005ca101458011005001208540130444515004c41208586160858a1710540150854612084c613204041800648181c4821218484122848212284cc182850214104c4141050c12084801470545110c5021724442120850015104431600404190854e100c4c81904482140048e16184ca16086451240504170054217006041704409110c40413204c01408606152844510046061320580190044d17004c81700544150850c17084c4131054c16104841220546156c4421118548100448612084001708400142064b13005c21700602131050019105041620505111844010084841608580150c403160058415085d0141050417005c213005c21,
  0x17384c012384c613084c412004ca19086471208540140860a15004021900608144840a14405021228400120848612384c014084ca120050a121060a16085cb100c440171048215004c218005021800545101c48012105821210540170040f1664443100860912105861300400160044314005021908402140c44412005c4191064312005021510540120c44012084441100484190c481100040719205c4120054219105c0192058c14105c419385521810542123058415084801610502100450212004c21800508100c442160860b121054012105821610484144850a1620641120854a18186441118443160864416044421100442121044c14085c6170858a1,
  0x16385c2113860217004c4161054217006021328500120860414005c4182448a15106401608580190044210084041700504172054c15184421318454140860618085c418005481500544182444a17004ce151044419005c1111460c160848c12084ca172860619105cc110044114105ca1314444140044211105c21904484162840a132848010006411018406130048010085821514442101464512105401514401130048a14084c6131058815005081510608110858011005c4120064e16285c0130850013105ca184058e1130602191860010005c01904408160040215085c013085c41718496160854019144c2162c40313106001404405170048213044491,
  0x1954448110c50219044c412004481408600110c4801710584150865014005c2101840219044841908400150854c161048413105ce13004d61608440190c400156850a1200542191860214105c0130c449120440115005021328507100448613085461924486150848014104c4140848010204c61410580104040012004021308406122854610085c0121040a1508540151054d100854a1208500170440118105821704409160440b192858415005c817104c1110c48214005c0100454417004c41108602111044610104841618584174054218006421110446151044217004841924400150864618085801804401171c40d1508540180850416005ca13084c01,
  0x180054011005c4130050816004051520500191444412105c011185801220400152060a19004091100482121048a110040215004021318584150858015044411714401191c484141444114005c41508580131064a18085c618144841208640111460312004c2152844613404c21828440182050210084821400580100048418105421000602111044912205c01508480141440410844491204407161c40317105c31140580198448419105ca15104c41210546170858210044ca15104011208480131058216105801704442154840a102060215084411428400131054213004c211006081828584131050613205801710483100840b190c407190850013105421,
  0x150848310144c416105c016085801620580181054217004c8101454a192c48613284c212104c012084801720504141848a1608584150040410805801208480150844d13086491118444100c540150c404100c44013104851128447150050217284c7100864815004431300500102060218184c21918600100064a112858017505401538485110c640170850010105c21140540180c496161050a120044213185c212104c0190044117004c214104ca16044071240444191850213004c415084c013084001900406140840012704461910502131040014086001608584140050216004441810504150848014085c310045c21710604140048a182449017186021,
  0x150c444112c48214184821300483100c6401910602161444319044c81500502155850010385401308484180050214004ca142050015085c41200605123864c152054511184c2161050a15004c21300582121c401140440313085c613105021208442100c6441510546140864616044401200608130058218186441010502161058b110040417084c4172858010104001000540152060013084c012105c4162060418044411804440110850a1438604160060214005831100402112c6021800508120840314085cc165850216105801808580190c444142854013106081718494170050819186411000404100054412105c81528500140c405162444016084461,
  0x14205811108480170854c121064a100c48c182060413005c2100454215106041310504191060619105c81028580100844010085c017085c41500482140c44215205801320485100041410144431430544121064312284c4151c40715005811108402112c50a12084841610440120864113284c111045081600402150840411005ca1800502130064416085cc1408504140040010084041204406145444113084c4140050215284841310500122064014104821710643110054014385c01310546100448c1908544122858012085c015085801310602174048a150050212105c0130040015105ca1210500140c402100851012084c0110860a180058416204801,
  0x1900441103c5401404447120858416105461710442141864912005841210645120858616204c01210482170048211344c210104801210542120844218105c413084c014104c2120050b100848417105ca1318485100c582120048416244051208641121440114004c81214403151058019205801410506100044616205401410482140048216284c0130040219244c0180044112005c311004021300608150044811005c2141848214005ca14084841704407111854812005c2171060712104c41738600191448218044861130540180850c15085461208641122044011084c0120848012105421618507111c60111204ce11005421200600110044712044011,
  0x1410480110840013205cd101060213004c2180064313105c4174854011044c61208643110454e13184c219005c41300440193844715104cb110c644150058e160048a14085c016105c2140058218004c81500510192054415004011108441132860112385c615104c21604404120848017086011104487100c54218304c2195040114004c4190c48b11004c21310542110848213204411510500130858015086061800440121850213004881418484140850414004c212004c412105c415086001328502131050015085461]

theorem S0 : RAFrame.seg TB 10 99780724298206201969 63 10 15 14 99752898761777419393 D0 1000000 = true := by decide +kernel

def D1 : List ℕ := [
  0x1200605121058215186421600642151440a150050217185c218105c612405081800504144050212106001308602103840515085c111084c01408600131060312485c4102444b19105881418605121060010005c6132060712205c016044401500482150050a190c4c017204c01528584170850415084461310604141c4431310544140c4451708640152064a171858215004821850401130048212005541700500102054111044c41418403110040014405c41814406191050310184841908546120858c1104404100454214105c01208543101c5481700483103c48013084c017004411818643121860419085c012084c018284021600542150050a17105421,
  0x130840414004841508486164050e1704408151060510004c5100850a13005c8150050414085401210645100c548141848217004821500582140064011045c2100c490151040a152050c1308500152840e1504442110048010004c01200402152850111045c2140440011304ca12104d013105461508540122850214044001100540190855018006451308503102c51218285021934442153058813104c21004486141050010005ce1000600140044012185821200584150444112104c214005841948446191844313004c2140c4021110488171854214105041918443180050219305821840504153054210044c2140c447130840a1600548130040210004c81,
  0x170c44010085c01428588150050e10005c111304c6161044413104c21300584122058416004821914444152c405182c48e140050a120854016086441500504100c4c4120058814105ca12184ca1410480110054415004421818582191058012105c81600502141058710284c8121054a150050217004c31110446171844215085421104540150864112084c0140044016185c4121050e12084071400502141444611085c0140040014005421524440110c540133848017204c01750600181055618105c111045021604444120848017104d01528640110460017084c6170861216104c41808540110c50414106461808604130040a152050211085c414085401,
  0x15104c214104c012404c2190050214004821630542141858011044801608541110849014105c413404801208540171048212104c0150864b11005081300542190448213004c21400640100840312005421710580190844116084d01620400180050216004441950640191c401110c487101050412104c21600582132854a180050f110c50a121060017204801610482131050014384c6170858a1210506190c4c4181c484121444314384811104400120860c15184001418482181850219185881218484122854814004c419085501514403131850812005021500602140044e170044210046021500584192054a15184c412084c41700443130048213285801,
  0x1428540100c4441100502100048210104ca1700645101c600160858418005c21200604190c4c0180850510084411610542120054415204c811005c2110840312005041610584170851019084021410544160858a16005c2160040211105461300441130060217004c41308600150864c1708645130054215184c415086461708600161054211004c4130859616104c0143860618284c2110050e143054414044411310482140444119044ce1710486190864113084c01210641100064c161048a1310482140058418086001408586190c480180444218105c212006021500609121061015004ce131050410005c2181844011044041010586143850017204001,
  0x130040217004c2150050218105c41900508124c4411914480110844d1028544155440c120858510244c6151058211005841620604160058a19085c01408500140040117004801010447120060818004c212104c014086411310502170044512084c0151060418244841410500120850619244c71128403165858412104ce12004c2122850615104c21300504132058d100c48a1220584181448017085801708500140c44b182058210104491208480151048810005c310004c2151060011304411200583111044c110040c100c50411004821610480150860413005d0130848413006021300544180864a11045421004582130050218005c4135054211245021,
  0x19085c0141048410284881710584122044010184c01100602113c4c510046441500642151054a1604419111064416004c213105861738501101c58013206441500504180854415044411600582160044417086001710442193840c1400484142050010085401914484142850418105081600483110058e123048a16204c418005081600547100458e1400600101c4c0192060211044841800644170c4401110582183060215006481818500100058a16005801008608141860416106491200504180c48412105801408480121060214004841910543100c4c0150844017105821900642181840514085c4151864416085cc17085001220504161040010104821,
  0x14105801320580160858013084c01828542130040e1804484172050c142850310004031710442170050213144401104541100c596112044414185481318482160048212106001004446171058211044861800408152058015086401010482191060110084c21000505110c583100840212184481300649130c40511046421600644160c44014104881108440160064b1208580190c48c120044012184401004540190c4ca192858417004ca13285c2171864a11405c813004c3113c5001804400100840015185c218004c3100054710045c8120c40112104c416205ca140060912285c1110464b130050110044481528504172844512486421000544104c4421,
  0x110c5421600442150051013105481400501111c482190c44411184d217084461310588131c4041028456110854211085421730442160844315086411210602160060010045c0120858012204c016206411208480182448a1500582141050014105c21700500100065311085001200446170440212185451008443170c405140054e1828500131060a1124544130059415004c4140844017105821218642150c44811044001700400150054a1208502110450612184021710583110840018105841200582152c40015105c11110440111864214104841500503100044113006011014600100c4c0130864113104c417084c4153058e1510480122040011085841,
  0x152050011004411310400132850a1308600132040c130848c187060310104c016104c41408504154058013004411000401141440318144841330485101040f190864017085c0121058212185421918502121054018106041510603121840218004041000400134849a141848215004c41704408162c448142864019205c41410540160c44c101c4c01308487100c482150c40b120c44117084801604440110c61019005801100405144c44316086041400602180054418084101530644181c40c12105c0181060110004c0160850014105811004503110c540130850013506001910602150054a16104c8181050c153840111205c0150864015104c814104011,
  0x15104c4142848819185871100584132850a101058019105161908580132040a1700542160054416085c01208580170860413104c0162c40119144c019204401000402105448014085c013084c01008640191054217004ca101444212005901508500131840210084c0172c40814005c111005801610582152848a12105001208500180860018205c0160858c142c40010044c212004ce170048419204461220504111c50214105841500583110440616185c214105c4111c542140054e19444021108588184060613004451000580190864310004461128544110854a150044e10045c11104602144048014104c4190854012684ca1210540141048a12084001,
  0x1208544160048416384041218542101840812004c21010540130840011084001008480120c440110464113405c4150c40514204801410482190050217104c012386441904484150858013084c0142854212284c01508484140840213285c219304081400608160054e120044a171048213004021400544121c44114105c2170060011005c0180c48415004c81800544141440410045041708407132858015104c212005c3110054010085c213185881128451101864417085c612084801410488163054216305021218482190444319244841300482173044411284431228544172c4401604404100444419085441600402102c5041004544121048217185841,
  0x180449017084461208483111458615105c817005021518642110050819185c414085c7104040a120850613086001114408120048415104c4140854110044c416105ca140050214006421700543110048211084541618440122850014105c217004c41714442180448a11404481410581110844710006401808546160440517104c61840582161c403140850015085401708504191c482121860815104c4180050414085001108402101c50418104c4130049c1208504141058a12185c418044041000480150848016086041500502121048613086031000504141060018084d01910580183c480140858616084c111084c510246411268540110858015086011,
  0x15184041100441170050212104861008440192c482141854215184c21800602140054417086001508640153848617044411428542150048416085c1100c54215286441700583100c5c01608480160858618384c01408540191448213184c4142050619085c0140860a112c540121048212004c011086461100480150864a17144431330582120044217006041108484130058413204c6131c442131060011004c61720480130040115105161904448140840215085c01508480124058818305821904484190c4041914400121058219305c31110402110050615204c0150848012044011508540181c407181054217485c011005401408484171854417285821,
  0x17004c21400588181050614085001308544190064219144c6141064b121058211286401120641100850019105c8131c40214004c2120440317205c01308481116448a12105c4171844c1100642100c5c8190040316304ce165850a1900602170048214005c2131858a120444518104c01008482102444915104d01908501101040410104c21810504160844917085c01208641121049013505c61920506110c5c018104c8172444118086401508488100c4c816304821200605110c640100844218004ca18084c615084041300542163064215004c41428502151858415085c6191c40411185061210482121860811145c013085c61228605110848018105821,
  0x150851612006421004482121054019206001608484141848a125858817184c4120848018084c6122058510104841400484140848015104821700544130860b1128508111044e16085401850500160864513005c21600580110c484191058010284021908642102040a1708488100054412005c415085801938605120064b1220581101058e131c44411044831100480130860013105411004508161c44914106021004590132850a19085c6132444313005c2130064215104401610502143060816006441908580141054215004c418044021608504180054911145c213105401408600140440519044c21410544141059017144401328502141060512004c21,
  0x13106021804482122c443174860e18005c218004ca122848814184d41004441153060215105c614104c213105451048482191c4c414106431200644150858012385c61738504140060a190444015084401210606100044115184821810500170850612104841950500181044011045c21000580130040015004c010004c41500582190054e13004801100500150858a16006021404447120058415384c016084861630407160050215184c6101c444121060419105ca1300602100049311146011220540133040615005521128443150c40111045c41900544130c4061408604170044517206401608484121050017085c613084c41500604114450215005441,
  0x181054215186451320546140850411185d013205c415005c410086401710402150040a151058217384491914482150060312005041410442150054e160440114184c216005c2161848e110060217004c2121048012104c21530508170048217184ca151c441160850d111c50015204861708500181044417085811008609102044117185021700545100848414044011800582120c40719105c218005881500484140850612085c711085841508400191040112084c01808508101854015086041458440120860a140058210005441304440120048215005c413084c417005c11114544191c4c9100c5801300441130050a142858110046021410540190c4801,
  0x1200504140848014205801208404171c441122c446121054413084841010441102850a191448a122054511105861710582141848818004ca1620480171048214184821204409150044912244051408586101840210244c0102c48411445441508480120850b112044015104c013105041408606190850415005021400544112050014105c414205c01914402110040319144011100502190054e1204401160064a17206431120502141054014204c412105041900606100064016104c0110864010184c01708484130059019405c2121060618285821614406150848014085c4161054b1044644173848414004c2130060214185821200500111850015085001,
  0x12085401238586190854418144801744440113058417286441060600110c6041844408171c40e12104c6180c40c100841012144451310482141c40413105c91024645130058e145864111046441854440180064414104061104580162060210005c4171048016084c01810582170840212004011124643110064019105c2161848214004c215005051110482171c40116005c21800542191060015085001208580110854012105821600642161060413005821110484181060712204d018084001704443150854011084c01420544120050a151050217105801610544120854b101850416085001408604130c401193c488110050a152440715104c812005821,
  0x151444314105c01208586152050211304c016084c01828542170c442110c64111004c010084c6161065110105081300543110050212105c7100854019106021400643130050212005421718645131050a1508486131054217005871110442100044c190050212104c016086021000540172054210006011210482142850010505c511084461200484120858618285421900582122854017285821300544130848417005c214104c0170850013105421200482132860016084c4161058017004061908400172840013085c2110c602140050e180050812184c2150054412084c61614441191851614104421718508181060013085001210502130c441100c4401,
  0x180860414105c612084c0120840b151048a161040512104c01308444130058213104c417006051028604160c404180440a11106031034441132c40a1404443150c444141844419285c214005c3111840210145c0100c4841308506101454a150850a15105861408500120044019005c610085c011144001310541111048411105021400445122858416104c217005c8170060110044c2110048815104c01510582120444a150848017085ca19044c415205441940401140040114185c41738442100860610085821614445141048210185c4141054416104c0100048017085c4122c400150850a130064217305c21200602151440411005421600504110c4961,
  0x12104c0145058c151050217005481328640151048416204061208504101060419044831118480111850013584c8180050310004c417106081728540111054e12285401518447172c4451408605120054a150848011084ca181050a14184021104504141060219005821300602170040219005421930640100858e1500582160844c19044c81500542191c4cb1020540160864d1310509115c54212005031100486110854416105841320480160040113084011200482120044a11285c2160840213084cc1300400150054214005ca170864a151444314005c2170c4021720444130054a19085c6121059310045c2150064312004c21430602172860013205801,
  0x171860f12285c0180854013204841900405120864414005c413084c010085c01008540121044819185441420600130860014084c015205861300440151054018105421900584160444118204c41308442181064214185821700483110054219005c21300602140058c10344c4180050219185841708540101060e1300542164050a1510604180054011005891018584150054214005021410501100c45014285421210486120440712084c0150444212085061300400101454111045821000600140848019244841910580110c6001810582181058413004c41208504170048418084c6140440612005421200644191448215005421700544160848310044821,
  0x18106161928582180040311105c41410440102c50415044421104652191040413104081700488190064511245c21500504130850411006441608480131054412084c0150c40319105c6122044716086001308500130864513004c217004d01110602172860a16004ca122850a18105c6103860218044841208480101050217004c4181c408122054013085c01440584121c44012005841608640150848014086001314415150c440130854c15105821114540140858210045c01728542151050016004401018600111c500170444010004c21000444160044618484c81000503111848814004ca1420540190860015385061308600160440115205c413006021,
  0x1108640170840512105001504441120c445181c44c1400504151048210004c21210480151048a130840414004c216004c81310492180c44b160c45010146051210542110050211144c61714401183440312085c4160060217006441808642100c582150048011005801510482120040219305841420540131050c10005801838580101048711044801008602171c40119305c21918542192850417044411304401140044611004c8113c4841304401160848414005841708500160858a14184c2180054414105c21300482120054816005c418105c8111c60416085401610482160048419085441814405160851e19105c212184d01108500131048417086401,
  0x143058812406451248504122050a150048e101450c130848617084861208400160850016085c2110848215004c412085061208580140860d1108640150848c16286021418602170054b1008405140860a11004481900445133854615084c4120048414085401408653130848c130858210044c6111058011004c61708544161850214405051100408170c40612005c7100854218006431100404130860014204c417004c4130864a11444c616085001610502162040718184c5110040419044ca16284c4191060a1320480110c480130444113084ca102860614086041318582113448310005c4120848c191c442190c4981320642110c4ca181058215005451,
  0x1204442100c50c141048417205441900608170844717004c415585d413004c410385001008444181858213004021600589110048a1210542163054414084c6120850017385c41608442150854a1204447121060415005c511084801414401141054015086441600582190050815104c015084401008542100860a19144431200400131058c140848013085041518645131060818004c110004c419185c217044011610506170854415584841110480193040410104001038441180c44015185c2170050010244c6100064016004001000482130048a1210502121048413304c21548482172864d130864512004841208486162054013105c2141440313105c41,
  0x1608644190064418085c0121058212344411014600180c486121054413205c6162058a14005841310644190850016105421200583110c480142058015085801208486160044115044411740541110c5911010444110044215105ca18085041900582134048419185c01004510131050015085061658487110048615085c4160048212005021700502130c4421108512162850e12184c41304406141858215104cc1734401190c48110344c0112c5441624447101844614104841818580100c4c8150060216284c2100050417285ca121858419086561500502191864312184c41804406120058a14404821200484190c4861200441102c494172441916084451,
  0x190854011086401510541101c5821904484190864113084c0120864411045cd1104544120854a12184c41810602150444318144941310486110840019244841518604140c4451208640190c4031900502121858a180860416004821600502180050011004c014086061918443131040914005821300482110064219144c8100444315004021400502190449416005c218005c41304444100050710045c016085c611044021010409141440411045ca191444417004c2121860213006041308546122054417185421700480110c4821410404100048a1904400130060a13205801408600170c4461104640140850015105c4150858c18105c7111c542191c4ca1,
  0x110454416104c41710485100c58013104c418105821800603110c600140860013205861308484140050215044491610542150058e1540608110058015105821804402141444014684c418104c012104c8120440611045421848503103c4421158440160050214284c4160050217005041110508130058410085c4160050a132864e18144401608442100058016084801308480131c441180c48618205c41510642110c582170440113105c11138483102c5c013085801740482150048414085801220645120058416204c0190c486180c4841510580152848214004c217004c212305821600482100840213105c2132864018404c1101c582140050416105441,
  0x14044421508580180c48211344801408584181058412004821300442120048412084801610542120054311004021400402102044011045c21700502133060b11105c2120064415084c5110c4841810584140058a14085c6172044017285c8191850419106421728480130044212105c412105c01000600161c44014084001230600110050612084c015085401218402122060710206041304408130c411190054415106421904488162850615205c4120440611045c214104801110645120854019105c215006421004483111c4011228580171044010004c018085c012084c01904402190854c190044011045881918502134048013084c0131060a16085c21,
  0x130c405162440111184011408481111c54012085c014105501708584130048212004c21500605123860013084461710588150054210105cc1924486130848010105c2152c407111c4c4152c400100c54a160864a1410580121058212044031508584120048811104c41800642191060512006421910548100450019285441208506160848210005d0151049013005041708600142060c14104851040582180050213105d2112448710045441700607100448213186431200502121854a131051613105c81300482120054216006021400643122848413105ca1458400131050215104c01408506120848c180851110104c5100051419144c4181448017044011,
  0x17284451400588181865d12204861308504181c48418205431104642161064410004031500442130050813005c210004c4150858617105421700544163854613084c01228644142848415085c2111c48415004ca1310508171440313004c01108544111450218144861820600140040115284c0190844613085c01110441100060018044441008486102060219044c8156840b110450413284c6110850a14284821400484142048c120858415004851024485101c59812285c816244411408580161058210145441740584190058412004001400588191864216204081310580100040019105c2192858016284c411085ca171050a1530484180858013044011,
  0x131444d182c48418004c21318442110460218185c1111c40912104841900643130058212104ca1918584101064416084001008500180840412005c21704441141c442140440213284c6132c402132858413044041020445100c440130c4031400642191854510044801908584182860512186021300540100860410105ca1908640180854a1608400181854416084c0181448611004c010204c41104482161c4001000480170860419005c21310540130850618085801408506190040d1418602151050a1308403120041912105c018084c01918440140840010084001700643101058410105401220401110c4c5110454419185021710584160064e19184421,
  0x12104841500541100448417084851024580170c44a1318542120048219005c413104821700644140044c111040013105081708441150048813305821608448170c40612085c0111448213004c41308480182c401114058c170860011144c418204d2131048215004c011004c41200508151864f120050215305c4180858013105c011244c219344c0100048018144421200442182844512105c0190858110105001108502180c40015184c4120858017144011800545100c4421604401141054413005421910580160854416005881508408190c480120c44316004c011184cc12205c0174048212006421510580161064310005041610645130850015044021,
  0x170044112104c3101c4c71004585110850019105011010401170860019105421610601120855017005c4101448a12205491108482151854212004c410084001308644141c4431708544133058212005c51008580140850013285031110405120854016505ca1310504190050215005da1808409171840316106511310644100858015085c2100864216305061108645130858015206411310544150864415005c214184c4181c40117206001608500130844019085d018185c418085c01210542121048a140054213004c8132858614085ca191449214085c4120054e10105061908404141860413204841110400160854012084801210482160048216005421,
  0x140060a132064513105c61300446181850e140058217005531000405150840112084051200502140040a180864418004c2141844212005c211144c41700402140060311006091218642191440412005021704441183060a15105c4112058617084d01200483100c481103c5821210616131060414304821814486120860015205d8170844612085101218584130848c18385c0150040e141844214105821600604165444011284c414104c2141044014285c21114544171860710146411208606150858016105c215484861000403110058012085c0130860013205c01900400161060c17105c21310500121054817004c3100048e18404c6160844019205001,
  0x14086041140540135864818004c4121050a15085c5110064417084861820606180858c131444413086411310602151064113105c21500642171848210005c810105441910580150c40416104c4140064111084c01118608113044018144011200601110460213184881408442184054910145c2160065015285c214004c41708446110c58c1308641122064b13285901300502180050218104c012085831000640180854a15004c2132440212104c219044031308481100c482170c4011810610112c6081618482170c44214105821820401165859615006481710480180864113184481710582171058111045c01858502170050212284c0154048413086041,
  0x15005c310104c41830510150854a13105001208484120c40115084c6160850414004821110480151048211045441708500191c44613105c414285801010402101050613085ca191050d100858016285c3101854213104c013086001510507110050615085801600440181850e15005041410548130050a112048016004071400645110844b14085c01710502180448417284c412085801914482162c44612084c415105c019085401204441120854110084c017104821440580110c58413105011128482170044414085c01610502160048214084031620580160848015084041310641130848417284c0160864c1608480163854a180060a150864417406401,
  0x110040211045131108500190044213404c213184821500484121058815005c414086451210484140064711045c2180050216004c4190c48417005c41710488150040212005021018442160054a17085c01520541111c5c017084cb102848012086401710442111c603120064416105c611005c0180850c141444d1400544100c50412305441220544120044b1808508100058c12205861508646110850417004c2131854218006021604402140060e13004c2111c605100c482150060214105401100446160050510044811004545110044218004c41508480171058a1420480131058610004c0180864417285c414005071114480120860b123060111305c41,
  0x1508646180860013084c211045441804482121050616284c011085041410542122854014144431708540181058217104c0110c54c12085c6100860b1218504142840213104801428504101058b101048217005c4140c4041600604150858015105111124642151050417285c7100c50217005421908403130850615084c016104c2111061015105061734445120050217004c2120044512286441900443151040814106461738584120054217006021704402121c4001118580172058612105c2192858a180448510046001308500192060a17186441610504173850415184c01000580181054010305c014085001408641130c44a15104c2110050015105451,
  0x100840a1000580110c584160054213005811030409112044015004c2140444315106421634442140054817184441708644151050414004c21700643110054818005021200544152048614086041804482112854015144081210500180c48110204c01210440110064014084c4121060013084c7110c400101c5c014084ca19105c2100458417184d0190c48a161048419105c0150848013105c4130444212084801608480161064e145440215105c1101460016084801108580120848016086041510580140c441101c44c12085c0152864210044c81728480120860210044c41500540100050012085801608400120850014004081508640150440e172058c1,
  0x11104431710502180050413286021310644140054e17004c816004c110046501908504110058816005021618654141840312005421310500150864512004c4150850614084cc15086041510580120858018105c3110c541103044216104841408442110c401170054415105c111185401810544141440717005c41310542180448213284c6190c48413006061030640112448a130040214185881700482151044712084811110402150050419204c012085441734404133860111284441108446180854412104921514407120c441140850b11005801108582151058211044801500400130060215004c4161044812004841528502102c443151064014085cb1,
  0x11044c0131048218244021208644170044410245801210589100c6041300482160060312004c412085cb11105831110442140044011145801804441120850c172854219184c2131058414005c2170444118005081400504120c405180c40311045411100440100c5c3111044110045441928500130848616106421530544111440318104c41718401131048416044421464444102060414104801914402193064419084c41400550121050e1510440190c4841700643121c4021318444132c40115005c51000401121050b110850619085841400488130840c100060419385841600580110848417084821068648160058416205011120480111054419286061,
  0x10184c3100048818005c4191058216005811120582141060413004c217004c814104c0150854012085061110409151850219284011608644160060f1100482111044018104c41510502141840a1008404101840411144021800508150064310004841508484190448215005481248611101c5871000441190c48613085061508604190050a16184071320402192058418004c2151060413285c61720606150c44210085481814480160850a17184c1111044012004c41508483100460215006011034602150440011084441720480120858811044801910502160064a1408540110040c18104001428582181c482130840212004001500548101064c15085c11,
  0x110c500122050310204c11100403171864414085841600550151444316106031210546171048215105c0151054a192064a10044881834442101450c15105821400548100064f110c60112084421118604181448418184c21510504162850012004401804407191448015084c0131444e121844214184c213005041420486150854013105021908403162860e150050217004881804482171064a18106411200443132854815185c81228492131c4021608581102054012205c0110c64511146421814447100444013085461514441180840116305421510584100c4401530440111044718004c215044421030510190040610305c21810603103048c13204cb1,
  0x10084ca160854012084401210602141058018085d6121064a1510486140850012105c2141060417005021410640160840a101448613105821800542150050217304031100588150040a120840012105c21210400120444c162844016085001320486164050a18085831120401121058412185821500502131c4011600602183444a17284ce180058212004c4120864015104821300582120040413104c2181060110105051110542170c40012004c4120848a131850218104c017244411004600160858012085c012206411210582160c446191044a19005c2101460111ac4c01708600190841017005c210084411900443101064013285cd10204c418086401,
  0x1100500190c40210004c01528543110c64112105421710500120c40210044c4140440118085c410044c0110054019105001118441181040b16104c219004031408442110c48019085441200582190440a190c4161430644144064215444001008543110048018106051008405143044116004821510486150854c130850b100040112284c41504447142c44012504c4130048414105021810643110454010004a41600400123040214105c0150848615084c3110844214004c21700502130058412384c0122848a1208504150064312406001928642102c4c51144607111850a111040115105c21104541110844114305c010085c411085c21008548142c4411,
  0x1408580120860415005c11018480160044612004c3100c5c01608484142c440110c604180854416185c4100c546191448814184c311285861808440160858016004411300504170840014086001310502170044a19104c212004c219044041308444191060615104c4150848019084c0150860d10045c01310602193054216005881618488153064219004441220580110c4801024540190864c14085c41258440180040616185c218285c012205c418044041808586121844118405c019085c4150054816005411004501100450219005c413084801840642190058211105c0132054016104c81528488100c4c2110048810004c412084cc18084c418005071,
  0x15005c7100058017105431018641100054015086401710482130050412205c6131044a150858013105c2101c4c81610586160864c19086401510502141840410245041410542110044411005c215305021210601110c5c412286421400506110054a14044411300582141050c172c44e131060013084c7100c4cb100458a12186421304401121848212184c8190054417085c0190c484130064011184c4180448816004c419085c016204c012105081700584180864011246041400602162864016104c811005c2170440117005881610586190864615085401808506152c4411310580143864410105cc1120500171050111045001000405110844019004ca1,
  0x123048213105c0141050310004c214104c014084c619084ca111048417005441518443190c48019084c01500448120848013084c617084c417005c218185821200642151864512105021000504101048213004c011004461700443140850a191c449170858015244041404408161848a17205401710484190c44012084c41100550110c4c41908400111460416006431100604190860211045041500404151050a18204c8110048412305c21400484140c445161440e1600604141440e1300542140440316085461908544130058212004c213105801908546142860312005421200440101864618084051200506100854c10005001120404130048210005021,
  0x171064312005421800445120c406110841211085031014445140060215004881418584130848c17085481108582120060216004c2130058418284ca150864019385461438484121860311584c013405c8100050214005421114580120444114384ca171860a151048a181054214004c414144421200483100c544121c403120850a141440011104821204403140844012105081400403120064816004c819005441610400110450618085801208540100854a131c4021200646110c40213044041310502132844c152054419005081730602110448212285401608480140860414004c8130058413004031520500180860013084cc1920601122064015084841,
  0x1000582100040c123444216204c5104858110184c0121c40119385c413184c4112850213005c217305021600484141060111104401510600143850616705c419084c017085c1112858a120860112085041200482171840511084c0131064418085c0180858013105c213004c416686441518480110c41010044c012084801504441190850a130060816104c6111448a1708484144048a1918608190448215005c8180040a151065512005c4140844c15104c4100848c120858d1010502180448214185441528448191850110204491508547101c644150054811005841320641121054212184c3111050418004c01100604170048214184c418204c0122844a1,
  0x162048017086001468480140840513104901430542100054a12085c0155060a14284c418106041320447121050018105c214005041608500172c40111044c213004c212005021218644172850510245021104542151860417204c01520482114864112a05c818105461620504171048111085c01300400150064110085871104582182c48110085c6170848110084c1100460a1600605110c605101c5c4170440119004c2131850110145801638580190860512105001210582140048a12044401300502181050012084821]

theorem S1 : RAFrame.seg TB 10 99808553400446149759 63 10 15 14 99780724298206201969 D1 1000000 = true := by decide +kernel

def D2 : List ℕ := [
  0x1300608151848814005c2171048617085c0100c4c311045821300642171860011044041300645112448e1310604130060a193c482110448014104c2122c44a1110544153058419205471004487101c4c6140c411192864415084861520496190448a151049e101c4c4171060014084c41800502131c44118004c21410504160c40613005821318504151c4411734402151060214005d012385c0190c4841404443145c444110044017304441100444110c50010045041210606150854019105c216105c61200400181c48a1310582162844014084c41110600161060b12205401910602164058018085c012104c416085c01328488170048216004ca19085401,
  0x12104421508441152854414106411104480101448415106421900544140c4431804482140049010084401310404150c40a1810580141444011045c412106101508644170440314105c8190058a1408600180040111106061408640100c4c018105c214184c0101c540130854416c0482142860415004021218448170c4061908449131040214004c4140858619085041300502140064816305c812185041838580140044017004881200484180840116105c4191064312084461510640151064215004c416104c8151048018106441300400120050210186031010480120864310004c014204c41534443130c403170c407182448017085c211044c015086441,
  0x120050211145041810584193054418085c0130854c14085c61610584102c45413004c21310480171054e10144491718642171440610204001208502110054419185841408640141c44e120044110145021818443140444715285461700409180c44411004c4120854610085c414184821410482110854e190064512084cc12105c816005c71000641111c40013004411000501111c54019105421204401140060510346041104501101c514160064e10045961210540100c48212004c4160858111085441800502120050214004c2151040412005041938600180c490130060d1010401111040318105c4121050019144821214401110c544190444115085801,
  0x110c50a14004c9110060011084821318488151848a140850015085c4101050c14105c2160050213105c4101050617085c412184c2161440010085461608586160864017444011700488130844018004c217105c1100454015204c71024582170048212005c21804447170048214306021310586190040011044c41400400180c4401818502163054a14085011008504180440814006021518544161050413044011828582131c401191448615106041608447130864512084031208588101c44211186481008648180064e10305821410580120860614084c01628642151854310105c3100860413105041550540131054111004031200504160c40210044c21,
  0x1400502170050214004841404441141060111304491910580120844019084011310643120040214004c214105c510005c217184c412085c01908653121044216044041208504110458214005891014503111050a1304404101444312104c21600481110844412084c01528544110c54413005ca171048813005c01018446120850419185c8121058012105c417044401928540160854a17285c0152c40118104c613084c710045801970602150444113104c41800542160058e1600642130048214285c0180c440120864a15005c814104c4160054217285c6190c48613084d811084c019004471300600110c54416085c015205441618584144060415044461,
  0x1500548193060215284c6140860018084c01308540122860512205001420604101448511005821600540110c542151058a101848215004c01108542164048a12105c0120c44010105881710486190864013084c018406491218582120c44718104001004504190058215004c218005c413105c419585c415086401410443130840014044411204448160044416084801214404141c4411308603112844012185c213106441310444100460010104481510500181058219104c416004c412086511210507112058416185c218004c81400500100060112105401038504170c400190c4001208481110454111285c2140058212105c01820580160848017384841,
  0x110040119084c0190840112085101318504141040512105081900582120044213004d018144841050480172444919004c210404001820540121058a13084801738503113050013484401900549101464b103c48419085801208540151048211005c218004c4140850416005c41508600150858417184d0141048412084c415004c410104021810641102840214104c3100050616085411000400130058710084c8160048218006021300502151c4011210600190040113185021808403120040716004c610044801308600110c502100445214085c612204041500502123c44d12205031000404180448214084401708441162854a160c44013005c416184401,
  0x1410582181054a140060215184c413104c2170060214004c2131860218285c01910642140048a120864017105081310500183c48c13084c0180c40013085861708480142058015204451210580131058a13086501518502140054a1520500132c44114004841508581113864a160058211045c417085c01308500171048416104ca100044713306441408547100444214405ca18105c217005c71000540190c4401110488190058414044051108401161c401120060414286091208407131048414186001104401130444211084c015104c01108642143054a13b050618284c414106421718642150064411244841200588171060a130060217004c011045421,
  0x112064018544051308644101044012144401610409190064217005c214104c41718644180850416004c218044821348582123050216105411120440163860416004c9100050218005421518483102850016385cc18385401408541111c48016144011210600130044014104801208486141060a17086441300544181064417205c41218404170444119285ce1620440181448c121048215005ce12284c018105c110004821104480160850412104cd1108501110844a141850418086001504441150848416084011310644180060011245841708486130840413005421200482123048a181058219106441318502181055c1210486110c480160864414184d61,
  0x16005c4120854511005471004442162848a11144c410044841020447160854016084c012104c417285821500643120c44c160054218144001520480150864112105441314444110848014085c413005c8160060b12084841400581110058016205c619285d61620506100c5481034606161064216284801238488100054016244441500482181044017285ca110c5c6152054013105c710104001510500180844516005c81200544140848414005c216186421410580191050e15005c2191054a1710488103c51014106021410586132854f110058217005021610586130858c1724402100864110184841218504173045915006021800604150860016086001,
  0x1100484130044011085c81628641120860614105ca120c4401910602191c48a181040515085c012684801708640182060a1000488130040511046061708480150858017184421808504190050310184c214104cc1720540112050415105c014204801308580102c4c41408602100c5441200403190044712044411630602191864414284c2181050015085801010482131848419085c0120864c1914402170048a182858212104401308441101c6001438640170444b16004c4180864a1518600101040115105c016086061908581111054010084c2130054a131050210004ca19086001528504130850a11044811000540150c4041618502120c40012004821,
  0x11005c01428544132060013144421014642131848011085141700582190449a130444e11284801508606180c490131064013105c217004041708540168848211184c01104585100048413205511000542171844218005421500582153048e1300542161860414106021800403180040318004d0130040116005c219005821810604131060a19005441608580170864014105041910508120c402101049017084cc112064417004c815005041308649101464416284c4151858e13005421900643120c44712105021210401170850a1218584150858013104c01018605121050014105c31018502131849413305c111084c814005c2160c4081500442100c5431,
  0x191044317004c9110c603110860911005041308444171048a13105001508605121064a16004c2150050e16004451608581112844214104c011205461208546111460216104c018085d016486421718580110c5421518504151048711004c4180448215006441610482130048c1004607122044013084c0140844115205801708644170064217005021804488190448217005141610503110058413005c0110c402131054013286441508641110864017084c419184c816185041408604171058419005821900502181060018604031510648170c442170040012104c01408400122054017085cb1030644142844811404c618104431600481100040517105c11,
  0x180064216004c2110054814105c013105c2190050d11044c213004841410584120840117084961230545110460014105821828484165044318085c61228482101059017005821540504171044115085c01414402160050416085801500440180844317104c51104606120858017085c012085c4190058e1718642171860415084841528446142840416084c21000584130058e1800486100054019086401410548140444f194064217185c41438484140064512104c5100464e1004644103454211305421700582160c447130850a190064c100c5821810441144050413084c31108442140050e10185c21610486181c40c16244021324440190c44615085c01,
  0x11205c018044071218448100c5c01610483110048412084801210482170054216185881818644171c44017004041020645120445310005c419104c2160c4401210641120860015105021234410133850510105c0141058310144431810601100448019084c01208484161048a1110447121840913085c017085c415184c0105060818184c21310504160058e1210440190c480192c484170864512005021800484140850013104821800584181048418105c4173440d121064e13004c61104480122064418285c4120060218004c81000442110460213005021800489112044016004c8120060e13044411300502191c442101858a1410644170c40414284c41,
  0x13384411540540174060213004841808480123848016084c71120443181060014086011110405112844316004c418285441508480150c440140840619105c2180050214185c5101040418084ca1600602170844d1818602151c4471800643100c59011105c617404451208505100c483110864311104ca1218642190050218004c417104c41408540122860e141054c12085401844405110c601100840a122854710006471010541101464d12384c613204401608480143844112205c0161050e140c4461500644170850410084031608582100454415005c21610640140850012084c61620500141050810384041008480110c4d0121c40814204c016085c11,
  0x1840588181848311284c41508442170c403162c40810045ca19086121700442126864512004c2190448a19205801024546130840412184c21610604130049311004441108440150440216006021604402141054412005c813104cd100c60a17385801818443162054419344421200584171049014104c216004c6101444015004c21110580170040a1018486191840218385441900644142050e11005c0180850310004c0151444a140850c18085801508640141054217004c81610484180050418184431228482103464217005ca140860618105841118401141850417086471220645111064112104c418105481714406170860015084c9110048014105481,
  0x11304421118544153864112205001708600130854c13084c014204c016084411608480172858219005c2171058a14005c215104c0132048016284021014440181050e14004d01008584131444512404c2120058a140848a18104411608549110844113184c4160848015105c214305441910447100840915005841420484120048a172050a15106001008644131840a14105c2131840212185c1110448214404c415004c41804406160845518144101410482140060311005c214106001208491110c5001408606132050811205c217184ca162850214005041708506140860414004d61308482111c5c9102064512084c014284841908440190858c12084801,
  0x1104504131064018086061910582192c403110048212185c2191c4821810646101040514084c013086041318542130040316185c2100054a10104c8180044217005021800583111844a160858012144021704408180044010084c0140c440190858c16386001208540180044719004c4141048216004c21900514125044316084c0170c445182064c1408446140860a1610496150040219144901810480171054110004c018105c416044411338484160044218004c21330504180044314085001308541100c4881110546170040316084861338640173850413004821400588163048212104c0131445a14105441610500151c402191064b120c40411105451,
  0x17104c0140860a1510540131048214185c8144058111045c41610506120850c1820401161058416105c2155848511304c413084c41410540150844115084c311044841408604151440013205841510644171c441160050213144031828485101048417104c4123064816006481310442110044615086401820501110c6101704448110850015084ca1610588101848010084801010482162040017004c4154064219005c2172c44414004c21200542121c403181844714005021400542190c440151054614405021728606131050213305421730542190448412084c0161c44310005c01404440172044410385c2152854414006041708543110050017086021,
  0x111848015084c6132860412385c41424407132064413005c214305021200544180044d1500482161444613205801014444180854417004c810144841200484100860012584c2150064a131050310005081200484150044017005c21418484150c440113848a190050b100c5c214484c41808600131440318085c0162055613104c012105c41720502100c54214184841110542160048415104001020502131050616085061320480151440216404c013044001604401171850217284c21130580121444011144801308584120044212084401400502171844915004c2180840111084001500604160858014205c0120444012185841308500141050213005421,
  0x17085c0170850510004c21300488171444018105c7101450416005c21328601110c50210104071118442100c500103c4c016144471600502181850219005821500544111448815005021210541101060215284841530542140064910004c21900542140064a13104c41628548131c40316085c1110860417105801108640101040312004ce17005c2171049012004c215204431510542160048218044421328482100840011045441204441170444316105811000444190440118004c213105c41500600100450019085401408500130858911045c2153060511004461218542120048212004861008548141064712085c41310440110c504161048616285471,
  0x10004ce19284c31000586180858a1400643120048a12284c9101041513105c010144841408405160055a14185811100480192054611104841310502180050213185421428486160848617205801508441130864017104c818004c7110850218005541604407180054212106031100506160044014084401900400100450b11184481410606146844615085c6113c5c810085c4131050216004c2191054617285021310600132c441160c40811105851010602170050212044031620646170c44013105c110144c015084861338540160850014105c418085c4101044b16104d015004c2141c45015085c012104c2190c40015005d014105c1101040013304c41,
  0x16144101310600180850a14185c21410480124060814044421614409111054014285d0102c60416405c413385c4141044a1600602171054015285081200502171848214105c017084c013104081410644193444413105821728500170c400100c44319305c310145c816405401828580110c485110454417285c6172860a170858019084c01608544120064512205c1110040c13004c41738606191440812004c2180048212185421300600110c480110454616084c0161048a161c40012105ca140440b1104606190850012104c414084041004442111450412105801608546160840d12184401300502151050014104ca14286451170542172854018104831,
  0x1118602150c4001800488142c400112858812105801608480130864013084c4150c4011320580161060217185021110441120c44318104ca170c440120040210005021300482150048413104931100600110860015184411728586180c44512386401308540160c40413004831030401150050212105ca1210444130058212284c4170050214184821510500100c4c41218482151064015084c418006081700488190044417104841320604190c408131440010006421118600133858d10044c41410641120854412104c0131054213105c012684881000401110858018084821004500120040018286041914484100840612105461518441182c406152c4471,
  0x19106551200488120064414044061418480111844112086401420649110464312004c415385841418608170040312004821828401140850017085ca130060218104c4123040814005c2121040c12085401810482150055111104901510484120c404171050415004c3111464312004ca18105c817004831014505100c482150048217105431108602140054010045c61810402160840017004ce121058613084c0191c40e150848711104c218004c213185c811045021800502181064413105861410482120060417085461708504130058215005881818482133058819005041808502104c44c15084c61410642163064216006421114580150c44a13005421,
  0x13044001010504140050413106021500642140050213006431008442130c40b122054a13305441938544180444416004401700442141054412005841520605110044816105c0180848016105c41008400140854414005c3100844012005c216404c1101050511284c510384841218440110448014105c5101c4c41728644160064216004c414085401420580190c48012084c616604021510508190064214004c4140850a191064110084c910085481520443181054216284c0190c44910046421104542141854818105841310610130440316086441810401170864015105021700644177840313106481318445162064414005401000584101050411144801,
  0x191060910005101308540131444411244c3112040c156044416105c219005cf100c645120054f1148642100450812004091934484100c6401408606101458814284c41210400124064a160c4441128444161854a110c4041214400120c45b17004c21510586160844417004c419405c215104c018085c015084c0121440915104841638608110454111085001840580101c4c0140854210104011200641110050614184021508580180848c14104821504400100858a133044017104c418005ca1924480130850c16085401310442160060214004821904483110c5c013084091108642190050010045811104480130854a1800600100050410185ca16205001,
  0x10004cc160c4011100400160c44c1308440180054217285001310503110c58a132c443102c54310146041518487110460a170444019185c8111048410006421628584120444116006041208480180864d102844b142049014185c215004c2180044214104c018204841410600132854418085801610545101c586173848013104c815285431100504123064611085ca1420644161064016385cb11005001008644154058010504821530489110054214105c612106431208441192c4801408609101c5821500504141058011045041210484160064215006041408484130058813005c21510405122c4401228644170860013384061708484171048111086401,
  0x130848418004961504406141440415006421810500131c44116085451048482120060216005041510484130854417004c411085c0131050816284841500502120050217104c013085c81104404191060c1320644132850a17004ca130858417185841558484180c4441000582153048310104c019085c414005841720480170864112085c013104ca17304471800544120040113105c6121048215006441308500101054219105c4190440418085c11010642182860614085811010502121058017085c416104411610482120444411104c4122058012084c01508604121048019084c01610582121048016105c21500484140848016104c2160844614006071,
  0x1418502170050213144001210582151854217004c41704440171054016105441504404111c502180054814185c0110054012084011608504120050215004c218004c41408484161840417405811108504160840616004421508580161440a142c4431708643110c4021918542170048311004091308612151444812106001210602154854214005481310500130c44417285c2111c4c41908443190864413185dc15106041428442122040210385431010400120048415084c014104ca111440919085c4121054016105c5101c58a11006401004546191058419144801004484150048214006041428640112844314084ce100860c1000502100054414105c01,
  0x14005841124543100854214106411108446152044a16105401410582140c445170048213005c21700488153844116004c2130444119005041908500120854014104821008449180848418004821510440110854013105441738480143849618004c2142c40811005c018105c21210547113460014505461414401181848219006421600482181060017105c818184821210584120058219005d4180040218005481810544161050019085c0150854311086481700444151064411144c219005451010502130054215004821600643121048012505c6151050815105421100482110464c160040611044c511085c612104441708502100854210404c018044001,
  0x1208601110c5411108542122440019005021210540190858012085d619005c217005421400642130064215005c81200484191040317004c81200580110c4c41914482102c48013085061210542100060215284801310402121444019105421600482151050c175858e19144841308440153048211204401114484160048214004c81300443101460a1910604101448a16205c111284421200403131848219305821510540121050219185c21748588121854a1210542124c44114185811000606191044214305c2140054414086001504401131044217104c41910405120050216184c0102448212005c213005041810487111460210084cb112054013004401,
  0x110054210106001910645122848814105001320540140850211185831000580111464a110c540130c4401810508161044016085d01510544160054215186441340502151058017004471510606171050216104001210648170050a1428405110c604131054814105441500484152850910004c21210546131c44816085d0160048e1318604141440f181050412144421410480120864112086461508584190058216004831110480120865017105c01804402130c440150858412104c0191060413284c213105c31108442170048213004c2190448413086441328580181054413104c217185c6100c4c21618502123c4401300504153044017004c210184841,
  0x1908506170c41012606491028540190444614105c6171844b1018602110840318185c1110848818004c415205c011145ca18105c311104c1110858c160850013104431428600142858212005441904446181048014104c214104841904401110864912005801134406190c40418185c2183444216005c216004c81604401180054a18206401900403130c44018004401330482150048e1518602170060a153848413004c2121840215005d1112c402152861111085561900542170048218004c413105031110443100854413084c0150864019144011600541111858a16184c2160064a171058212105c4141854814104ca11186021518642130054213084011,
  0x1400485110c504120c44413084081370650153c40a15004c214104c61528503101048414585c0120044316084961600541102c600130044010045881618405190c4861228484140c4441100448180040216184c2191064112104841728502144044512004c8110440412084c414706451200482150054b1010488141054a140050816104c01918401160054412284431510480141064a142444015105041410582161064614085c111004021904444103849610085c3100444517204831000500151060216185811008403110c644140c44210084401808602110044114084841300541110458414144501300440151064c17084841300608161040012284c41,
  0x12004ca17205c0132048014205441700488151440511004841808500190c48017284431310640190c484162848013084c41608440181064512004c81518484150850014085001438580171054219004c41708650102c444191064110085441600482100050212005c1110058a19144801620584150050417205c01910601110054017085061708491100c5061608600130c4401700403122840313185d0100c612160c44a141054c160854c18285421300402140058111005801414404121054218185c4140854617085801308480152858216004c7102c64112385c6141060e155848014105421218480111c48311045c21300542100450611185ca140050e1,
  0x19085041548602101040210005c0170851815204801538506142050011144c310004c3110048311005c4161048a19085c619086001308584123048214004c2120058a1308582110c5c51104544131c44e101448613085861020501110c48212004081600503100048212004431510584134064617084c012084c014086411210504162c4471400608151858217004c21310582110c5c21528647111c4c01620506190860612206001408544150040412084841500542140054815005821200643121c441150c40012285001310481101c60417086011104640160c441101c4c01108402102454218006041608407182060019206441010644111458412306431,
  0x131064c130858418105801904440140058811006431000604174c44010005c2141440412185831018582120054218005031118481101454411004c21900548151848419206401404440120058611005001310642154c44117186431200542190050e1028500181844117286401808507100844617084c012084411908540170864311004c617084911014602150844114005421300403122444013105c415005821900400113c6001030540160848019086001310502160060213105c311004811000402140848c160844d1204447170858310045c215006041108540172048a1900584140850017105021230500100c4c415085401210602151864312286401,
  0x1210405131050210006001240504121064813104c4161048019085001220485100058217185811000402100844a1904442110850614085c41310601110c482161c444132854212105461738401160864017284c4130c44618204061208580162058a130040412086411028542151848816004c418084841410640140860413485c41420446190c4801420584141858415085401908641122050c121050a180854016286021210540120855019004441808584140050511045071108580160844017284431318545101054215105911118582160c400120c40512044031510600100040512304c214104c01908546130848014104c2171c44e140048215106441,
  0x170048a1508540160864e100848a182050017085c6150c4001710642140c400170058213004c812285c01310509100840b13104c0130848417044471014506120854010244c41710641120860c19086451200405120840513004821900443181048410004ca100844419005c2152848f1100406190854a121858011304ca121054014084801510482151c44817404801210642150058e19705001914488140841f16185c0100458c13085cc150858a1500542150060010185c41500482120048214104801408644160048a18084c018085c0111450417105431100403160c440134064218285c41900614181c443132858010045c61400407160044a110c4c41,
  0x181044d1700443150860012084801208544120060412505c01608504170061510004c21618544141044310104c61710610121c44c13144051500440150844d14005441708500160854416005041138401161058210045841910602120054413085841400584171054910105c0191c4401110544160064418144041020544191441211045401608580130044614005ce19105841600542191058613105201118446100448012085441418405152050013084c21008646113458013285c4141054218305c11100500160044914004431320480190858a140060413105021300502130c405140050111046021400600100448015085c41210541110c54215044481,
  0x170848013105c8170058216005021700642150840311045861210502171060211004c31000642110459111204001110440110858a18005c2110459613205c0130c40315284c01208600138040b16006021304443162851111104041820400100858010105c21710486181050a140848418104c0130850013084901410601101050a15085c013105c21408447130064c10104421700542151050a13204411210504181840918185c6100c5821318548131060018585c212486021630482161044411106041300602132848d110c601112050b104064213105c41300641101c5c4170864210045c111084ca194c488172040115105441900644150c44015105021,
  0x14104c0120840513006481300482122040612184881200542190050419086411220500120850016205c4180054214004da191850818004c816306021500484111060e17004c21000409120054418085c4150c44814105081020455181058e1010500120850413004821200404152440c170848a161050015084801408607100860413005cf10104c612204c619105c218185881938401116458e130064819005c711004c416005c418184031310605111c540121060a163040219086401450506191061613084811000440120060217004c81604404182860414085501718644140850a130044610045041818484172058012205c11108640160848015085401,
  0x141064810044ca12185ca14105421910600152048a12005021810640140445719006421900608151064a11045821128403111c4c01208486150850413284c2110844b1308580170840716085801620484120044515104ca160c449130050415084ca141048a1708447120040e1904402180050111184001714404120854110086001838585110050816004c4180850612084c018285c215005421908403131048a1320586131058218344491910642170444412385001608500100864a1500400102048e1528440150858617284c815044081904400100050412285c016106041508544141854216044421500580100460013086401608480120864015105c21,
  0x12005821210508100c5021810402111854015105441508600150c4001808580170860415004821910506160848c1710602141058419004c1102c61016004c417085c41300582183050212185c217185441708640151444215144401008600180844113085c010244491414446150c44012284841624400170844113144431710584160848c1310540110464019184411500502190050218004c4140860413004c217185c21700484193c4801208484130060419084d01818504100444217285ca1740642170054212286001314402131058511104841800541101854016084c11004484120054214005c219005c210044ce14285801508401181444210046421,
  0x120854413004c219005441208580190c480142858215105041930582160c400193448212005cf1018503103064310184841608483100048412004c8153c44614005821600502141848415084c0161048810046021710582110840514085c01210502140058415085841528440150848419004c217185481644400170860a14005c21404402102848012085401608484180054414085061610510110044d190060a13084c51110484170065413004ce181848a1504442142854e1318582120048e1700482141864110004c412184c219004441810602182848015044021408603101c50218106441518548111448311144c4123840717184821100606110c5c21,
  0x1710640100c4c8132c4471004546180848013084441210500152060016105c111145001708540161060215186011030500120858614104821510540142044c171048a1310482122860012104091500544100c4801708542110c65018085c0100444618005841808500110c584140054818044421110446152844215005021204404171054310105811008400143044014005891014581112c6441708403190850417005801004600162048111344c01308481111048415104c412084c0172058417185c7113054418004c51028402150064011045c0131050711006181508600111450a15004411304407170050311185421904482134058c121048417085001,
  0x1500548190448212106041700484182854217285401708540122058311005401508606150848012044021508500131444010085c111184801260443150440d16085c6191040411285c41700403120064213004821418502120058414205801808590114c582170060a190854013286021510540150858c16084861308540162860813004c2170441416005821604407191064a15005441524441101c484191050014105041300410111054111004c416006081900642170844119004cb110850012104c0102040010005c41818496120849018105c41510446141050213005c01104480180858416184881430640100c6441508481110c48214184c818285801,
  0x1610608131058a171058017085c4141844519385ca160048419085c013086441800482160c40614005c81510480140850014204c616085c018084cc172054a19004c415084801308480110044914085c014105c81700588181850414105821430484150444516404c012084c410005c2141040417285c01908546150848417005c01100586133c40614085c0160c443170444418084c4180064818004c81400481110464814004821100480110c54212106441304440110848511104ca1208480101058a1508541110458310205c2170444416085c01920501102860214004821300482113c40012185c81800604121444411104c4170854014284d613004411,
  0x150844a1728542110c48217304d017084c01410602130050414004001200483110c48a190049a171440a1600644160848011245ca180060417085c015084801610602154440316104801504444110048013084ca14104c012105c4130858018084c61708644131060613204c617205c4170048311004021918604160860414084431528642120050417205801528616150864013205c6120850412004c412085841610484170060a1310409151058511184c4120c44610245c2101c482111c6001310480100048013105801100646180854414186421600542131c4081300508150044217005881828484130c4451904407122844211004c2110c50216104801,
  0x14085521770502141848810045c414106441208502111c480192048417105401520400150848613204831018606121054212004841304400150054212105461408486120440c100840519104c6141844018006021004504180860013384051428405121058013085d219084c0131048511084c01408400121060413105021434408164850111086031030544125044519204411610600152055016084481608642101c54015004091810608150840314084c013104c4170040113005841204442123444212204c616086461300441120048212044021348544130854d1028641100064418005c218105c412006421100648171c403122c40312284c412085801,
  0x1608586131050412104c2142844714105c212105ca13485821308402120844015205c41500642190c440101049013005c4130858018285c4171044210085431000488160054415084801124540142854216105c015205801508404100c442190860415006021730584120864417106001528404152840212005851010609100059016085841818608120064215104c11020400131440117105d016004821100400100c483100044a16004401200580110458a19006421200582190050214184001000600162050412186031100482131858011005c11020480180844513304c8153440a100464f103850816005421600503110c481100844417185c215004841,
  0x181058a1710480140854017084841418486100c4841410484170858013105c4111c400100060e1610646150c40c17084c01600443140850c140850616084ce11185061208584180051416005421918547102c544102c54411104001108401161059614085c6170858614104841238644140050413105021810519112048415184c414104841608600130848018105c217044021000584181050414104851004480150c4441818580100c5c010345c414004c21200541111854210044ca16004821800510191054a141048c10084841108600123850c1214404132054413004821200646110860416206461708501100040112085ca120064219005c415084861,
  0x16004821910643100854216004c8161058a19304851108544190044214005821710640140850416005c21800508120050214184881710584171040418105c0100044016184c8181c40210005c217185c4122048a170050310105c5101c44119185c4122048c14085001514401180058a19284c819004ce181050418184c414085c0151049017105c2190058e14185c2160040412085c61310540110c50a1308600160848619084841510586132064417186421430582161048211005c416305c41608640140860012086041]

theorem S2 : RAFrame.seg TB 10 99836379105611416187 63 10 15 14 99808553400446149759 D2 1000000 = true := by decide +kernel

def D3 : List ℕ := [
  0x172854819105c3100444b1504402160864015085c013205401528582140c40b1228640141c442162060a15004c21200582160050217005c41520480112048615385c01038580150848015104821300488140064a1324404121440a15004c91018402121058613105c413204c0192858412204d0120440f16085041418608111458415005021600501110054a1118540100c48010085021700502141064310006081118480180044317105ce17044441408600181050214004cb102444519086401510583110054212184c21110604110454814705801310645111058215004ca14284c21500508121054111205c415384021208480140854012084c412006481,
  0x13104c2122440813244401124400142051015005821300583100c5801810488184054a171048016405141500502120048e18004ca133044e16205c015104431318589111848418085c014284451408540180860510304871118400132848510105c31000403172064016085c013105c21710540191054011044c017104c4103c580121444212005021830502171048a18004c813004c21218504192064e110454a130048813105c0181048412286101908484150c40019005441214402110044110145471004540170840512105c0190848415184c010045c01708480140861e1228640101c50c14104c411084841218504110c5c0120864c170860013044021,
  0x1220480120848011086021104480132858216186491100481101c6021428486121058216305c419084c417004c417205c410145041410584170050e1210646171054216004c0111c5c2110844316044411400484142440011106431000402161440613085c0130c44110084841900544140864a1600510190444012004c81200405162060014004411400642150060419104c212284c414005841310500101c44210004c1100044019104c4181c4041808586150441214184c1101461c1200486112840116305c2191040011005541300582141040116105421004550120848616204011528542181058413184c2170444213285401318440120044315104801,
  0x10184901410447180044718044421300544122054613004411200584170c4431904442121854213186041014445150848a1600602101454014085801910405120858a1410540153840617085c61908480120848014284c21304402101048c120c400152c4021200502130440f1510582130440211004d0130848c12084901800482181850412086011108482110854611385c2170040312104c0121050216184821458441100845114104c6132c402180c44612244001128546180860013405c4130860a14044481500604120858415105c019204c61910543110c40b17184d013085401708606192444b1600407110065a1510502100054013084c018084801,
  0x110c4c01708546121c402170864017044001328506180850019205c71108640141c40519184821500480110450012104c217285461210484152858218104451700581112c404161064c1808552190c400125060a140444312044401518603100058413384c211045ca1504442102c6421800602131058015084801450644130050217185c415085401218401120058213105c0191c440140064812005401018580161044110086441608580150c44412184431304418100050413044041210541101c6041820542110c544173040a110450615105c41808504160048212005c2171059e180040311084401308404111c58814186031044445170444619186411,
  0x14004c215184811000504140060710204c311146081900483101044c15184421908582111044117004c2170054217286521420480150855215205c010245c014105041608480110c4c0131064219284c610285c816106001300441101864215104c0130860a15005081400504110044216084c0150854017284c9102c4c216004c814106461208484140048814005801008400100c50218306001008404182060d105060110105881924408182058418005881618588180440010004c016205041818582150050214005421504405110850a1638480191048010045c41410503111848016085441630488191064414305c214284c41518504120854015204801,
  0x16206401228588181054018085c6170858a190050e111864419085ca19186041508489100450d11006441318482101464a12004051210602150058219004c2101040113105021810484150064214004c213104811038581101c44011146021714404180440a15085c4110064217104c013104c4151050217004841108582110c5021808401131c44119004841500403181054813104841300548182848a130054010205c8151064014085001214402140c402100854110084841210480124440216004c2150058214004881510500174054212005021310584120840b11184011900441171860219184c1110844213105441708440151040013105c710185441,
  0x1700540111844115084c614084d0130060e150044b1810502120050813105c0180c44310044c7101448414404c5111458a1310584170c4401620586130850414105841200508160048216005d0150860c190864110404c214144001808501112058015105c217005c3100060a160850613205041300582161060019084c01500402102c4c415105841520600120848013204801638580170c44c100c50616284431628606172064a17005c419284c110084081604402131864815106411010482150048213105c61208480130858413106081004480160040112004c4170864a13106401328584192059711106041200580110c4801000500120848014085401,
  0x170060217004ce17104c411004c01104586181050217105431000400122060019084c417004c21600645112044419185081818482151848212105ca12005081610550141858216005421400584190858015104841510483101845413004c218104c4131440014204c71110442124860a171050419204801510484131064610044441510610141064a190050214105c810045441704444180044810286001104540181444415085c016206401108500192c40a19144081610484150c44017004c412104c812005c1100840113404c0132850414105001004494110454711044c81004440130c44012184041034480120840b14186021700602131054416185c21,
  0x131048310005c017104431700650141065415105c0170848013084c0130c40a150060214185841704400101460a12105ca1208500150848416004c213044441910504141054211044d01808600102444c1850540122051110305c2170050a130c40019104cb110858011144081404402142c449121848212044011318504162844314184491440606131840312204841428600170850a14104c01910614140048a15104c413104c419084c613206041228487100865510086421410580180440017305021824446110064218305821510447170044912105ca1514444142058012104441308606140848019085c4121858215184821010500140850416006421,
  0x12304c411144c41408480150c400150860015104431510484190054415085061308510160c40d162054c141054419044411910645111c40117106441368405150040b1308604131058c12104ca100858613086441400502182c4441334402180058a1708487102054211245c4130c40014105c4150864015004411310600130848012084c2103c60816104c418485421200484171c441122840519084ca130048413105c4134050e130060412105ca150044214385401618441160c40e160c44011104021448542180c40117504ca1300502120058815005c218004c2171050418005021710643110858e14004c415086401310452111c501110448419005941,
  0x18005c41708643100064014385051000504140854015284c311005c218004c11008582151440410204451818543110060213005c818106401408640140848018105821410540112850218105c0112454019104c2150060413104481218502140048417086031114540131048e14004c41408545101058016086401210482130c443103c440100c50216305c8150054412384c414105ca123054610046001870484191040214004c1110058014085041604402140c4001734441181854214105801320584181048418004c2160c40b121050710044c0153854a10044841628582140c44015004c412084c41800604190850413184ca140854410004c212185c21,
  0x1300542170058e1514404100050815044411400541110064013104c81518483103048219485c2170054217004c2141860215005c81500484135064412106001320584192044d19584411008407163848416004c4162064017404c219105c61514402162850013685c6131051016085c412005421400504150c405141441917104c016384c417204401104604140858111105821718403120060215005031118580101040017005c2140060415104021700504172c40a1320580162050018584c1100050310085c1110848e1430641101464412004821604401121444014205001400401121850816004c41508551110844310044421100646140044112006021,
  0x1520580142850711045c412085c619044411000562162050a191848417144441108603110848818185c214404c613144471214440110850016084401408604171044b1310580180858418244421820580180840c10104c2121054a130058f10005041220500140044113006451008641101058812105c7100c60a1208580110c648102458911006441518403150044117004c61000445150058212184c216105ca190048a1520504160444918085c0131040814104801408540142054c18085cc1604402160864a11005c21228447120440b15004c21810489110844213305441100401190444118005881044640170850017085c61800400110454413104c21,
  0x1004441171058511004c21200653100860f100051016285c8130064a140c4441600642160064a18084441000409120048413084c412105c615085c01410642170444211105c01320504180050410445821400604190860014084801310640110c40a16085c417044411200484150864418005001104481101048310004c21310506132440010045c61310504170844518404c0180c4401308444192844519004c21610480160040218104c21218482150054a19204901314444111048012084c0190854413105c01304400130c440141858e15104821108481100454816044411810484190054217006021818582150048212105061208482101860014484021,
  0x1508486122064014285c2172c4001404402191060217144041810604180050e141059014184c8151050413004c213004c4130844117284881400608120c440180064215005c6110040114084c7113448a1628484170060814185c816304081918648120050415144041908580150c4001700444100848414044021310507100c508131048110284031314442121860215006021700602132858c1014488140058e1700544102060019084901720400150840c150444413384cc12384c01808583100858011344c414486021618502154848e191054019204c018004041004584101c482190048213006041220504140064217106011108644170058212004821,
  0x150044314085c013004001418484182054016085001608486150858a161444410005491100604130440013105c012384c0180840513305c417385c41500490132054019204d21510582130050a140864419306021200582184860414505051110586161060216005441208580120854019104c1110854415104821400642130058216106441500648134854213004c21200606101040714104c016085c014105141600504150040112185c416184001910604170060510385401330443180440015185ce17005ca19284ca1408484130061211045071004504140054215404401500401131060017084c417004c91100482172040112105c4121064614004081,
  0x1114540140840017284c61000603102058e18104c0170c4041610550141c4481814400151044919105c012044011808480130864511004c2132844011104451620484170048212004ca1410588111448415005421200541111854c1500448140854015205c1102048a171440016085841310640135050a1904404171050310184c2124864f100c4c6120854610145821934441161060419004c417285c41710642160054214104801810642141848010086411008542171058412184c21240540120848412005c21510481100848619085061410642160058418085801210541100840811186091100484110854c110c586110440116004d4170c44014006041,
  0x101444017085441518488121054416006441308484132444814105c21808440181044515005c31000584120440014286401624405132064018384861508480190848017084c4161858410145c81800410101450e16004841810582100040217004c41208540171c44213205841510486111448217404ca121444019104cb10084561800484120c40519085c0101040211004441100542150844715004ca1910409182850617284c4170850019105c0110450015085c618084cc16044001810441140860c11144c111144c415005811100642110c4c214184c419284ca18085c71120600141844013285041004484132064018084011310482160054217485881,
  0x110050016104ca1210589115c4ca1608657111040015205c0142064510084001400584150848416105031030604132850411144c41900484141c44016005841510600110460a141050018085c6161048a1110544131058215105c4160050a131060416084c014085c012085001420487111040213005c2171c400110c402133844d1600482193054415204cc142064015085c013105c8171850818004c11100546130850417004c0110044113085441600502180040411085801400447130440217104861310542161060013085401908480141c441150850019204921208480130440513105c61708482100c508142858111085801708482100454014104821,
  0x1320582110454a17105801608600181064217005c9102848014284ca161c400181854212004c41410445180844112104941500483110c401160c403110040315185d01810510122858a1408480131048412086441004544120848015084801008606160854417004c1111c4c212004c2140c44813084c414104c413184c310005c813185041904442160c40518085801308484120444216105801928482125858210204031730502140048212004c2120064217004881210500180440215285c216004c213284ce11245411000480151054214004c110184831000484141054c13084c5110c40112205441508401111054a12106401608541110044211084c21,
  0x14005c213005c711004841828484170058212004c21710580182058019244001308500130c4041300490132c44a11106041404400130054218004c2133c40118086001510508170058215005841508584101c502121048410044441308484181864a180848412044481200543110044218004c212105c01208504161c40817044081404404122054012085c014285c817105401414442150844116104ca120840316085401408542100450418284c41910506104c4411608500171048211105841400544120044116004c21410501111440010184801908508112044c11045811108501100c60211084091900403160858210045441300590150860012204411,
  0x1200542131058011245c4100044312284001604440121055017084431720580120848412004881710500131c400161060017084d01500650142050c1410542192854a1000404100c4841710580154060219284011208612183854415084411324440150058111085c2181054a171048015105ca13206011120480140850419005c813105401310482120048910446021400480110c58219005c8162864111104c2130048010046001200441120064217004c414084851118590181048817305c1100848212044041820510190c4081008481101064217004c4170864014205c911205021700482190840d19004c01004580183860018104c4161840314004011,
  0x151048212084411404443170848412005841608540180854013284c310184841208584150048110004411618440110458d11044c111205821230442180050218004081000443131058614105c2140050215105c019205ca121050019105031118542181050010085c01208544160048213005041308484130440415084da1104500130c44a120444217106441528640151440119005c2171048c122048416004c412004411310646100c583110060311004c01120480121040213005421500544180858013104411000506120844114085c6192850817105cc18184421530443163864019084c415104c0142040311004d216085c01620512170850413004821,
  0x120c441150850417004c0114858419005021500504151058a122060c1208590181058017084801708600160444012006021614444191044b100048e111c6051104484180050213184881310584160044b1714443130865817085c019104821528580140854013085001010542191050012084811020540160860415104c019085411008480161054310004801104487100c54e13044441114407111c484143844b1400582180048311105c01908644170040518085401228548141054d11284401108442141050014084c418104c013105c4181064417084c0121059613405c11114580181064814004c211144c014104c011104431428602130444417085c61,
  0x130050911285c0170860612084ce11544c7110c402160848017344001218542151064310005441518542141444310005c4140044210184c01204447185444c1320584131860213005041208480130850412104801318440150058817006421510600121048213305431100645100848617085cc111461012084c0120864110505401308608110464711244d013085c11108581101c604181854812104c417104c6150850711085c01308447180040315085001210482130064417085c41800540111c5c3100050013086401408500190860014105c21210540121054511105c218004841708581100c5c213004c111045091100514102c602110c480111c4c41,
  0x13184c414284c0101c6461208543110850217104c01308644170054413084c014044401518648151860110184c0110c61c1500489100044110004c014104441440583100c5c013404821514443100458218005c41908586142058c17104821300542191c44814005c416205c0140854a19104d0140060217005c2122854012086041610605111050110384c412004821740446102c4c216305041704442130444815105021210580100c5c615085011128444110848414184c8180048815105401310504160858014284c219104801700449121064218004c2130058217105401208600191844115044121004544182444019104541014640180860613004131,
  0x115448418005051114409190848c11105441908656162040016184821900601102058418204841900648170444411045c4181848a151044216184821520442110c48619086041614444171850211045c41408604150c440123064214185821100403150054217004c2170050418585c5100840014086001808580122054a140060213005821300544162c40416204c41400503111c400110848416105c2180048216005041910582164050c12086401828542140048e131850417244441214444190064416105c110184c01610508120048111004c41200501101848619105c816185c8121064014284881500484140440518005401004644161050418004c21,
  0x17104c213306451108540110044317085ca132c44016105821240440160c40a10185c81104582164440418006421310606120c4061208480120848014104c2130444011185801710403160064a133850c1420401130850016084401438640162060415004011100484181864416285041410482151440614044401418508150044412205c01610582151c441120048817144581928542140048218004051210503111044012205c01308440160858411046481504443100c503111864416105c0140044d15004821210644140440814105c0181c4001628604120440111145c012105941510586150848614204c6121058412084841308403140850015084c01,
  0x14084cc190848210044c41308403150858012085841748586112454415105c4140c446120848018085c01328504141058110085c1110450110004401308544162860615084c012104c41538600101444411404c817105c0187050214004821604442111848417106481300544120850413004c212004c4151c442121054218106461800443160c404130048418144081300582154050013084c01510588151860610245821628544142854415004051208545111850215005c21610540150854416105431100544190c4401400482121054110204811018406171858216105c0140855216085c61204407160858415104c3101c4841208602101c58617705041,
  0x13004ca15084c617044421708600163848016104c2114454018085c019206001238400143c400190854017084c41904442100840015584c4140048214244021404441161064412285021230548130048213084421058405141040318104011510580112040916004c2151060019085841630582120050f100040216004451204442170c44413186481100502141854310004c213284c415005ca160864c1908480150858613084c0104448414204ca17004ca19085061024606102450019105421600580100048a120840014104c4150058212005d1110858d10085c619405841908481110c5841738481100c602150044b13085ca1300582190054a14285161,
  0x1708500120c44310044c41400401150044b160848018085c0130850414005021714400160858015086441218644180444213204c4170050414204c418104c4140050413384901218502191054410045041210610161065017104051418442100c48014504c018204031108409141058016085c8110c64a1208640140c44a1704404130c4001408500160c406183c4441500642122c4001320441140858012205001308580190444212285c8120050a15105c21800504171444a12104c81118542160040219005021418644170864413004c414104c41508584121054910085c219106401644444170860011145c419085c014085c0131444a12084c413004ce1,
  0x140860615086001154506170c44b14086061520580125050015084531510544122054c1508600140c44416285521708506150844118044401200542151048014085801320546180864711244961708644161050011104c218184431310540160860415105801808584120058a1408441142058614284c21200582191860213105c018085001308540130855619444401908640120864414004c2160050a162048c18084c0161064815185401104603110854215004c4120850a13105001410500110c48819306021558544110048217184d0130844116086401210648142858a121055219085801310602152854415004c2140845219105c6150860017085c01,
  0x1710494152848a13284801508540170858413304c21528502110448a1810504161048018085c0172058417004d3110044516084cb11284ca1710442110c60416104881818582150050212106401528443140044913005ce131050111105421730502140058414084841410586121054a1204442162060012106021728604111c48214005c2172850415184c215304c4150848013085811140542181858417084801528508120054a150864014084c018104c0110c48213004c212006421404444171064216185c21328604140048212184c2181058a14006081600482140048217184ca150848412185101228502141058617086501810640182048015104841,
  0x120861b1100440130850a12105c4130064413085101404450152860212004c4121844119285d2181444f15105c21330583110048a16085c017105021610644123050815004841208441130848a140054817105811100444110048418005c217284c0132048016085401320586140844018085c01628584131060214105c012085c013104ca1210482141050412004c21718547110058a1500502186060411245001408601110845613004c21328506122050415004821528540141048217006081310480131048811345ce12004821404444191058a1810445162048111045c018285c219105061720500131060211146041200482131064015085c211004c61,
  0x121444016104881200602150050417205c418004c21900484150848019004411924447150848c1628584180850413005c412085841400583110048215144401228584190858018084c017104c2140c44017004c217186481318482151054013085401304442150854617085001728580110c54e14005881900503110048214486481340504160050217004841408540121048413405021300505111c54614104821310600122860214004c413105481200484184054815105c617284c2151060c110c500131060216005c2141050c141064a14104c215105061510502181064416305c41808600185844011046001408492160864a1628484131048013286101,
  0x150044113005ce18005021414444161848412205c0110c58c122444211045c21518503110060213104c417105401410545110858a16005d014105041308580182850418105141700484175444012204c014285821200488150050218004d4152850c140860013204c4170054511044c01208516190444c112064a11144c218005c2170050414085041300442182850a1610480152050017104c9110054a160854013084c0140045b14585c11108602130048816004c21218443190048818184821400502151048016204411228544151050215005421500482121058015085d012104c0150860013084861408604140060415206461210484120854014144421,
  0x16044421240502172854011084841500445150850c13205461508540192050017086001808652180858618086041300502193060414284c814185d6170444b1500542181058a170050814105c612085c0190850511005041608504162848a1728441152058017084c61510587110050614106421104642173050817304c1110848413004421510446110c54216186021500645112848a1438640140854415005d412144441300481110044015205401240584130044316084c01908541110848417184c215285801610588151058413005081800482120048219005501210604151054214704c615284c4120860c190860416005041310584130860012105101,
  0x191054216185441440642111458711246021800542120844213285c2141064414184c51104601110860013084c01220546152055213105c218005ce131054c1428504190860a140050a17205c0141c448181064219105401708546120850c13085c614106441514442111864211145c01910642120058213005c819005421918652111c4c413044411340504140048414085801210640110c50415205c0120c44c140850015205001720584141050016204861420512130850013105c214104c017105c216005c2141850814004401104484190048217006041610644160864111204441600644180844b15584c613104821300484120860c132064019205cc1,
  0x180858a13006441304442120c444131060412306441618441130054e161848216044501518442160044f17084c011004491808500162848416104c2140044312105c612204c413004c4182054f11004c41108441171044516004c21304442161848214106401338540140849c181c4561108504140050213005c8151048015105c2164064b11185041928504131064c1104580160858c12084801238484151054012106021518542164864216104c0160860a1310604140050212104c0130854015085401238480121064814105001410545110c585110850013106021800588151850a191050418104c218005041410582161864a13205c4160048212144401,
  0x1804444142050614085841710600142054617204c0120850a121858812184c4160864c12085d2120864c170864415285c01308504194048615205461420480130864a16286071110502111450c1808451166064415084841318502112864417004c81200545110c60415085c0142860818084411210504130050212305821600502155849816084451500482111044516105c012084861508544190050813006421930584161050214044401108584170854a16005c21600544162854414104ce120054419084801608484150048817244421908502111854419004c414105441620544160060212005821448584140850c144060217005ce120060412084401,
  0x12004c41820600110c582111c50017204841510600170850414185481410441130850415006101410542130049412004c8150048c11044c415104c0150854012104841510580113448414905ce121064016105421600542172854013104821618482190058911004c818184841718441144058416104ca121060018104c41910500110450015085c4134444017385061408440190858014085c0153850311086431108442150044214385c211244c2170064214005841404440151854a1908480120044a111c480131064218184d0152058015104c8170060412085841914440123860a130058216185001134640161064415085841300448161848814185821,
  0x160044d18184821948601110844819404d012004ce18105001238485110c640122064017086061558542140060213004ce163c442120850c15085061238500130850013104c217185421200602140048214104c0180860013405c3110064414104c4140864013084c017204c01720506170c440183c44612205401808604180844c114c5c2171c444130044c14004c0111c5061714444111048415084c01708504150048416085441944443171064613105c415085041208441181860417586041820580130864014285c21248582130054213105c4130054311004841420580132860a13084cc12084c0153860a163064412105081528544150050415144481,
  0x121060e131860111004c61508604131054012084801528542163054415084861120480161060218184d51158484160058a12204c014385061910484140850c1908583110054018385841240644140054212285041528600140858a150054215005c217285c71104580170c45213085c01238644170050212185081818504161048a165860419105c21840640172864219005821300547111044211544c012205c018444441128542154064c120854414004ca121058a152060c1628604121060416004431208540140864619085401238480180860014084c41428542113844317284c1112850311105c61608486130844517185421210646181048414086401,
  0x12086061208504170064219305c2131050017084c01304442122858412405c2141848414284841704440120058415004411300542127058a161048c180c4521440542144850815185c214104d61610610151444411004ca192050a1630582141048a190060e160444011004841208441160048e19005c2191444415105c01520580180854415004c3110844018005c21700482190054a162860a17085c4131848814044421400482162044317085901618605111048214004ce14404c413004821318608190048815004c4151048216004c41918441150c445140050216004c2130044e1910540112c48a12085841230502141064111085d0140044515085001,
  0x17105841610540164048a15104c8191c442170058415105ce112c5c012044461700584133850017105c418085801408540171050a13085c013085801520540142848212105c1111060412084c41510484151854214105ca17006041208484120060611084c0111c550110844d164848812185c81500542121064a1310480110c500143860415005c212105ca16005c41820447121048215005c4170854012384461808506141050412086441730482120c44614005081610580160044115005c21318602140064419084411510442111458418405ca140c4421808440132048c15004411728580192048018085c412005c416284d41818642121858815185441,
  0x1300542190048511384cc14284ca160858013085c51118442150048414084c615106421104484180850013085841410580160854015084841700650121064511085001408606191058216005c0113460417005c415284c8162864a15006041420546180848615705871100446160858c120860c160850015385061610642190c44012184c212005ca14084c41400482141858419404c41210582161048019704451608540150860c1808484110050412085c01910602193054212004c415205ca17285801820504191864e12004c416105c2180048816005ce1200502141050311045c2180048218184c2121054a111464c1908540152048013084c015086441,
  0x14304c217184c011044d21208506160860a1500502141054412184c216004c2140050212184c81230482154864a13086441210644190048219005421810550171850413105021900540110c50a1408604141c45016106021218482191854815144441510600190864c122048411046421300482151058417004841738492120848019804c017104c418284ce1200485110044213404ca150044114185c41720480150c44013084c01810502163060219004c21400548161864215004c2121055814084c4163058e14305421400502131060014105ca1388508170050413105841808446142064a12005d016204c0130c44012105c71108586110449013284841,
  0x15085c416005821900484151054414205801838506190044312084c0141064a19085401410584131048418084ca1500584151050419205c418005481210484181060413105c01520480161050213284c4170844112304c219106041424440152864417105801738580162050111045c1112054a170048414105161208584142848014104c4190c444121060c18104c0110c54211045421624446135444018186521104600130848417005021430482190064e13104ca1500482121054015086441600543110064218104c015205001528547110460a160848615085401700444110c5ce121848e141864e181864218284c416004a61300604130858417186421,
  0x1720580182050417105cc1210584131054216105c0170864015286021218508192854018085c0170854a151054a15006021728584121064a161058413106041758504170058216004c214185421710586170860419304c4140858411105d81828488110450e161049c1910480181c4401210642110c64a151058a120858012205451100488191054a19004c212005c4142064a19105c31100440163855217004411530504170850c18104821218542131054012105c816104c016085c01408580141060213005021818602150050812185c219305021730540110c60a18205d01248642150058212005d0180854619085401210643111050a130444211004961,
  0x12304c21318584170860014085841900484142848815004c2122850c16085c41328580161058216005c21600606110064612284821530581111044012006051110458111c5c013205c412106401208480182c44814004c21900482140064218185421500504192444a130049012105c21510481110448711084ca191050c1208540121060a15084801438540140c44412105041430504150860c145858213004c31110540141050417085d8131050a19204cc160444211004421608500150044118105c013204ca191050015084c4120058415204841200542191048418004c41808484180054213104ca1810504161054015084c41200602141050413306441,
  0x190844316085401208500121c440151860212585041400600112460215004c8120048e1210506110860414184c215004c7110054a1610585111856017004c2160060213005dc12104ca142860a1730446190064214004c414444481418542121049014106061208447150854014084c617205ca12185c416104c812185801104592160848a19106461308480172850815105401638640152060014105c51108480111464415085801608644171048c1310542190058a190851e150044718006041408480140848811084c217004c0110c5421710480140848c180c44c18204c61908544150050813005431108448140858018204c012104c812104c014385441,
  0x140c4481108542160060e16004821528500171048a18204c41348484150854613085041800445183854415104c41418482120064215004c4160860017104c4162444211004c511004c21200584131844312085011110482133064212106401308580110044119104c0121445014085c4140064816304821810504190050218004c11100604111c4c213105c4143060214004821400502131060414005421200604122c447190054215184c417104c81300443160049013384c015085401510602180054213304c8151058015085c11138484123050215004c419104c219105c417285c015205901600442170050a1310602181048a17284c0145444016004461,
  0x1210604131060218004841408646110c584140c4401518484130848c16084ca19005c8180444815286441500602151058013105c4131054215185c2151048412005421610644110464a120850618105c2130c44013004c4190848418406001208480131050416205c911084841908500135060016085c5110050817185c214184d013085001420506180848413004ca15384cc151050213004c211044c21300642191049214085801408502110844514084841400482154c44811005c81600482120050212186421700488120050a120848c191060a130860012084801710642160c442130848419004c4130c45517184c4170c4401108644141059217086001,
  0x14104801310542150050814184861104586192c4421900504160858011144c4152054416184c21748548190050419284c4140864017104c216004c21404448160048e140054812284c41310500161050415385061524444121045315285821510644130054416105ce1300502145044912285ca191444317084c414184d61720600130858417004ca11104431510592172048414106001608484170060213105c015084851128584172858013105041808600160854612084c711084c018085c01200455170848417285c61]

theorem S3 : RAFrame.seg TB 10 99864185642740312723 63 10 15 14 99836379105611416187 D3 1000000 = true := by decide +kernel

def D4 : List ℕ := [
  0x160c22205050b8415142c585010c8c13042a004c4098019042a005c20c0e122030306050983110c240c4450b8014042a004c409841504220044108821308263c4420882151c32105000902130c22004408b8711042c185420982181432185c20b10161430085c60c01110430105c20902150028184418c84141026105480a0014102c005c10a8013082c205050c0012142408482099e18042e186010900120426106400a83110a2e1c4400b86150022005c50a0c131426406440984170622084420a85110424185420885182c26105050988140032144410906141c2a306010a8412002a286040c80160830105020c08130422045400b02120c322054088821,
  0x110a26105410b00180426144400b02190a22104c00c8216002e084c00b81110a2600501098417002e085c20c8415202e104c20904190028086450c04170026285010a0a150828486020a84120828144420c0215002a28604088118042c00580888411102e105020b8212082c10484088f16082a285410b00120424244400980120824205820a8419002a284820c0215002808640088e15082c185410a8015042c185008886141622284820a0416183208588098618282c006410980151026204470883160828004458b2814042e004c40c00131030004c20a82152424086030902170030106420a02150026204c00c80110e24185ce0c84130828104810b0c1,
  0x1200220c5850b82120024284c40a80110428005420c04190830085c30b81111822004c78886120432284820c0a1304220c5008880140622184800982170028085000904150432104c00a0311002c105820a04181422104418b0414142810640090111102c184400900190426284428c8417142c286430a8215002a085800a8212002e084800982180024085050c81110432185c7088611062e004448c11110c2a104840a0b111422104c20b0013042a005010a09110028044420b821200263850509881104220c5408884121028005410906120424005050c10190832085c1888215082e085000a88120822045010c0419002420500098511082c205420b8c1,
  0x15082c206430c02160c24084820c10180026106040c00120428005050b02130830285c2098012042e00481098416002a084850a8015082a085000a0611022c08441891017042c004c20a82150822005810a80121c26004820a83110830186020b00110024105c00c8415042a004c20b84130828086030984160430104800a04131424085830b9416002c0c446088219002408480098a161024185010986120426105800c82130030085c20a8018042600601090c150e22005030a8011122e284870984170e22085060c08170e22205090902192030105820880110024106010b84150028404810c8a150828105420c81111c26105c08884110428106000c0a1,
  0x14042c10480888411082c10484090012202a105810c83111030085418880150028106010a0014102c0c441088213003204440098414002e284840a8015083008600098817002c10601088d120424005810884110022104820b00160826084800988171828104810b80122222085800c8111042e105c2088313002e086400c85110424044420882110024084428c0415082a306420988120824185480b04130c22086010b0416002a086480b0017042a244400b001600220c5850a0213003028545090419082e244400c10170430004c10b0014042400481888411002c105080b0215002a085400a82180026084820a0612042e285400902120824605c109801,
  0x12082a005820b82111630184810c83111a2c084c20a05110c32105010881130832084c00c82120e22105820a0212002610601090013042e106000982160828106400a84151c2400482098217082e005420c04161032004840a80130826105c20984151024104c00a8219002a104850a04141026004810b0c13082e085c60b82140832106400a02120026204408c0212002e384830a84171c2c185810b06131c2c005c10a00170e22305400982130826305420b041204261054b0b8413142c044410a8014043010540090814002c085820980151024005c20a02141430006000883141426105020a02130222004400a1014002a086400b02120024085c288801,
  0x12202c085820900130824085c28880140426104c00982180c2a206000b0416042e00586888017002a085c00982140824286000b8214002c08580888412082a285410c80110822145c10906190824044400b80170424285800902180422045020a8111002208440089415082420640090412042e004820a89110822004470b1c16082600601088b150024405018894110032104c20a8c150432585820980170826205800a02120024105820b08190c26084c30c16180430104c0888418042410600090217002e385c20b8612082808505888013082a205c80882111a24284800c96160432004870b041308281c4410904170c2c004408900151c2c3050509821,
  0x150828005440b8a170026206018880160c2a004448b8a12042a106080a8014342c1c4420a84141426105800881170422045460b0f110028085400a8414042e184410881171428205400b8814202610643090011002c105400b84121032004c10980140828086050902110e2c005c40c8012043230501090015042e005020b0216002e084c50984180622045c20904170622105400a82180028004408b8c12082e144440900121028006020902150026085c00c82120c28104870a85110026086420c0016082808545098614042814441088c120828284c20a80160426106030c1019042a105000982120c2a0848c0c0215002a106470b841800282054588801,
  0x130424005010b00190828284810980140c2204542090416002e405010b00150222004c10882150832084800904170826106010c0111042c005810b0416082a106000a081808260060a0a8415002a105810a00180828084800c01110c2e104800c02140824005810b0412302e084820c001704302c4400b02140832004418a00191428405070900161c260c442088e181c24006010a0a13002a044458c8619042e185020a88181830105c20c02140028105c10a8416082a30481098411022c105c10b9019082c004810a00121a22085800880112624106420c82190c26085020b00120426106450c80110022044820a8a160030085c0098e190c240858009021,
  0x121028285030c02150c26106050c8217142a004828883140424185c10906131c2610500098216002c20603888813082e186018880131c24284c0089714102e005ce0904160222086010a00130432005050b00110632084c00b84150426044410b8413002e085c60b0a15102c004c10900160622285400c0415042c186410c80171222106000982172024004c00881160026106450981111a2c386400c90171c3200441898012042c004458a0e13002808485090a14002e084c5088117042e584820b00120222085c10a06190422185cd0c8014082e10641090014042c005c10986191428105820c04171c301c4438c0013082e385830c84110422045010b001,
  0x110426084c00b8a160424105c50c0413002a044440a0418042a004c10a821104220c4c20c0412002e085800903110026205800c0215002e204820c04180028086000981110c26006010980130828585010a8019042c005410c06181422204c20a00140428004c20c02180a22004c20a0415202e385c20a8016082c086060b81110c24006420982120028086050900141024304c20908160032104810a801608220c5460c08180c2e206000b8418062200641098012042a104c50906140430105020b05111428004c10b80142826106050a0617042a105400a0415042c006040a80150824004408a00180a22106420a02160222385c20a001210221c5c109001,
  0x142822006420900160432306410901110424105800a02170826004810c8612102e106400a02150c2e084cb8880111432086030a90151c2c54440098413082c284c20a0c172830106000982161430004c38888150424106000c0217142400441890415142c005c4098414082810482090416242c085880984140028285820902170024084c00a0215002a086420c0017083008503888011042210485090216082c00581098413002a104c40c01110426185810904190024284810b0c150824104c20988150c26104c10b80130428005c10a16190222084800a8818002a085480c88111a32406000a04170430004c1098018042e405400a021700242444309871,
  0x16082204641090a150024385400b021506220050008851708220c5c20a8a180824005410c00150430184820c8e110228084c20c0018062218581090013082e105c10b0614042a184c1098619082a685420a04160030205020c0415202a005420982190a22005c10980120424104c308851614300444b08801520325c4460b8e1808262864309021320240444d0a0c160430105800b82180c2610500088113002c586410a8616042c004c20902181426484c20c02170c30084c00a84132c28086420a0615042e004820a8a141026006410c8015103008440890012042c005410910191828205408884152c2e085c3090a13082e104c1098c1304300c4410a021,
  0x121c2a606410a8617082e086060b02120024084c00982140826005050904180426184840c0c110a2e404840c0c132622084c3888817042e48488091618042c304840882110230005c10a00140432305c10982112a26205050b8b11122c004810c8012102a284800c881100220c6430b02174432405c20980130022385810c0015042400604098a140032044440c04150824105440a80111232104c30b84160826084c00b02142022044c10c8014042a305410b8019082a044400a0418082e004c10a06161026006010a0013042e005850b841900220c5410a8a170830186010a98171e22106030c84131022046410c06171032285450a00130222185c00a821,
  0x150024085420b00190426005050a82120c22304498a841900301444108801808220c483098218082e104c50c00190826084c30c0211002c205490b02170c2c144470b8c13042c1c444098211122c004418a84151222146410980121430105850c0a160432005c20b84161026305c20c0417082a204820c92180826106410c80180428004c08888120a22085420c8211102214481090019042c106490a0a18142e105c40a8019102e185870980140428105400b04191c2e10500090216003220582090a160222104840984140c2a085830a0a12002204489090217022210602888211002e105070984180832106000982130c28105440a8418002c105c40a801,
  0x191c30004840b0415002a205820a04140a22005c10c84171824084450980130830204830b041808261c4400b04140c28085000c00110022084408a801504281c4410b0012082e086060b0a120c22084428904171026284c00b0a150826404c5088917002e084c30904131222204400900131030004c40c8014042a044408c8412082c00481090a180c24104820880110224104800c8413082e385400c02110224085460982121222046410a8017202a085800c8217082a005020a84120428005810b0016082c206490a0e170030405420b8511122a105840a051100222048c0a02180c2c10585090413042a004868880170832185410a041800262058209841,
  0x1618220c542090015042a004810980170a22085c20904190030104c2088b121030285000a8417142e044410910140426004810b8015102c285c30c9019102e284c50986140c22045400b8214002c0c4420a80170824085030b0414082a084820a00120426285c50900131c26006420902160032205800b82170024084c00a82150030286010b04160024205c00983110826106000c85110422004c5098216082e106000c02170032104818886161030105c50a8c170828285010a0015082608581888019002808500088319082c1864a0c8012042a284c2090416082a00582098213182e085430902140828005020902150c2a0844689821208280050088821,
  0x11022e185030884110e2e444400b0815003010581098c13082e084800b0219082e106420c8614042410582088115042a305840c04152c24184c20a8212002210601090619082a085430c8511102400541090415002a104448a80141026005c50c88160c2a08500098815002a504428a001404221c5420c02140826004840a8011122800484090416082610580098215002c086000a82130c24084c2088116282c005410c8613062210546098414142c184408c04120830185410906190426884800b04120424005410c8a131428106000988140824005010c86130428284c288821104241c4410904180022184850a001604324064609821202223864009021,
  0x140024105c18880182024144470a84120022545830a02120032044410b83110c24385c00b0219002c086470883130826085030a02120c2e086060982120024084c7088313042c185420a03110832105800c8219002808640090a171c28005c0888016082a105c00990190424084408a00120424184c10984180c2e00441898011022e0060509091108260054b0a0e150826104c2088517182a086000a04151424084c00984140426304c10b80140430005040b84190222405c20a06110232104800c84121028004810c04180c2e085000a0214082a004810881180426105000983110024105010c0419082a0060709041200242c4400888132030784410a861,
  0x18002a084800a8a180430105800902180030084820c8c121c241054188821404260064a0a0416042224480888015002c285010a0617042a00481098019142a105810a0b112422085800c8413142408646098212082e184810a84170c320c4430a08150c2e085c20900161c28004c10a8615042a186020c8216082420441088317082c1c4420902170c2808543090418042e105c30a0216002a084860b84150430005c10c84180c2c085c009881544241c442098511043010640098415042a20440890a12002e085400a0418043218602088b17102c005420a04120832086060a01113c30005420a82150c30085000902160824106000a82120830106400c021,
  0x150432044440b80190830204c00902121830086020a8016042e144400b86110022046010a0616102c105420c8c1604260058b0902190832104c80a0616102e006020a021502221054a0a0a170028084c0098412082e104820b08130024086000984180826285810a8a130222086400902130026286030895171822044800b04121024286420c8412002a104c10900150824044428b83110022104820c00130424285800a0219002c085400a07110428405408880160c32084c60a821408301c441090013082e086000908161422045010b8412002c244400a02150026085820a8a19082a305c10906161030185440900160826084800982161424005c0088d1,
  0x12202c105c2098212082e005c18890190832305410b12140432785c00881130c24205c20b83110428106070a0416082a005450a08180c302c4418a82170c24206050984150032204c30a82130030204c00b84120432105400b0212042228440898616102a586420c90170828185420900111e24204820c00190824244430a02160222085800982180026105050a04170222185800c07110424085400a84191026185010c06180424485810c0012102a004c50c02141430105420b0a14082a106420c04130828304810a00171022045420b8215002a106010900150432005810904120832004c8098711002c005ca0b8019082e086020a0617082a106010b001,
  0x16102600442898e140028204820a0c170622004c2098e180824185810c0016282c004838880190c24004408b00151028185810c0017043000544888412002c285480904170826285010912140424285418884110026184c40a12170426104428a8612102a0c4410b08140c2c086420a06170022044800982160a22004810980181022045c20a84170428005878880150426105c0098011062a404810a90150c2a505048882130826444470a8012042c006010c12130622184410a0c14062210482088714102c005810b0412002a285c1090c170424004c10984170c28084830b08150c2c385830a0219082e084418982170422245410900121424084820a0c1,
  0x12042a005420b22120622004810b0014042e185c20982110822345c10a0a18082404441098419242a385c00b8812082c0064d0a8612042e005c20a0217082c006470900150622146420a8217002a084c00a02160c2c084820c0416082a18581098418002e205420900181026104c00a04141222004810b0c1504240060109001308220c5c2090418002a10481098615042c084408c10180026084c20b8013082a08500090215082c005010980140c220c6020a821500300c446090416043210540088518043210602888018082620480090a16042e004810b0013082e10547090016042a405450a80120424006400883181032285430911110424305c409001,
  0x130826106020b88130c32205490c80110822045450984160028204c50903110424086030c02150c32184408b06121222005820a821400320848c0882110a2c005040a04171222184430c8213082c185450a04161024485010904160222505050a00130430185810b0013042e18581888014102e004820c02160024086420a8413002e20602090012042a005c5098e120026106010b8014102a005408880132028285820b86150828284820982140028085c60b8215002c386400a88190028085c00b0a19102a105400a88140c24205460b88160c30205c08881140c24085800904131c2a28541088411062c084c009881518283c4430c82150826005c10c801,
  0x8cd120c24084c00c0413042c005050a08120a22005400881180024084800b02190222085030982130828306050902151822144c4098016042e186410a91111832084800a081108221c481098612042a004810c0014142e086000900111e30104c10c04180026085c20c80130428004850b08131824144440c0013042a005420a84181430085c0088315082a18548090a142622006480984120826006480a0219002a285420a8413022200480098e14002a105810b06190426405c20a8711102418581088115082e205080a001]

theorem S4 : RAFrame.seg TB 10 99876372021712761067 127 11 15 15 99864185642740312723 D4 1000000 = true := by decide +kernel

theorem cover : RAFrame.Inv 99752898761777419393 99876372021712761067 := by
  have h0 := RAFrame.inv_init 99752898761777419393 (RAFrame.cOK_prime _ _ _ _ _ _ _ TOK P0)
  have h1 := RAFrame.seg_sound TB 10 99752898761777419393 _ _ _ _ _ TOK _ _ _ S0 h0
  have h2 := RAFrame.seg_sound TB 10 99752898761777419393 _ _ _ _ _ TOK _ _ _ S1 h1
  have h3 := RAFrame.seg_sound TB 10 99752898761777419393 _ _ _ _ _ TOK _ _ _ S2 h2
  have h4 := RAFrame.seg_sound TB 10 99752898761777419393 _ _ _ _ _ TOK _ _ _ S3 h3
  have h5 := RAFrame.seg_sound TB 10 99752898761777419393 _ _ _ _ _ TOK _ _ _ S4 h4
  exact h5

end RAData

theorem solution (n : Nat)
    (hn : 99752898761777419393 < n) (hupper : n <= 99876372021712761067) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  exact RAFrame.finish 99752898761777419393 99876372021712761067 99752898761777419393 (99876372021712761067) RAData.cover (by norm_num) (by norm_num) n hn hupper
