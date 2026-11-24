-- Prove2me | solution 1 for SchoenfeldBRH.finitepsi_chunk2
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:08:34.623486+00:00
-- url     : https://prove2.me/submissions/7b2c54f9-7bf4-4d34-a394-307e158e8f59

import Mathlib

set_option linter.all false

namespace FinitePsi

def P : Nat := 129150405245356758951128837939389870063162700601269812726926098829920304165120204220589959940818708176830946524771060295498039124201406810520856934647865088430953560875653428566985048570882677821329196481215292503014034401044680012107736697561649621856185162540641496254997701110
def T : Nat := 11998169471918091112318812876937091662894933294512790097478624296976974992863551857893611351475199215017339160242261906255110389975279580853209338723815801944170964318388994939717965300638273661184172

def isPrB (p : Nat) : Bool :=
  Nat.ble 2 p && (List.range 26).all (fun m => Nat.blt m 2 || Nat.blt p (m * m) || !(p % m == 0))

def cval (m : Nat) : Nat :=
  if Nat.gcd m P = 1 then m
  else if (Nat.gcd m P) ^ 19 % m = 0 ∧ Nat.gcd m P < 666 ∧ T.testBit (Nat.gcd m P) = true then Nat.gcd m P
  else 1

def prodC : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | a, j+1, acc => prodC (a+1) j (acc * cval (a+1))

def W : Nat := 2 ^ 20
def lgL : ℚ := 6931471803 / 10 ^ 10
def lgH : ℚ := 6931471808 / 10 ^ 10
def piH : ℚ := 31416 / 10 ^ 4

/-- lower bound for √a · log² a / (8π), given s ≤ 2^10 √a and 2^eA ≤ fa^256, fa ≤ a -/
def fLow (s eA : Nat) : ℚ :=
  ((s : ℚ) / 2 ^ 10) * ((eA : ℚ) * lgL / 256) ^ 2 / (8 * piH)

/-- data: (B, K, e1, e2, eA, s, fa) -/
abbrev Blk := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def blockOK (B : Nat) (a : ℚ) (lo hi1 s eA : Nat) : Bool :=
  decide ((B : ℚ) ≤ a) ||
   (decide ((B : ℚ) - lo * lgL / W ≤ fLow s eA) && decide ((hi1 : ℚ) * lgH / W - a < fLow s eA))

def bitsOK (X e : Nat) : Bool := Nat.ble (1 <<< e) X && Nat.blt X (1 <<< (e + 1))

def run : Nat → Nat → Nat → ℚ → List Blk → Option (Nat × Nat × Nat)
  | A, lo, hi, a, [] => if decide ((A : ℚ) ≤ a) then some (A, lo, hi) else none
  | A, lo, hi, a, (B, K, e1, e2, eA, s, fa) :: rest =>
    let R1 := prodC A (B - 1 - A) 1
    let R2 := R1 * cval B
    let q := W / K
    if A < B && B < 452929 && 0 < K && W % K == 0 && decide ((A : ℚ) ≤ a)
        && Nat.ble 1 fa && decide ((fa : ℚ) ≤ a) && decide (((s : ℚ) / 2 ^ 10) ^ 2 ≤ a)
        && bitsOK (fa ^ 256) eA && bitsOK (R1 ^ K) e1 && bitsOK (R2 ^ K) e2
        && blockOK B a lo (hi + (e1 + 1) * q) s eA then
      run B (lo + e2 * q) (hi + (e2 + 1) * q) (max a B) rest
    else none

end FinitePsi


namespace FinitePsi
open Real Finset ArithmeticFunction

theorem isPrB_sound {p : ℕ} (hp : p < 676) (h : isPrB p = true) : p.Prime := by
  unfold isPrB at h
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hnp
  have hm := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : (p.minFac).Prime := Nat.minFac_prime (by omega)
  have hm2 := hmp.two_le
  have hm26 : p.minFac < 26 := by nlinarith
  have hd := Nat.minFac_dvd p
  rcases hall p.minFac hm26 with (h1 | h1) | h1
  · omega
  · nlinarith
  · exact h1 (Nat.eq_zero_of_dvd_of_lt (by omega) (by omega) |> fun _ => Nat.mod_eq_zero_of_dvd hd)

theorem isPrB_complete {p : ℕ} (h : p.Prime) : isPrB p = true := by
  unfold isPrB
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  refine ⟨h.two_le, fun m _ => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have hdvd : m ∣ p := Nat.dvd_of_mod_eq_zero h3
  rcases h.eq_one_or_self_of_dvd m hdvd with h4 | h4
  · omega
  · subst h4; nlinarith [h.two_le]

theorem hP1 : ∀ p < 666, isPrB p = true → P % p = 0 ∧ P % (p * p) ≠ 0 := by decide +kernel
theorem hP2 : Nat.factorial 665 % P = 0 := by decide +kernel
theorem hT : ∀ g < 666, T.testBit g = isPrB g := by decide +kernel
theorem hgap : ∀ q < 673, 666 ≤ q → isPrB q = false := by decide +kernel

theorem prime_dvd_P {p : ℕ} (hp : p.Prime) : p ∣ P ↔ p ≤ 665 := by
  constructor
  · intro h
    have : p ∣ Nat.factorial 665 := h.trans (Nat.dvd_of_mod_eq_zero hP2)
    exact (Nat.Prime.dvd_factorial hp).1 this
  · intro h
    exact Nat.dvd_of_mod_eq_zero (hP1 p (by omega) (isPrB_complete hp)).1

theorem prime_sq_not_dvd_P {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ P := by
  intro h
  have h1 : p ∣ P := (Dvd.intro_left _ (by ring) : p ∣ p ^ 2).trans h
  have h2 := (prime_dvd_P hp).1 h1
  have := (hP1 p (by omega) (isPrB_complete hp)).2
  exact this (Nat.mod_eq_zero_of_dvd (by rw [← pow_two]; exact h))

theorem cval_spec {m : ℕ} (h1 : 1 ≤ m) (h2 : m < 452929) :
    Λ m = Real.log (cval m) ∧ cval m ≠ 0 := by
  unfold cval
  by_cases hg : Nat.gcd m P = 1
  · rw [if_pos hg]
    refine ⟨?_, by omega⟩
    by_cases hm1 : m = 1
    · subst hm1; simp
    have hpr : m.Prime := by
      by_contra hnp
      have hq := Nat.minFac_sq_le_self (by omega) hnp
      have hqp : (m.minFac).Prime := Nat.minFac_prime hm1
      have hq673 : m.minFac < 673 := by nlinarith
      have hq665 : m.minFac ≤ 665 := by
        by_contra hc
        have := hgap m.minFac hq673 (by omega)
        rw [isPrB_complete hqp] at this
        exact Bool.noConfusion this
      have hdP := (prime_dvd_P hqp).2 hq665
      have := Nat.dvd_gcd (Nat.minFac_dvd m) hdP
      rw [hg] at this
      exact hqp.one_lt.ne' (Nat.dvd_one.1 this)
    exact vonMangoldt_apply_prime hpr
  · rw [if_neg hg]
    set g := Nat.gcd m P with hgdef
    by_cases ht : g ^ 19 % m = 0 ∧ g < 666 ∧ T.testBit g = true
    · rw [if_pos ht]
      obtain ⟨ha, hb, hc⟩ := ht
      have hgp : g.Prime := isPrB_sound (by omega) (by rw [← hT g hb]; exact hc)
      obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hgp).1 (Nat.dvd_of_mod_eq_zero ha)
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hmi
        apply hg; rw [hgdef, hmi]; simp
      refine ⟨?_, hgp.ne_zero⟩
      rw [hmi, vonMangoldt_apply_pow hi0, vonMangoldt_apply_prime hgp]
    · rw [if_neg ht]
      refine ⟨?_, one_ne_zero⟩
      simp only [Nat.cast_one, Real.log_one]
      rw [vonMangoldt_eq_zero_iff]
      intro hpp
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      apply ht
      have hgd : g ∣ p ^ k := Nat.gcd_dvd_left _ _
      obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow hp).1 hgd
      have hi0 : i ≠ 0 := by
        rintro rfl; exact hg (by simpa using hgi)
      have hpg : p ∣ g := by rw [hgi]; exact dvd_pow_self p hi0
      have hpP : p ∣ P := hpg.trans (Nat.gcd_dvd_right _ _)
      have hp665 := (prime_dvd_P hp).1 hpP
      have hi1 : i = 1 := by
        by_contra hne
        apply prime_sq_not_dvd_P hp
        have : p ^ 2 ∣ g := by rw [hgi]; exact pow_dvd_pow p (by omega)
        exact this.trans (Nat.gcd_dvd_right _ _)
      rw [hi1, pow_one] at hgi
      rw [hgi]
      have hk19 : k ≤ 19 := by
        by_contra hc
        have : 2 ^ 20 ≤ p ^ k := calc
          2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        omega
      refine ⟨Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hk19), by omega, ?_⟩
      rw [hT p (by omega)]; exact isPrB_complete hp

theorem prodC_eq (j : ℕ) : ∀ a acc, prodC a j acc = acc * ∏ m ∈ Ioc a (a + j), cval m := by
  induction j with
  | zero => intro a acc; simp [prodC]
  | succ j ih =>
    intro a acc
    rw [prodC, ih, ← prod_Ioc_consecutive _ (Nat.le_succ a) (by omega : a + 1 ≤ a + (j + 1)),
      Nat.Ioc_succ_singleton, prod_singleton, show a + 1 + j = a + (j + 1) by omega]
    ring

theorem psi_nat (n : ℕ) : Chebyshev.psi n = ∑ m ∈ Ioc 0 n, Λ m := by
  simp [Chebyshev.psi]

theorem psi_diff {a b : ℕ} (h : a ≤ b) :
    Chebyshev.psi b - Chebyshev.psi a = ∑ m ∈ Ioc a b, Λ m := by
  rw [psi_nat, psi_nat, ← sum_Ioc_consecutive _ (Nat.zero_le a) h]; ring

theorem log_prodC {a j : ℕ} (h : a + j < 452929) :
    Real.log (prodC a j 1) = Chebyshev.psi (a + j : ℕ) - Chebyshev.psi a := by
  rw [psi_diff (by omega), prodC_eq, one_mul, Nat.cast_prod,
    Real.log_prod (fun m hm => by
      have := (cval_spec (m := m) (by simp at hm; omega) (by simp at hm; omega)).2
      exact_mod_cast this)]
  refine sum_congr rfl (fun m hm => ?_)
  simp only [mem_Ioc] at hm
  exact ((cval_spec (by omega) (by omega)).1).symm

end FinitePsi


namespace FinitePsi
open Real Finset ArithmeticFunction

noncomputable def fR (x : ℝ) : ℝ := Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

theorem fR_mono {a x : ℝ} (ha : 1 ≤ a) (hx : a ≤ x) : fR a ≤ fR x := by
  unfold fR
  have h1 : Real.sqrt a ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have h2 : 0 ≤ Real.log a := Real.log_nonneg ha
  have h3 : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx
  have h4 : Real.log a ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ h2 h3 2
  have := Real.pi_pos
  gcongr

theorem log_lower {e n : ℕ} {K : ℕ} (hK : 0 < K) (hn : 0 < n) (h : 2 ^ e ≤ n ^ K) :
    (e : ℝ) * Real.log 2 ≤ K * Real.log n := by
  have h' : ((2 : ℝ) ^ e) ≤ (n : ℝ) ^ K := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow, Real.log_pow] at this

theorem log_upper {e n : ℕ} {K : ℕ} (hn : 0 < n) (h : n ^ K < 2 ^ (e + 1)) :
    K * Real.log n < ((e : ℝ) + 1) * Real.log 2 := by
  have h' : (n : ℝ) ^ K < (2 : ℝ) ^ (e + 1) := by exact_mod_cast h
  have := Real.log_lt_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this; linarith

theorem fLow_le {s eA fa : ℕ} {a : ℝ} (hs : ((s : ℝ) / 2 ^ 10) ^ 2 ≤ a) (hfa1 : 1 ≤ fa)
    (hfa : (fa : ℝ) ≤ a) (heA : 2 ^ eA ≤ fa ^ 256) : ((fLow s eA : ℚ) : ℝ) ≤ fR a := by
  unfold fLow fR lgL piH
  push_cast
  have ha1 : (1 : ℝ) ≤ a := le_trans (by exact_mod_cast hfa1) hfa
  have hsq : (s : ℝ) / 2 ^ 10 ≤ Real.sqrt a := Real.le_sqrt_of_sq_le hs
  have hl := log_lower (K := 256) (by norm_num) (by omega) heA
  have hlfa : Real.log fa ≤ Real.log a := Real.log_le_log (by exact_mod_cast (by omega : 0 < fa)) hfa
  have hl2 := Real.log_two_gt_d9
  have hL : (eA : ℝ) * (6931471803 / 10 ^ 10) / 256 ≤ Real.log a := by
    have : (eA : ℝ) * (6931471803 / 10 ^ 10) ≤ eA * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); norm_num at hl2 ⊢; linarith
    push_cast at hl
    linarith
  have hL0 : 0 ≤ (eA : ℝ) * (6931471803 / 10 ^ 10) / 256 := by positivity
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h2 : ((eA : ℝ) * (6931471803 / 10 ^ 10) / 256) ^ 2 ≤ Real.log a ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hs0 : (0 : ℝ) ≤ (s : ℝ) / 2 ^ 10 := by positivity
  calc (s : ℝ) / 2 ^ 10 * ((eA : ℝ) * (6931471803 / 10 ^ 10) / 256) ^ 2 / (8 * (31416 / 10 ^ 4))
      ≤ Real.sqrt a * Real.log a ^ 2 / (8 * (31416 / 10 ^ 4)) := by
        gcongr
    _ ≤ Real.sqrt a * Real.log a ^ 2 / (8 * Real.pi) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        norm_num at hpi ⊢; linarith

theorem block_bound {A B : ℕ} {a x L U Fl : ℝ} (hA : (A : ℝ) ≤ a) (ha1 : 1 ≤ a) (hx : a ≤ x)
    (hxB : x < B) (hL : L ≤ Chebyshev.psi A) (hU : Chebyshev.psi ((B - 1 : ℕ) : ℝ) ≤ U)
    (hF : Fl ≤ fR a) (c1 : (B : ℝ) - L ≤ Fl) (c2 : U - a < Fl) :
    |Chebyshev.psi x - x| < fR x := by
  have hfx := fR_mono ha1 hx
  have hx0 : 0 ≤ x := by linarith
  have hpA : Chebyshev.psi A ≤ Chebyshev.psi x := Chebyshev.psi_mono (by linarith)
  have hpB : Chebyshev.psi x ≤ Chebyshev.psi ((B - 1 : ℕ) : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor x]
    apply Chebyshev.psi_mono
    have : ⌊x⌋₊ < B := (Nat.floor_lt hx0).2 hxB
    exact_mod_cast (by omega : ⌊x⌋₊ ≤ B - 1)
  rw [abs_lt]; constructor <;> linarith

def Good (A lo hi : ℕ) : Prop :=
  (lo : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi A ∧ Chebyshev.psi A ≤ (hi : ℝ) / 1048576 * Real.log 2

theorem bitsOK_iff {X e : ℕ} (h : bitsOK X e = true) : 2 ^ e ≤ X ∧ X < 2 ^ (e + 1) := by
  unfold bitsOK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft] at h
  exact h

theorem run_sound : ∀ (l : List Blk) (A lo hi : ℕ) (a : ℚ) (A' lo' hi' : ℕ),
    run A lo hi a l = some (A', lo', hi') → Good A lo hi →
    (∀ x : ℝ, (a : ℝ) ≤ x → x < A' → |Chebyshev.psi x - x| < fR x) ∧ Good A' lo' hi' := by
  intro l
  induction l with
  | nil =>
    intro A lo hi a A' lo' hi' h hG
    simp only [run] at h
    split_ifs at h with h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨fun x hx hxA => ?_, hG⟩
    have : ((A : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast (of_decide_eq_true h1)
    push_cast at this
    linarith
  | cons blk rest ih =>
    intro A lo hi a A' lo' hi' h hG
    obtain ⟨B, K, e1, e2, eA, s, fa⟩ := blk
    simp only [run] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAB, hB⟩, hK⟩, hWK⟩, hAa⟩, hfa1⟩, hfaa⟩, hsa⟩, heA⟩, he1⟩, he2⟩, hblk⟩ := hc
    have hAB' : A < B := by simpa using hAB
    have hB' : B < 452929 := by simpa using hB
    have hK' : 0 < K := by simpa using hK
    -- the products
    set R1 := prodC A (B - 1 - A) 1 with hR1
    have hlogR1 : Real.log R1 = Chebyshev.psi ((B - 1 : ℕ) : ℝ) - Chebyshev.psi A := by
      rw [hR1, log_prodC (by omega), show A + (B - 1 - A) = B - 1 by omega]
    have hR1pos : 0 < R1 := by
      rw [hR1, prodC_eq, one_mul]
      apply Finset.prod_pos
      intro m hm; simp only [mem_Ioc] at hm
      exact Nat.pos_of_ne_zero (cval_spec (by omega) (by omega)).2
    have hcB := cval_spec (m := B) (by omega) hB'
    have hlogR2 : Real.log ((R1 * cval B : ℕ) : ℝ) = Chebyshev.psi (B : ℝ) - Chebyshev.psi A := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast hR1pos.ne') (by exact_mod_cast hcB.2), hlogR1, ← hcB.1]
      have := psi_diff (a := B - 1) (b := B) (by omega)
      rw [show Ioc (B - 1) B = {B} by ext m; simp; omega] at this
      simp at this
      rw [show ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 by push_cast [Nat.cast_sub (by omega : 1 ≤ B)]; ring] at *
      linarith
    have hR2pos : 0 < R1 * cval B := Nat.mul_pos hR1pos (Nat.pos_of_ne_zero hcB.2)
    obtain ⟨e1lo, e1hi⟩ := bitsOK_iff he1
    obtain ⟨e2lo, e2hi⟩ := bitsOK_iff he2
    obtain ⟨eAlo, -⟩ := bitsOK_iff heA
    have l1u := log_upper hR1pos e1hi
    have l2l := log_lower hK' hR2pos e2lo
    have l2u := log_upper hR2pos e2hi
    -- q * K = W
    have hqK : ((1048576 / K : ℕ) : ℝ) * K = 1048576 := by
      have : 1048576 / K * K = 1048576 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (by simpa [W] using hWK))
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK'
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    obtain ⟨hGl, hGu⟩ := hG
    -- new Good
    have hqd : ∀ t : ℝ, t * ((1048576 / K : ℕ) : ℝ) / 1048576 = t / K := by
      intro t
      rw [div_eq_div_iff (by norm_num) hKpos.ne', mul_assoc, hqK]
    have k2l : (e2 : ℝ) * ((1048576 / K : ℕ) : ℝ) / 1048576 * Real.log 2 ≤
        Chebyshev.psi (B : ℝ) - Chebyshev.psi A := by
      rw [hqd, ← hlogR2, div_mul_eq_mul_div, div_le_iff₀ hKpos]; linarith
    have k2u : Chebyshev.psi (B : ℝ) - Chebyshev.psi A ≤
        ((e2 : ℝ) + 1) * ((1048576 / K : ℕ) : ℝ) / 1048576 * Real.log 2 := by
      rw [hqd, ← hlogR2, div_mul_eq_mul_div, le_div_iff₀ hKpos]; linarith
    have k1u : Chebyshev.psi ((B - 1 : ℕ) : ℝ) - Chebyshev.psi A ≤
        ((e1 : ℝ) + 1) * ((1048576 / K : ℕ) : ℝ) / 1048576 * Real.log 2 := by
      rw [hqd, ← hlogR1, div_mul_eq_mul_div, le_div_iff₀ hKpos]; linarith
    have hGood : Good B (lo + e2 * (W / K)) (hi + (e2 + 1) * (W / K)) := by
      simp only [Good, W]
      push_cast
      constructor <;> linarith
    obtain ⟨ihx, ihG⟩ := ih B _ _ (max a B) A' lo' hi' h hGood
    refine ⟨fun x hx hxA => ?_, ihG⟩
    by_cases hxB : x < B
    · -- block case
      unfold blockOK at hblk
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hblk
      have haR : ((A : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hAa
      push_cast at haR
      have hfaR : ((fa : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hfaa
      push_cast at hfaR
      have hfa1' : 1 ≤ fa := by simpa using hfa1
      have ha1 : (1 : ℝ) ≤ a := le_trans (by exact_mod_cast hfa1') hfaR
      have hsR : (((s : ℚ) / 2 ^ 10) ^ 2 : ℚ) ≤ a := hsa
      have hsR' : ((s : ℝ) / 2 ^ 10) ^ 2 ≤ (a : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).2 hsR; push_cast at this; exact this
      have hF := fLow_le hsR' hfa1' hfaR eAlo
      rcases hblk with hBa | ⟨c1, c2⟩
      · have : ((B : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hBa
        push_cast at this; linarith
      · have c1R : (((B : ℚ) - lo * lgL / W : ℚ) : ℝ) ≤ ((fLow s eA : ℚ) : ℝ) := by exact_mod_cast c1
        have c2R : ((((hi + (e1 + 1) * (W / K) : ℕ) : ℚ) * lgH / W - a : ℚ) : ℝ) < ((fLow s eA : ℚ) : ℝ) := by
          exact_mod_cast c2
        simp only [lgL, lgH, W] at c1R c2R
        push_cast at c1R c2R
        have hl2l : (6931471803 / 10 ^ 10 : ℝ) ≤ Real.log 2 := by
          have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
        have hl2u : Real.log 2 ≤ (6931471808 / 10 ^ 10 : ℝ) := by
          have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
        apply block_bound haR ha1 hx hxB (L := (lo : ℝ) * (6931471803 / 10 ^ 10) / 1048576)
          (U := ((hi : ℝ) + ((e1 : ℝ) + 1) * ((1048576 / K : ℕ) : ℝ)) * (6931471808 / 10 ^ 10) / 1048576)
          (hF := hF)
        · have : (lo : ℝ) * (6931471803 / 10 ^ 10) ≤ lo * Real.log 2 :=
            mul_le_mul_of_nonneg_left hl2l (by positivity)
          nlinarith
        · -- ψ(B-1) ≤ ψ A + log R1 ≤ hi/W log2 + (e1+1)/K log 2
          have hq0 : (0 : ℝ) ≤ ((1048576 / K : ℕ) : ℝ) := by positivity
          have : ((hi : ℝ) + ((e1 : ℝ) + 1) * ((1048576 / K : ℕ) : ℝ)) * Real.log 2 ≤
              ((hi : ℝ) + ((e1 : ℝ) + 1) * ((1048576 / K : ℕ) : ℝ)) * (6931471808 / 10 ^ 10) :=
            mul_le_mul_of_nonneg_left hl2u (by positivity)
          nlinarith
        · linarith
        · linarith
    · push Not at hxB
      exact ihx x (by push_cast; exact max_le hx hxB) hxA

end FinitePsi

set_option maxHeartbeats 4000000 in
theorem solution :
    ((324600561728 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (214499 : ℝ) ∧
      Chebyshev.psi (214499 : ℝ) ≤ (324603956688 : ℝ) / 1048576 * Real.log 2) →
    (∀ x : ℝ, (214499 : ℝ) ≤ x → x < (330047 : ℝ) →
      |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ∧
    ((499553927232 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (330047 : ℝ) ∧
      Chebyshev.psi (330047 : ℝ) ≤ (499559583184 : ℝ) / 1048576 * Real.log 2) := by
  intro hG
  have hrun : FinitePsi.run 214499 324600561728 324603956688 (214499 : ℚ) [(217333, 32, 124182, 124749, 4533, 474255, 214499),
    (220021, 16, 65704, 65988, 4538, 477378, 217333),
    (222841, 32, 125006, 125575, 4543, 480321, 220021),
    (225613, 32, 130251, 130821, 4548, 483389, 222841),
    (228469, 32, 128866, 129435, 4552, 486387, 225613),
    (231169, 16, 66252, 66537, 4557, 489455, 228469),
    (234103, 32, 124934, 125505, 4561, 492339, 231169),
    (237034, 16, 65956, 65956, 4566, 495454, 234103),
    (239915, 16, 65880, 65880, 4570, 498546, 237034),
    (242794, 16, 68805, 68805, 4575, 501566, 239915),
    (245789, 16, 69589, 69875, 4579, 504567, 242794),
    (248737, 16, 69370, 69657, 4584, 507669, 245789),
    (251701, 16, 68432, 68719, 4588, 510705, 248737),
    (254803, 16, 68497, 68785, 4592, 513738, 251701),
    (257897, 16, 71294, 71294, 4597, 516894, 254803),
    (261010, 16, 71220, 71220, 4601, 520023, 257897),
    (264121, 16, 71161, 71161, 4606, 523152, 261010),
    (267228, 16, 71789, 71789, 4610, 526261, 264121),
    (270337, 16, 75606, 75894, 4615, 529347, 267228),
    (273517, 16, 72066, 72355, 4619, 532417, 270337),
    (276671, 16, 73580, 73869, 4623, 535540, 273517),
    (279991, 16, 73286, 73575, 4627, 538619, 276671),
    (283181, 16, 76757, 77047, 4632, 541841, 279991),
    (286493, 16, 73928, 74218, 4636, 544919, 283181),
    (289877, 16, 75739, 75739, 4640, 548096, 286493),
    (293185, 16, 76243, 76243, 4645, 551323, 289877),
    (296513, 16, 73551, 73551, 4649, 554460, 293185),
    (299725, 16, 72014, 72014, 4653, 557598, 296513),
    (302869, 16, 71734, 71734, 4657, 560610, 299725),
    (306001, 16, 77525, 77525, 4661, 563543, 302869),
    (309383, 16, 77299, 77299, 4665, 566449, 306001),
    (312757, 16, 76345, 76637, 4669, 569571, 309383),
    (316103, 16, 77724, 77724, 4673, 572668, 312757),
    (319495, 16, 83493, 83493, 4677, 575723, 316103),
    (323009, 16, 82539, 82832, 4681, 578804, 319495),
    (326561, 16, 81439, 81732, 4685, 581978, 323009),
    (330047, 16, 82094, 82387, 4689, 585170, 326561)] = some (330047, 499553927232, 499559583184) := by
    decide +kernel
  obtain ⟨h1, h2⟩ := FinitePsi.run_sound _ _ _ _ _ _ _ _ hrun (by simp only [FinitePsi.Good]; push_cast; exact hG)
  refine ⟨fun x hx hxA => ?_, by simp only [FinitePsi.Good] at h2; push_cast at h2; exact h2⟩
  have := h1 x (by push_cast; norm_num at hx ⊢; linarith) (by push_cast at hxA ⊢; linarith)
  simpa [FinitePsi.fR] using this
