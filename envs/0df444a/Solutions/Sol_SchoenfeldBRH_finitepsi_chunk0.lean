-- Prove2me | solution 1 for SchoenfeldBRH.finitepsi_chunk0
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:08:33.26763+00:00
-- url     : https://prove2.me/submissions/2e58234c-6d68-4a0d-8c3b-33350071e0bf

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

theorem solution :
    (∀ x : ℝ, (73.2 : ℝ) ≤ x → x < (101113 : ℝ) →
      |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ∧
    ((152949030976 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (101113 : ℝ) ∧
      Chebyshev.psi (101113 : ℝ) ≤ (152950689232 : ℝ) / 1048576 * Real.log 2) := by
  have hrun : FinitePsi.run 1 0 0 (366/5 : ℚ) [(73, 1024, 104601, 110939, 1584, 8761, 73),
    (79, 131072, 0, 826249, 1584, 8761, 73),
    (86, 16384, 130416, 130416, 1613, 9101, 79),
    (92, 16384, 106098, 106098, 1645, 9496, 86),
    (97, 131072, 0, 865063, 1670, 9821, 92),
    (102, 16384, 109088, 109088, 1689, 10085, 97),
    (107, 16384, 109551, 220003, 1708, 10341, 102),
    (113, 16384, 110889, 222631, 1725, 10592, 107),
    (126, 16384, 94721, 94721, 1745, 10885, 113),
    (131, 16384, 130886, 246122, 1786, 11494, 126),
    (142, 8192, 116465, 116465, 1800, 11720, 131),
    (153, 8192, 118436, 118436, 1830, 12202, 142),
    (164, 8192, 119958, 119958, 1857, 12666, 153),
    (175, 4096, 75852, 75852, 1883, 13113, 164),
    (188, 8192, 122746, 122746, 1907, 13546, 175),
    (199, 4096, 93355, 124635, 1933, 14040, 188),
    (221, 16384, 126502, 126502, 1954, 14445, 199),
    (228, 8192, 128020, 128020, 1993, 15222, 221),
    (240, 4096, 96683, 96683, 2005, 15462, 228),
    (257, 4096, 75650, 108441, 2024, 15863, 240),
    (276, 4096, 99092, 99092, 2049, 16415, 257),
    (293, 4096, 116655, 150220, 2075, 17011, 276),
    (313, 4096, 67759, 101715, 2097, 17528, 293),
    (339, 4096, 102709, 102709, 2122, 18116, 313),
    (358, 4096, 115330, 115330, 2151, 18853, 339),
    (379, 4096, 122054, 157140, 2171, 19374, 358),
    (407, 2048, 70584, 70584, 2192, 19935, 379),
    (432, 2048, 71385, 71385, 2219, 20658, 407),
    (458, 2048, 90058, 90058, 2241, 21283, 432),
    (490, 2048, 90936, 90936, 2262, 21914, 458),
    (523, 2048, 93989, 112484, 2287, 22667, 490),
    (562, 4096, 130334, 130334, 2311, 23418, 523),
    (587, 2048, 74995, 93831, 2338, 24275, 562),
    (620, 1024, 66270, 66270, 2354, 24809, 587),
    (659, 2048, 100279, 119457, 2374, 25497, 620),
    (701, 2048, 96285, 115645, 2397, 26287, 659),
    (750, 2048, 120083, 120083, 2420, 27111, 701),
    (793, 2048, 117739, 117739, 2444, 28043, 750),
    (835, 1024, 69340, 69340, 2465, 28836, 793),
    (883, 1024, 74863, 84884, 2484, 29589, 835),
    (941, 2048, 120882, 141112, 2505, 30428, 883),
    (995, 1024, 76190, 76190, 2528, 31411, 941),
    (1049, 1024, 82899, 93175, 2549, 32300, 995),
    (1103, 1024, 82509, 92859, 2568, 33165, 1049),
    (1171, 1024, 72742, 83180, 2587, 34008, 1103),
    (1237, 1024, 94359, 104878, 2609, 35041, 1171),
    (1303, 1024, 95131, 105727, 2629, 36015, 1237),
    (1381, 1024, 83330, 94012, 2648, 36963, 1303),
    (1455, 1024, 107342, 107342, 2670, 38053, 1381),
    (1531, 1024, 107935, 118770, 2689, 39059, 1455),
    (1609, 1024, 119620, 130527, 2708, 40067, 1531),
    (1693, 1024, 103918, 114901, 2726, 41075, 1609),
    (1783, 1024, 121184, 132244, 2745, 42133, 1693),
    (1877, 1024, 127654, 138789, 2764, 43238, 1783),
    (1978, 1024, 111704, 111704, 2783, 44364, 1877),
    (2058, 512, 67934, 67934, 2803, 45542, 1978),
    (2153, 512, 79133, 84802, 2817, 46453, 2058),
    (2269, 512, 68156, 73864, 2834, 47514, 2153),
    (2376, 512, 80139, 80139, 2853, 48777, 2269),
    (2477, 512, 87764, 93537, 2870, 49914, 2376),
    (2617, 512, 69545, 75358, 2886, 50963, 2477),
    (2726, 512, 99112, 99112, 2906, 52384, 2617),
    (2837, 512, 84929, 90802, 2921, 53464, 2726),
    (2963, 512, 82439, 88344, 2936, 54541, 2837),
    (3109, 512, 88831, 94771, 2952, 55739, 2963),
    (3248, 512, 84585, 84585, 2970, 57096, 3109),
    (3368, 512, 101761, 101761, 2986, 58359, 3248),
    (3509, 512, 93222, 93222, 2999, 59427, 3368),
    (3640, 512, 120851, 120851, 3014, 60658, 3509),
    (3797, 512, 112337, 118425, 3028, 61780, 3640),
    (3943, 512, 109859, 115975, 3044, 63098, 3797),
    (4099, 512, 104751, 110895, 3057, 64300, 3943),
    (4261, 512, 117049, 123223, 3072, 65559, 4099),
    (4451, 512, 117602, 123807, 3086, 66842, 4261),
    (4636, 512, 121271, 121271, 3102, 68316, 4451),
    (4806, 256, 71851, 71851, 3117, 69722, 4636),
    (5003, 256, 70118, 73264, 3131, 70989, 4806),
    (5209, 256, 70939, 74099, 3145, 72429, 5003),
    (5417, 256, 68120, 71295, 3160, 73905, 5209),
    (5616, 256, 73164, 73164, 3175, 75366, 5417),
    (5820, 256, 79868, 79868, 3188, 76738, 5616),
    (6042, 256, 76977, 76977, 3201, 78119, 5820),
    (6257, 256, 82150, 85379, 3215, 79595, 6042),
    (6481, 256, 87324, 90565, 3228, 80999, 6257),
    (6719, 256, 81628, 84883, 3241, 82436, 6481),
    (6961, 256, 87519, 90787, 3254, 83936, 6719),
    (7213, 256, 88397, 91678, 3267, 85434, 6961),
    (7489, 256, 85488, 88782, 3280, 86967, 7213),
    (7737, 256, 105624, 105624, 3294, 88615, 7489),
    (8029, 256, 97754, 97754, 3306, 90071, 7737),
    (8302, 256, 106727, 106727, 3320, 91755, 8029),
    (8598, 256, 93508, 93508, 3332, 93302, 8302),
    (8859, 256, 110591, 110591, 3345, 94950, 8598),
    (9165, 256, 110987, 110987, 3356, 96381, 8859),
    (9463, 256, 119836, 123217, 3369, 98031, 9165),
    (9769, 256, 108392, 111785, 3381, 99612, 9463),
    (10093, 256, 112156, 115561, 3393, 101210, 9769),
    (10399, 256, 117657, 121074, 3405, 102875, 10093),
    (10729, 256, 114642, 118070, 3416, 104422, 10399),
    (11087, 256, 120185, 123625, 3427, 106066, 10729),
    (11450, 256, 129222, 129222, 3439, 107821, 11087),
    (11809, 256, 117555, 117555, 3451, 109572, 11450),
    (12136, 256, 130046, 130046, 3463, 111277, 11809),
    (12495, 128, 68413, 68413, 3473, 112807, 12136),
    (12874, 128, 72395, 72395, 3483, 114463, 12495),
    (13249, 128, 73499, 75252, 3494, 116186, 12874),
    (13681, 128, 70229, 71988, 3505, 117866, 13249),
    (14087, 128, 79256, 81020, 3517, 119772, 13681),
    (14537, 128, 68923, 70693, 3528, 121537, 14087),
    (14929, 128, 80196, 81971, 3539, 123463, 14537),
    (15361, 128, 81773, 83553, 3549, 125116, 14929),
    (15773, 128, 78732, 80517, 3560, 126914, 15361),
    (16193, 128, 75966, 77756, 3569, 128604, 15773),
    (16657, 128, 77208, 79003, 3579, 130305, 16193),
    (17155, 128, 86655, 86655, 3590, 132159, 16657),
    (17627, 128, 92856, 94661, 3600, 134120, 17155),
    (18121, 128, 86793, 88604, 3611, 135953, 17627),
    (18593, 128, 92457, 94272, 3621, 137845, 18121),
    (19166, 128, 84552, 84552, 3630, 139628, 18593),
    (19636, 128, 93896, 93896, 3641, 141763, 19166),
    (20153, 128, 100745, 100745, 3650, 143491, 19636),
    (20709, 128, 93466, 93466, 3660, 145368, 20153),
    (21226, 128, 101066, 101066, 3670, 147359, 20709),
    (21783, 128, 105011, 105011, 3679, 149188, 21226),
    (22349, 128, 108044, 109894, 3689, 151132, 21783),
    (22937, 128, 104623, 106477, 3698, 153083, 22349),
    (23555, 128, 109526, 109526, 3708, 155084, 22937),
    (24097, 128, 115387, 117250, 3718, 157159, 23555),
    (24697, 128, 100422, 102290, 3726, 158957, 24097),
    (25343, 128, 110346, 112218, 3735, 160924, 24697),
    (25989, 128, 118119, 118119, 3745, 163015, 25343),
    (26640, 128, 117461, 117461, 3754, 165080, 25989),
    (27288, 128, 128102, 128102, 3763, 167134, 26640),
    (27967, 128, 121823, 123714, 3772, 169155, 27288),
    (28649, 128, 125422, 127317, 3781, 171246, 27967),
    (29339, 128, 127123, 129023, 3790, 173322, 28649),
    (30086, 128, 121398, 121398, 3799, 175397, 29339),
    (30756, 128, 121990, 121990, 3808, 177616, 30086),
    (31428, 64, 66859, 66859, 3816, 179582, 30756),
    (32163, 128, 125400, 125400, 3824, 181534, 31428),
    (32855, 64, 70568, 70568, 3833, 183644, 32163),
    (33601, 64, 72098, 73061, 3840, 185609, 32855),
    (34351, 64, 68396, 69360, 3849, 187705, 33601),
    (35111, 64, 69505, 70471, 3857, 189788, 34351),
    (35951, 64, 70624, 71592, 3865, 191876, 35111),
    (36762, 64, 77083, 77083, 3874, 194158, 35951),
    (37561, 64, 77242, 78214, 3882, 196335, 36762),
    (38447, 64, 73997, 74972, 3890, 198457, 37561),
    (39295, 64, 80502, 80502, 3899, 200784, 38447),
    (40163, 64, 80666, 81645, 3907, 202987, 39295),
    (41078, 64, 78390, 78390, 3915, 205216, 40163),
    (41941, 64, 82472, 83455, 3923, 207541, 41078),
    (42767, 64, 85580, 86564, 3931, 209710, 41941),
    (43661, 64, 75886, 76873, 3938, 211765, 42767),
    (44587, 64, 83443, 84431, 3945, 213966, 43661),
    (45553, 64, 85088, 86079, 3953, 216224, 44587),
    (46528, 64, 86253, 86253, 3961, 218553, 45553),
    (47477, 64, 83436, 83436, 3969, 220880, 46528),
    (48394, 64, 83584, 83584, 3976, 223121, 47477),
    (49313, 64, 89717, 89717, 3984, 225266, 48394),
    (50297, 64, 95371, 95371, 3990, 227394, 49313),
    (51345, 64, 90380, 90380, 3998, 229652, 50297),
    (52338, 64, 97725, 97725, 4005, 232032, 51345),
    (53410, 64, 97909, 97909, 4012, 234265, 52338),
    (54486, 64, 97082, 97082, 4020, 236652, 53410),
    (55552, 64, 95740, 95740, 4027, 239024, 54486),
    (56604, 64, 103989, 103989, 4034, 241351, 55552),
    (57689, 64, 103659, 104671, 4041, 243625, 56604),
    (58733, 64, 99782, 100796, 4048, 245949, 57689),
    (59743, 64, 97512, 98527, 4055, 248165, 58733),
    (60859, 64, 93502, 94519, 4061, 250289, 59743),
    (62011, 64, 102822, 103841, 4068, 252616, 60859),
    (63258, 64, 106569, 106569, 4075, 254996, 62011),
    (64429, 64, 110322, 110322, 4082, 257547, 63258),
    (65639, 64, 112629, 112629, 4089, 259920, 64429),
    (66875, 64, 110186, 110186, 4096, 262349, 65639),
    (68084, 64, 119095, 119095, 4103, 264808, 66875),
    (69390, 64, 112955, 112955, 4110, 267191, 68084),
    (70630, 64, 113315, 113315, 4117, 269741, 69390),
    (71872, 64, 118648, 118648, 4123, 272141, 70630),
    (73173, 64, 123482, 123482, 4130, 274523, 71872),
    (74527, 64, 122653, 123689, 4136, 276997, 73173),
    (75883, 64, 126478, 127515, 4143, 279548, 74527),
    (77281, 64, 125128, 125128, 4150, 282079, 75883),
    (78653, 64, 128069, 129110, 4156, 284666, 77281),
    (80069, 64, 127954, 127954, 4163, 287182, 78653),
    (81463, 32, 67552, 68074, 4169, 289755, 80069),
    (82811, 64, 128517, 129562, 4176, 292267, 81463),
    (84263, 64, 125833, 126880, 4182, 294675, 82811),
    (85733, 32, 67073, 67597, 4188, 297247, 84263),
    (87256, 32, 67438, 67438, 4195, 299829, 85733),
    (88734, 64, 127188, 127188, 4201, 302480, 87256),
    (90129, 32, 71584, 71584, 4207, 305031, 88734),
    (91696, 32, 69578, 69578, 4213, 307420, 90129),
    (93222, 32, 74432, 74432, 4220, 310080, 91696),
    (94777, 32, 71102, 71631, 4226, 312650, 93222),
    (96269, 32, 71996, 72525, 4232, 315247, 94777),
    (97849, 32, 69181, 69711, 4238, 317718, 96269),
    (99439, 32, 73527, 74059, 4244, 320315, 97849),
    (101113, 32, 73631, 74163, 4249, 322907, 99439)] = some (101113, 152949030976, 152950689232) := by
    decide +kernel
  obtain ⟨h1, h2⟩ := FinitePsi.run_sound _ _ _ _ _ _ _ _ hrun (by simp only [FinitePsi.Good, Nat.cast_zero, zero_div, zero_mul, Nat.cast_one, Chebyshev.psi_one]; norm_num)
  refine ⟨fun x hx hxA => ?_, by simp only [FinitePsi.Good] at h2; push_cast at h2; exact h2⟩
  have := h1 x (by push_cast; norm_num at hx ⊢; linarith) (by push_cast at hxA ⊢; linarith)
  simpa [FinitePsi.fR] using this
