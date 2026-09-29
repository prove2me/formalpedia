-- Prove2me | solution 1 for bp_frey_package_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-20T01:07:49.24009+00:00
-- url     : https://prove2.me/submissions/996de885-819f-4946-9e74-a2c3689524b2

import Definitions.Def_bp_FreyPackage
import Mathlib.Tactic.ModCases

/-!
Proof of `bp_frey_package_of_counterexample`: a counterexample to FLT for prime
p ≥ 5 yields a Frey package after normalization. Mirrors blueprint Lemma 2.5.2
(`FreyPackage.of_not_FermatLastTheorem_p_ge_5` in the Imperial College FLT repo).

Steps: (1) divide a, b, c through by gcd(a,b) to make them pairwise coprime;
(2) WLOG b is even, by permuting (swap a↔b) or substituting (b,c) ↦ (-c,-b);
(3) WLOG a ≡ 3 mod 4, by negating a, b, c if a ≡ 1 mod 4. Each step preserves
the Fermat equation because p is odd.
-/

/-- A common factor of two of a, b, c with a^p + b^p = c^p divides the third,
so gcd(a, b) = gcd(a, c). -/
private lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p)
    (h : a ^ p + b ^ p = c ^ p) : gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

theorem solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) :
    Nonempty FreyPackage := by
  have p_odd := pp.odd_of_ne_two (by omega)
  -- (1) Divide through by gcd a b to make a, b coprime.
  have ⟨a, b, c, a0, b0, c0, ab, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ a ^ p + b ^ p = c ^ p := by
    obtain ⟨d, a', b', d0, cop, a_eq, b_eq⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left b ha)
    simp only [a_eq, mul_pow, b_eq] at H
    rw [← add_mul, mul_comm] at H
    obtain ⟨c', rfl⟩ := (Int.pow_dvd_pow_iff pp.ne_zero).1 ⟨_, H.symm⟩
    rw [mul_pow] at H
    have a0' := left_ne_zero_of_mul (a_eq ▸ ha)
    have b0' := left_ne_zero_of_mul (b_eq ▸ hb)
    have c0' := right_ne_zero_of_mul hc
    exact ⟨a', b', c', a0', b0', c0', cop, mul_left_cancel₀ (pow_ne_zero _ (mod_cast d0.ne')) H⟩
  -- (2) WLOG b is even (one of a, b, c must be).
  have ⟨a, b, c, a0, b0, c0, ab, eb, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ Even b ∧ a ^ p + b ^ p = c ^ p := by
    if eb : Even b then
      exact ⟨a, b, c, a0, b0, c0, ab, eb, H⟩
    else if ea : Even a then
      exact ⟨b, a, c, b0, a0, c0, Int.gcd_comm a b ▸ ab, ea, by rwa [add_comm]⟩
    else
      refine ⟨a, -c, -b, a0, neg_ne_zero.2 c0, neg_ne_zero.2 b0, ?_, even_neg.2 ?_, ?_⟩
      · refine Int.gcd_neg.trans (.trans (.symm ?_) ab)
        exact Nat.cast_inj.1 (gcdab_eq_gcdac pp.pos H)
      · refine ((Int.even_pow (n := p)).1 (H.symm ▸ Int.even_add.2 (iff_of_false ?_ ?_))).1
        · exact fun h => ea (Int.even_pow.1 h).1
        · exact fun h => eb (Int.even_pow.1 h).1
      · simp [p_odd.neg_pow, ← H]
  -- (3) WLOG a ≡ 3 mod 4. Since b is even and gcd(a, b) = 1, a is odd, so a ≡ 1 or 3 mod 4.
  have ⟨a, b, c, ha0, hb0, hc0, ab, ha3, eb, hFLT⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧
        a ≡ 3 [ZMOD 4] ∧ Even b ∧ a ^ p + b ^ p = c ^ p := by
    have a_odd' : ∀ {i}, a ≡ i [ZMOD 4] → ¬2 ∣ i := fun ai ei => by
      have ea := (dvd_sub_right ei).1 (.trans (by decide) (Int.modEq_iff_dvd.1 ai))
      simpa (config := {decide := true}) [gcd, ab] using dvd_gcd ea (even_iff_two_dvd.1 eb)
    mod_cases a_mod : a % 4
    · cases a_odd' a_mod (by decide)
    · exact ⟨-a, -b, -c, neg_ne_zero.2 a0, neg_ne_zero.2 b0, neg_ne_zero.2 c0,
        by rwa [Int.neg_gcd, Int.gcd_neg], a_mod.neg, eb.neg,
        by simp [p_odd.neg_pow, ← H, add_comm]⟩
    · cases a_odd' a_mod (by decide)
    · exact ⟨a, b, c, a0, b0, c0, ab, a_mod, eb, H⟩
  -- (4) Build the package.
  exact ⟨{
    a, b, c, ha0, hb0, hc0, p, pp, hp5, hFLT
    hgcdab := by simp [gcd, ab]
    ha4 := (ZMod.intCast_eq_intCast_iff ..).2 ha3
    hb2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 (even_iff_two_dvd.1 eb)
  }⟩
