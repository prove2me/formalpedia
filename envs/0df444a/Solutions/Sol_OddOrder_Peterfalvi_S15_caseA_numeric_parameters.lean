-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseA_numeric_parameters
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:42.789208+00:00
-- url     : https://prove2.me/submissions/feec474f-5693-48fc-985d-ffabeffc3f27

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- Exponential estimate for the case-A branch of **Peterfalvi (13.13)**:
`16n ≤ 5·2^(n-1)` for `n ≥ 5`.  Equivalently, `n/2^(n-1) ≤ 5/16`; this is the
decaying upper bound that contradicts (13.11.b). -/
private theorem sixteen_mul_le_five_mul_two_pow_pred {n : ℕ} (hn : 5 ≤ n) :
    16 * n ≤ 5 * 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        16 * (n + 1) ≤ 2 * (16 * n) := by omega
        _ ≤ 2 * (5 * 2 ^ (n - 1)) := Nat.mul_le_mul_left 2 ih
        _ = 5 * 2 ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
          ring

/-- **Peterfalvi (13.13), pure numeric core.**  If `q` is an odd prime, (13.10) holds with
`c = 1`, and the case-A block action gives
`u ∣ ((p - 1) / 2)^(q - 1)`, then the (13.11) lower estimates force
`q = 3` and `u = (p - 1)^2 / 4`.

For `q ≥ 5`, the divisibility bound and `2·((p-1)/2) = p-1 < p` give
`m < q/2^(q-1) ≤ 5/16`, contradicting `m > 7/10`.  At `q = 3`, a proper divisor `u`
of `((p-1)/2)^2` is at most half that square, contradicting (13.11.c). -/
theorem _root_.solution {p q u : ℕ} {m : ℚ}
    (hp3 : 3 ≤ p) (hqprime : q.Prime) (hqne2 : q ≠ 2)
    (hpeven : 2 ∣ p - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m)
    (h13c : q = 3 → (((p ^ 2 - 1 : ℕ) : ℚ) / 6) < (u : ℚ))
    (hanalytic : (u : ℚ) >
      m * ((p ^ (q - 1) : ℕ) : ℚ) / (q : ℚ))
    (hdiv : u ∣ ((p - 1) / 2) ^ (q - 1)) :
    q = 3 ∧ u = (p - 1) ^ 2 / 4 := by
  let a := (p - 1) / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    omega
  have hsplit : p - 1 = 2 * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' hpeven).symm
  have hdiv' : u ∣ a ^ (q - 1) := by simpa [a] using hdiv
  have hu_le : u ≤ a ^ (q - 1) :=
    Nat.le_of_dvd (pow_pos ha_pos _) hdiv'
  have hq3le : 3 ≤ q := by
    have := hqprime.two_le
    omega
  have hq3or5 : q = 3 ∨ 5 ≤ q := by
    by_cases hq3 : q = 3
    · exact Or.inl hq3
    · right
      by_contra hq5
      have hq4 : q = 4 := by omega
      subst q
      norm_num at hqprime
  have hq3 : q = 3 := by
    rcases hq3or5 with hq3 | hq5
    · exact hq3
    · exfalso
      have hqRpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqprime.pos
      have hpRpos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
      have hpPowRpos : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
      have huR : (u : ℚ) ≤ (a : ℚ) ^ (q - 1) := by exact_mod_cast hu_le
      have hpowcast : (((p ^ (q - 1) : ℕ) : ℚ)) = (p : ℚ) ^ (q - 1) := by
        push_cast
        ring
      rw [hpowcast] at hanalytic
      have hanalytic' : m * (p : ℚ) ^ (q - 1) / (q : ℚ) < (u : ℚ) := hanalytic
      rw [div_lt_iff₀ hqRpos] at hanalytic'
      have hmp : m * (p : ℚ) ^ (q - 1) < (a : ℚ) ^ (q - 1) * (q : ℚ) :=
        hanalytic'.trans_le (mul_le_mul_of_nonneg_right huR (le_of_lt hqRpos))
      have hp1cast : (((p - 1 : ℕ) : ℚ)) = (p : ℚ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
        rfl
      have hsplitR : (p : ℚ) - 1 = 2 * (a : ℚ) := by
        have h := congrArg (fun n : ℕ => (n : ℚ)) hsplit
        push_cast at h
        rw [hp1cast] at h
        exact h
      have hpred : (p - 1) ^ (q - 1) < p ^ (q - 1) :=
        Nat.pow_lt_pow_left (by omega) (by omega)
      have hpredR : ((p : ℚ) - 1) ^ (q - 1) < (p : ℚ) ^ (q - 1) := by
        have h : (((p - 1) ^ (q - 1) : ℕ) : ℚ) < ((p ^ (q - 1) : ℕ) : ℚ) := by
          exact_mod_cast hpred
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at h
        exact h
      have htwoa : (2 : ℚ) ^ (q - 1) * (a : ℚ) ^ (q - 1) =
          ((p : ℚ) - 1) ^ (q - 1) := by
        rw [← mul_pow, ← hsplitR]
      have hmul := mul_lt_mul_of_pos_right hmp
        (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)
      have hcancel :
          (m * (2 : ℚ) ^ (q - 1)) * (p : ℚ) ^ (q - 1) <
            (q : ℚ) * (p : ℚ) ^ (q - 1) := by
        calc
          (m * (2 : ℚ) ^ (q - 1)) * (p : ℚ) ^ (q - 1)
              = (m * (p : ℚ) ^ (q - 1)) * (2 : ℚ) ^ (q - 1) := by ring
          _ < ((a : ℚ) ^ (q - 1) * (q : ℚ)) * (2 : ℚ) ^ (q - 1) := hmul
          _ = (q : ℚ) * ((p : ℚ) - 1) ^ (q - 1) := by rw [← htwoa]; ring
          _ < (q : ℚ) * (p : ℚ) ^ (q - 1) :=
            mul_lt_mul_of_pos_left hpredR hqRpos
      have hm2pow : m * (2 : ℚ) ^ (q - 1) < (q : ℚ) :=
        lt_of_mul_lt_mul_right hcancel (le_of_lt hpPowRpos)
      have hmupper : m < (q : ℚ) / (2 : ℚ) ^ (q - 1) :=
        (lt_div_iff₀ (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)).mpr hm2pow
      have hnat := sixteen_mul_le_five_mul_two_pow_pred hq5
      have hnatR : (16 : ℚ) * (q : ℚ) ≤ 5 * (2 : ℚ) ^ (q - 1) := by
        exact_mod_cast hnat
      have hratio : (q : ℚ) / (2 : ℚ) ^ (q - 1) ≤ (5 : ℚ) / 16 := by
        rw [div_le_div_iff₀ (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)
          (by norm_num : (0 : ℚ) < 16)]
        nlinarith [hnatR]
      linarith [hm5 hq5, hmupper, hratio]
  have hdiv2 : u ∣ a ^ 2 := by simpa [hq3] using hdiv'
  have htarget : (p - 1) ^ 2 / 4 = a ^ 2 := by
    rw [hsplit, mul_pow]
    norm_num
  have hueq : u = a ^ 2 := by
    by_contra hne
    have hule : u ≤ a ^ 2 := Nat.le_of_dvd (pow_pos ha_pos 2) hdiv2
    have hult : u < a ^ 2 := lt_of_le_of_ne hule hne
    obtain ⟨k, hk⟩ := hdiv2
    have hk0 : k ≠ 0 := by
      intro hk0
      subst k
      simp at hk
      omega
    have hk1 : k ≠ 1 := by
      intro hk1
      subst k
      simp at hk
      omega
    have hk2 : 2 ≤ k := by omega
    have hu2 : 2 * u ≤ a ^ 2 := by
      calc
        2 * u = u * 2 := Nat.mul_comm _ _
        _ ≤ u * k := Nat.mul_le_mul_left u hk2
        _ = a ^ 2 := hk.symm
    have hlower := h13c hq3
    have hp2one : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hp2cast : (((p ^ 2 - 1 : ℕ) : ℚ)) = (p : ℚ) ^ 2 - 1 := by
      push_cast [Nat.cast_sub hp2one]
      ring
    rw [hp2cast] at hlower
    have hu2R : (2 : ℚ) * (u : ℚ) ≤ (a : ℚ) ^ 2 := by exact_mod_cast hu2
    have hp1cast : (((p - 1 : ℕ) : ℚ)) = (p : ℚ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      rfl
    have hsplitR : (p : ℚ) - 1 = 2 * (a : ℚ) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) hsplit
      push_cast at h
      rw [hp1cast] at h
      exact h
    have haR : (a : ℚ) = ((p : ℚ) - 1) / 2 := by linarith [hsplitR]
    rw [haR] at hu2R
    have hp3R : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
    nlinarith [hlower, hu2R, hp3R]
  exact ⟨hq3, hueq.trans htarget.symm⟩

end OddOrder.Peterfalvi.S15
