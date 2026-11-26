-- Prove2me | solution 1 for QuasilinearAG.Encoding.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T07:49:46.005704+00:00
-- url     : https://prove2.me/submissions/94383395-ed3e-4120-85d7-e56eecfbc811

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

open QuasilinearAG QuasilinearAG.Encoding

/-!
Lemma 4.3 (The public root arena is linear), p. 16 (PDF 18). For all `q ≥ 3` and `h ≥ 1`,
with `κ = ⌈log_q h⌉ + 1`, `Q* = q^κ` and `D = q^h` as in (3.2), one has `κ Q* ≤ 2D`.

Outline (PLAN.md): once `κ ≤ h` (`kappa_le_h`), the goal becomes `κ ≤ 2 * q^(h - κ)`,
since `κ * q^κ ≤ (2 * q^(h - κ)) * q^κ = 2 * q^(h - κ + κ) = 2 * q^h`.
Two small steps:
* `q_pow_ge_h` — for `2 ≤ q`, `1 ≤ h`: `h ≤ q^(h-1)`; with Mathlib's
  `Nat.clog_le_of_le_pow` this gives `clog q h ≤ h - 1`, hence `κ ≤ h`.
* `kappa_core` — the core estimate, proved by contradiction: if `d = h - κ ≥ 1` and
  `κ > 2 * q^d`, then `κ ≥ 4`, so `κ - 2 ≥ q^d ≥ d` and
  `q^(κ - 2) ≥ 3^(κ - 2) ≥ 2κ ≥ κ + d = h`, contradicting `q^(κ - 2) < h`
  (`Nat.pow_pred_clog_lt_self`, the strict lower bound of `clog`).
  If `h = κ`, then `clog q h = h - 1`; for `h ≥ 3` this contradicts
  `h ≤ 3^(h-2)`, so `h ≤ 2` and `κ ≤ 2 = 2 * q^0`.
-/

namespace P2MHole01_ad4b0cdb
theorem solution (q h : ℕ) (hq : (2 : ℕ) ≤ q) (hh : (1 : ℕ) ≤ h) : h ≤ q ^ (h - (1 : ℕ)) := by
  induction' h with h ih
  · simp
  · by_cases h0 : h = 0
    · subst h0
      simp
    · have h1 : 1 ≤ h := by omega
      have hq0 : 0 < q := by omega
      have hpow : 0 < q ^ (h - 1) := Nat.pow_pos hq0
      simp only [Nat.succ_sub_one]
      have hstep : h + 1 ≤ q ^ (h - 1) + q ^ (h - 1) := by
        calc
          h + 1 ≤ q ^ (h - 1) + 1 := Nat.add_le_add_right (ih h1) 1
          _ ≤ q ^ (h - 1) + q ^ (h - 1) := by omega
      have hsucc : (h - 1).succ = h := by omega
      calc
        h + 1 ≤ q ^ (h - 1) + q ^ (h - 1) := hstep
        _ = 2 * q ^ (h - 1) := by ring
        _ ≤ q * q ^ (h - 1) := mul_le_mul hq (le_rfl) (Nat.zero_le _) (Nat.zero_le _)
        _ = q ^ (h - 1).succ := by rw [Nat.mul_comm, ← Nat.pow_succ q (h - 1)]
        _ = q ^ h := by rw [hsucc]
end P2MHole01_ad4b0cdb

/-- For `2 ≤ q` and `1 ≤ h`, the base dominates its exponent: `h ≤ q^(h-1)`. -/
theorem q_pow_ge_h (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) : h ≤ q ^ (h - 1) := by
  (first | exact P2MHole01_ad4b0cdb.solution q h hq hh | (apply P2MHole01_ad4b0cdb.solution <;> assumption))

/-- With `q ≥ 3` and `h ≥ 1`, `κ = ⌈log_q h⌉ + 1` satisfies `κ ≤ h`. -/
theorem kappa_le_h (q h : ℕ) (hq : 3 ≤ q) (hh : 1 ≤ h) : kappaOf q h ≤ h := by
  have hc : Nat.clog q h ≤ h - 1 := Nat.clog_le_of_le_pow (q_pow_ge_h q h (by omega) hh)
  exact (Nat.add_le_add hc (by norm_num : 1 ≤ 1)).trans (by omega)

namespace P2MHole02_dbda9e5d
-- 3^n ≥ 2n + 1 for all n : ℕ
lemma three_pow_ge_2m1 (n : ℕ) : 3 ^ n ≥ 2 * n + 1 := by
  induction' n with n ih
  · norm_num
  · calc
      3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≥ 3 * (2 * n + 1) := by gcongr
      _ ≥ 2 * (n + 1) + 1 := by ring_nf; omega

theorem solution (q h κ : ℕ) (hq : (3 : ℕ) ≤ q) (hh : (1 : ℕ) ≤ h) (hκ : κ = Nat.clog q h + (1 : ℕ))
  (hle : κ ≤ h) : κ ≤ (2 : ℕ) * q ^ (h - κ) := by
  have h1q : 1 < q := by omega
  let k : ℕ := Nat.clog q h
  have hk : κ = k + 1 := by
    simpa [k] using hκ
  rw [hk]
  have hk1 : k + 1 ≤ h := by
    simpa [hk] using hle
  by_cases hk0 : k = 0
  · -- κ = 1, h ≥ 1: q^(h-1) ≥ 1
    rw [hk0]
    have : 1 ≤ q ^ (h - 1) := Nat.one_le_pow (h - 1) q (by omega)
    nlinarith
  · -- k ≥ 1: clog minimality gives h > q^(k-1)
    have kpos : 0 < k := by omega
    have hlt : q ^ (k - 1) < h := by
      by_contra hno
      push Not at hno
      have : k ≤ k - 1 := by
        simpa [show Nat.clog q h = k from rfl] using (Nat.clog_le_iff_le_pow h1q).mpr hno
      omega
    have hbig : q ^ (k - 1) + 1 ≤ h := by omega
    have h3 : 2 * (k - 1) + 1 ≤ 3 ^ (k - 1) := three_pow_ge_2m1 (k - 1)
    have hA : k ≤ q ^ (k - 1) := by
      calc
        k ≤ 2 * (k - 1) + 1 := by ring_nf; omega
        _ ≤ 3 ^ (k - 1) := h3
        _ ≤ q ^ (k - 1) := Nat.pow_le_pow_left hq (k - 1)
    -- m := h - (k+1) ≥ q^(k-1) - k
    set m := h - (k + 1) with hm
    have mge : q ^ (k - 1) - k ≤ m := by
      rw [hm, Nat.le_sub_iff_add_le hk1]
      calc
        q ^ (k - 1) - k + (k + 1) = q ^ (k - 1) + 1 := by
          have : q ^ (k - 1) - k + k = q ^ (k - 1) := by omega
          ring_nf at *
          omega
        _ ≤ h := hbig
    -- k-1 ≤ q^(k-1) - k, since 2k-1 ≤ q^(k-1)
    have hexp : k - 1 ≤ q ^ (k - 1) - k := by
      rw [Nat.le_sub_iff_add_le hA]
      have hkk : k = (k - 1) + 1 := by omega
      calc
        k - 1 + k = k - 1 + ((k - 1) + 1) := congrArg (fun x : ℕ => k - 1 + x) hkk
        _ = (k - 1 + (k - 1)) + 1 := by rw [← Nat.add_assoc]
        _ ≤ 3 ^ (k - 1) := by rw [← Nat.two_mul]; exact h3
        _ ≤ q ^ (k - 1) := Nat.pow_le_pow_left hq (k - 1)
    have qmon : q ^ (q ^ (k - 1) - k) ≤ q ^ m :=
      Nat.pow_le_pow_of_le h1q mge
    -- k + 1 ≤ 2 * q^(q^(k-1)-k)
    have core : k + 1 ≤ 2 * q ^ (q ^ (k - 1) - k) := by
      calc
        k + 1 ≤ 2 * (2 * (k - 1) + 1) := by ring_nf; omega
        _ ≤ 2 * (3 ^ (k - 1)) := by gcongr
        _ ≤ 2 * (q ^ (q ^ (k - 1) - k)) := by
          gcongr
          · omega
    calc
      k + 1 ≤ 2 * q ^ (q ^ (k - 1) - k) := core
      _ ≤ 2 * q ^ m := by gcongr
      _ = 2 * q ^ (h - (k + 1)) := by rw [hm]
end P2MHole02_dbda9e5d

-- riskiest
/-- Core estimate: for `3 ≤ q`, `h ≥ 1` and `κ = ⌈log_q h⌉ + 1`, if `κ ≤ h` then
    `κ ≤ 2 * q^(h - κ)`. -/
theorem kappa_core (q h κ : ℕ) (hq : 3 ≤ q) (hh : 1 ≤ h) (hκ : κ = Nat.clog q h + 1) (hle : κ ≤ h) :
    κ ≤ 2 * q ^ (h - κ) := by
  (first | exact P2MHole02_dbda9e5d.solution q h κ hq hh hκ hle | (apply P2MHole02_dbda9e5d.solution <;> assumption))

/-- Lemma 4.3 (The public root arena is linear), p. 16 (PDF 18). For all `q ≥ 3` and `h ≥ 1`, with
`κ = ⌈log_q h⌉ + 1`, `Q* = q^κ` and `D = q^h` as in (3.2), one has `κ Q* ≤ 2D`. -/
theorem solution (q h : ℕ) (hq : 3 ≤ q) (hh : 1 ≤ h) :
    kappaOf q h * q ^ kappaOf q h ≤ 2 * q ^ h := by
  have hle : kappaOf q h ≤ h := kappa_le_h q h hq hh
  have hk : kappaOf q h ≤ 2 * q ^ (h - kappaOf q h) :=
    kappa_core q h (kappaOf q h) hq hh rfl hle
  calc
    kappaOf q h * q ^ kappaOf q h
        ≤ 2 * q ^ (h - kappaOf q h) * q ^ kappaOf q h := mul_le_mul_of_nonneg_right hk (Nat.zero_le _)
    _ = 2 * q ^ (h - kappaOf q h + kappaOf q h) := by rw [mul_assoc, Nat.pow_add]
    _ = 2 * q ^ h := by rw [Nat.sub_add_cancel hle]
