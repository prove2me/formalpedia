-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_call_balance
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:53:32.205144+00:00
-- url     : https://prove2.me/submissions/31ec78a9-611f-4cd8-8aed-e502f4a1eb4f

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution (D n g s : ℝ)
    (hD : 1 ≤ D) (_hn : 1 ≤ n) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) :
    g / D ^ s ≤ 2 * D ^ (-s / 2) ∧
    g * D ^ (1 / 2 - s) / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g * D ≤ 2 * n * D ^ (-s / 2) ∧
    1 / g ≤ D ^ (-s / 2) := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hDnonneg : 0 ≤ D := le_of_lt hDpos
  have hDpowpos (x : ℝ) : 0 < D ^ x := Real.rpow_pos_of_pos hDpos x
  have hDpow_nonneg (x : ℝ) : 0 ≤ D ^ x := (hDpowpos x).le
  have hDmono {x y : ℝ} (hxy : x ≤ y) : D ^ x ≤ D ^ y :=
    Real.rpow_le_rpow_of_exponent_le hD hxy
  have hs0half : 0 ≤ s / 2 := by positivity
  have hsHalf' : s ≤ 1 / 2 := hsHalf
  have hsExp : s / 2 - 1 / 2 ≤ -s / 2 := by linarith
  have hhalf : Real.sqrt D = D ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have hratio1 : D ^ (1 / 2 - s) / Real.sqrt D = D ^ (-s) := by
    rw [hhalf, ← Real.rpow_sub hDpos]
    congr 1
    ring
  have hratio2 : D ^ (s / 2) / Real.sqrt D = D ^ (s / 2 - 1 / 2) := by
    rw [hhalf, ← Real.rpow_sub hDpos]
  have hprod : D ^ (s / 2) * D ^ (-s) = D ^ (-s / 2) := by
    rw [← Real.rpow_add hDpos]
    congr 1
    ring
  have hneg : -s / 2 = -(s / 2) := by ring
  have hpowInv : D ^ (-s / 2) = 1 / D ^ (s / 2) := by
    rw [hneg, Real.rpow_neg hDnonneg]
    simp [div_eq_mul_inv]
  have hprodBuild : D ^ (1 + s / 2) * D ^ (s / 2) ≤ n := by
    have hpow : D ^ (1 + s / 2) * D ^ (s / 2) = D ^ (1 + s) := by
      rw [← Real.rpow_add hDpos]
      congr 1
      ring
    rw [hpow]
    exact hbuild
  have hfourthPow : D ^ (1 + s / 2) ≤ n / D ^ (s / 2) :=
    (le_div_iff₀ (hDpowpos (s / 2))).2 hprodBuild
  have hlast : 1 / g ≤ D ^ (-s / 2) := by
    have hgpos : 0 < g := lt_of_lt_of_le (hDpowpos (s / 2)) hgLo
    rw [div_le_iff₀ hgpos]
    have hinv : D ^ (s / 2) * D ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add hDpos]
      have he : s / 2 + -s / 2 = 0 := by ring
      rw [he, Real.rpow_zero]
    calc
      1 = D ^ (s / 2) * D ^ (-s / 2) := hinv.symm
      _ ≤ g * D ^ (-s / 2) :=
        mul_le_mul_of_nonneg_right hgLo (hDpow_nonneg (-s / 2))
      _ = D ^ (-s / 2) * g := by ring
  refine ⟨?_, ?_, ?_, ?_, hlast⟩
  · apply (div_le_iff₀ (hDpowpos s)).2
    have hR : (2 * D ^ (-s / 2)) * D ^ s = 2 * D ^ (s / 2) := by
      calc
        (2 * D ^ (-s / 2)) * D ^ s = 2 * (D ^ (-s / 2) * D ^ s) := by ring
        _ = 2 * D ^ (-s / 2 + s) := by rw [← Real.rpow_add hDpos]
        _ = 2 * D ^ (s / 2) := by congr 1 <;> ring
    rw [hR]
    exact hgHi
  · rw [mul_div_assoc, hratio1]
    calc
      g * D ^ (-s) ≤ (2 * D ^ (s / 2)) * D ^ (-s) :=
        mul_le_mul_of_nonneg_right hgHi (hDpow_nonneg (-s))
      _ = 2 * D ^ (-s / 2) := by rw [← hprod]; ring
  · rw [hhalf]
    apply (div_le_iff₀ (hDpowpos (1 / 2 : ℝ))).2
    calc
      g ≤ 2 * D ^ (s / 2) := hgHi
      _ ≤ 2 * D ^ (1 / 2 - s / 2) := by
        exact mul_le_mul_of_nonneg_left (hDmono (by linarith)) (by norm_num)
      _ = 2 * D ^ (-s / 2) * D ^ (1 / 2 : ℝ) := by
        calc
          2 * D ^ (1 / 2 - s / 2) = 2 * D ^ (-s / 2 + (1 / 2 : ℝ)) := by
            congr 1 <;> ring
          _ = 2 * (D ^ (-s / 2) * D ^ (1 / 2 : ℝ)) := by
            rw [← Real.rpow_add hDpos]
          _ = 2 * D ^ (-s / 2) * D ^ (1 / 2 : ℝ) := by ring
  · calc
      g * D ≤ (2 * D ^ (s / 2)) * D :=
        mul_le_mul_of_nonneg_right hgHi (le_of_lt hDpos)
      _ = 2 * D ^ (1 + s / 2) := by
        calc
          (2 * D ^ (s / 2)) * D = 2 * (D ^ (s / 2) * D ^ (1 : ℝ)) := by
            rw [Real.rpow_one]
            ring_nf
          _ = 2 * D ^ (s / 2 + 1) := by rw [← Real.rpow_add hDpos]
          _ = 2 * D ^ (1 + s / 2) := by congr 1 <;> ring
      _ ≤ 2 * (n / D ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left hfourthPow (by norm_num)
      _ = 2 * n * D ^ (-s / 2) := by
        rw [hpowInv]
        ring

#print axioms solution
