-- Prove2me | solution 1 for ValiantBorder.allFields
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:09:49.644809+00:00
-- url     : https://prove2.me/submissions/09a45d8d-bc58-475c-8f69-d5220d59d8b7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_closedLaurentLowerBound
import Theorems.Thm_ValiantBorder_laurentTransfer
import Theorems.Thm_ValiantBorder_hcInVNP

/-! The field-transfer argument and growth estimates are adapted from Claude (Anthropic),
*VP ≠ VNP over every field*, Appendix N, Theorem N.5. The source files are
`vp-vnp/Paper/{Approximate,Fields,Rate}.lean` at commit
11b6c7e3c927df2658f513b6b68ea7f8929c62c5 of `anthropics/formal-math` (Apache-2.0).
This version applies the three named platform theorems to the published class definitions. -/

open MvPolynomial Statement
universe u

private theorem hc_map (F : Type u) [Field F] (m : ℕ) :
    MvPolynomial.map (Int.castRingHom F) (hc ℤ m) = hc F m := by
  simp only [hc, map_sum, map_prod, map_X]

private theorem perm_map (F : Type u) [Field F] (m : ℕ) :
    MvPolynomial.map (Int.castRingHom F) (perm ℤ m) = perm F m := by
  simp only [perm, map_sum, map_prod, map_X]

private theorem exists_closed (p : ℕ) (hp : p = 0 ∨ p.Prime) : ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with rfl | hp
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

/-- 2 is not 0 in characteristic other than 2. -/
private theorem two_ne_zero_of_char (K : Type) [Field K] (p : ℕ) [CharP K p] (hp : p = 0 ∨ p.Prime) (h2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h3
  rcases hp with rfl | hp
  · simp at h3
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

private theorem thm_main_form {m : ℕ} (hm : 2 ≤ m) (c : ℝ) :
    (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) = (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hL : 0 < Real.logb 2 m := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < m))
  conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm0, ← Real.rpow_mul (by norm_num)]
  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hL, Real.rpow_one, mul_left_comm]
  congr 2
  rw [Real.rpow_logb (by norm_num) (by norm_num) hm0]

private theorem beyond_of_rate {m s : ℕ} (hm : 2 ≤ m) (h : (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) :
    (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  rwa [thm_main_form hm, one_div_mul_eq_div]

private theorem exists_beyond_poly {c : ℝ} (hc : 0 < c) (m₀ C : ℕ) :
    ∃ m ≥ m₀, ¬ (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < ((m ^ C + C : ℕ) : ℝ) := by
  have ht : Filter.Tendsto (fun m : ℕ => c * Real.logb 2 m ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp
      ((Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  obtain ⟨m, hm1, hm2⟩ := ((Filter.eventually_ge_atTop (m₀ + C + 2)).and
    (ht.eventually_ge_atTop ((C + 1 : ℕ) : ℝ))).exists
  refine ⟨m, by omega, fun hb => ?_⟩
  have h3 : (m : ℝ) ^ ((C + 1 : ℕ) : ℝ) < ((m ^ C + C : ℕ) : ℝ) :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m)) hm2) hb
  rw [Real.rpow_natCast] at h3
  have h4 : m ^ (C + 1) < m ^ C + C := by exact_mod_cast h3
  have h5 : 1 ≤ m ^ C := Nat.one_le_pow _ _ (by omega)
  have h6 : m ^ C * (C + 1) ≤ m ^ C * m := Nat.mul_le_mul_left _ (by omega)
  rw [pow_succ] at h4
  nlinarith

theorem solution : MainTheoremApprox.{u} ∧ SeparationClosure.{u} := by
  have main : ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (hc F m) s → Beyond (1 / 1600 ^ 2) m s) ∧
      (p ≠ 2 → Approximates (perm F m) s → Beyond (1 / 1600 ^ 2) m s) := by
    intro p
    by_cases hp : p = 0 ∨ p.Prime
    · obtain ⟨K, _, _, _⟩ := exists_closed p hp
      obtain ⟨M, bounds⟩ := ValiantBorder.closedLaurentLowerBound K
      refine ⟨M + 2, fun F _ _ m hm s => ⟨fun h => ?_, fun hne h => ?_⟩⟩
      · rw [← hc_map F m] at h
        obtain ⟨Q, hQ, hs⟩ := ValiantBorder.laurentTransfer (K := K) p (hc ℤ m) h
        rw [hc_map] at hs
        exact beyond_of_rate (by omega) ((bounds m (by omega) s Q hQ).1 hs)
      · rw [← perm_map F m] at h
        obtain ⟨Q, hQ, hs⟩ := ValiantBorder.laurentTransfer (K := K) p (perm ℤ m) h
        rw [perm_map] at hs
        exact beyond_of_rate (by omega) ((bounds m (by omega) s Q hQ).2 (two_ne_zero_of_char K p hp hne) hs)
    · exact ⟨0, fun F _ _ => absurd (CharP.char_is_prime_or_zero F p).symm hp⟩
  refine ⟨⟨1 / 1600 ^ 2, by norm_num, main⟩, fun F _ h => ?_⟩
  obtain ⟨a, ha⟩ := h (ValiantBorder.hcInVNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨M, hM⟩ := main p
  obtain ⟨m, hm, hgrowth⟩ := exists_beyond_poly (by norm_num : 0 < (1 / 1600 ^ 2 : ℝ)) M a
  exact hgrowth ((hM F m hm _).1 (ha m).2.2)
