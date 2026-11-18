-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.auxiliary_lower_advice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:46:16.11051+00:00
-- url     : https://prove2.me/submissions/d6f9210e-7bfd-45d2-b7b2-af84f37df2a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StudentTeacher976_Adaptivity_good_pair_advice_cover
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_advice_implementation
import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion
set_option autoImplicit false
open StudentTeacher976.Adaptivity

namespace StudentTeacher976.Adaptivity

private theorem crossing_fixed_point (g : ℕ → ℕ) (hg : Monotone g)
    (n B : ℕ) (hpos : 1 ≤ g n) (hB : 0 < B ∧ g (n * B) ≤ B) :
    ∃ k, 0 < k ∧ k ≤ B ∧ k = g (n * k) := by
  have hex : ∃ k, 0 < k ∧ g (n * k) ≤ k := ⟨B, hB⟩
  let k := Nat.find hex
  have hk : 0 < k ∧ g (n * k) ≤ k := Nat.find_spec hex
  have hkle : k ≤ B := Nat.find_min' hex hB
  refine ⟨k, hk.1, hkle, ?_⟩
  apply Nat.le_antisymm
  · by_cases h1 : k = 1
    · simpa [h1] using hpos
    · have hprev : ¬ (0 < k - 1 ∧ g (n * (k - 1)) ≤ k - 1) :=
        Nat.find_min hex (show k - 1 < k by omega)
      have hm := hg (Nat.mul_le_mul_left n (Nat.sub_le k 1))
      omega
  · exact hk.2

 theorem fixed_point_poly_bound (g : ℕ → ℕ) (hg : Monotone g)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ m : ℕ, 0 < m → 1 ≤ g m ∧ (g m : ℝ) ≤ (m : ℝ) ^ (1 - ε)) :
    ∃ d : ℕ, ∀ n : ℕ, 0 < n → ∃ k : ℕ,
      0 < k ∧ k ≤ (n + 1) ^ d ∧ k = g (n * k) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (1 / ε)
  have hdε : 1 ≤ (d : ℝ) * ε := by
    have := (div_lt_iff₀ hε).mp hd
    linarith
  refine ⟨d, ?_⟩
  intro n hn
  let B := (n + 1) ^ d
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBre : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hpow : (n : ℝ) ^ (1 - ε) < (B : ℝ) ^ ε := by
    calc
      (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ = (n : ℝ) := Real.rpow_one _
      _ < (n : ℝ) + 1 := by linarith
      _ = ((n : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ ((d : ℝ) * ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hdε
      _ = (B : ℝ) ^ ε := by
        simp only [B, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  have hstrict : ((n * B : ℕ) : ℝ) ^ (1 - ε) < (B : ℝ) := by
    calc
      ((n * B : ℕ) : ℝ) ^ (1 - ε) =
          (n : ℝ) ^ (1 - ε) * (B : ℝ) ^ (1 - ε) := by
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      _ < (B : ℝ) ^ ε * (B : ℝ) ^ (1 - ε) :=
        mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hBre _)
      _ = (B : ℝ) := by
        rw [← Real.rpow_add hBre]
        simp
  have hnat : g (n * B) < B := by
    exact_mod_cast lt_of_le_of_lt (hbound (n * B) (by positivity)).2 hstrict
  exact crossing_fixed_point g hg n B (hbound n hn).1 ⟨hBpos, Nat.le_of_lt hnat⟩

end StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hgame : auxiliaryRelation W r ∈ ST i r q) :
    L ∈ DeltaPoly i := by
  obtain ⟨ε, hε, hb⟩ := hr.2.2.2
  have hpoints := fixed_point_poly_bound r hr.2.1 ε hε hb
  apply auxiliary_advice_implementation i L W r q hr hq hgame hpoints
  exact good_pair_advice_cover i L W r q hr hq
