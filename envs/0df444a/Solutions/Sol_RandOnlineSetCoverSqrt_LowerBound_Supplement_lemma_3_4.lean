-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:58:16.864181+00:00
-- url     : https://prove2.me/submissions/e921bb6a-1957-4c72-be08-ad14d31ed7d8

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_3

section
set_option autoImplicit false

namespace RandOnlineSetCoverSqrt.Dev.L34
open RandOnlineSetCoverSqrt.LowerBound

/-- The family of all `k`-subsets of `Fin m` is union-expanding with `q = choose r k + 1`:
`choose r k + 1` distinct `k`-sets cannot fit inside a set of size at most `r`. -/
theorem allSubsets_unionExpanding (m k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) (hrm : r ≤ m) :
    UnionExpanding k (Nat.choose r k + 1) r
      ((Finset.univ : Finset (Fin m)).powersetCard k) := by
  refine ⟨hk, hkr, hrm, ?_, ?_, ?_⟩
  · have := Nat.choose_pos hkr; omega
  · intro W hW; exact (Finset.mem_powersetCard.mp hW).2
  · intro Q hQ hcard
    by_contra h
    rw [not_lt] at h
    have hsub : Q ⊆ (Q.biUnion id).powersetCard k := by
      intro W hW
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_biUnion_of_mem id hW, (Finset.mem_powersetCard.mp (hQ hW)).2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_powersetCard] at h1
    have h2 := Nat.choose_le_choose k h
    omega

theorem card_allSubsets (m k : ℕ) :
    ((Finset.univ : Finset (Fin m)).powersetCard k).card = Nat.choose m k := by
  simp

/-- `m^m / m! ≤ e^m`. -/
theorem pow_div_factorial_le (m : ℕ) :
    ((m : ℝ) ^ m / (m.factorial : ℝ)) ≤ Real.exp 1 ^ m := by
  rw [← Real.exp_nat_mul, mul_one]
  exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg m) m

/-- The hypothesis of Lemma 3.3 in the case `q = m`, `M ≤ m R / (4e)`. -/
theorem hyp_bound (m r M : ℕ) (A T : ℝ) (hm : 1 ≤ m) (hT : 0 < T) (hA : 0 < A)
    (hM : (M : ℝ) ≤ m * (A / T) / (4 * Real.exp 1)) :
    (Nat.choose M m : ℝ) * (Nat.choose m r : ℝ) * (T / A) ^ m < 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set x : ℝ := m * (A / T) / (4 * Real.exp 1) with hx
  have hx0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (Nat.choose M m : ℝ) ≤ x ^ m / (m.factorial : ℝ) := by
    calc (Nat.choose M m : ℝ) ≤ (M : ℝ) ^ m / (m.factorial : ℝ) := Nat.choose_le_pow_div m M
      _ ≤ x ^ m / (m.factorial : ℝ) := by
        gcongr
  have h2 : (Nat.choose m r : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m r
  have hTA : 0 ≤ (T / A) ^ m := by positivity
  have hxTA : x * (T / A) * 2 = (m : ℝ) * (1 / (2 * Real.exp 1)) := by
    rw [hx]; field_simp; ring
  have key : x ^ m / (m.factorial : ℝ) * 2 ^ m * (T / A) ^ m
      = ((m : ℝ) ^ m / (m.factorial : ℝ)) * (1 / (2 * Real.exp 1)) ^ m := by
    have : x ^ m * 2 ^ m * (T / A) ^ m = (m : ℝ) ^ m * (1 / (2 * Real.exp 1)) ^ m := by
      rw [← mul_pow, ← mul_pow, ← mul_pow, ← hxTA]; ring
    calc x ^ m / (m.factorial : ℝ) * 2 ^ m * (T / A) ^ m
        = (x ^ m * 2 ^ m * (T / A) ^ m) / (m.factorial : ℝ) := by ring
      _ = _ := by rw [this]; ring
  have h3 : ((m : ℝ) ^ m / (m.factorial : ℝ)) * (1 / (2 * Real.exp 1)) ^ m ≤ (1 / 2) ^ m := by
    calc ((m : ℝ) ^ m / (m.factorial : ℝ)) * (1 / (2 * Real.exp 1)) ^ m
        ≤ Real.exp 1 ^ m * (1 / (2 * Real.exp 1)) ^ m := by
          gcongr; exact pow_div_factorial_le m
      _ = (1 / 2) ^ m := by
          rw [← mul_pow]; congr 1; field_simp
  have h4 : ((1 : ℝ) / 2) ^ m < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  calc (Nat.choose M m : ℝ) * (Nat.choose m r : ℝ) * (T / A) ^ m
      ≤ x ^ m / (m.factorial : ℝ) * 2 ^ m * (T / A) ^ m := by
        gcongr
    _ = _ := key
    _ ≤ (1 / 2) ^ m := h3
    _ < 1 := h4

end RandOnlineSetCoverSqrt.Dev.L34

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.Dev.L34 in
theorem chk_lemma_3_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ m k r : ℕ, 1 ≤ k → k ≤ r → r ≤ m →
      32 * Real.exp 1 ≤ (Nat.choose m k : ℝ) / (Nat.choose r k : ℝ) →
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : Family m,
        C.card = N + min m (Nat.choose r k + 1) ∧
        UnionExpanding k (min m (Nat.choose r k + 1)) r C ∧
        c * ((1 / (m : ℝ)) * ((Nat.choose m k : ℝ) / (Nat.choose r k : ℝ))) ≤
          (N : ℝ) / ((min m (Nat.choose r k + 1) : ℕ) : ℝ) ^ 2 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1; linarith
  refine ⟨1 / (8 * Real.exp 1), by positivity, ?_⟩
  intro m k r hk hkr hrm hR
  set A : ℕ := Nat.choose m k with hAdef
  set T : ℕ := Nat.choose r k with hTdef
  have hTpos : 1 ≤ T := Nat.choose_pos hkr
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hA32 : 32 * (T : ℝ) ≤ A := by
    have h := (le_div_iff₀ hTr).mp hR
    nlinarith
  have hrm' : r < m := by
    rcases Nat.lt_or_ge r m with h | h
    · exact h
    · exfalso
      have : r = m := le_antisymm hrm h
      subst this
      have : (A : ℝ) = T := rfl
      linarith
  have hm2 : 2 ≤ m := by omega
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  rcases Nat.lt_or_ge T m with hTm | hTm
  · -- Case `T < m`: all `k`-subsets.
    have hq : min m (T + 1) = T + 1 := by omega
    rw [hq]
    have hAT : T + 2 ≤ A := by
      have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
      have : (T : ℝ) + 2 ≤ A := by linarith
      exact_mod_cast this
    refine ⟨A - (T + 1), by omega, (Finset.univ : Finset (Fin m)).powersetCard k, ?_,
      allSubsets_unionExpanding m k r hk hkr hrm, ?_⟩
    · rw [card_allSubsets]; omega
    · have hTm' : (T : ℝ) ≤ m := by exact_mod_cast hTm.le
      have hcast : ((A - (T + 1) : ℕ) : ℝ) = (A : ℝ) - T - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      push_cast
      have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
      have hApos : (0 : ℝ) < A := by linarith
      have lhs : 1 / (8 * Real.exp 1) * (1 / (m : ℝ) * ((A : ℝ) / T)) =
          (A : ℝ) / (8 * Real.exp 1 * m * T) := by
        field_simp
      rw [lhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ((T : ℝ) + 1) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
      have h2 : (A : ℝ) / 2 ≤ A - T - 1 := by linarith
      have h3 : (T : ℝ) ≤ Real.exp 1 * m := by nlinarith
      calc (A : ℝ) * (T + 1) ^ 2 ≤ A * (4 * T ^ 2) := by gcongr
        _ = ((A : ℝ) / 2) * (8 * (T : ℝ) * T) := by ring
        _ ≤ ((A : ℝ) - T - 1) * (8 * (Real.exp 1 * m) * T) := by gcongr; linarith
        _ = (A - T - 1) * (8 * Real.exp 1 * m * T) := by ring
  · -- Case `T ≥ m`: Lemma 3.3 with `q = m`.
    have hq : min m (T + 1) = m := by omega
    rw [hq]
    have hTm' : (m : ℝ) ≤ T := by exact_mod_cast hTm
    have hm0 : (0 : ℝ) < m := by linarith
    have hApos : (0 : ℝ) < A := by linarith
    set x : ℝ := m * ((A : ℝ) / T) / (4 * Real.exp 1) with hx
    have hx8 : 8 * (m : ℝ) ≤ x := by
      rw [hx, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hR hm0.le]
    have hx0 : 0 ≤ x := by linarith
    set M : ℕ := ⌊x⌋₊ with hMdef
    have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0
    have hMx1 : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
    have hxA : x ≤ A := by
      have h1 : (m : ℝ) * ((A : ℝ) / T) ≤ (T : ℝ) * ((A : ℝ) / T) := by gcongr
      have h2 : (T : ℝ) * ((A : ℝ) / T) = A := by field_simp
      rw [hx, div_le_iff₀ (by positivity)]
      nlinarith
    have hMA : M ≤ A := by
      have : (M : ℝ) ≤ A := le_trans hMx hxA
      exact_mod_cast this
    have h8M : 8 * m < M + 1 := by
      have : ((8 * m : ℕ) : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨C, hC, hCU⟩ := lemma_3_3 m k m r M hk hkr hrm hm2 hMA
      (hyp_bound m r M (A : ℝ) (T : ℝ) (by omega) hTr hApos hMx)
    refine ⟨M - m, by omega, C, by rw [hC]; omega, hCU, ?_⟩
    have hcast : ((M - m : ℕ) : ℝ) = (M : ℝ) - m := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast]
    have lhs : 1 / (8 * Real.exp 1) * (1 / (m : ℝ) * ((A : ℝ) / T)) = (x / 2) / (m : ℝ) ^ 2 := by
      rw [hx]; field_simp; ring
    rw [lhs]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

end RandOnlineSetCoverSqrt.LowerBound.Supplement
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_lemma_3_4 := @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_lemma_3_4
