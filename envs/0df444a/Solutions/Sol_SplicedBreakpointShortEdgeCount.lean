-- Prove2me | solution 1 for SplicedBreakpointShortEdgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:14.236975+00:00
-- url     : https://prove2.me/submissions/db42b838-a0bb-471c-8c31-7af401961f2f

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set
theorem _root_.solution (k n K c m : ℕ) (δ σ τ a' b' : ℝ) (s sA : ℕ → ℝ)
    (hmonoS : MonotoneOn s (Set.Icc 0 k))
    (hs0 : s 0 = 0) (hm1 : 1 ≤ m) (hmK : m + 2 ≤ K)
    (htail : ∀ i : ℕ, 1 ≤ i → i ≤ m → c + (i - 1) ≤ k ∧ sA i = s (c + (i - 1)) + σ)
    (hhead : ∀ i : ℕ, m < i → i ≤ K - 1 → i - m ≤ k ∧ sA i = s (i - m) + τ)
    (hsplice : s (c + (m - 1)) + σ = τ)
    (hmargin : b' - τ < a' - σ)
    (hcount : ((Finset.Icc 1 k).filter
      (fun j => (a' - σ ≤ s (j - 1) ∨ s j ≤ b' - τ) ∧ s j - s (j - 1) < δ)).card ≤ n) :
    ((Finset.Icc 2 (K - 1)).filter
      (fun i => a' ≤ sA (i - 1) ∧ sA i ≤ b' ∧ sA i - sA (i - 1) < δ)).card ≤ n := by
-- BODY
  have hmnS : ∀ a b : ℕ, a ≤ b → b ≤ k → s a ≤ s b := by
    intro a b hab hb
    exact hmonoS (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  have hsAm : sA m = τ := by
    obtain ⟨-, h⟩ := htail m hm1 le_rfl
    rw [h, hsplice]
  -- tail package: for `2 ≤ i ≤ m`, the index `c + (i-1)` is a legitimate edge index of `s`
  -- whose two endpoint values are the shifted values `sA i - σ`, `sA (i-1) - σ`.
  have T : ∀ i : ℕ, 2 ≤ i → i ≤ m →
      1 ≤ c + (i - 1) ∧ c + (i - 1) ≤ k ∧
      s (c + (i - 1)) = sA i - σ ∧ s (c + (i - 1) - 1) = sA (i - 1) - σ := by
    intro i hi2 him
    obtain ⟨hle, heq⟩ := htail i (by omega) him
    obtain ⟨-, heq'⟩ := htail (i - 1) (by omega) (by omega)
    have hidx : c + (i - 1) - 1 = c + (i - 1 - 1) := by omega
    refine ⟨by omega, hle, by rw [heq]; ring, ?_⟩
    rw [hidx, heq']; ring
  -- head package: for `m < i ≤ K-1`, the index `i - m` is a legitimate edge index of `s`
  -- whose two endpoint values are the shifted values `sA i - τ`, `sA (i-1) - τ`; at the splice
  -- index `i = m+1` the lower endpoint is `s 0 = 0 = sA m - τ`.
  have H : ∀ i : ℕ, m < i → i ≤ K - 1 →
      1 ≤ i - m ∧ i - m ≤ k ∧
      s (i - m) = sA i - τ ∧ s (i - m - 1) = sA (i - 1) - τ := by
    intro i him hiK
    obtain ⟨hle, heq⟩ := hhead i him hiK
    refine ⟨by omega, hle, by rw [heq]; ring, ?_⟩
    rcases Nat.lt_or_ge i (m + 2) with hlt | hge
    · have hi : i = m + 1 := by omega
      subst hi
      have h0 : m + 1 - m - 1 = 0 := by omega
      have h1 : m + 1 - 1 = m := by omega
      rw [h0, h1, hs0, hsAm]; ring
    · obtain ⟨-, heq'⟩ := hhead (i - 1) (by omega) (by omega)
      have hidx : i - m - 1 = i - 1 - m := by omega
      rw [hidx, heq']; ring
  -- across the splice the two stretches land in disjoint ranges, by the margin `b' - τ < a' - σ`
  have cross : ∀ P Q : ℕ, 2 ≤ P → P ≤ m → m < Q → Q ≤ K - 1 →
      a' ≤ sA (P - 1) → sA Q ≤ b' → c + (P - 1) ≠ Q - m := by
    intro P Q hP2 hPm hQm hQK hPw hQw heq
    obtain ⟨-, -, -, h4⟩ := T P hP2 hPm
    obtain ⟨hq1, hq2, h3, -⟩ := H Q hQm hQK
    have hstep : s (Q - m - 1) ≤ s (Q - m) := hmnS _ _ (by omega) hq2
    rw [heq] at h4
    linarith
  refine le_trans (Finset.card_le_card_of_injOn
    (fun i => if i ≤ m then c + (i - 1) else i - m) ?_ ?_) hcount
  · intro i hi
    obtain ⟨hiI, hlo, hhi, hshort⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi2, hiK⟩ := Finset.mem_Icc.mp hiI
    by_cases hcase : i ≤ m
    · obtain ⟨h1, h2, h3, h4⟩ := T i hi2 hcase
      have hΦ : (fun i => if i ≤ m then c + (i - 1) else i - m) i = c + (i - 1) := if_pos hcase
      rw [hΦ]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Or.inl ?_, ?_⟩
      · rw [h4]; linarith
      · rw [h3, h4]; linarith
    · obtain ⟨h1, h2, h3, h4⟩ := H i (by omega) hiK
      have hΦ : (fun i => if i ≤ m then c + (i - 1) else i - m) i = i - m := if_neg hcase
      rw [hΦ]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Or.inr ?_, ?_⟩
      · rw [h3]; linarith
      · rw [h3, h4]; linarith
  · intro x hx y hy hxy
    obtain ⟨hxI, hxlo, hxhi, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hyI, hylo, hyhi, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    obtain ⟨hx2, hxK⟩ := Finset.mem_Icc.mp hxI
    obtain ⟨hy2, hyK⟩ := Finset.mem_Icc.mp hyI
    have hxy' : (if x ≤ m then c + (x - 1) else x - m) =
        (if y ≤ m then c + (y - 1) else y - m) := hxy
    by_cases hxm : x ≤ m <;> by_cases hym : y ≤ m
    · rw [if_pos hxm, if_pos hym] at hxy'; omega
    · rw [if_pos hxm, if_neg hym] at hxy'
      exact absurd hxy' (cross x y hx2 hxm (by omega) hyK hxlo hyhi)
    · rw [if_neg hxm, if_pos hym] at hxy'
      exact absurd hxy'.symm (cross y x hy2 hym (by omega) hxK hylo hxhi)
    · rw [if_neg hxm, if_neg hym] at hxy'; omega
