-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.num_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:43.112124+00:00
-- url     : https://prove2.me/submissions/fe227036-887c-41d8-9fcb-721e32ae226b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_SqSumLe
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_sq_sum_le
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_sq_sum_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
