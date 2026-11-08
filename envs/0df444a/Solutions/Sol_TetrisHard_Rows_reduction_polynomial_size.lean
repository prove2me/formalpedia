-- Prove2me | solution 1 for TetrisHard.Rows.reduction_polynomial_size
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:40:54.166911+00:00
-- url     : https://prove2.me/submissions/154bf520-7ba1-4996-ab23-2d4699b4507d

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace Aux_Tetris_poly
open TetrisHard.Rows

theorem ulen (ns : List ℕ) : (unaryCode ns).length = (ns.map (· + 1)).sum := by
  unfold unaryCode
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro n _
  simp

theorem code_le (p : Piece) : p.code + 1 ≤ 7 := by cases p <;> simp [Piece.code]

theorem block_len (a : ℕ) : (integerBlock a).length = 5 * a + 5 := by
  simp [integerBlock, initiator, filler, terminator, List.length_flatten, List.sum_replicate]
  ring

theorem num_len (P : ThreePartition) :
    (numberPieces P).length = ∑ i, (5 * P.entry i + 5) := by
  unfold numberPieces
  rw [List.length_flatMap, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp [block_len]

theorem rows_len (B : Board) : B.rows.flatten.length = B.height * B.width := by
  unfold Board.rows
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  simp

end Aux_Tetris_poly

open TetrisHard.Rows Aux_Tetris_poly in
theorem solution (staging : ℕ) :
    ∃ C k : ℕ, ∀ P : ThreePartition, P.Valid → P.Normalized →
      (baseGame P staging).code.length ≤ C * (P.code.length + 1) ^ k := by
  refine ⟨(staging + 30) * (staging + 30) + 20 * (staging + 30), 2, fun P _ _ => ?_⟩
  set E := ∑ i, P.entry i with hE
  have hL : P.code.length = P.s + 1 + (P.target + 1) + (E + 3 * P.s) := by
    unfold ThreePartition.code
    rw [ulen]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons, List.map_ofFn,
      List.sum_ofFn, Function.comp_apply, Finset.sum_add_distrib]
    simp [hE]
    try ring
  set L := P.code.length with hLdef
  have hlen : (basePieces P).length = 5 * E + 5 * (3 * P.s) + P.s + 1 + (3 * P.target / 2 + 5) := by
    unfold basePieces
    simp only [List.length_append, List.length_replicate, List.length_singleton, num_len]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hE]
    try ring
  have hsum : ((basePieces P).map (fun p => p.code + 1)).sum ≤ 7 * (basePieces P).length := by
    have := List.sum_le_card_nsmul ((basePieces P).map (fun p => p.code + 1)) 7 (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact code_le p)
    simpa [mul_comm] using this
  have hcodeG : (baseGame P staging).code.length =
      (baseHeight P + 3 * P.s + staging + 1) + (6 * P.s + 3 + 1) +
        (baseHeight P + 3 * P.s + staging) * (6 * P.s + 3) +
        ((basePieces P).length + 1 + ((basePieces P).map (fun p => p.code + 1)).sum) := by
    unfold Game.code
    rw [List.length_append, List.length_append, ulen, ulen, rows_len]
    have hh : (baseGame P staging).board.height = baseHeight P + 3 * P.s + staging := rfl
    have hw : (baseGame P staging).board.width = 6 * P.s + 3 := rfl
    have hp : (baseGame P staging).pieces = basePieces P := rfl
    rw [hh, hw, hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hcomp2 : ((basePieces P).map Piece.code).map (· + 1) = (basePieces P).map (fun p => p.code + 1) := by
      rw [List.map_map]; rfl
    rw [hcomp2]
    ring
  rw [hcodeG]
  have hbh : baseHeight P = 6 * P.target + 22 := rfl
  have h1 : P.s ≤ L := by omega
  have h2 : P.target ≤ L := by omega
  have h3 : E ≤ L := by omega
  have h4 : 3 * P.target / 2 ≤ 2 * L := by omega
  set c := staging + 30 with hcdef
  have hcL : 30 * L ≤ c * L := Nat.mul_le_mul_right _ (by omega)
  have hcL1 : c * (L + 1) = c * L + c := by ring
  have hA : baseHeight P + 3 * P.s + staging ≤ c * (L + 1) := by omega
  have hB : 6 * P.s + 3 ≤ c * (L + 1) := by omega
  have hC : (basePieces P).length ≤ c * (L + 1) := by rw [hlen]; omega
  have hAB := Nat.mul_le_mul hA hB
  have hX : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hY : c * (L + 1) ≤ c * (L + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have hYY : c * (L + 1) * (c * (L + 1)) = c * c * (L + 1) ^ 2 := by ring
  have h3 : 3 ≤ c * (L + 1) ^ 2 := by
    have := Nat.mul_le_mul_left c hX
    omega
  have hfin : (c * c + 20 * c) * (L + 1) ^ 2 = c * c * (L + 1) ^ 2 + 20 * (c * (L + 1) ^ 2) := by ring
  rw [hfin]
  omega
