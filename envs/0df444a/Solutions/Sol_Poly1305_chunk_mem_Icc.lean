-- Prove2me | solution 1 for Poly1305.chunk_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:01.674377+00:00
-- url     : https://prove2.me/submissions/1bae31f7-2217-404b-8ae9-ef9b1ddbe3b6

import Definitions.Def_Poly1305Bernstein

section
section
namespace Poly1305.DefsChunk

theorem byteAt_lt (m : Message) (k : ℕ) : byteAt m k < 256 := (m.getD k 0).isLt

theorem sum_lt (f : ℕ → ℕ) (hf : ∀ j, f j < 256) (k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ (8 * j) * f j < 2 ^ (8 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 ^ (8 * k) * f k ≤ 2 ^ (8 * k) * 255 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (hf k))
    have h2 : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by ring, pow_add]; norm_num
    omega

end Poly1305.DefsChunk

namespace Poly1305

theorem chunk_mem_Icc_dev (m : Message) (i : ℕ) (hi : 1 ≤ i) (hiq : i ≤ numChunks m) :
    1 ≤ chunk m i ∧ chunk m i ≤ 2 ^ 129 := by
  unfold chunk
  split_ifs with h
  · have := DefsChunk.sum_lt (fun j => byteAt m (16 * i - 16 + j))
      (fun j => DefsChunk.byteAt_lt _ _) 16
    constructor
    · omega
    · have : (2 : ℕ) ^ 129 = 2 ^ (8 * 16) + 2 ^ 128 := by norm_num
      omega
  · have hk : m.length % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have := DefsChunk.sum_lt (fun j => byteAt m (16 * i - 16 + j))
      (fun j => DefsChunk.byteAt_lt _ _) (m.length % 16)
    have hp : 2 ^ (8 * (m.length % 16)) ≤ 2 ^ 128 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2 ^ (8 * (m.length % 16)) := Nat.pow_pos (by norm_num)
    constructor
    · omega
    · have : (2 : ℕ) ^ 129 = 2 ^ 128 + 2 ^ 128 := by norm_num
      omega

end Poly1305

end
end

section
open Poly1305

theorem solution (m : Message) (i : ℕ) (hi : 1 ≤ i) (hiq : i ≤ numChunks m) :
    1 ≤ chunk m i ∧ chunk m i ≤ 2 ^ 129 := by
  apply Poly1305.chunk_mem_Icc_dev <;> assumption

end
