-- Prove2me | solution 1 for SymmetricRendezvousLine.symmetric_rendezvous_value_lt_4_2574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:34:23.89521+00:00
-- url     : https://prove2.me/submissions/6267eb90-b18b-427a-b695-f54433915c0b

import Mathlib
import Definitions.Def_SymmetricRendezvousLine_defs

set_option autoImplicit false

/-!
# A symmetric rendezvous strategy on the line with expected meeting time below 4.2574

The strategy is 15-Markovian: time is cut into blocks of length 15; at the start of every block the player
draws, independently of everything else, a sign `σ` and one of finitely many unit-speed zigzag patterns
(`G` below, with integer weights), and follows `σ ·` that pattern during the block.  For every pair of
patterns and signs, either the players meet at an integer time of the block, or the gap is back to `2` at
the end of the block (checked by the kernel).  Hence the meeting time is at most
`G = ∑ₖ (∏_{l<k} a_l) τ_k` (blocks are i.i.d.), whose expectation is `T₀ (1 - A₀)⁻¹`, computed exactly.
-/

namespace RdvCert

open MeasureTheory ProbabilityTheory SymmetricRendezvousLine
open scoped ENNReal

/-! ## The finite certificate -/

/-- per pattern: offset positions (`16 + position`) at local times `1..15`, and the integer weight -/
def G : List (List ℕ × ℕ) := [
  ([17, 18, 17, 16, 15, 14, 13, 12, 11, 12, 13, 14, 15, 16, 17], 9),
  ([17, 16, 15, 16, 17, 16, 15, 14, 13, 12, 13, 14, 15, 16, 17], 6),
  ([17, 16, 15, 14, 15, 16, 17, 16, 17, 16, 15, 16, 17, 18, 19], 9),
  ([17, 16, 17, 16, 15, 14, 15, 16, 15, 14, 13, 14, 15, 16, 17], 13),
  ([17, 16, 17, 16, 15, 14, 13, 14, 15, 16, 17, 16, 17, 18, 19], 9),
  ([17, 16, 15, 16, 15, 16, 15, 14, 15, 16, 17, 16, 17, 18, 19], 9),
  ([17, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 14, 15, 16, 17], 12),
  ([17, 16, 15, 16, 15, 14, 15, 16, 17, 18, 17, 16, 17, 18, 19], 13),
  ([17, 18, 17, 16, 15, 14, 13, 14, 13, 14, 13, 12, 13, 14, 15], 12),
  ([17, 16, 15, 14, 15, 16, 17, 18, 17, 16, 15, 14, 15, 16, 17], 15),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 12, 11, 10, 11, 12, 13], 11),
  ([17, 16, 15, 14, 13, 14, 15, 16, 17, 18, 19, 20, 19, 20, 21], 5),
  ([17, 16, 15, 14, 15, 16, 17, 16, 15, 16, 17, 18, 17, 18, 19], 18),
  ([17, 16, 15, 16, 15, 14, 15, 16, 17, 16, 17, 18, 17, 18, 19], 9),
  ([17, 18, 17, 16, 15, 14, 13, 14, 13, 12, 13, 14, 13, 14, 15], 13),
  ([17, 16, 17, 16, 15, 16, 15, 14, 13, 12, 13, 14, 13, 14, 15], 8),
  ([17, 16, 17, 16, 15, 14, 15, 14, 15, 16, 15, 16, 15, 16, 17], 9),
  ([17, 16, 15, 16, 15, 16, 15, 16, 15, 16, 15, 16, 15, 16, 17], 7),
  ([17, 16, 15, 14, 15, 16, 17, 18, 17, 16, 15, 16, 15, 16, 17], 11),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 12, 11, 12, 11, 12, 13], 9),
  ([17, 16, 15, 14, 15, 16, 15, 16, 17, 18, 19, 18, 17, 18, 19], 15),
  ([17, 18, 17, 16, 15, 14, 13, 12, 13, 14, 15, 14, 13, 14, 15], 18),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 14, 15, 14, 13, 14, 15], 12),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 14, 15, 14, 13, 14, 15], 11),
  ([17, 16, 15, 14, 15, 16, 17, 16, 17, 18, 17, 16, 15, 16, 17], 16),
  ([17, 16, 17, 16, 15, 14, 15, 16, 15, 16, 15, 14, 13, 14, 15], 10),
  ([17, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15], 7),
  ([17, 18, 17, 16, 15, 14, 13, 14, 15, 14, 13, 12, 11, 12, 13], 19),
  ([17, 16, 17, 16, 15, 16, 15, 14, 15, 14, 13, 12, 11, 12, 13], 8),
  ([17, 16, 15, 16, 17, 16, 15, 16, 15, 14, 13, 12, 11, 12, 13], 9),
  ([17, 16, 15, 14, 15, 16, 15, 16, 17, 18, 17, 18, 19, 18, 19], 8),
  ([17, 18, 17, 16, 15, 14, 13, 12, 13, 14, 13, 14, 15, 14, 15], 8),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 14, 13, 14, 15, 14, 15], 9),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 14, 15], 7),
  ([17, 16, 17, 16, 15, 14, 13, 14, 15, 16, 17, 18, 17, 16, 17], 11),
  ([17, 16, 15, 16, 15, 16, 15, 14, 15, 16, 17, 18, 17, 16, 17], 7),
  ([17, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 16, 15, 14, 15], 11),
  ([17, 16, 15, 16, 15, 14, 15, 16, 17, 18, 17, 18, 17, 16, 17], 10),
  ([17, 18, 17, 16, 15, 14, 13, 14, 13, 14, 13, 14, 13, 12, 13], 12),
  ([17, 16, 17, 16, 15, 16, 15, 14, 13, 14, 13, 14, 13, 12, 13], 8),
  ([17, 16, 17, 16, 15, 14, 15, 14, 15, 16, 17, 16, 15, 14, 15], 8),
  ([17, 16, 15, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15, 14, 15], 8),
  ([17, 16, 15, 14, 15, 16, 17, 18, 17, 16, 17, 16, 15, 14, 15], 12),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 12, 13, 12, 11, 10, 11], 11),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 16, 15, 14, 13, 12, 13], 12),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 16, 15, 14, 13, 12, 13], 9),
  ([17, 16, 17, 16, 15, 14, 15, 16, 17, 16, 15, 14, 13, 12, 13], 10),
  ([17, 16, 17, 16, 15, 14, 15, 14, 15, 14, 15, 16, 17, 18, 17], 9),
  ([17, 16, 15, 16, 15, 16, 15, 16, 15, 14, 15, 16, 17, 18, 17], 8),
  ([17, 16, 15, 14, 15, 16, 15, 16, 17, 18, 17, 18, 19, 20, 19], 11),
  ([17, 18, 17, 16, 15, 14, 13, 12, 13, 14, 13, 14, 15, 16, 15], 10),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 14, 13, 14, 15, 16, 15], 10),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 16, 15], 10),
  ([17, 16, 15, 14, 15, 16, 17, 16, 17, 16, 17, 16, 17, 18, 17], 13),
  ([17, 16, 17, 16, 15, 14, 15, 16, 15, 14, 15, 14, 15, 16, 15], 11),
  ([17, 16, 17, 16, 15, 16, 15, 14, 13, 14, 13, 12, 13, 14, 13], 9),
  ([17, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15, 14, 15, 16, 15], 9),
  ([17, 16, 15, 16, 17, 16, 15, 16, 15, 14, 13, 12, 13, 14, 13], 11),
  ([17, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 16, 15, 16, 15], 8),
  ([17, 16, 17, 16, 15, 14, 15, 14, 15, 16, 17, 16, 15, 16, 15], 7),
  ([17, 16, 15, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15, 16, 15], 7),
  ([17, 16, 15, 14, 15, 16, 17, 18, 17, 16, 17, 16, 15, 16, 15], 10),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 12, 13, 12, 11, 12, 11], 9),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 16, 15, 14, 13, 14, 13], 10),
  ([17, 16, 15, 14, 13, 14, 15, 16, 17, 18, 19, 20, 21, 20, 19], 6),
  ([17, 16, 15, 16, 15, 16, 15, 14, 15, 16, 17, 18, 19, 18, 17], 6),
  ([17, 16, 15, 14, 15, 16, 17, 16, 15, 16, 17, 18, 19, 18, 17], 19),
  ([17, 16, 15, 16, 17, 16, 15, 14, 13, 14, 15, 16, 17, 16, 15], 9),
  ([17, 16, 15, 16, 15, 14, 15, 16, 17, 16, 17, 18, 19, 18, 17], 11),
  ([17, 18, 17, 16, 15, 14, 13, 14, 13, 12, 13, 14, 15, 14, 13], 14),
  ([17, 16, 17, 16, 15, 16, 15, 14, 13, 12, 13, 14, 15, 14, 13], 10),
  ([17, 16, 17, 16, 15, 14, 15, 14, 15, 16, 15, 16, 17, 16, 15], 10),
  ([17, 16, 15, 16, 15, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15], 10),
  ([17, 16, 15, 14, 15, 16, 17, 18, 17, 16, 15, 16, 17, 16, 15], 21),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 12, 11, 12, 13, 12, 11], 17),
  ([17, 16, 15, 14, 15, 16, 15, 16, 17, 18, 19, 18, 19, 18, 17], 9),
  ([17, 18, 17, 16, 15, 14, 13, 12, 13, 14, 15, 14, 15, 14, 13], 10),
  ([17, 16, 15, 16, 17, 16, 15, 14, 15, 14, 15, 14, 15, 14, 13], 10),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 14, 15, 14, 15, 14, 13], 6),
  ([17, 16, 15, 14, 15, 16, 17, 16, 17, 18, 17, 16, 17, 16, 15], 15),
  ([17, 16, 17, 16, 15, 14, 15, 16, 15, 16, 15, 14, 15, 14, 13], 8),
  ([17, 18, 17, 16, 15, 14, 13, 14, 15, 14, 13, 12, 13, 12, 11], 18),
  ([17, 16, 17, 16, 15, 16, 15, 14, 15, 14, 13, 12, 13, 12, 11], 7),
  ([17, 16, 15, 14, 15, 16, 15, 16, 17, 18, 19, 20, 19, 18, 17], 9),
  ([17, 18, 17, 16, 15, 14, 13, 12, 13, 14, 15, 16, 15, 14, 13], 13),
  ([17, 16, 15, 14, 15, 16, 17, 16, 17, 16, 17, 18, 17, 16, 15], 16),
  ([17, 16, 17, 16, 15, 14, 15, 16, 15, 14, 15, 16, 15, 14, 13], 14),
  ([17, 16, 15, 16, 15, 16, 17, 16, 15, 14, 15, 16, 15, 14, 13], 8),
  ([17, 16, 15, 16, 15, 16, 15, 16, 17, 16, 15, 16, 15, 14, 13], 9),
  ([17, 16, 15, 16, 17, 16, 15, 16, 15, 14, 13, 14, 13, 12, 11], 12),
  ([17, 16, 15, 16, 15, 14, 15, 16, 17, 18, 19, 18, 17, 16, 15], 10),
  ([17, 18, 17, 16, 15, 14, 13, 14, 13, 14, 15, 14, 13, 12, 11], 9),
  ([17, 16, 17, 16, 15, 16, 15, 14, 13, 14, 15, 14, 13, 12, 11], 10),
  ([17, 18, 17, 16, 15, 14, 15, 14, 13, 14, 13, 12, 11, 10, 9], 9),
  ([17, 16, 15, 14, 15, 16, 17, 18, 19, 18, 17, 16, 15, 14, 13], 12)]

/-- meeting test in sign case `k` (`0:++, 1:+-, 2:-+, 3:--`) for offset positions `a` (I), `b` (II) -/
def hit : ℕ → ℕ → ℕ → Bool
  | 0, a, b => b + 2 == a
  | 1, a, b => a + b == 34
  | 2, a, b => a + b == 30
  | _, a, b => a + 2 == b

/-- the gap is back to `2` -/
def gap2 : ℕ → ℕ → ℕ → Bool
  | 0, a, b => a == b
  | 1, a, b => a + b == 32
  | 2, a, b => a + b == 32
  | _, a, b => b == a

/-- `(τ, noMeet, bad)` for sign case `k`; `t` counts the steps done -/
def scan (k : ℕ) : ℕ → List ℕ → List ℕ → ℕ × ℕ × ℕ
  | t, a :: as, b :: bs =>
      if hit k a b then (t + 1, 0, 0)
      else match as, bs with
        | [], _ => (t + 1, 1, if gap2 k a b then 0 else 1)
        | _, [] => (t + 1, 1, if gap2 k a b then 0 else 1)
        | _, _ => scan k (t + 1) as bs
  | t, _, _ => (t, 1, 1)

/-- weighted contribution of one pattern pair in sign case `k` -/
def F (k : ℕ) (g h : List ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((g.2 * h.2) * (scan k 0 g.1 h.1).1, (g.2 * h.2) * (scan k 0 g.1 h.1).2.1, (scan k 0 g.1 h.1).2.2)

/-- total over all pattern pairs in sign case `k` -/
def tot (k : ℕ) : ℕ × ℕ × ℕ := (G.map fun g => (G.map (F k g)).sum).sum

/-- one row of the check; sign case `3` is case `0` with the players swapped (`tot3`) -/
def rowT (g : List ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((G.map (F 0 g)).sum + (G.map (F 1 g)).sum) + ((G.map (F 2 g)).sum + (G.map (F 0 g)).sum)

theorem chunk0 : ((G.take 8).map rowT).sum = (1417081, 1828, 0) := by decide +kernel

theorem chunk1 : (((G.drop 8).take 8).map rowT).sum = (1555482, 2834, 0) := by decide +kernel

theorem chunk2 : ((((G.drop 8).drop 8).take 8).map rowT).sum = (1560686, 2292, 0) := by decide +kernel

theorem chunk3 : (((((G.drop 8).drop 8).drop 8).take 8).map rowT).sum = (1397711, 2738, 0) := by decide +kernel

theorem chunk4 : ((((((G.drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1264223, 2236, 0) := by decide +kernel

theorem chunk5 : (((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1309636, 2500, 0) := by decide +kernel

theorem chunk6 : ((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1432661, 1712, 0) := by decide +kernel

theorem chunk7 : (((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1182678, 1434, 0) := by decide +kernel

theorem chunk8 : ((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1508840, 2062, 0) := by decide +kernel

theorem chunk9 : (((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1682315, 3262, 0) := by decide +kernel

theorem chunk10 : ((((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1517103, 2406, 0) := by decide +kernel

theorem chunk11 : (((((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).take 8).map rowT).sum = (1154540, 1462, 0) := by decide +kernel

theorem chunk_end : (((((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).map rowT).sum = 0 := by decide +kernel

theorem G_len : ∀ i : Fin G.length, (G.get i).1.length = 15 := by decide +kernel

/-- offset position of pattern `i` at local time `t` (time `0` is offset `16`) -/
def posN (i : Fin G.length) (t : ℕ) : ℕ := (16 :: (G.get i).1).getD t 16

theorem G_step : ∀ i : Fin G.length, ∀ r : Fin 15,
    posN i ((r : ℕ) + 1) = posN i (r : ℕ) + 1 ∨ posN i (r : ℕ) = posN i ((r : ℕ) + 1) + 1 := by
  decide +kernel

theorem G_wsum : (G.map Prod.snd).sum = 1002 := by decide +kernel

-- the data are only ever evaluated by the kernel checks above
attribute [irreducible] G

theorem split_sum (f : List ℕ × ℕ → ℕ × ℕ × ℕ) (l : List (List ℕ × ℕ)) (s : ℕ) :
    (l.map f).sum = ((l.take s).map f).sum + ((l.drop s).map f).sum := by
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

theorem rows_eq : (G.map rowT).sum = (16982956, 26766, 0) := by
  rw [split_sum rowT G 8, chunk0,
    split_sum rowT (G.drop 8) 8, chunk1,
    split_sum rowT ((G.drop 8).drop 8) 8, chunk2,
    split_sum rowT (((G.drop 8).drop 8).drop 8) 8, chunk3,
    split_sum rowT ((((G.drop 8).drop 8).drop 8).drop 8) 8, chunk4,
    split_sum rowT (((((G.drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk5,
    split_sum rowT ((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk6,
    split_sum rowT (((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk7,
    split_sum rowT ((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk8,
    split_sum rowT (((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk9,
    split_sum rowT ((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk10,
    split_sum rowT (((((((((((G.drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8).drop 8) 8, chunk11, chunk_end]
  decide +kernel

/-! ## Semantics of the scan -/

theorem scan_nil (k t : ℕ) (bs : List ℕ) : scan k t [] bs = (t, 1, 1) := by
  cases bs <;> rfl

theorem scan_cons_nil (k t a : ℕ) (as : List ℕ) : scan k t (a :: as) [] = (t, 1, 1) := rfl

theorem scan_one (k t a b : ℕ) (bs : List ℕ) :
    scan k t [a] (b :: bs) = if hit k a b then (t + 1, 0, 0)
      else (t + 1, 1, if gap2 k a b then 0 else 1) := rfl

theorem scan_two_one (k t a a' b : ℕ) (as : List ℕ) :
    scan k t (a :: a' :: as) [b] = if hit k a b then (t + 1, 0, 0)
      else (t + 1, 1, if gap2 k a b then 0 else 1) := rfl

theorem scan_two (k t a a' b b' : ℕ) (as bs : List ℕ) :
    scan k t (a :: a' :: as) (b :: b' :: bs) = if hit k a b then (t + 1, 0, 0)
      else scan k (t + 1) (a' :: as) (b' :: bs) := rfl

theorem scan_hit (k : ℕ) : ∀ (as bs : List ℕ) (t : ℕ), (scan k t as bs).2.1 = 0 →
    ∃ m, m < as.length ∧ (scan k t as bs).1 = t + m + 1 ∧
      hit k (as.getD m 16) (bs.getD m 16) = true
  | [], bs, t, h => by simp [scan_nil] at h
  | a :: as, [], t, h => by simp [scan_cons_nil] at h
  | [a], b :: bs, t, h => by
    rw [scan_one] at h ⊢
    by_cases hk : hit k a b = true
    · exact ⟨0, by simp, by simp [hk], by simpa using hk⟩
    · simp [hk] at h
  | a :: a' :: as, [b], t, h => by
    rw [scan_two_one] at h ⊢
    by_cases hk : hit k a b = true
    · exact ⟨0, by simp, by simp [hk], by simpa using hk⟩
    · simp [hk] at h
  | a :: a' :: as, b :: b' :: bs, t, h => by
    rw [scan_two] at h ⊢
    by_cases hk : hit k a b = true
    · exact ⟨0, by simp, by simp [hk], by simpa using hk⟩
    · rw [if_neg hk] at h ⊢
      obtain ⟨m, hm, h1, h2⟩ := scan_hit k (a' :: as) (b' :: bs) (t + 1) h
      refine ⟨m + 1, by simp at hm ⊢; omega, by rw [h1]; omega, by simpa using h2⟩

theorem scan_miss (k : ℕ) : ∀ (as bs : List ℕ) (t : ℕ), as.length = bs.length → as ≠ [] →
    (scan k t as bs).2.1 ≠ 0 → (scan k t as bs).2.2 = 0 →
    (scan k t as bs).2.1 = 1 ∧ (scan k t as bs).1 = t + as.length ∧
      gap2 k (as.getD (as.length - 1) 16) (bs.getD (as.length - 1) 16) = true
  | [], _, _, _, hne, _, _ => absurd rfl hne
  | [a], [], _, hl, _, _, _ => by simp at hl
  | [a], b :: b' :: bs, _, hl, _, _, _ => by simp at hl
  | [a], [b], t, _, _, h1, h2 => by
    rw [scan_one] at h1 h2 ⊢
    by_cases hk : hit k a b = true
    · simp [hk] at h1
    · by_cases hg : gap2 k a b = true
      · simp [hk, hg]
      · simp [hk, hg] at h2
  | a :: a' :: as, [], _, hl, _, _, _ => by simp at hl
  | a :: a' :: as, [b], _, hl, _, _, _ => by simp at hl
  | a :: a' :: as, b :: b' :: bs, t, hl, _, h1, h2 => by
    rw [scan_two] at h1 h2 ⊢
    by_cases hk : hit k a b = true
    · simp [hk] at h1
    · rw [if_neg hk] at h1 h2 ⊢
      obtain ⟨e1, e2, e3⟩ :=
        scan_miss k (a' :: as) (b' :: bs) (t + 1) (by simpa using hl) (by simp) h1 h2
      refine ⟨e1, by rw [e2]; simp only [List.length_cons]; omega, ?_⟩
      simpa using e3

/-! ## Patterns, signs, and the per-pair quantities -/

/-- a block choice: a sign and a pattern -/
abbrev α := Bool × Fin G.length

def sgZ (b : Bool) : ℤ := if b then 1 else -1

/-- signed position of choice `u` at local time `t` -/
def spos (u : α) (t : ℕ) : ℤ := sgZ u.1 * ((posN u.2 t : ℤ) - 16)

def kc : Bool → Bool → ℕ
  | true, true => 0
  | true, false => 1
  | false, true => 2
  | false, false => 3

def res (u v : α) : ℕ × ℕ × ℕ := scan (kc u.1 v.1) 0 (G.get u.2).1 (G.get v.2).1

/-- the meeting time within the block (or `15`) -/
def tau (u v : α) : ℕ := (res u v).1

/-- `1` if the players do not meet within the block -/
def aa (u v : α) : ℕ := (res u v).2.1

def Wt (u : α) : ℕ := (G.get u.2).2

theorem hit_sem (s₁ s₂ : Bool) (a b : ℕ) (h : hit (kc s₁ s₂) a b = true) :
    2 + sgZ s₂ * ((b : ℤ) - 16) - sgZ s₁ * ((a : ℤ) - 16) = 0 := by
  cases s₁ <;> cases s₂ <;> simp [hit, kc, sgZ] at h ⊢ <;> omega

theorem gap2_sem (s₁ s₂ : Bool) (a b : ℕ) (h : gap2 (kc s₁ s₂) a b = true) :
    sgZ s₂ * ((b : ℤ) - 16) - sgZ s₁ * ((a : ℤ) - 16) = 0 := by
  cases s₁ <;> cases s₂ <;> simp [gap2, kc, sgZ] at h ⊢ <;> omega

theorem posN_succ (i : Fin G.length) (m : ℕ) : posN i (m + 1) = (G.get i).1.getD m 16 := rfl

theorem aa_zero (u v : α) (h : aa u v = 0) :
    1 ≤ tau u v ∧ tau u v ≤ 15 ∧ 2 + spos v (tau u v) - spos u (tau u v) = 0 := by
  obtain ⟨m, hm, h1, h2⟩ := scan_hit (kc u.1 v.1) (G.get u.2).1 (G.get v.2).1 0 h
  rw [G_len] at hm
  have ht : tau u v = m + 1 := by
    rw [show tau u v = (scan (kc u.1 v.1) 0 (G.get u.2).1 (G.get v.2).1).1 from rfl, h1]; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [ht]
  have := hit_sem u.1 v.1 _ _ h2
  simp only [spos, posN_succ]
  exact this

/-! ## Sums over the certificate -/

theorem sum_fin_get_gen {M : Type} [AddCommMonoid M] (f : List ℕ × ℕ → M)
    (l : List (List ℕ × ℕ)) : ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn]
  rfl

theorem sum_fin_get {M : Type} [AddCommMonoid M] (f : List ℕ × ℕ → M) :
    ∑ i : Fin G.length, f (G.get i) = (G.map f).sum :=
  sum_fin_get_gen f G

theorem scan_swap : ∀ (as bs : List ℕ) (t : ℕ), scan 3 t as bs = scan 0 t bs as
  | [], [], t => rfl
  | [], b :: bs, t => by rw [scan_nil, scan_cons_nil]
  | a :: as, [], t => by rw [scan_nil, scan_cons_nil]
  | [a], [b], t => by rw [scan_one, scan_one]; rfl
  | [a], b :: b' :: bs, t => by rw [scan_one, scan_two_one]; rfl
  | a :: a' :: as, [b], t => by rw [scan_one, scan_two_one]; rfl
  | a :: a' :: as, b :: b' :: bs, t => by
    rw [scan_two, scan_two, scan_swap (a' :: as) (b' :: bs) (t + 1)]; rfl

theorem tot3 : tot 3 = tot 0 := by
  have h3 : ∀ g h, F 3 g h = F 0 h g := fun g h => by
    simp only [F, scan_swap, Nat.mul_comm g.2 h.2]
  unfold tot
  simp only [← sum_fin_get]
  simp only [h3]
  exact Finset.sum_comm

/-- generic form (all value-level terms contain variables, so the kernel never evaluates the certificate here) -/
theorem rows_total_gen (l : List (List ℕ × ℕ)) (a b c R : List ℕ × ℕ → ℕ × ℕ × ℕ)
    (hR : ∀ g, R g = (a g + b g) + (c g + a g)) (T0 T1 T2 : ℕ × ℕ × ℕ)
    (h0 : (l.map a).sum = T0) (h1 : (l.map b).sum = T1) (h2 : (l.map c).sum = T2) :
    (l.map R).sum = (T0 + T1) + (T2 + T0) := by
  rw [← h0, ← h1, ← h2, show R = fun g => (a g + b g) + (c g + a g) from funext hR]
  simp only [List.sum_map_add]

theorem rows_total : (G.map rowT).sum = (tot 0 + tot 1) + (tot 2 + tot 0) :=
  rows_total_gen G (fun g => (G.map (F 0 g)).sum) (fun g => (G.map (F 1 g)).sum)
    (fun g => (G.map (F 2 g)).sum) rowT (fun _ => rfl) (tot 0) (tot 1) (tot 2) rfl rfl rfl

theorem tot_eq : (tot 0 + tot 1) + (tot 2 + tot 3) = (16982956, 26766, 0) := by
  rw [tot3, ← rows_total, rows_eq]

theorem sum_alpha2 {M : Type} [AddCommMonoid M] (f : α → α → M) :
    ∑ u : α, ∑ v : α, f u v =
      ∑ s₁ : Bool, ∑ s₂ : Bool, ∑ i : Fin G.length, ∑ j : Fin G.length, f (s₁, i) (s₂, j) := by
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun s₁ _ => Finset.sum_comm

theorem sum_sign (s₁ s₂ : Bool) : ∑ i : Fin G.length, ∑ j : Fin G.length,
      ((Wt (s₁, i) * Wt (s₂, j) * tau (s₁, i) (s₂, j), Wt (s₁, i) * Wt (s₂, j) * aa (s₁, i) (s₂, j),
        (res (s₁, i) (s₂, j)).2.2) : ℕ × ℕ × ℕ) = tot (kc s₁ s₂) := by
  unfold tot
  rw [← sum_fin_get]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_fin_get]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- generic form: `T`, `V` are variables, so the kernel's defeq checks never evaluate the certificate -/
theorem sum_all_gen (T : ℕ → ℕ × ℕ × ℕ) (V : ℕ × ℕ × ℕ)
    (hT : ∀ s₁ s₂ : Bool, ∑ i : Fin G.length, ∑ j : Fin G.length,
      ((Wt (s₁, i) * Wt (s₂, j) * tau (s₁, i) (s₂, j), Wt (s₁, i) * Wt (s₂, j) * aa (s₁, i) (s₂, j),
        (res (s₁, i) (s₂, j)).2.2) : ℕ × ℕ × ℕ) = T (kc s₁ s₂))
    (hV : (T 0 + T 1) + (T 2 + T 3) = V) :
    ∑ u : α, ∑ v : α, ((Wt u * Wt v * tau u v, Wt u * Wt v * aa u v, (res u v).2.2) : ℕ × ℕ × ℕ) = V := by
  rw [sum_alpha2, ← hV]
  simp only [Fintype.sum_bool, hT, show kc true true = 0 from rfl, show kc true false = 1 from rfl,
    show kc false true = 2 from rfl, show kc false false = 3 from rfl]

theorem sum_all :
    ∑ u : α, ∑ v : α, ((Wt u * Wt v * tau u v, Wt u * Wt v * aa u v, (res u v).2.2) : ℕ × ℕ × ℕ) =
      (16982956, 26766, 0) :=
  sum_all_gen tot _ sum_sign tot_eq

theorem sum_NT : ∑ u : α, ∑ v : α, Wt u * Wt v * tau u v = 16982956 := by
  have := congrArg Prod.fst sum_all
  simpa only [Prod.fst_sum] using this

theorem sum_NA : ∑ u : α, ∑ v : α, Wt u * Wt v * aa u v = 26766 := by
  have := congrArg (fun x => x.2.1) sum_all
  simpa only [Prod.fst_sum, Prod.snd_sum] using this

theorem all_good (u v : α) : (res u v).2.2 = 0 := by
  have := congrArg (fun x => x.2.2) sum_all
  simp only [Prod.snd_sum] at this
  exact (Finset.sum_eq_zero_iff.mp ((Finset.sum_eq_zero_iff.mp this) u (Finset.mem_univ _)))
    v (Finset.mem_univ _)

theorem aa_ne (u v : α) (h : aa u v ≠ 0) :
    aa u v = 1 ∧ tau u v = 15 ∧ spos v 15 - spos u 15 = 0 := by
  have hl : (G.get u.2).1.length = (G.get v.2).1.length := by rw [G_len, G_len]
  have hne : (G.get u.2).1 ≠ [] := by
    intro e; have := G_len u.2; rw [e] at this; simp at this
  obtain ⟨e1, e2, e3⟩ := scan_miss (kc u.1 v.1) (G.get u.2).1 (G.get v.2).1 0 hl hne h (all_good u v)
  rw [G_len] at e2 e3
  rw [show (15 - 1 : ℕ) = 14 from rfl] at e3
  refine ⟨e1, e2.trans (zero_add 15), ?_⟩
  have := gap2_sem u.1 v.1 _ _ e3
  have hu : posN u.2 15 = (G.get u.2).1.getD 14 16 := posN_succ u.2 14
  have hv : posN v.2 15 = (G.get v.2).1.getD 14 16 := posN_succ v.2 14
  rw [spos, spos, hu, hv]
  exact this

/-! ## The strategy -/

/-- velocity during `[j, j+1]` -/
def vel (ω : ℕ → α) (j : ℕ) : ℤ := spos (ω (j / 15)) (j % 15 + 1) - spos (ω (j / 15)) (j % 15)

/-- position at integer time `m` -/
def ipos (ω : ℕ → α) (m : ℕ) : ℤ := ∑ j ∈ Finset.range m, vel ω j

/-- the realised path: linear interpolation of `ipos` -/
noncomputable def rpath (ω : ℕ → α) (t : ℝ) : ℝ :=
  (ipos ω ⌊t⌋₊ : ℝ) + (t - ⌊t⌋₊) * (vel ω ⌊t⌋₊ : ℝ)

theorem spos_step (u : α) (r : ℕ) (hr : r < 15) : |spos u (r + 1) - spos u r| ≤ 1 := by
  have h : posN u.2 (r + 1) = posN u.2 r + 1 ∨ posN u.2 r = posN u.2 (r + 1) + 1 :=
    G_step u.2 ⟨r, hr⟩
  have hs : sgZ u.1 = 1 ∨ sgZ u.1 = -1 := by unfold sgZ; split <;> simp
  simp only [spos]
  rw [abs_le]
  rcases hs with hs | hs <;> rw [hs] <;> constructor <;> omega

theorem vel_abs (ω : ℕ → α) (j : ℕ) : |vel ω j| ≤ 1 :=
  spos_step _ _ (Nat.mod_lt _ (by norm_num))

theorem ipos_succ (ω : ℕ → α) (m : ℕ) : ipos ω (m + 1) = ipos ω m + vel ω m :=
  Finset.sum_range_succ _ _

theorem ipos_lip' (ω : ℕ → α) (m : ℕ) : ∀ d : ℕ, |ipos ω (m + d) - ipos ω m| ≤ d
  | 0 => by simp
  | d + 1 => by
    have h1 := abs_le.mp (ipos_lip' ω m d)
    have h2 := abs_le.mp (vel_abs ω (m + d))
    rw [← add_assoc, ipos_succ, abs_le]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem ipos_lip (ω : ℕ → α) {m n : ℕ} (h : m ≤ n) : |ipos ω n - ipos ω m| ≤ (n : ℤ) - m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have := ipos_lip' ω m d
  push_cast
  linarith

theorem rpath_nat (ω : ℕ → α) (m : ℕ) : rpath ω m = ipos ω m := by
  simp [rpath]

theorem rpath_lip_le (ω : ℕ → α) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |rpath ω t - rpath ω s| ≤ t - s := by
  unfold rpath
  have hmn : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hst
  have hm1 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs
  have hm2 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (hs.trans hst)
  have hn2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  set m := ⌊s⌋₊
  set n := ⌊t⌋₊
  have hvm := abs_le.mp (vel_abs ω m)
  have hvn := abs_le.mp (vel_abs ω n)
  have hvm1 : (-1 : ℝ) ≤ vel ω m := by exact_mod_cast hvm.1
  have hvm2 : (vel ω m : ℝ) ≤ 1 := by exact_mod_cast hvm.2
  have hvn1 : (-1 : ℝ) ≤ vel ω n := by exact_mod_cast hvn.1
  have hvn2 : (vel ω n : ℝ) ≤ 1 := by exact_mod_cast hvn.2
  rw [abs_le]
  rcases Nat.eq_or_lt_of_le hmn with h | h
  · rw [← h]
    rw [← h] at hn1 hn2 hvn1 hvn2
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hst) (by linarith : (0 : ℝ) ≤ 1 + vel ω m)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hst) (by linarith : (0 : ℝ) ≤ 1 - vel ω m)]
  · have hmn' : m + 1 ≤ n := h
    have hI := abs_le.mp (ipos_lip ω hmn')
    have hI1 : ((ipos ω n : ℤ) : ℝ) - ipos ω (m + 1) ≤ n - (m + 1) := by exact_mod_cast hI.2
    have hI2 : -((n : ℝ) - (m + 1)) ≤ ((ipos ω n : ℤ) : ℝ) - ipos ω (m + 1) := by exact_mod_cast hI.1
    have hs1 : ((ipos ω (m + 1) : ℤ) : ℝ) = ipos ω m + vel ω m := by
      rw [ipos_succ]; push_cast; ring
    have ht0 : (0 : ℝ) ≤ t - n := by linarith
    have hs0 : (0 : ℝ) ≤ m + 1 - s := by linarith
    constructor
    · nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 + vel ω n),
        mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 + vel ω m)]
    · nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - vel ω n),
        mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - vel ω m)]

theorem rpath_feasible (ω : ℕ → α) : IsFeasiblePath (rpath ω) := by
  refine ⟨by simp [rpath, ipos], fun s t hs ht => ?_⟩
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonpos (by linarith : s - t ≤ 0)]
    linarith [rpath_lip_le ω hs h]
  · rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
    exact rpath_lip_le ω ht h

theorem vel_meas (j : ℕ) : Measurable fun ω : ℕ → α => (vel ω j : ℝ) :=
  (measurable_of_finite (fun a : α => ((spos a (j % 15 + 1) - spos a (j % 15) : ℤ) : ℝ))).comp
    (measurable_pi_apply (j / 15))

theorem rpath_meas (t : ℝ) : Measurable fun ω : ℕ → α => rpath ω t := by
  have : (fun ω : ℕ → α => rpath ω t) = fun ω =>
      (∑ j ∈ Finset.range ⌊t⌋₊, (vel ω j : ℝ)) + (t - ⌊t⌋₊) * (vel ω ⌊t⌋₊ : ℝ) := by
    funext ω; simp [rpath, ipos]
  rw [this]
  exact (Finset.measurable_sum _ fun j _ => vel_meas j).add ((vel_meas _).const_mul _)

/-- `1 / D` -/
noncomputable def Dinv : ℝ≥0∞ := (((2004 : ℕ) : ℝ≥0∞))⁻¹

/-- the block distribution -/
noncomputable def wt (u : α) : ℝ≥0∞ := (Wt u : ℝ≥0∞) * Dinv

noncomputable def μ0 : Measure α := ∑ u, wt u • Measure.dirac u

theorem lintegral_μ0 (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂μ0 = ∑ u, wt u * f u := by
  simp [μ0, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

theorem sum_Wt : ∑ u : α, Wt u = 2004 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have : ∑ i : Fin G.length, Wt (true, i) = 1002 := by
    rw [← G_wsum, ← sum_fin_get]; rfl
  have h2 : ∑ i : Fin G.length, Wt (false, i) = 1002 := this
  rw [this, h2]

theorem sum_wt : ∑ u : α, wt u = 1 := by
  simp only [wt]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_Wt, Dinv]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)

instance : IsProbabilityMeasure μ0 :=
  ⟨by simp [μ0, sum_wt]⟩

/-- the strategy -/
noncomputable def S : MixedStrategy where
  Ω := ℕ → α
  P := Measure.infinitePi fun _ : ℕ => μ0
  path := rpath
  path_feasible := rpath_feasible
  path_measurable := rpath_meas

/-! ## Block structure -/

theorem spos_zero (u : α) : spos u 0 = 0 := by simp [spos, posN]

theorem ipos_block_step (ω : ℕ → α) (l : ℕ) :
    ∀ t, t ≤ 15 → ipos ω (15 * l + t) = ipos ω (15 * l) + spos (ω l) t
  | 0, _ => by simp [spos_zero]
  | t + 1, h => by
    rw [← add_assoc, ipos_succ, ipos_block_step ω l t (by omega)]
    have h1 : (15 * l + t) / 15 = l := by omega
    have h2 : (15 * l + t) % 15 = t := by omega
    simp only [vel, h1, h2]
    ring

theorem ipos_block (ω : ℕ → α) : ∀ l, ipos ω (15 * l) = ∑ j ∈ Finset.range l, spos (ω j) 15
  | 0 => by simp [ipos]
  | l + 1 => by
    rw [Finset.sum_range_succ, ← ipos_block ω l, show 15 * (l + 1) = 15 * l + 15 by ring,
      ipos_block_step ω l 15 le_rfl]

/-- orientation twist -/
def tw (b : Bool) (u : α) : α := (if b then u.1 else !u.1, u.2)

theorem tw_tw (b : Bool) (u : α) : tw b (tw b u) = u := by
  obtain ⟨s, i⟩ := u
  cases b <;> simp [tw]

def twE (b : Bool) : α ≃ α := ⟨tw b, tw b, tw_tw b, tw_tw b⟩

theorem spos_tw (b : Bool) (u : α) (t : ℕ) : sgZ b * spos u t = spos (tw b u) t := by
  obtain ⟨s, i⟩ := u
  cases b <;> cases s <;> simp [spos, tw, sgZ]

theorem orient_eq (b : Bool) : orient b = (sgZ b : ℝ) := by
  cases b <;> simp [orient, sgZ]

theorem sum_tw (b : Bool) (f : α → ℝ≥0∞) : ∑ u, wt u * f (tw b u) = ∑ u, wt u * f u :=
  Equiv.sum_comp (twE b) (fun u => wt u * f u)

/-! ## Pointwise bound -/

/-- meeting time upper bound from one meeting point -/
theorem meetingTime_le_of {x y : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (h : x t = y t) :
    meetingTime x y ≤ ENNReal.ofReal t := iInf₂_le t ⟨ht, h⟩

noncomputable def cA (u v : α) : ℝ≥0∞ := (aa u v : ℝ≥0∞)
noncomputable def cT (u v : α) : ℝ≥0∞ := (tau u v : ℝ≥0∞)

noncomputable def term (u v : ℕ → α) (k : ℕ) : ℝ≥0∞ :=
  (∏ l ∈ Finset.range k, cA (u l) (v l)) * cT (u k) (v k)

theorem tsum_top (u v : ℕ → α) (h : ∀ l, aa (u l) (v l) ≠ 0) : ∑' k, term u v k = ⊤ := by
  have e : ∀ k, term u v k = 15 := fun k => by
    rw [term, Finset.prod_eq_one fun l _ => by simp [cA, (aa_ne _ _ (h l)).1], one_mul]
    simp [cT, (aa_ne _ _ (h k)).2.1]
  rw [tsum_congr e]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

theorem tsum_ge (u v : ℕ → α) (L : ℕ) (hlt : ∀ l < L, aa (u l) (v l) ≠ 0) :
    ((15 * L + tau (u L) (v L) : ℕ) : ℝ≥0∞) ≤ ∑' k, term u v k := by
  refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (L + 1)))
  have hp : ∀ k ≤ L, ∏ l ∈ Finset.range k, cA (u l) (v l) = 1 := fun k hk =>
    Finset.prod_eq_one fun l hl => by
      simp [cA, (aa_ne _ _ (hlt l (by simp at hl; omega))).1]
  rw [Finset.sum_range_succ, term, hp L le_rfl, one_mul]
  have hs : ∀ k ∈ Finset.range L, term u v k = 15 := fun k hk => by
    rw [term, hp k (by simp at hk; omega), one_mul]
    simp [cT, (aa_ne _ _ (hlt k (by simpa using hk))).2.1]
  rw [Finset.sum_congr rfl hs]
  simp only [cT, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem pos_block (b : Bool) (ω : ℕ → α) (L t : ℕ) (ht : t ≤ 15) :
    orient b * rpath ω ((15 * L + t : ℕ) : ℝ) =
      ((∑ j ∈ Finset.range L, spos (tw b (ω j)) 15 + spos (tw b (ω L)) t : ℤ) : ℝ) := by
  rw [rpath_nat, ipos_block_step ω L t ht, ipos_block, orient_eq, ← Int.cast_mul, mul_add,
    Finset.mul_sum]
  simp only [spos_tw]

theorem pointwise (b₁ b₂ : Bool) (p : (ℕ → α) × (ℕ → α)) :
    meetingTime (fun t => orient b₁ * rpath p.1 t) (fun t => 2 + orient b₂ * rpath p.2 t) ≤
      ∑' k, term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k := by
  by_cases h : ∃ l, aa (tw b₁ (p.1 l)) (tw b₂ (p.2 l)) = 0
  · classical
    have hL := Nat.find_spec h
    have hlt : ∀ l < Nat.find h, aa (tw b₁ (p.1 l)) (tw b₂ (p.2 l)) ≠ 0 :=
      fun l hl => Nat.find_min h hl
    obtain ⟨_, h15, hgap⟩ := aa_zero _ _ hL
    refine le_trans ?_ (tsum_ge (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) _ hlt)
    rw [← ENNReal.ofReal_natCast]
    refine meetingTime_le_of (Nat.cast_nonneg _) ?_
    rw [pos_block _ _ _ _ h15, pos_block _ _ _ _ h15]
    have hs : ∑ j ∈ Finset.range (Nat.find h), spos (tw b₂ (p.2 j)) 15 =
        ∑ j ∈ Finset.range (Nat.find h), spos (tw b₁ (p.1 j)) 15 :=
      Finset.sum_congr rfl fun j hj => by
        have := (aa_ne _ _ (hlt j (Finset.mem_range.mp hj))).2.2
        linarith
    rw [hs]
    have : (2 : ℝ) = ((2 : ℤ) : ℝ) := by norm_num
    rw [this, ← Int.cast_add, Int.cast_inj]
    linarith
  · push Not at h
    rw [tsum_top _ _ h]
    exact le_top

/-! ## Integration -/

/-- `A₀ = P(no meeting in a block)` -/
noncomputable def A0 : ℝ≥0∞ := ∑ u, wt u * ∑ v, wt v * cA u v
/-- `T₀ = E[time used in a block]` -/
noncomputable def T0 : ℝ≥0∞ := ∑ u, wt u * ∑ v, wt v * cT u v

theorem meas_pair (l : ℕ) (f : α → α → ℝ≥0∞) :
    Measurable fun z : (ℕ → α) × (ℕ → α) => f (z.1 l) (z.2 l) := by
  have h2 : Measurable fun q : α × α => f q.1 q.2 := measurable_of_finite _
  have h3 : Measurable fun z : (ℕ → α) × (ℕ → α) => (z.1 l, z.2 l) :=
    Measurable.prodMk ((measurable_pi_apply l).comp measurable_fst)
      ((measurable_pi_apply l).comp measurable_snd)
  exact h2.comp h3

theorem lintegral_prod_coords (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ℕ)
    (f : ℕ → α → ℝ≥0∞) :
    ∫⁻ ω, ∏ l ∈ s, f l (ω l) ∂(Measure.infinitePi fun _ : ℕ => μ) = ∏ l ∈ s, ∫⁻ a, f l a ∂μ := by
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun s (fun l (ω : ℕ → α) => f l (ω l))
    (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun l => f l)
      (fun l => measurable_of_finite _))
    (fun l => (measurable_of_finite (f l)).comp (measurable_pi_apply l))
  refine h.trans (Finset.prod_congr rfl fun l _ => ?_)
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) l).lintegral_comp
    (measurable_of_finite _)

theorem lintegral_prod_pairs (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ℕ)
    (c : ℕ → α → α → ℝ≥0∞) :
    ∫⁻ z, ∏ l ∈ s, c l (z.1 l) (z.2 l)
        ∂((Measure.infinitePi fun _ : ℕ => μ).prod (Measure.infinitePi fun _ : ℕ => μ)) =
      ∏ l ∈ s, ∫⁻ a, ∫⁻ b, c l a b ∂μ ∂μ := by
  have hm : Measurable fun z : (ℕ → α) × (ℕ → α) => ∏ l ∈ s, c l (z.1 l) (z.2 l) :=
    Finset.measurable_prod _ fun l _ => meas_pair l (c l)
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ a : ℕ → α, ∫⁻ b, ∏ l ∈ s, c l (a l) (b l) ∂(Measure.infinitePi fun _ : ℕ => μ) =
      ∏ l ∈ s, ∫⁻ b, c l (a l) b ∂μ := fun a => lintegral_prod_coords μ s (fun l b => c l (a l) b)
  simp only [hin]
  exact lintegral_prod_coords μ s (fun l a => ∫⁻ b, c l a b ∂μ)

theorem lint_tw (b₁ b₂ : Bool) (f : α → α → ℝ≥0∞) :
    ∫⁻ a, ∫⁻ b, f (tw b₁ a) (tw b₂ b) ∂μ0 ∂μ0 = ∑ u, wt u * ∑ v, wt v * f u v := by
  simp only [lintegral_μ0]
  calc ∑ u, wt u * ∑ v, wt v * f (tw b₁ u) (tw b₂ v) = ∑ u, wt u * ∑ v, wt v * f (tw b₁ u) v :=
        Finset.sum_congr rfl fun u _ =>
          congrArg (fun x => wt u * x) (sum_tw b₂ (fun v => f (tw b₁ u) v))
    _ = ∑ u, wt u * ∑ v, wt v * f u v := sum_tw b₁ (fun u => ∑ v, wt v * f u v)

/-- factor `l` of the `k`-th term -/
noncomputable def cc (b₁ b₂ : Bool) (k l : ℕ) (a b : α) : ℝ≥0∞ :=
  if l < k then cA (tw b₁ a) (tw b₂ b) else cT (tw b₁ a) (tw b₂ b)

theorem lint_term (b₁ b₂ : Bool) (k : ℕ) :
    ∫⁻ p, term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k
        ∂((Measure.infinitePi fun _ : ℕ => μ0).prod (Measure.infinitePi fun _ : ℕ => μ0)) =
      A0 ^ k * T0 := by
  have e : (fun p : (ℕ → α) × (ℕ → α) => term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k) =
      fun p => ∏ l ∈ Finset.range (k + 1), cc b₁ b₂ k l (p.1 l) (p.2 l) := by
    funext p
    rw [Finset.prod_range_succ, term]
    congr 1
    · exact Finset.prod_congr rfl fun l hl => by simp [cc, Finset.mem_range.mp hl]
    · simp [cc]
  rw [e, lintegral_prod_pairs, Finset.prod_range_succ]
  have h1 : ∀ l ∈ Finset.range k, ∫⁻ a, ∫⁻ b, cc b₁ b₂ k l a b ∂μ0 ∂μ0 = A0 := fun l hl => by
    simp only [cc, if_pos (Finset.mem_range.mp hl)]
    exact lint_tw b₁ b₂ cA
  have h2 : ∫⁻ a, ∫⁻ b, cc b₁ b₂ k k a b ∂μ0 ∂μ0 = T0 := by
    simp only [cc, if_neg (lt_irrefl k)]
    exact lint_tw b₁ b₂ cT
  rw [Finset.prod_congr rfl h1, h2, Finset.prod_const, Finset.card_range]

theorem term_meas (b₁ b₂ : Bool) (k : ℕ) :
    Measurable fun p : (ℕ → α) × (ℕ → α) =>
      term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k :=
  (Finset.measurable_prod _ fun l _ => meas_pair l (fun a b => cA (tw b₁ a) (tw b₂ b))).mul
    (meas_pair k (fun a b => cT (tw b₁ a) (tw b₂ b)))

theorem geom (A T : ℝ≥0∞) : ∑' k : ℕ, A ^ k * T = T * (1 - A)⁻¹ := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

theorem E_le : expectedMeetingTime S S ≤ T0 * (1 - A0)⁻¹ := by
  have hb : ∀ b₁ b₂ : Bool,
      ∫⁻ p, meetingTime (fun t => orient b₁ * rpath p.1 t) (fun t => 2 + orient b₂ * rpath p.2 t)
        ∂((Measure.infinitePi fun _ : ℕ => μ0).prod (Measure.infinitePi fun _ : ℕ => μ0)) ≤
        T0 * (1 - A0)⁻¹ := by
    intro b₁ b₂
    calc _ ≤ ∫⁻ p, ∑' k, term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k
            ∂((Measure.infinitePi fun _ : ℕ => μ0).prod (Measure.infinitePi fun _ : ℕ => μ0)) :=
          lintegral_mono fun p => pointwise b₁ b₂ p
      _ = ∑' k, ∫⁻ p, term (fun l => tw b₁ (p.1 l)) (fun l => tw b₂ (p.2 l)) k
            ∂((Measure.infinitePi fun _ : ℕ => μ0).prod (Measure.infinitePi fun _ : ℕ => μ0)) :=
          lintegral_tsum fun k => (term_meas b₁ b₂ k).aemeasurable
      _ = ∑' k : ℕ, A0 ^ k * T0 := by simp only [lint_term]
      _ = T0 * (1 - A0)⁻¹ := geom A0 T0
  unfold expectedMeetingTime
  calc (1 / 4 : ℝ≥0∞) * ∑ b₁ : Bool, ∑ b₂ : Bool, _ ≤
        (1 / 4 : ℝ≥0∞) * ∑ b₁ : Bool, ∑ b₂ : Bool, T0 * (1 - A0)⁻¹ := by
        gcongr with b₁ _ b₂ _
        exact hb b₁ b₂
    _ = T0 * (1 - A0)⁻¹ := by
        simp only [Fintype.sum_bool]
        rw [show T0 * (1 - A0)⁻¹ + T0 * (1 - A0)⁻¹ + (T0 * (1 - A0)⁻¹ + T0 * (1 - A0)⁻¹) =
          4 * (T0 * (1 - A0)⁻¹) by ring, ← mul_assoc, one_div,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ## The numbers -/

theorem T0_eq : T0 = ((16982956 : ℕ) : ℝ≥0∞) * Dinv ^ 2 := by
  have h : ∀ u v, wt u * (wt v * cT u v) = ((Wt u * Wt v * tau u v : ℕ) : ℝ≥0∞) * Dinv ^ 2 := by
    intro u v; simp only [wt, cT]; push_cast; ring
  simp only [T0, Finset.mul_sum, h, ← Finset.sum_mul]
  rw [← sum_NT]
  simp only [Nat.cast_sum]

theorem A0_eq : A0 = ((26766 : ℕ) : ℝ≥0∞) * Dinv ^ 2 := by
  have h : ∀ u v, wt u * (wt v * cA u v) = ((Wt u * Wt v * aa u v : ℕ) : ℝ≥0∞) * Dinv ^ 2 := by
    intro u v; simp only [wt, cA]; push_cast; ring
  simp only [A0, Finset.mul_sum, h, ← Finset.sum_mul]
  rw [← sum_NA]
  simp only [Nat.cast_sum]

theorem final_core :
    ((16982956 : ℕ) : ℝ) * (1 / 2004) ^ 2 * (1 - ((26766 : ℕ) : ℝ) * (1 / 2004) ^ 2)⁻¹ < 42574 / 10000 :=
  by norm_num

theorem V_lt : T0 * (1 - A0)⁻¹ < 42574 / 10000 := by
  have hD : Dinv ^ 2 = ENNReal.ofReal ((1 / 2004) ^ 2) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2004), Dinv, one_div,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2004)]
    norm_num
  have e1 : T0 = ENNReal.ofReal (((16982956 : ℕ) : ℝ) * (1 / 2004) ^ 2) := by
    rw [T0_eq, hD, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((16982956 : ℕ) : ℝ)),
      ENNReal.ofReal_natCast]
  have e2 : 1 - A0 = ENNReal.ofReal (1 - ((26766 : ℕ) : ℝ) * (1 / 2004) ^ 2) := by
    rw [A0_eq, hD, ENNReal.ofReal_sub 1 (by positivity : (0 : ℝ) ≤ ((26766 : ℕ) : ℝ) * (1 / 2004) ^ 2),
      ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((26766 : ℕ) : ℝ)),
      ENNReal.ofReal_natCast]
  have hpos : (0 : ℝ) < 1 - ((26766 : ℕ) : ℝ) * (1 / 2004) ^ 2 := by norm_num
  rw [e1, e2, ← ENNReal.ofReal_inv_of_pos hpos,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((16982956 : ℕ) : ℝ) * (1 / 2004) ^ 2)]
  have e3 : (42574 / 10000 : ℝ≥0∞) = ENNReal.ofReal (42574 / 10000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10000)]
    norm_num
  rw [e3, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 42574 / 10000)]
  exact final_core

end RdvCert

-- The statement below is the platform statement verbatim.
open SymmetricRendezvousLine in
theorem solution :
    symmetricRendezvousValue < (42574 / 10000 : ENNReal) := by
  exact lt_of_le_of_lt (iInf_le _ RdvCert.S) (RdvCert.E_le.trans_lt RdvCert.V_lt)
