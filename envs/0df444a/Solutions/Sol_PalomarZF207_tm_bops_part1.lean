-- Prove2me | solution 1 for PalomarZF207.tm_bops_part1
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:46:39.965713+00:00
-- url     : https://prove2.me/submissions/a0a958c0-cdd3-47e2-9b4a-7d2a95faa471

import Definitions.Def_palomar_zf207_tm_check

open PalomarZF207TMCheck

private theorem chkBOps_append : ∀ ops1 ops2 p1 p2 p3,
    chkBOps p1 ops1 = some p2 → chkBOps p2 ops2 = some p3 → chkBOps p1 (ops1 ++ ops2) = some p3
  | [], _, _, _, _, h1, h2 => by injection h1 with h; subst h; exact h2
  | op :: ops1, ops2, p1, p2, p3, h1, h2 => by
    simp only [List.cons_append]
    unfold chkBOps at h1 ⊢
    cases hb : chkBOp p1 op with
    | none => rw [hb] at h1; contradiction
    | some pm => rw [hb] at h1; dsimp only at h1 ⊢; exact chkBOps_append ops1 ops2 pm p2 p3 h1 h2

private theorem chkBOpsTo_of_append {ops1 ops2 : List BOp} {p1 p2 p3 : List Bool}
    (h1 : chkBOps p1 ops1 = some p2) (h2 : chkBOpsTo p2 ops2 p3 = true) :
    chkBOpsTo p1 (ops1 ++ ops2) p3 = true := by
  unfold chkBOpsTo at h2 ⊢
  cases h : chkBOps p2 ops2 with
  | none => rw [h] at h2; contradiction
  | some p' => rw [h] at h2; rw [chkBOps_append ops1 ops2 p1 p2 p' h1 h]; exact h2

set_option maxRecDepth 8192 in
private theorem c0 : chkBOpsTo (pB 149) bopsChunk0 (pB 1356437) = true := rfl

private def c1a : List BOp := [.popPair4, .pushR3, .copy3_4, .pushR3, .copy3_8]
private def c1b : List BOp := [.popPair4, .pushR3, .copy3_5, .pushR3, .copy3_8]
private def c1c : List BOp := [.popPair4, .popPair4, .popPair4, .pushR3, .copy3_8]

set_option maxRecDepth 8192 in
private theorem c1_a : chkBOps (pB 1356437) c1a = some (pB 7123605) := rfl
set_option maxRecDepth 8192 in
private theorem c1_b : chkBOps (pB 7123605) c1b = some (pB 27046549) := rfl
set_option maxRecDepth 8192 in
private theorem c1_c : chkBOpsTo (pB 27046549) c1c (pB 56406677) = true := rfl

private theorem c1 : chkBOpsTo (pB 1356437) bopsChunk1 (pB 56406677) = true :=
  chkBOpsTo_of_append c1_a (chkBOpsTo_of_append c1_b c1_c)

private def c2a : List BOp := [.pushR3, .copy3_4, .popPair4, .inc3 2, .pushR3]
private def c2b : List BOp := [.inc3 1, .popPair4, .pushR3, .copy3_4, .popPair4]
private def c2c : List BOp := [.inc3 2, .pushR3, .inc3 1, .popPair4, .pushR3]

set_option maxRecDepth 8192 in
private theorem c2_a : chkBOps (pB 56406677) c2a = some (pB 81572501) := rfl
set_option maxRecDepth 8192 in
private theorem c2_b : chkBOps (pB 81572501) c2b = some (pB 450671253) := rfl
set_option maxRecDepth 8192 in
private theorem c2_c : chkBOpsTo (pB 450671253) c2c (pB 98349717) = true := rfl

private theorem c2 : chkBOpsTo (pB 56406677) bopsChunk2 (pB 98349717) = true :=
  chkBOpsTo_of_append c2_a (chkBOpsTo_of_append c2_b c2_c)

set_option maxRecDepth 8192 in
private theorem c3 : chkBOpsTo (pB 98349717) bopsChunk3 (pB 192721557) = true := rfl

theorem solution :
    chkBOpsTo (pB 149) bopsChunk0 (pB 1356437) = true ∧
    chkBOpsTo (pB 1356437) bopsChunk1 (pB 56406677) = true ∧
    chkBOpsTo (pB 56406677) bopsChunk2 (pB 98349717) = true ∧
    chkBOpsTo (pB 98349717) bopsChunk3 (pB 192721557) = true :=
  ⟨c0, c1, c2, c3⟩
