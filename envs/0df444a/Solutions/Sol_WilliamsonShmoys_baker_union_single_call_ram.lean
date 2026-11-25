-- Prove2me | solution 1 for WilliamsonShmoys.baker_union_single_call_ram
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:30:09.815512+00:00
-- url     : https://prove2.me/submissions/29992499-a964-4ad6-9e07-93cd0dded1eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_RAMSandboxOdd
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_ram_baker_seg_input
import Theorems.Thm_WilliamsonShmoys_ram_baker_seg_registers
import Theorems.Thm_WilliamsonShmoys_ram_baker_seg_levels
import Theorems.Thm_WilliamsonShmoys_ram_baker_seg_union
import Theorems.Thm_WilliamsonShmoys_ram_baker_seg_output
import Theorems.Thm_WilliamsonShmoys_sandbox_odd_simulation
import Theorems.Thm_WilliamsonShmoys_treewidth_of_equiv_hom
import Theorems.Thm_WilliamsonShmoys_union_graph_iso
import Theorems.Thm_WilliamsonShmoys_baker_union_output_bound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace FIN
open WilliamsonShmoys PlanarRAMInstruction

def sbList (base T ONE exit : ℕ) : List PlanarRAMInstruction → ℕ → List PlanarRAMInstruction
  | [], _ => []
  | ins :: rest, k =>
    (sandboxTriple base T ONE exit k ins).1 :: (sandboxTriple base T ONE exit k ins).2.1 ::
      (sandboxTriple base T ONE exit k ins).2.2 :: sbList base T ONE exit rest (k + 1)

lemma sbList_length (base T ONE exit : ℕ) :
    ∀ (q : List PlanarRAMInstruction) (k : ℕ), (sbList base T ONE exit q k).length = 3 * q.length := by
  intro q
  induction q with
  | nil => intro k; rfl
  | cons ins rest ih => intro k; simp only [sbList, List.length_cons, ih]; ring

lemma sbList_get (base T ONE exit : ℕ) :
    ∀ (q : List PlanarRAMInstruction) (k i : ℕ) (ins : PlanarRAMInstruction), q[i]? = some ins →
      (sbList base T ONE exit q k)[3 * i]? = some (sandboxTriple base T ONE exit (k + i) ins).1 ∧
      (sbList base T ONE exit q k)[3 * i + 1]? = some (sandboxTriple base T ONE exit (k + i) ins).2.1 ∧
      (sbList base T ONE exit q k)[3 * i + 2]? = some (sandboxTriple base T ONE exit (k + i) ins).2.2 := by
  intro q
  induction q with
  | nil => intro k i ins h; simp at h
  | cons a rest ih =>
    intro k i ins h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [sbList]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) i ins h
      rw [show k + (i + 1) = k + 1 + i by ring]
      refine ⟨?_, ?_, ?_⟩
      · rw [show 3 * (i + 1) = 3 * i + 3 by ring]; simpa [sbList] using h1
      · rw [show 3 * (i + 1) + 1 = 3 * i + 1 + 3 by ring]; simpa [sbList] using h2
      · rw [show 3 * (i + 1) + 2 = 3 * i + 2 + 3 by ring]; simpa [sbList] using h3

lemma codeAt_head (C rest : List PlanarRAMInstruction) : CodeAt (C ++ rest) 0 C := by
  intro i hi
  rw [Nat.zero_add, List.getElem?_append_left hi]

lemma codeAt_shift (A p : List PlanarRAMInstruction) (b : ℕ) (C : List PlanarRAMInstruction) (h : CodeAt p b C) :
    CodeAt (A ++ p) (A.length + b) C := by
  intro i hi
  rw [show A.length + b + i = A.length + (b + i) by ring, List.getElem?_append_right (by omega)]
  rw [show A.length + (b + i) - A.length = b + i by omega]
  exact h i hi

lemma sandboxed_at (A rest q : List PlanarRAMInstruction) (T ONE exit : ℕ) :
    SandboxedOddAt (A ++ (sbList A.length T ONE exit q 0 ++ rest)) q A.length T ONE exit := by
  intro i ins h
  obtain ⟨h1, h2, h3⟩ := sbList_get A.length T ONE exit q 0 i ins h
  have hlen := sbList_length A.length T ONE exit q 0
  have hi : i < q.length := by
    by_contra hc; push_neg at hc; rw [List.getElem?_eq_none hc] at h; simp at h
  rw [Nat.zero_add] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), show A.length + 3 * i - A.length = 3 * i by omega,
      List.getElem?_append_left (by omega), h1]
  · rw [List.getElem?_append_right (by omega), show A.length + 3 * i + 1 - A.length = 3 * i + 1 by omega,
      List.getElem?_append_left (by omega), h2]
  · rw [List.getElem?_append_right (by omega), show A.length + 3 * i + 2 - A.length = 3 * i + 2 by omega,
      List.getElem?_append_left (by omega), h3]


def P1 : List PlanarRAMInstruction := [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7]
def P2 : List PlanarRAMInstruction := [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (12 + 7) (12 + 4), natAdd 2 2 0, natAdd 3 3 4, jump (12 + 3)]
def P3 : List PlanarRAMInstruction := [natConst 5 8, natConst 6 32, natBranch 2 5 (19 + 9) (19 + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (19 + 2)]
def P4 : List PlanarRAMInstruction := [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (28 + 7) (28 + 10), natSub 8 8 10, natAdd 9 9 11, jump (28 + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 14) (28 + 17), natSub 8 8 10, natAdd 9 9 11, jump (28 + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 21) (28 + 24), natSub 8 8 10, natAdd 9 9 11, jump (28 + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 28) (28 + 31), natSub 8 8 10, natAdd 9 9 11, jump (28 + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 35) (28 + 38), natSub 8 8 10, natAdd 9 9 11, jump (28 + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 42) (28 + 45), natSub 8 8 10, natAdd 9 9 11, jump (28 + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12]
def G0 : List PlanarRAMInstruction := [natConst 10 2, natConst 11 1, natConst 12 0]
def P5 : List PlanarRAMInstruction := [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (79 + 12) (79 + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (79 + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0]
def SQ : List PlanarRAMInstruction := [natAdd 13 0 12, natAdd 20 0 0, natConst 19 2, natAdd 31 0 11, natConst 1 0, natConst 3 0, natBranch 0 3 (95 + 10) (95 + 7), natAdd 1 1 0, natAdd 3 3 11, jump (95 + 6), natAdd 28 1 1, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 5 20 20, natAdd 5 5 5, natAdd 5 5 5, natAdd 28 28 5, natConst 5 48, natAdd 28 28 5, natConst 2 36, natAdd 3 20 10, natConst 4 0, natBranch 0 4 (95 + 28) (95 + 24), natStore 2 12, natAdd 2 2 3, natAdd 4 4 11, jump (95 + 23)]
def P6 : List PlanarRAMInstruction := [natConst 29 0, natAdd 30 28 12, natBranch 13 29 (123 + 58) (123 + 3), natLoad 22 30, natBranch 22 12 (123 + 5) (123 + 55), natStore 30 11, natConst 15 1, natConst 14 2, natConst 23 0, natConst 24 0, natConst 25 36, natConst 26 36, natAdd 27 28 12, natBranch 13 24 (123 + 8 + 5 + 27) (123 + 8 + 5 + 1), natLoad 22 27, natBranch 22 15 (123 + 8 + 5 + 3) (123 + 8 + 5 + 22), natBranch 15 22 (123 + 8 + 5 + 4) (123 + 8 + 5 + 22), natConst 16 0, natAdd 17 25 12, natAdd 18 26 12, natAdd 21 28 12, natBranch 13 16 (123 + 8 + 5 + 8 + 14) (123 + 8 + 5 + 8 + 1), natLoad 22 17, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 3), natLoad 22 18, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 9), natLoad 22 21, natBranch 22 12 (123 + 8 + 5 + 8 + 7) (123 + 8 + 5 + 8 + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump (123 + 8 + 5 + 8), natAdd 24 24 11, natAdd 25 25 20, natAdd 26 26 19, natAdd 27 27 19, jump (123 + 8 + 5), natBranch 11 23 (123 + 8 + 33) (123 + 8 + 36), natAdd 15 15 11, natAdd 14 14 11, jump (123 + 8), natConst 24 0, natAdd 27 28 12, natBranch 13 24 (123 + 44 + 11) (123 + 44 + 3), natLoad 22 27, natBranch 22 12 (123 + 44 + 8) (123 + 44 + 5), natBranch 22 31 (123 + 44 + 6) (123 + 44 + 8), natAdd 22 22 31, natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (123 + 44 + 2), natAdd 29 29 11, natAdd 30 30 19, jump (123 + 2)]
def G1 : List PlanarRAMInstruction := [natAdd 16 34 12, natAdd 17 13 10]
def P7a : List PlanarRAMInstruction := [natConst 24 0, natAdd 27 28 12, natBranch 13 24 (183 + 12) (183 + 3), natLoad 22 27, natSub 22 22 17, natBranch 16 22 (183 + 6) (183 + 8), natSub 22 22 16, jump (183 + 5), natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (183 + 2)]
def G2 : List PlanarRAMInstruction := [natAdd 2 1 1, natConst 5 97, natAdd 2 2 5]
def P8 : List PlanarRAMInstruction := [natConst 0 1, natConst 4 2, natConst 6 0, realZero 0, natBranch 2 0 (198 + 9) (198 + 5), natStore 0 6, realStore 0 0, natAdd 0 0 4, jump (198 + 4)]
def P7b : List PlanarRAMInstruction := [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 26 32 32, natAdd 30 28 26, natConst 8 0, natConst 6 0, natBranch 34 6 (207 + 11) (207 + 8), natAdd 8 8 32, natAdd 6 6 2, jump (207 + 7), natAdd 10 8 8, natSub 24 10 26, natConst 10 1, natStore 10 8, natAdd 8 34 34, natAdd 8 8 34, natConst 10 3, natStore 10 8, natConst 6 0, natConst 18 5, natConst 22 1, natBranch 34 6 (207 + 54) (207 + 23), natAdd 12 28 0, natConst 20 32, natConst 16 36, natBranch 30 12 (207 + 51) (207 + 27), natLoad 8 12, natBranch 8 6 (207 + 29) (207 + 30), natBranch 6 8 (207 + 44) (207 + 30), realLoad 0 20, realStore 22 0, natAdd 14 28 0, natBranch 30 14 (207 + 46) (207 + 34), natLoad 10 14, natBranch 10 6 (207 + 36) (207 + 37), natBranch 6 10 (207 + 40) (207 + 37), natLoad 10 16, natBranch 2 10 (207 + 39) (207 + 40), natStore 18 2, natAdd 14 14 4, natAdd 16 16 4, natAdd 18 18 4, jump (207 + 33), natAdd 16 16 26, natAdd 18 18 26, natAdd 18 18 24, natAdd 12 12 4, natAdd 20 20 4, natAdd 22 22 4, jump (207 + 26), natAdd 18 18 26, natAdd 6 6 2, jump (207 + 22)]
def G3 : List PlanarRAMInstruction := [natConst 0 0, natConst 4 0, natConst 6 0, natConst 8 1, natBranch 32 6 (261 + 8) (261 + 5), natAdd 4 4 32, natAdd 6 6 8, jump (261 + 4), natAdd 28 4 4, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 6 32 32, natAdd 6 6 6, natAdd 6 6 6, natAdd 6 6 6, natAdd 28 28 6, natConst 6 48, natAdd 28 28 6, natAdd 40 32 0, natAdd 42 28 0, natConst 2 1]
def Q10a (X : ℕ) : List PlanarRAMInstruction := [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 24 32 32, natAdd 18 28 24, natConst 26 0, natConst 6 0, natBranch 34 6 (X + 11) (X + 8), natAdd 26 26 32, natAdd 6 6 2, jump (X + 7), natConst 30 0, natConst 6 0, natBranch 26 6 (X + 17) (X + 14), natAdd 30 30 26, natAdd 6 6 2, jump (X + 13), natAdd 30 30 30, natConst 8 5, natAdd 14 30 8, natConst 6 0, natConst 20 0, natAdd 22 14 0, realZero 4, natBranch 34 6 (X + 50) (X + 25), realZero 2, natAdd 10 28 0, natConst 16 32, natAdd 12 14 0, natBranch 18 10 (X + 41) (X + 30), natLoad 8 12, natBranch 2 8 (X + 32) (X + 37), natLoad 8 10, natBranch 8 6 (X + 34) (X + 35), natBranch 6 8 (X + 37) (X + 35), realLoad 0 16, realAdd 2 2 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 16 16 4, jump (X + 29), natBranch 6 0 (X + 43) (X + 42), realBranch 2 4 (X + 47) (X + 43), realZero 4, realAdd 4 4 2, natAdd 20 6 0, natAdd 22 14 0, natAdd 14 14 24, natAdd 6 6 2, jump (X + 24)]
def G4 (X : ℕ) : List PlanarRAMInstruction := [natConst 0 0, natAdd 32 40 0, natAdd 28 42 0]
def Q10b (X : ℕ) : List PlanarRAMInstruction := [natConst 0 0, natConst 2 1, natConst 4 2, natConst 36 16, natAdd 24 32 32, natAdd 18 28 24, natConst 30 0, natConst 6 0, natBranch 32 6 (X + 53 + 12) (X + 53 + 9), natAdd 30 30 32, natAdd 6 6 2, jump (X + 53 + 8), natAdd 26 30 0, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natConst 8 32, natAdd 38 30 8, natAdd 10 28 0, natAdd 12 22 0, natBranch 18 10 (X + 53 + 34) (X + 53 + 22), natLoad 8 12, natBranch 2 8 (X + 53 + 24) (X + 53 + 29), natLoad 8 10, natBranch 8 20 (X + 53 + 26) (X + 53 + 27), natBranch 20 8 (X + 53 + 29) (X + 53 + 27), natStore 38 2, jump (X + 53 + 30), natStore 38 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 38 38 36, jump (X + 53 + 21), natAdd 0 26 32, natAdd 0 0 2, natAdd 8 30 36, natStore 8 8, natAdd 1 0 0, natAdd 1 1 1, natAdd 1 1 1, natAdd 1 1 1, natLoad 1 1, natBranch 0 1 (X + 53 + 48) (X + 53 + 44), natStore 0 1, natConst 1 1, natSub 0 0 1, jump (X + 53 + 38)]
def HL (X : ℕ) : List PlanarRAMInstruction := [halt]
@[simp] lemma P1_len : P1.length = 12 := rfl
@[simp] lemma P2_len : P2.length = 7 := rfl
@[simp] lemma P3_len : P3.length = 9 := rfl
@[simp] lemma P4_len : P4.length = 48 := rfl
@[simp] lemma G0_len : G0.length = 3 := rfl
@[simp] lemma P5_len : P5.length = 16 := rfl
@[simp] lemma SQ_len : SQ.length = 28 := rfl
@[simp] lemma P6_len : P6.length = 58 := rfl
@[simp] lemma G1_len : G1.length = 2 := rfl
@[simp] lemma P7a_len : P7a.length = 12 := rfl
@[simp] lemma G2_len : G2.length = 3 := rfl
@[simp] lemma P8_len : P8.length = 9 := rfl
@[simp] lemma P7b_len : P7b.length = 54 := rfl
@[simp] lemma G3_len : G3.length = 22 := rfl
@[simp] lemma Q10a_len (X : ℕ) : (Q10a X).length = 50 := rfl
@[simp] lemma G4_len (X : ℕ) : (G4 X).length = 3 := rfl
@[simp] lemma Q10b_len (X : ℕ) : (Q10b X).length = 48 := rfl
@[simp] lemma HL_len (X : ℕ) : (HL X).length = 1 := rfl

def L0 : List PlanarRAMInstruction := P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3
def L1 (X : ℕ) : List PlanarRAMInstruction := Q10a X ++ G4 X ++ Q10b X ++ HL X
def prog (solver : List PlanarRAMInstruction) : List PlanarRAMInstruction :=
  L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length))

lemma L0_length : L0.length = 283 := by simp only [L0, List.length_append, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]

lemma code_P1 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 0 P1 := by
  have h := codeAt_shift ([]) (P1 ++ ((P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P1 (codeAt_head _ _)
  rw [show ([] : List PlanarRAMInstruction).length + 0 = 0 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = ([]) ++ (P1 ++ ((P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P2 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 12 P2 := by
  have h := codeAt_shift (P1) (P2 ++ ((P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P2 (codeAt_head _ _)
  rw [show (P1 : List PlanarRAMInstruction).length + 0 = 12 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1) ++ (P2 ++ ((P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P3 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 19 P3 := by
  have h := codeAt_shift (P1 ++ P2) (P3 ++ ((P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P3 (codeAt_head _ _)
  rw [show (P1 ++ P2 : List PlanarRAMInstruction).length + 0 = 19 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2) ++ (P3 ++ ((P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P4 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 28 P4 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3) (P4 ++ ((G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P4 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 : List PlanarRAMInstruction).length + 0 = 28 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3) ++ (P4 ++ ((G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_G0 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 76 G0 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4) (G0 ++ ((P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 G0 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 : List PlanarRAMInstruction).length + 0 = 76 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4) ++ (G0 ++ ((P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P5 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 79 P5 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0) (P5 ++ ((SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P5 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 : List PlanarRAMInstruction).length + 0 = 79 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0) ++ (P5 ++ ((SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_SQ (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 95 SQ := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5) (SQ ++ ((P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 SQ (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 : List PlanarRAMInstruction).length + 0 = 95 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5) ++ (SQ ++ ((P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P6 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 123 P6 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ) (P6 ++ ((G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P6 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ : List PlanarRAMInstruction).length + 0 = 123 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ) ++ (P6 ++ ((G1 ++ P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_G1 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 181 G1 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6) (G1 ++ ((P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 G1 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 : List PlanarRAMInstruction).length + 0 = 181 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6) ++ (G1 ++ ((P7a ++ G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P7a (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 183 P7a := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1) (P7a ++ ((G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P7a (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 : List PlanarRAMInstruction).length + 0 = 183 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1) ++ (P7a ++ ((G2 ++ P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_G2 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 195 G2 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a) (G2 ++ ((P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 G2 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a : List PlanarRAMInstruction).length + 0 = 195 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a) ++ (G2 ++ ((P8 ++ P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P8 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 198 P8 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2) (P8 ++ ((P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P8 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 : List PlanarRAMInstruction).length + 0 = 198 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2) ++ (P8 ++ ((P7b ++ G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_P7b (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 207 P7b := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8) (P7b ++ ((G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 P7b (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 : List PlanarRAMInstruction).length + 0 = 207 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8) ++ (P7b ++ ((G3) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_G3 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) 261 G3 := by
  have h := codeAt_shift (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b) (G3 ++ (([]) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) 0 G3 (codeAt_head _ _)
  rw [show (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b : List PlanarRAMInstruction).length + 0 = 261 by simp only [List.length_append, List.length_nil, P1_len, P2_len, P3_len, P4_len, G0_len, P5_len, SQ_len, P6_len, G1_len, P7a_len, G2_len, P8_len, P7b_len, G3_len]] at h
  have hp : prog solver = (P1 ++ P2 ++ P3 ++ P4 ++ G0 ++ P5 ++ SQ ++ P6 ++ G1 ++ P7a ++ G2 ++ P8 ++ P7b) ++ (G3 ++ (([]) ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ L1 (283 + 3 * solver.length)))) := by
    simp only [prog, L0, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_Q10a (solver : List PlanarRAMInstruction) : CodeAt (prog solver) (283 + 3 * solver.length + 0) (Q10a (283 + 3 * solver.length)) := by
  have h := codeAt_shift (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ ([])))
    (Q10a (283 + 3 * solver.length) ++ (G4 (283 + 3 * solver.length) ++ Q10b (283 + 3 * solver.length) ++ HL (283 + 3 * solver.length))) 0 _ (codeAt_head _ _)
  have hl : (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ ([]))).length + 0 = 283 + 3 * solver.length + 0 := by
    simp only [List.length_append, sbList_length, Nat.add_zero, List.length_nil, L0_length, Q10a_len, G4_len, Q10b_len, HL_len]
    try omega
  rw [hl] at h
  have hp : prog solver = (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ ([]))) ++
      (Q10a (283 + 3 * solver.length) ++ (G4 (283 + 3 * solver.length) ++ Q10b (283 + 3 * solver.length) ++ HL (283 + 3 * solver.length))) := by
    simp only [prog, L1, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_G4 (solver : List PlanarRAMInstruction) : CodeAt (prog solver) (283 + 3 * solver.length + 50) (G4 (283 + 3 * solver.length)) := by
  have h := codeAt_shift (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length))))
    (G4 (283 + 3 * solver.length) ++ (Q10b (283 + 3 * solver.length) ++ HL (283 + 3 * solver.length))) 0 _ (codeAt_head _ _)
  have hl : (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length)))).length + 0 = 283 + 3 * solver.length + 50 := by
    simp only [List.length_append, sbList_length, Nat.add_zero, List.length_nil, L0_length, Q10a_len, G4_len, Q10b_len, HL_len]
    try omega
  rw [hl] at h
  have hp : prog solver = (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length)))) ++
      (G4 (283 + 3 * solver.length) ++ (Q10b (283 + 3 * solver.length) ++ HL (283 + 3 * solver.length))) := by
    simp only [prog, L1, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_Q10b (solver : List PlanarRAMInstruction) : CodeAt (prog solver) (283 + 3 * solver.length + 53) (Q10b (283 + 3 * solver.length)) := by
  have h := codeAt_shift (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length))))
    (Q10b (283 + 3 * solver.length) ++ (HL (283 + 3 * solver.length))) 0 _ (codeAt_head _ _)
  have hl : (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length)))).length + 0 = 283 + 3 * solver.length + 53 := by
    simp only [List.length_append, sbList_length, Nat.add_zero, List.length_nil, L0_length, Q10a_len, G4_len, Q10b_len, HL_len]
    try omega
  rw [hl] at h
  have hp : prog solver = (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length)))) ++
      (Q10b (283 + 3 * solver.length) ++ (HL (283 + 3 * solver.length))) := by
    simp only [prog, L1, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h
lemma code_HL (solver : List PlanarRAMInstruction) : CodeAt (prog solver) (283 + 3 * solver.length + 101) (HL (283 + 3 * solver.length)) := by
  have h := codeAt_shift (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length) ++ Q10b (283 + 3 * solver.length))))
    (HL (283 + 3 * solver.length) ++ ([])) 0 _ (codeAt_head _ _)
  have hl : (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length) ++ Q10b (283 + 3 * solver.length)))).length + 0 = 283 + 3 * solver.length + 101 := by
    simp only [List.length_append, sbList_length, Nat.add_zero, List.length_nil, L0_length, Q10a_len, G4_len, Q10b_len, HL_len]
    try omega
  rw [hl] at h
  have hp : prog solver = (L0 ++ (sbList 283 0 2 (283 + 3 * solver.length) solver 0 ++ (Q10a (283 + 3 * solver.length) ++ G4 (283 + 3 * solver.length) ++ Q10b (283 + 3 * solver.length)))) ++
      (HL (283 + 3 * solver.length) ++ ([])) := by
    simp only [prog, L1, List.append_assoc, List.nil_append, List.append_nil]
  rw [hp]; exact h

lemma sandboxed (solver : List PlanarRAMInstruction) :
    SandboxedOddAt (prog solver) solver 283 0 2 (283 + 3 * solver.length) := by
  have h := sandboxed_at L0 (L1 (283 + 3 * solver.length)) solver 0 2 (283 + 3 * solver.length)
  rw [L0_length] at h
  exact h

open scoped BigOperators

lemma run_add (p : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun p s (a + b) = planarRAMRun p (planarRAMRun p s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma time_total (n k t C₀ d₀ τ1 τ2 τ3 τ4 τs τ6 : ℕ) (hk : 0 < k)
    (hτ1 : τ1 ≤ 800 * k + 8 * (n + 1) * (n + 1) + 900) (hτ2 : τ2 ≤ 9 * n + 24)
    (hτ3 : τ3 ≤ 40 * (n + 1) * (n + 1) + 260) (hτ4 : τ4 ≤ ((11 * n + 20) * n + 12) * k + 4 * n + 50)
    (hτs : τs ≤ 3 * t + 1) (hτ6 : τ6 ≤ (16 * n + 24) * k + 26 * n + 52)
    (ht : t + 1 ≤ C₀ * 2 ^ (d₀ * (3 * k)) * (k * n + 1) ^ 2) :
    τ1 + τ2 + τ3 + τ4 + τs + τ6 + 1 ≤ (3000 + 3 * C₀) * 2 ^ ((3 * d₀ + 2) * k) * (n + 1) ^ 2 := by
  have hkQ : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hD1 : 1 ≤ 2 ^ (d₀ * (3 * k)) := Nat.one_le_two_pow
  have hpow : 2 ^ ((3 * d₀ + 2) * k) = 2 ^ (d₀ * (3 * k)) * 2 ^ k * 2 ^ k := by
    rw [← pow_add, ← pow_add]; ring_nf
  have hsq : (k * n + 1) ^ 2 ≤ k * k * (n + 1) ^ 2 := by
    have h1 : k * n + 1 ≤ k * (n + 1) := by nlinarith
    have := Nat.pow_le_pow_left h1 2
    calc (k * n + 1) ^ 2 ≤ (k * (n + 1)) ^ 2 := this
      _ = k * k * (n + 1) ^ 2 := by ring
  have hrest : τ1 + τ2 + τ3 + τ4 + τ6 ≤ 2245 * k * (n + 1) ^ 2 := by nlinarith
  set P := (n + 1) ^ 2 with hP
  set Q := 2 ^ k with hQ
  set D := 2 ^ (d₀ * (3 * k)) with hD
  rw [hpow]
  have h1 : 2245 * k * P ≤ 2245 * (D * Q * Q) * P := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left
    calc k ≤ Q := hkQ
      _ = 1 * 1 * Q := by ring
      _ ≤ D * Q * Q := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul hD1; exact Nat.one_le_two_pow
  have h2 : 3 * (t + 1) ≤ 3 * C₀ * (D * Q * Q) * P := by
    have := Nat.mul_le_mul_left 3 ht
    calc 3 * (t + 1) ≤ 3 * (C₀ * D * (k * n + 1) ^ 2) := this
      _ ≤ 3 * (C₀ * D * (k * k * P)) := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact hsq
      _ ≤ 3 * (C₀ * D * (Q * Q * P)) := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul hkQ hkQ
      _ = 3 * C₀ * (D * Q * Q) * P := by ring
  have e3 : (3000 + 3 * C₀) * (D * Q * Q) * P = 3000 * (D * Q * Q) * P + 3 * C₀ * (D * Q * Q) * P := by ring
  have e4 : 2245 * (D * Q * Q) * P ≤ 3000 * (D * Q * Q) * P := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
  omega

lemma diag_ne (n v w v' : ℕ) (hv : v < n) (hw : w < n) (hv' : v' < n) (hvw : v ≠ w) :
    36 + 2 * v * n + 2 * w ≠ 36 + v' * (2 * n + 2) := by
  intro h
  have h1 : v * n + w = v' * n + v' := by
    have e1 : 2 * v * n = 2 * (v * n) := by ring
    have e2 : v' * (2 * n + 2) = 2 * (v' * n + v') := by ring
    omega
  have hn : 0 < n := by omega
  have q1 : (v * n + w) / n = v := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hw, Nat.zero_add]
  have q2 : (v' * n + v') / n = v' := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hv', Nat.zero_add]
  have r1 : (v * n + w) % n = w := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
  have r2 : (v' * n + v') % n = v' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv']
  rw [h1] at q1 r1
  omega

end FIN

open FIN

set_option maxHeartbeats 16000000 in
theorem solution
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) (hC₀ : 0 < C₀) (hd₀ : 0 < d₀)
    (hsolver : ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
      let G := SimpleGraph.fromRel (fun u v => edge u v = true)
      RobertsonSeymour1986.GM5.TreewidthLE G w →
      ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * w) * (n + 1) ^ 2 ∧
        let result := WilliamsonShmoys.planarRAMRun solver (WilliamsonShmoys.planarRAMInput n w edge weight) t
        solver[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
        (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
        G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
        ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
          ∑ i ∈ S, weight i ≤ ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i) :
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        RobertsonSeymour1986.GM5.TreewidthLE
          (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧
            G.Adj x.2 y.2 ∧ WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧
              WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val))
          (3 * k) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := WilliamsonShmoys.planarRAMRun program (WilliamsonShmoys.planarRAMInput n k edge weight) t
          program[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
          ∀ j < k, ∀ S : Finset (Fin n),
            (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
              WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j)).IsIndepSet
              (S : Set (Fin n)) →
            ∑ i ∈ S, (if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0) ≤
              ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i := by
  classical
  refine ⟨FIN.prog solver, 3000 + 3 * C₀, 3 * d₀ + 2, by omega, by omega, ?_⟩
  intro k hk n edge weight G hTW
  set p := FIN.prog solver with hp
  set X := 283 + 3 * solver.length with hX
  -- Seg1
  obtain ⟨τ1, hτ1, s1pc, s1_0, s1_32, s1_34, s1_10, s1_11, s1_12, s1E, s1Z, s1R, s1Ro⟩ :=
    WilliamsonShmoys.ram_baker_seg_input p (FIN.code_P1 solver) (FIN.code_P2 solver) (FIN.code_P3 solver)
      (FIN.code_P4 solver) (FIN.code_G0 solver) (FIN.code_P5 solver) n k edge weight
  set S1 := WilliamsonShmoys.planarRAMRun p (WilliamsonShmoys.planarRAMInput n k edge weight) τ1 with hS1
  obtain ⟨pc1, M1, R1⟩ := S1
  simp only at s1pc s1_0 s1_32 s1_34 s1_10 s1_11 s1_12 s1E s1Z s1R s1Ro
  subst s1pc
  -- Seg2
  obtain ⟨τ2, hτ2, s2pc, s2_13, s2_20, s2_19, s2_31, s2_11, s2_12, s2_10, s2_0, s2_1, s2_28, s2D, s2fr, s2r⟩ :=
    WilliamsonShmoys.ram_baker_seg_registers p 95 (FIN.code_SQ solver) n M1 R1 s1_0 s1_10 s1_11 s1_12
  set S2 := WilliamsonShmoys.planarRAMRun p ⟨95, M1, R1⟩ τ2 with hS2
  obtain ⟨pc2, M2, R2⟩ := S2
  simp only at s2pc s2_13 s2_20 s2_19 s2_31 s2_11 s2_12 s2_10 s2_0 s2_1 s2_28 s2D s2fr s2r
  subst R2
  have e2 : pc2 = 123 := by omega
  subst e2
  have k2 : ∀ a, 32 ≤ a → (∀ v, v < n → a ≠ 36 + v * (2 * n + 2)) → M2 a = M1 a := fun a ha hd =>
    s2fr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hd
  have hdiagZ : ∀ a, 48 + 2 * (n * n) ≤ a → ∀ v, v < n → a ≠ 36 + v * (2 * n + 2) := by
    intro a ha v hv h
    have := Nat.mul_le_mul_right (2 * n + 2) (show v + 1 ≤ n by omega)
    have e : (v + 1) * (2 * n + 2) = v * (2 * n + 2) + (2 * n + 2) := by ring
    have e2 : n * (2 * n + 2) = 2 * (n * n) + 2 * n := by ring
    omega
  -- Seg3a
  obtain ⟨τ3, hτ3, s3pc, s3_32, s3_34, s3_28, s3L, s3E, s3odd, s3Rodd, s3Rev⟩ :=
    WilliamsonShmoys.ram_baker_seg_levels p (FIN.code_P6 solver) (FIN.code_G1 solver) (FIN.code_P7a solver)
      (FIN.code_G2 solver) (FIN.code_P8 solver) n k hk edge M2 R1 s2_0 s2_10 s2_11 s2_12 s2_13 s2_19 s2_20 s2_31
      s2_28 s2_1 (by rw [k2 32 le_rfl (fun v _ => by omega), s1_32]) (by rw [k2 34 (by omega) (fun v _ => by omega), s1_34])
      (fun v w hvw => by
        rw [k2 _ (by omega) (fun v' hv' => diag_ne n v w v' v.isLt w.isLt hv' (fun h => hvw (Fin.ext h))), s1E v w])
      s2D
      (fun a ha => by rw [k2 a (by omega) (hdiagZ a ha), s1Z a ha])
      (fun a ha hna => s1Ro a ha hna)
  set S3 := WilliamsonShmoys.planarRAMRun p ⟨123, M2, R1⟩ τ3 with hS3
  obtain ⟨pc3, M3, R3⟩ := S3
  simp only at s3pc s3_32 s3_34 s3_28 s3L s3E s3odd s3Rodd s3Rev
  subst s3pc
  -- Seg3b
  obtain ⟨τ4, hτ4, s4pc, s4rel, s4_32, s4_34, s4_28, s4_40, s4_42, s4ev, s4Rev⟩ :=
    WilliamsonShmoys.ram_baker_seg_union p (FIN.code_P7b solver) (FIN.code_G3 solver) n k hk M3 R3
      s3_32 s3_34 s3_28 s3odd s3Rodd
  set S4 := WilliamsonShmoys.planarRAMRun p ⟨207, M3, R3⟩ τ4 with hS4
  -- edge table facts at the start of Seg3b
  have hmk : ∀ v : Fin n, (fun i => M3 ((16 * (n * n) + 16 * n + 48) + 2 * i)) v.val = WilliamsonShmoys.bakerLevel G v % k := fun v => s3L v
  have heb : ∀ v w : Fin n, (1 ≤ (fun v w => M3 (36 + 2 * v * n + 2 * w)) v.val w.val ↔
      (edge v w && decide (v ≠ w)) = true) := by
    intro v w
    simp only
    rw [s3E v w]
    by_cases hvw : v = w
    · subst hvw
      rw [show 36 + 2 * v.val * n + 2 * v.val = 36 + v.val * (2 * n + 2) by ring, s2D v.val v.isLt]
      simp
    · rw [k2 _ (by omega) (fun v' hv' => diag_ne n v w v' v.isLt w.isLt hv' (fun h => hvw (Fin.ext h))), s1E v w]
      by_cases he : edge v w = true
      · simp [he, hvw]
      · simp [he]
  have hG0 : SimpleGraph.fromRel (fun u v : Fin n => (edge u v && decide (u ≠ v)) = true) = G := by
    ext u v
    simp only [G, SimpleGraph.fromRel_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    constructor
    · rintro ⟨h, ⟨h1, -⟩ | ⟨h1, -⟩⟩
      · exact ⟨h, Or.inl h1⟩
      · exact ⟨h, Or.inr h1⟩
    · rintro ⟨h, h1 | h1⟩
      · exact ⟨h, Or.inl ⟨h1, h⟩⟩
      · exact ⟨h, Or.inr ⟨h1, fun e => h e.symm⟩⟩
  have hTW' : RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun x y : Fin (k * n) => (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M3 (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) x y = true)) (3 * k) := by
    apply WilliamsonShmoys.treewidth_of_equiv_hom _ _ finProdFinEquiv (3 * k) _ hTW
    intro a b hab
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso; have := a.isLt; subst hn; simp at this
    · have iso := WilliamsonShmoys.union_graph_iso hn (fun v w => edge v w && decide (v ≠ w))
        (WilliamsonShmoys.bakerLevel G) (fun i => M3 ((16 * (n * n) + 16 * n + 48) + 2 * i)) (fun v w => M3 (36 + 2 * v * n + 2 * w)) hmk heb
        (finProdFinEquiv.symm a) (finProdFinEquiv.symm b)
      rw [hG0, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at iso
      exact iso.1 hab
  -- the solver
  obtain ⟨t, ht, hhalt, hbits, hind, hopt⟩ := hsolver (3 * k) (k * n) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M3 (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R3 (32 + 2 * (x.val % n)) else 0) hTW'
  set Sin := WilliamsonShmoys.planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M3 (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R3 (32 + 2 * (x.val % n)) else 0) with hSin
  set Sout := WilliamsonShmoys.planarRAMRun solver Sin t with hSout
  -- the sandbox
  obtain ⟨τs, hτs, sbpc, sbrel, sbev, sbRev⟩ := WilliamsonShmoys.sandbox_odd_simulation p solver 283 0 2 X
    (by norm_num) (by norm_num) (by norm_num) (FIN.sandboxed solver) t Sin _ hhalt s4rel (by rw [s4pc]; rfl)
  set S5 := WilliamsonShmoys.planarRAMRun p S4 τs with hS5
  obtain ⟨pc5, M5, R5⟩ := S5
  simp only at sbpc sbrel sbev sbRev
  subst sbpc
  have hca : WilliamsonShmoys.CodeAt p X (FIN.Q10a X) := by have := FIN.code_Q10a solver; rwa [Nat.add_zero] at this
  obtain ⟨τ6, hτ6, s6pc, cs, hcs, hW, hout⟩ := WilliamsonShmoys.ram_baker_seg_output p X hca
    (FIN.code_G4 solver) (FIN.code_Q10b solver) n k hk M5 R5
    ((sbev 32 (by norm_num) (by norm_num)).trans s4_32) ((sbev 34 (by norm_num) (by norm_num)).trans s4_34)
    ((sbev 28 (by norm_num) (by norm_num)).trans s4_28) ((sbev 40 (by norm_num) (by norm_num)).trans s4_40)
    ((sbev 42 (by norm_num) (by norm_num)).trans s4_42)
  set F := WilliamsonShmoys.planarRAMRun p ⟨X, M5, R5⟩ τ6 with hF
  -- data facts after the sandbox
  have dL : ∀ v : Fin n, M5 ((16 * (n * n) + 16 * n + 48) + 2 * v.val) = WilliamsonShmoys.bakerLevel G v % k := fun v => by
    rw [sbev _ (by omega) (by omega), s4ev _ (by omega) (by omega), s3L v]
  have dR : ∀ v : Fin n, R5 (32 + 2 * v.val) = weight v := fun v => by
    rw [sbRev _ (by omega), s4Rev _ (by omega) (by omega), s3Rev _ (by omega) (by omega), s1R v]
  have dB : ∀ c v, M5 (5 + 2 * (k * n) * (k * n) + 2 * c * n + 2 * v) = Sout.natMem (2 + k * n * (k * n) + (c * n + v)) := by
    intro c v
    rw [show 5 + 2 * (k * n) * (k * n) + 2 * c * n + 2 * v = 2 * (2 + k * n * (k * n) + (c * n + v)) + 1 by ring]
    exact sbrel.2.1 _
  -- total time and final state
  have hrun : WilliamsonShmoys.planarRAMRun p (WilliamsonShmoys.planarRAMInput n k edge weight)
      (τ1 + τ2 + τ3 + τ4 + τs + τ6) = F := by
    rw [FIN.run_add, FIN.run_add, FIN.run_add, FIN.run_add, FIN.run_add, ← hS1, ← hS2, ← hS3, ← hS4, ← hS5]
  refine ⟨τ1 + τ2 + τ3 + τ4 + τs + τ6, ?_, ?_⟩
  · exact time_total n k t C₀ d₀ τ1 τ2 τ3 τ4 τs τ6 hk hτ1 hτ2 hτ3 hτ4 hτs hτ6 ht
  dsimp only
  rw [hrun]
  have hpcF : F.pc = X + 101 := s6pc
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [hpcF]
    have := FIN.code_HL solver 0 (by simp [FIN.HL])
    simpa [FIN.HL] using this
  · rw [hout i.val i.isLt]; split_ifs <;> omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨fun x => x.elim0, fun j _ S _ => ?_⟩
    rw [Finset.eq_empty_of_forall_notMem (fun x => x.elim0) (s := S),
      Finset.eq_empty_of_forall_notMem (fun x => x.elim0) (s := WilliamsonShmoys.planarRAMOutput 0 F)]
    simp
  -- the solver output as a subset of the union vertex set
  set e : Fin k × Fin n ≃ Fin (k * n) := finProdFinEquiv with he
  have ediv : ∀ x : Fin k × Fin n, (e x).val / n = x.1.val ∧ (e x).val % n = x.2.val := by
    intro x
    simp only [he, finProdFinEquiv_apply_val]
    constructor
    · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt x.2.isLt, Nat.zero_add]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]
  have iso : ∀ a b : Fin k × Fin n,
      (SimpleGraph.fromRel (fun x y : Fin (k * n) => (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M3 (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) x y = true)).Adj (e a) (e b) ↔
      (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧ WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val)).Adj a b := by
    intro a b
    have := WilliamsonShmoys.union_graph_iso hn (fun v w => edge v w && decide (v ≠ w))
      (WilliamsonShmoys.bakerLevel G) (fun i => M3 ((16 * (n * n) + 16 * n + 48) + 2 * i)) (fun v w => M3 (36 + 2 * v * n + 2 * w)) hmk heb a b
    rw [hG0] at this
    exact this
  set A : Finset (Fin k × Fin n) := Finset.univ.filter (fun x => Sout.natMem (2 + k * n * (k * n) + (e x).val) = 1) with hA
  have memOut : ∀ y : Fin (k * n), y ∈ WilliamsonShmoys.planarRAMOutput (k * n) Sout ↔
      Sout.natMem (2 + k * n * (k * n) + y.val) = 1 := by
    intro y; simp [WilliamsonShmoys.planarRAMOutput]
  have outA : WilliamsonShmoys.planarRAMOutput (k * n) Sout = A.map e.toEmbedding := by
    ext y
    rw [memOut, Finset.mem_map_equiv]
    simp [hA]
  have wt : ∀ x : Fin k × Fin n, (fun x : Fin (k * n) => if M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R3 (32 + 2 * (x.val % n)) else 0) (e x) = if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0 := by
    intro x
    simp only
    rw [(ediv x).1, (ediv x).2, s3L x.2, s3Rev _ (by omega) (by omega), s1R x.2]
  have hAind : (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧ WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧ WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val)).IsIndepSet (A : Set (Fin k × Fin n)) := by
    intro x hx y hy hxy hadj
    have hx' : e x ∈ WilliamsonShmoys.planarRAMOutput (k * n) Sout := by
      rw [memOut]; simpa [hA] using hx
    have hy' : e y ∈ WilliamsonShmoys.planarRAMOutput (k * n) Sout := by
      rw [memOut]; simpa [hA] using hy
    exact hind hx' hy' (fun h => hxy (e.injective h)) ((iso x y).2 hadj)
  have hoptA : ∀ S : Finset (Fin k × Fin n), (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧ WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧ WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val)).IsIndepSet (S : Set (Fin k × Fin n)) →
      ∑ x ∈ S, (if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0) ≤ ∑ x ∈ A, (if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0) := by
    intro S hS
    have hS' : (SimpleGraph.fromRel (fun x y : Fin (k * n) => (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M3 ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M3 (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) x y = true)).IsIndepSet
        ((S.map e.toEmbedding : Finset (Fin (k * n))) : Set (Fin (k * n))) := by
      intro a ha b hb hab hadj
      rw [Finset.coe_map, Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      exact hS hx hy (fun h => hab (by rw [h])) ((iso x y).1 hadj)
    have := hopt _ hS'
    rw [outA, Finset.sum_map, Finset.sum_map] at this
    simp only [Equiv.coe_toEmbedding] at this
    simpa only [wt] using this
  have bitle : ∀ c v, c < k → v < n → Sout.natMem (2 + k * n * (k * n) + (c * n + v)) ≤ 1 := by
    intro c v hc hv
    have hlt : c * n + v < k * n := by
      have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
      have e' : (c + 1) * n = c * n + n := by ring
      omega
    exact hbits ⟨c * n + v, hlt⟩
  have memA : ∀ (c : Fin k) (v : Fin n), (c, v) ∈ A ↔ Sout.natMem (2 + k * n * (k * n) + (c.val * n + v.val)) = 1 := by
    intro c v
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, he, finProdFinEquiv_apply_val]
    rw [show v.val + n * c.val = c.val * n + v.val by ring]
  have sumA : ∀ c : Fin k, ∑ x ∈ A.filter (fun x => x.1 = c), (if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0) =
      ∑ j ∈ Finset.range n, (if 1 ≤ M5 (5 + 2 * (k * n) * (k * n) + 2 * c.val * n + 2 * j) ∧
        M5 ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ c.val then R5 (32 + 2 * j) else 0) := by
    intro c
    have hmap : A.filter (fun x => x.1 = c) =
        (Finset.univ.filter (fun v : Fin n => (c, v) ∈ A)).map ⟨fun v => (c, v), fun a b h => by simpa using h⟩ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hx, rfl⟩; exact ⟨x.2, hx, rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact ⟨hv, rfl⟩
    rw [hmap, Finset.sum_map, Finset.sum_filter]
    rw [← Fin.sum_univ_eq_sum_range (fun j => if 1 ≤ M5 (5 + 2 * (k * n) * (k * n) + 2 * c.val * n + 2 * j) ∧
        M5 ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ c.val then R5 (32 + 2 * j) else 0) n]
    apply Finset.sum_congr rfl
    intro v _
    rw [dB, dL v, dR v]
    have hb := bitle c.val v.val c.isLt v.isLt
    by_cases h1 : Sout.natMem (2 + k * n * (k * n) + (c.val * n + v.val)) = 1
    · rw [if_pos ((memA c v).2 h1)]
      show (if WilliamsonShmoys.bakerLevel G v % k ≠ c.val then weight v else 0) = _
      by_cases h2 : WilliamsonShmoys.bakerLevel G v % k ≠ c.val
      · rw [if_pos h2, if_pos ⟨by omega, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg (fun h => h1 ((memA c v).1 h)), if_neg (fun h => h1 (by omega))]
  have hbestA : ∀ c : Fin k, ∑ x ∈ A.filter (fun x => x.1 = c), (if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0) ≤
      ∑ x ∈ A.filter (fun x => x.1 = (⟨cs, hcs⟩ : Fin k)), (if WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val then weight x.2 else 0) := by
    intro c
    rw [sumA c, sumA ⟨cs, hcs⟩]
    have := hW c.val c.isLt
    simpa using this
  obtain ⟨hI, hB⟩ := WilliamsonShmoys.baker_union_output_bound G (WilliamsonShmoys.bakerLevel G) k weight A
    hAind hoptA ⟨cs, hcs⟩ hbestA
  have hO : WilliamsonShmoys.planarRAMOutput n F =
      Finset.univ.filter (fun v => ((⟨cs, hcs⟩ : Fin k), v) ∈ A ∧ WilliamsonShmoys.bakerLevel G v % k ≠ cs) := by
    ext v
    simp only [WilliamsonShmoys.planarRAMOutput, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hout v.val v.isLt, dB, dL v, memA]
    have hb := bitle cs v.val hcs v.isLt
    simp only
    split_ifs with h
    · simp only [true_iff]; exact ⟨by omega, h.2⟩
    · simp only [show ¬ ((0 : ℕ) = 1) by omega, false_iff, not_and]
      intro h1 h2; exact h ⟨by omega, h2⟩
  rw [hO]
  exact ⟨hI, hB⟩
