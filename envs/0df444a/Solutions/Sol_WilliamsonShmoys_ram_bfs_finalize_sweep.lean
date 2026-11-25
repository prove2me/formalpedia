-- Prove2me | solution 1 for WilliamsonShmoys.ram_bfs_finalize_sweep
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T02:41:41.135677+00:00
-- url     : https://prove2.me/submissions/34545bb6-951e-4954-9338-da6377ee26d0

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace FS
open WilliamsonShmoys PlanarRAMInstruction

lemma step_exec (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execInstr ins s := by
  unfold planarRAMStep
  rw [h]
  cases ins <;> rfl

lemma run_add (p : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun p s (a + b) = planarRAMRun p (planarRAMRun p s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma run_succ (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMRun p (planarRAMStep p s) t := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply]

lemma run_zero (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 0 = s := rfl

lemma step_at (p : List PlanarRAMInstruction) (b k : ℕ) {s : PlanarRAMState} (ins : PlanarRAMInstruction)
    (h1 : s.pc = b + k) (h2 : p[b + k]? = some ins) : planarRAMStep p s = execInstr ins s :=
  step_exec p s ins (by rw [h1]; exact h2)

lemma codeAt_sub (p : List PlanarRAMInstruction) (base off : ℕ) (code sub : List PlanarRAMInstruction)
    (hcode : CodeAt p base code) (hsub : ∀ i, i < sub.length → code[off + i]? = sub[i]?) :
    CodeAt p (base + off) sub := by
  intro i hi
  have h := hsub i hi
  have hlen : off + i < code.length := by
    by_contra hc
    push_neg at hc
    rw [List.getElem?_eq_none hc] at h
    exact absurd h.symm (by simp [List.getElem?_eq_getElem hi])
  rw [add_assoc, hcode (off + i) hlen, h]

section
variable (p : List PlanarRAMInstruction) (g : ℕ)
  (hcode : CodeAt p g
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (g + 11) (g + 3),
      natLoad 22 27,
      natBranch 22 12 (g + 8) (g + 5),
      natBranch 22 31 (g + 6) (g + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (g + 2)])
include hcode

set_option maxHeartbeats 4000000 in
lemma fin_loop (n LVB : ℕ) (hLVB : 36 ≤ LVB) :
    ∀ (r w : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = n →
      M 13 = n → M 24 = w → M 27 = LVB + 2 * w → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 →
      M 31 = n + 1 →
      ∃ τ, τ ≤ 9 * r + 1 ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ).pc = g + 11 ∧
        (∀ j, w ≤ j → j < n → (planarRAMRun p ⟨g + 2, M, R⟩ τ).natMem (LVB + 2 * j) =
          if 1 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ n + 1 then M (LVB + 2 * j) + (n + 1)
          else M (LVB + 2 * j)) ∧
        (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, w ≤ j → j < n → a ≠ LVB + 2 * j) →
          (planarRAMRun p ⟨g + 2, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ).realMem = R := by
  have c0 : p[g + 0]? = some (natConst 24 0) := by simpa using hcode 0 (by simp)
  have c1 : p[g + 1]? = some (natAdd 27 28 12) := by simpa using hcode 1 (by simp)
  have c2 : p[g + 2]? = some (natBranch 13 24 (g + 11) (g + 3)) := by simpa using hcode 2 (by simp)
  have c3 : p[g + 3]? = some (natLoad 22 27) := by simpa using hcode 3 (by simp)
  have c4 : p[g + 4]? = some (natBranch 22 12 (g + 8) (g + 5)) := by simpa using hcode 4 (by simp)
  have c5 : p[g + 5]? = some (natBranch 22 31 (g + 6) (g + 8)) := by simpa using hcode 5 (by simp)
  have c6 : p[g + 6]? = some (natAdd 22 22 31) := by simpa using hcode 6 (by simp)
  have c7 : p[g + 7]? = some (natStore 27 22) := by simpa using hcode 7 (by simp)
  have c8 : p[g + 8]? = some (natAdd 24 24 11) := by simpa using hcode 8 (by simp)
  have c9 : p[g + 9]? = some (natAdd 27 27 19) := by simpa using hcode 9 (by simp)
  have c10 : p[g + 10]? = some (jump (g + 2)) := by simpa using hcode 10 (by simp)
  intro r
  induction r with
  | zero =>
    intro w M R hw h13 h24 h27 h28 h11 h12 h19 h31
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p g 2 _ rfl c2, run_zero]
    simp only [execInstr, show M 13 ≤ M 24 by omega, if_true]
    refine ⟨trivial, fun j hj1 hj2 => by omega, fun a _ _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro w M R hw h13 h24 h27 h28 h11 h12 h19 h31
    have hlt : ¬ M 13 ≤ M 24 := by omega
    have hwn : w < n := by omega
    have n11 : LVB + 2 * w ≠ 11 := by omega
    have n12 : LVB + 2 * w ≠ 12 := by omega
    have n13 : LVB + 2 * w ≠ 13 := by omega
    have n19 : LVB + 2 * w ≠ 19 := by omega
    have n22 : LVB + 2 * w ≠ 22 := by omega
    have n24 : LVB + 2 * w ≠ 24 := by omega
    have n27 : LVB + 2 * w ≠ 27 := by omega
    have n28 : LVB + 2 * w ≠ 28 := by omega
    have n31 : LVB + 2 * w ≠ 31 := by omega
    have n11' : (11 : ℕ) ≠ LVB + 2 * w := by omega
    have n12' : (12 : ℕ) ≠ LVB + 2 * w := by omega
    have n13' : (13 : ℕ) ≠ LVB + 2 * w := by omega
    have n19' : (19 : ℕ) ≠ LVB + 2 * w := by omega
    have n22' : (22 : ℕ) ≠ LVB + 2 * w := by omega
    have n24' : (24 : ℕ) ≠ LVB + 2 * w := by omega
    have n27' : (27 : ℕ) ≠ LVB + 2 * w := by omega
    have n28' : (28 : ℕ) ≠ LVB + 2 * w := by omega
    have n31' : (31 : ℕ) ≠ LVB + 2 * w := by omega
    have hne : ∀ k, k ≤ 31 → LVB + 2 * w ≠ k := fun k hk => by omega
    -- one iteration, three paths
    have one : ∃ τ1, τ1 ≤ 9 ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).pc = g + 2 ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 13 = n ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 24 = w + 1 ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 27 = LVB + 2 * (w + 1) ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 28 = LVB ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 11 = 1 ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 12 = 0 ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 19 = 2 ∧ (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem 31 = n + 1 ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem (LVB + 2 * w) = (if 1 ≤ M (LVB + 2 * w) ∧ M (LVB + 2 * w) ≤ n + 1 then M (LVB + 2 * w) + (n + 1)
          else M (LVB + 2 * w)) ∧
        (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → a ≠ LVB + 2 * w → (planarRAMRun p ⟨g + 2, M, R⟩ τ1).natMem a = M a) ∧
        (planarRAMRun p ⟨g + 2, M, R⟩ τ1).realMem = R := by
      by_cases hz : M (LVB + 2 * w) ≤ 0
      · refine ⟨6, by omega, ?_⟩
        rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at p g 2 _ rfl c2]
        rw [run_succ, step_at p g 3 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]) c3]
        rw [run_succ, step_at p g 4 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]) c4]
        rw [run_succ, step_at p g 8 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]) c8]
        rw [run_succ, step_at p g 9 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]) c9]
        rw [run_succ, step_at p g 10 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]) c10]
        rw [run_zero]
        simp only [execInstr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]; done)
          | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]; omega)
          | (intro a a22 a24 a27 _; simp [Function.update_apply, a22, a24, a27])
          | skip
        · rw [if_neg (by omega)]
          simp (disch := omega) only [Function.update_apply, if_neg]
      · by_cases hb : M (LVB + 2 * w) ≤ n + 1
        · refine ⟨9, by omega, ?_⟩
          rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at p g 2 _ rfl c2]
          rw [run_succ, step_at p g 3 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c3]
          rw [run_succ, step_at p g 4 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c4]
          rw [run_succ, step_at p g 5 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c5]
          rw [run_succ, step_at p g 6 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c6]
          rw [run_succ, step_at p g 7 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c7]
          rw [run_succ, step_at p g 8 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c8]
          rw [run_succ, step_at p g 9 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c9]
          rw [run_succ, step_at p g 10 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']) c10]
          rw [run_zero]
          simp only [execInstr]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first
            | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']; done)
            | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']; omega)
            | (rw [if_pos (show 1 ≤ M (LVB + 2 * w) ∧ M (LVB + 2 * w) ≤ n + 1 from ⟨by omega, hb⟩)]; simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']; done)
            | (rw [if_pos (show 1 ≤ M (LVB + 2 * w) ∧ M (LVB + 2 * w) ≤ n + 1 from ⟨by omega, hb⟩)]; simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb, n11, n12, n13, n19, n22, n24, n27, n28, n31, n11', n12', n13', n19', n22', n24', n27', n28', n31']; omega)
            | (intro a a22 a24 a27 aL; simp [Function.update_apply, a22, a24, a27, aL, h11, h12, h13, h19, h28, h31, h24, h27]; done)
        · refine ⟨7, by omega, ?_⟩
          rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at p g 2 _ rfl c2]
          rw [run_succ, step_at p g 3 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c3]
          rw [run_succ, step_at p g 4 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c4]
          rw [run_succ, step_at p g 5 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c5]
          rw [run_succ, step_at p g 8 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c8]
          rw [run_succ, step_at p g 9 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c9]
          rw [run_succ, step_at p g 10 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz, hb]) c10]
          rw [run_zero]
          simp only [execInstr]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first
            | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]; done)
            | (simp [Function.update_apply, h11, h12, h13, h19, h28, h31, h24, h27, hlt, hwn, hz]; omega)
            | (intro a a22 a24 a27 _; simp [Function.update_apply, a22, a24, a27])
            | skip
          · rw [if_neg (by omega)]
            simp (disch := omega) only [Function.update_apply, if_neg]
    obtain ⟨τ1, hτ1, m1, m13, m24, m27, m28, m11, m12, m19, m31, mw, mfr, mr⟩ := one
    set S1 := planarRAMRun p ⟨g + 2, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at m1 m13 m24 m27 m28 m11 m12 m19 m31 mw mfr mr
    subst m1; subst mr
    obtain ⟨τ2, hτ2, r1, rL, rfr, rr⟩ := ih (w + 1) M1 R1 (by omega) m13 m24 m27 m28 m11 m12 m19 m31
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    refine ⟨r1, ?_, ?_, rr⟩
    · intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with h | h
      · subst h
        rw [rfr _ (by omega) (by omega) (by omega) (fun j' h1 _ => by omega), mw]
      · rw [rL j h hj2, mfr _ (by omega) (by omega) (by omega) (by omega)]
    · intro a a22 a24 a27 aL
      rw [rfr a a22 a24 a27 (fun j h1 h2 => aL j (by omega) h2), mfr a a22 a24 a27 (aL w le_rfl (by omega))]

lemma fin_sweep (n LVB : ℕ) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0) (h19 : M 19 = 2)
    (h31 : M 31 = n + 1) :
    ∃ τ, τ ≤ 9 * n + 3 ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).pc = g + 11 ∧
      (∀ j, j < n → (planarRAMRun p ⟨g, M, R⟩ τ).natMem (LVB + 2 * j) =
        if 1 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ n + 1 then M (LVB + 2 * j) + (n + 1)
        else M (LVB + 2 * j)) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨g, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).realMem = R := by
  have c0 : p[g + 0]? = some (natConst 24 0) := by simpa using hcode 0 (by simp)
  have c1 : p[g + 1]? = some (natAdd 27 28 12) := by simpa using hcode 1 (by simp)
  have e2 : planarRAMRun p ⟨g, M, R⟩ 2 = ⟨g + 2, Function.update (Function.update M 24 0) 27 LVB, R⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, run_succ, step_at p g 0 _ (by simp) c0,
      run_succ, step_at p g 1 _ (by simp [execInstr]) c1, run_zero]
    simp [execInstr, Function.update_apply, h28, h12]
  obtain ⟨τ, hτ, r1, rL, rfr, rr⟩ := fin_loop p g hcode n LVB hLVB n 0 (Function.update (Function.update M 24 0) 27 LVB) R (by omega)
    (by simp [Function.update_apply, h13]) (by simp) (by simp) (by simp [Function.update_apply, h28])
    (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h12])
    (by simp [Function.update_apply, h19]) (by simp [Function.update_apply, h31])
  refine ⟨2 + τ, by omega, ?_⟩
  rw [run_add, e2]
  have hu : ∀ j, (Function.update (Function.update M 24 0) 27 LVB) (LVB + 2 * j) = M (LVB + 2 * j) := by
    intro j; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨r1, fun j hj => ?_, fun a a22 a24 a27 aL => ?_, rr⟩
  · rw [rL j (Nat.zero_le _) hj, hu j]
  · rw [rfr a a22 a24 a27 (fun j _ hj => aL j hj), Function.update_of_ne a27, Function.update_of_ne a24]

end

end FS

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (g : ℕ)
    (hcode : CodeAt p g
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (g + 11) (g + 3),
      natLoad 22 27,
      natBranch 22 12 (g + 8) (g + 5),
      natBranch 22 31 (g + 6) (g + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (g + 2)])
    (n LVB : ℕ) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0) (h19 : M 19 = 2)
    (h31 : M 31 = n + 1) :
    ∃ τ, τ ≤ 9 * n + 3 ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).pc = g + 11 ∧
      (∀ j, j < n → (planarRAMRun p ⟨g, M, R⟩ τ).natMem (LVB + 2 * j) =
        if 1 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ n + 1 then M (LVB + 2 * j) + (n + 1)
        else M (LVB + 2 * j)) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨g, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).realMem = R :=
  FS.fin_sweep p g hcode n LVB hLVB M R h13 h28 h11 h12 h19 h31
