-- Prove2me | solution 1 for WilliamsonShmoys.ram_bfs_row_scan
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T00:24:32.644854+00:00
-- url     : https://prove2.me/submissions/e0e9b8a6-6671-44aa-9856-d9d53623eee1

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace RW
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

section
variable (p : List PlanarRAMInstruction) (b : ℕ)
  (hcode : CodeAt p b
    [natBranch 13 16 (b + 14) (b + 1),
      natLoad 22 17,
      natBranch 11 22 (b + 5) (b + 3),
      natLoad 22 18,
      natBranch 11 22 (b + 5) (b + 9),
      natLoad 22 21,
      natBranch 22 12 (b + 7) (b + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump b])
include hcode

/-- One iteration of the row scan, from the loop head with `w < n`. -/
lemma row_iter (M : ℕ → ℕ) (R : ℕ → ℝ) (n w pr pc la : ℕ) (hw : w < n)
    (h13 : M 13 = n) (h16 : M 16 = w) (h17 : M 17 = pr) (h18 : M 18 = pc) (h21 : M 21 = la)
    (h11 : M 11 = 1) (h12 : M 12 = 0) (h19 : M 19 = 2)
    (hla : 32 ≤ la) (hpr : 32 ≤ pr) (hpc : 32 ≤ pc) :
    let trig := (1 ≤ M pr ∨ 1 ≤ M pc) ∧ M la = 0
    ∃ τ, τ ≤ 14 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).pc = b ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 16 = w + 1 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 17 = pr + 2 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 18 = pc + M 20 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 21 = la + 2 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 23 = (if trig then 1 else M 23) ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem la = (if trig then M 14 else M la) ∧
      (∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ la →
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R := by
  intro trig
  have c0 : p[b + 0]? = some (natBranch 13 16 (b + 14) (b + 1)) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natLoad 22 17) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natBranch 11 22 (b + 5) (b + 3)) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natLoad 22 18) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natBranch 11 22 (b + 5) (b + 9)) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natLoad 22 21) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natBranch 22 12 (b + 7) (b + 9)) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natStore 21 14) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 23 11 12) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 16 16 11) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (natAdd 17 17 19) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 18 18 20) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natAdd 21 21 19) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (jump b) := by simpa using hcode 13 (by simp)
  have la11 : la ≠ 11 := by omega
  have la11' : (11:ℕ) ≠ la := by omega
  have la12 : la ≠ 12 := by omega
  have la12' : (12:ℕ) ≠ la := by omega
  have la13 : la ≠ 13 := by omega
  have la13' : (13:ℕ) ≠ la := by omega
  have la14 : la ≠ 14 := by omega
  have la14' : (14:ℕ) ≠ la := by omega
  have la16 : la ≠ 16 := by omega
  have la16' : (16:ℕ) ≠ la := by omega
  have la17 : la ≠ 17 := by omega
  have la17' : (17:ℕ) ≠ la := by omega
  have la18 : la ≠ 18 := by omega
  have la18' : (18:ℕ) ≠ la := by omega
  have la19 : la ≠ 19 := by omega
  have la19' : (19:ℕ) ≠ la := by omega
  have la20 : la ≠ 20 := by omega
  have la20' : (20:ℕ) ≠ la := by omega
  have la21 : la ≠ 21 := by omega
  have la21' : (21:ℕ) ≠ la := by omega
  have la22 : la ≠ 22 := by omega
  have la22' : (22:ℕ) ≠ la := by omega
  have la23 : la ≠ 23 := by omega
  have la23' : (23:ℕ) ≠ la := by omega
  have pr11 : pr ≠ 11 := by omega
  have pr11' : (11:ℕ) ≠ pr := by omega
  have pr12 : pr ≠ 12 := by omega
  have pr12' : (12:ℕ) ≠ pr := by omega
  have pr13 : pr ≠ 13 := by omega
  have pr13' : (13:ℕ) ≠ pr := by omega
  have pr14 : pr ≠ 14 := by omega
  have pr14' : (14:ℕ) ≠ pr := by omega
  have pr16 : pr ≠ 16 := by omega
  have pr16' : (16:ℕ) ≠ pr := by omega
  have pr17 : pr ≠ 17 := by omega
  have pr17' : (17:ℕ) ≠ pr := by omega
  have pr18 : pr ≠ 18 := by omega
  have pr18' : (18:ℕ) ≠ pr := by omega
  have pr19 : pr ≠ 19 := by omega
  have pr19' : (19:ℕ) ≠ pr := by omega
  have pr20 : pr ≠ 20 := by omega
  have pr20' : (20:ℕ) ≠ pr := by omega
  have pr21 : pr ≠ 21 := by omega
  have pr21' : (21:ℕ) ≠ pr := by omega
  have pr22 : pr ≠ 22 := by omega
  have pr22' : (22:ℕ) ≠ pr := by omega
  have pr23 : pr ≠ 23 := by omega
  have pr23' : (23:ℕ) ≠ pr := by omega
  have pc11 : pc ≠ 11 := by omega
  have pc11' : (11:ℕ) ≠ pc := by omega
  have pc12 : pc ≠ 12 := by omega
  have pc12' : (12:ℕ) ≠ pc := by omega
  have pc13 : pc ≠ 13 := by omega
  have pc13' : (13:ℕ) ≠ pc := by omega
  have pc14 : pc ≠ 14 := by omega
  have pc14' : (14:ℕ) ≠ pc := by omega
  have pc16 : pc ≠ 16 := by omega
  have pc16' : (16:ℕ) ≠ pc := by omega
  have pc17 : pc ≠ 17 := by omega
  have pc17' : (17:ℕ) ≠ pc := by omega
  have pc18 : pc ≠ 18 := by omega
  have pc18' : (18:ℕ) ≠ pc := by omega
  have pc19 : pc ≠ 19 := by omega
  have pc19' : (19:ℕ) ≠ pc := by omega
  have pc20 : pc ≠ 20 := by omega
  have pc20' : (20:ℕ) ≠ pc := by omega
  have pc21 : pc ≠ 21 := by omega
  have pc21' : (21:ℕ) ≠ pc := by omega
  have pc22 : pc ≠ 22 := by omega
  have pc22' : (22:ℕ) ≠ pc := by omega
  have pc23 : pc ≠ 23 := by omega
  have pc23' : (23:ℕ) ≠ pc := by omega
  have hnw : ¬ M 13 ≤ M 16 := by omega
  by_cases hA : 1 ≤ M pr
  · by_cases hZ : M la = 0
    · have ht : trig := ⟨Or.inl hA, hZ⟩
      refine ⟨12, by norm_num, ?_⟩
      rw [show (12 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p b 0 _ (by simp [execInstr, Function.update_apply, *]) c0]
      rw [run_succ, step_at p b 1 _ (by simp [execInstr, Function.update_apply, *]) c1]
      rw [run_succ, step_at p b 2 _ (by simp [execInstr, Function.update_apply, *]) c2]
      rw [run_succ, step_at p b 5 _ (by simp [execInstr, Function.update_apply, *]) c5]
      rw [run_succ, step_at p b 6 _ (by simp [execInstr, Function.update_apply, *]) c6]
      rw [run_succ, step_at p b 7 _ (by simp [execInstr, Function.update_apply, *]) c7]
      rw [run_succ, step_at p b 8 _ (by simp [execInstr, Function.update_apply, *]) c8]
      rw [run_succ, step_at p b 9 _ (by simp [execInstr, Function.update_apply, *]) c9]
      rw [run_succ, step_at p b 10 _ (by simp [execInstr, Function.update_apply, *]) c10]
      rw [run_succ, step_at p b 11 _ (by simp [execInstr, Function.update_apply, *]) c11]
      rw [run_succ, step_at p b 12 _ (by simp [execInstr, Function.update_apply, *]) c12]
      rw [run_succ, step_at p b 13 _ (by simp [execInstr, Function.update_apply, *]) c13]
      rw [run_zero]
      simp only [execInstr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro a ha16 ha17 ha18 ha21 ha22 ha23 hala; simp [Function.update_apply, *])
        | (simp [Function.update_apply, *, trig])
        | (simp [Function.update_apply, *, trig]; omega)
    · have ht : ¬ trig := fun h => hZ h.2
      refine ⟨10, by norm_num, ?_⟩
      rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p b 0 _ (by simp [execInstr, Function.update_apply, *]) c0]
      rw [run_succ, step_at p b 1 _ (by simp [execInstr, Function.update_apply, *]) c1]
      rw [run_succ, step_at p b 2 _ (by simp [execInstr, Function.update_apply, *]) c2]
      rw [run_succ, step_at p b 5 _ (by simp [execInstr, Function.update_apply, *]) c5]
      rw [run_succ, step_at p b 6 _ (by simp [execInstr, Function.update_apply, *]) c6]
      rw [run_succ, step_at p b 9 _ (by simp [execInstr, Function.update_apply, *]) c9]
      rw [run_succ, step_at p b 10 _ (by simp [execInstr, Function.update_apply, *]) c10]
      rw [run_succ, step_at p b 11 _ (by simp [execInstr, Function.update_apply, *]) c11]
      rw [run_succ, step_at p b 12 _ (by simp [execInstr, Function.update_apply, *]) c12]
      rw [run_succ, step_at p b 13 _ (by simp [execInstr, Function.update_apply, *]) c13]
      rw [run_zero]
      simp only [execInstr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro a ha16 ha17 ha18 ha21 ha22 ha23 hala; simp [Function.update_apply, *])
        | (simp [Function.update_apply, *, trig])
        | (simp [Function.update_apply, *, trig]; omega)
  · by_cases hB : 1 ≤ M pc
    · by_cases hZ : M la = 0
      · have ht : trig := ⟨Or.inr hB, hZ⟩
        refine ⟨14, by norm_num, ?_⟩
        rw [show (14 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at p b 0 _ (by simp [execInstr, Function.update_apply, *]) c0]
        rw [run_succ, step_at p b 1 _ (by simp [execInstr, Function.update_apply, *]) c1]
        rw [run_succ, step_at p b 2 _ (by simp [execInstr, Function.update_apply, *]) c2]
        rw [run_succ, step_at p b 3 _ (by simp [execInstr, Function.update_apply, *]) c3]
        rw [run_succ, step_at p b 4 _ (by simp [execInstr, Function.update_apply, *]) c4]
        rw [run_succ, step_at p b 5 _ (by simp [execInstr, Function.update_apply, *]) c5]
        rw [run_succ, step_at p b 6 _ (by simp [execInstr, Function.update_apply, *]) c6]
        rw [run_succ, step_at p b 7 _ (by simp [execInstr, Function.update_apply, *]) c7]
        rw [run_succ, step_at p b 8 _ (by simp [execInstr, Function.update_apply, *]) c8]
        rw [run_succ, step_at p b 9 _ (by simp [execInstr, Function.update_apply, *]) c9]
        rw [run_succ, step_at p b 10 _ (by simp [execInstr, Function.update_apply, *]) c10]
        rw [run_succ, step_at p b 11 _ (by simp [execInstr, Function.update_apply, *]) c11]
        rw [run_succ, step_at p b 12 _ (by simp [execInstr, Function.update_apply, *]) c12]
        rw [run_succ, step_at p b 13 _ (by simp [execInstr, Function.update_apply, *]) c13]
        rw [run_zero]
        simp only [execInstr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (intro a ha16 ha17 ha18 ha21 ha22 ha23 hala; simp [Function.update_apply, *])
          | (simp [Function.update_apply, *, trig])
          | (simp [Function.update_apply, *, trig]; omega)
      · have ht : ¬ trig := fun h => hZ h.2
        refine ⟨12, by norm_num, ?_⟩
        rw [show (12 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at p b 0 _ (by simp [execInstr, Function.update_apply, *]) c0]
        rw [run_succ, step_at p b 1 _ (by simp [execInstr, Function.update_apply, *]) c1]
        rw [run_succ, step_at p b 2 _ (by simp [execInstr, Function.update_apply, *]) c2]
        rw [run_succ, step_at p b 3 _ (by simp [execInstr, Function.update_apply, *]) c3]
        rw [run_succ, step_at p b 4 _ (by simp [execInstr, Function.update_apply, *]) c4]
        rw [run_succ, step_at p b 5 _ (by simp [execInstr, Function.update_apply, *]) c5]
        rw [run_succ, step_at p b 6 _ (by simp [execInstr, Function.update_apply, *]) c6]
        rw [run_succ, step_at p b 9 _ (by simp [execInstr, Function.update_apply, *]) c9]
        rw [run_succ, step_at p b 10 _ (by simp [execInstr, Function.update_apply, *]) c10]
        rw [run_succ, step_at p b 11 _ (by simp [execInstr, Function.update_apply, *]) c11]
        rw [run_succ, step_at p b 12 _ (by simp [execInstr, Function.update_apply, *]) c12]
        rw [run_succ, step_at p b 13 _ (by simp [execInstr, Function.update_apply, *]) c13]
        rw [run_zero]
        simp only [execInstr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (intro a ha16 ha17 ha18 ha21 ha22 ha23 hala; simp [Function.update_apply, *])
          | (simp [Function.update_apply, *, trig])
          | (simp [Function.update_apply, *, trig]; omega)
    · have ht : ¬ trig := fun h => h.1.elim hA hB
      refine ⟨10, by norm_num, ?_⟩
      rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p b 0 _ (by simp [execInstr, Function.update_apply, *]) c0]
      rw [run_succ, step_at p b 1 _ (by simp [execInstr, Function.update_apply, *]) c1]
      rw [run_succ, step_at p b 2 _ (by simp [execInstr, Function.update_apply, *]) c2]
      rw [run_succ, step_at p b 3 _ (by simp [execInstr, Function.update_apply, *]) c3]
      rw [run_succ, step_at p b 4 _ (by simp [execInstr, Function.update_apply, *]) c4]
      rw [run_succ, step_at p b 9 _ (by simp [execInstr, Function.update_apply, *]) c9]
      rw [run_succ, step_at p b 10 _ (by simp [execInstr, Function.update_apply, *]) c10]
      rw [run_succ, step_at p b 11 _ (by simp [execInstr, Function.update_apply, *]) c11]
      rw [run_succ, step_at p b 12 _ (by simp [execInstr, Function.update_apply, *]) c12]
      rw [run_succ, step_at p b 13 _ (by simp [execInstr, Function.update_apply, *]) c13]
      rw [run_zero]
      simp only [execInstr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro a ha16 ha17 ha18 ha21 ha22 ha23 hala; simp [Function.update_apply, *])
        | (simp [Function.update_apply, *, trig])
        | (simp [Function.update_apply, *, trig]; omega)

lemma row_loop :
    ∀ (r w pr pc la : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = M 13 →
      M 16 = w → M 17 = pr → M 18 = pc → M 21 = la → M 11 = 1 → M 12 = 0 → M 19 = 2 →
      32 ≤ la → 32 ≤ pr → 32 ≤ pc →
      (∀ j j', j < r → j' < r → la + 2 * j ≠ pr + 2 * j' ∧ la + 2 * j ≠ pc + j' * M 20) →
      ∃ τ, τ ≤ 14 * r + 1 ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 14 ∧
        (∀ j, j < r → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (la + 2 * j) =
          if (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then M 14
          else M (la + 2 * j)) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem 23 =
          (if ∃ j, j < r ∧ (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then 1
            else M 23) ∧
        (∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → a ≠ 23 → (∀ j, j < r → a ≠ la + 2 * j) →
          (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R := by
  intro r
  induction r with
  | zero =>
    intro w pr pc la M R hw h16 h17 h18 h21 h11 h12 h19 hla hpr hpc hdis
    have c0 : p[b + 0]? = some (natBranch 13 16 (b + 14) (b + 1)) := by simpa using hcode 0 (by simp)
    refine ⟨1, by norm_num, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 0 _ (by simp) c0, run_zero]
    have hle : M 13 ≤ M 16 := by omega
    simp only [execInstr, if_pos hle]
    refine ⟨by simp, fun j hj => by omega, ?_, fun a _ _ _ _ _ _ _ => by simp, by simp⟩
    simp
  | succ r ih =>
    intro w pr pc la M R hw h16 h17 h18 h21 h11 h12 h19 hla hpr hpc hdis
    obtain ⟨τ1, hτ1, q1, q16, q17, q18, q21, q23, qla, qfr, qr⟩ :=
      row_iter p b hcode M R (M 13) w pr pc la (by omega) rfl h16 h17 h18 h21 h11 h12 h19 hla hpr hpc
    set s1 := planarRAMRun p ⟨b, M, R⟩ τ1 with hs1
    obtain ⟨pc1, M1, R1⟩ := s1
    simp only at q1 q16 q17 q18 q21 q23 qla qfr qr
    subst q1; subst qr
    have hd0 := hdis 0 0 (by omega) (by omega)
    have f : ∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ la → M1 a = M a := qfr
    have e13 : M1 13 = M 13 := f 13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have e11 : M1 11 = 1 := (f 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h11
    have e12 : M1 12 = 0 := (f 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h12
    have e19 : M1 19 = 2 := (f 19 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h19
    have e20 : M1 20 = M 20 := f 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have e14 : M1 14 = M 14 := f 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have epr : ∀ j, j < r → M1 (pr + 2 + 2 * j) = M (pr + 2 * (j + 1)) := by
      intro j hj
      rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun h => (hdis 0 (j + 1) (by omega) (by omega)).1 (by omega))]
      congr 1; ring
    have epc : ∀ j, j < r → M1 (pc + M1 20 + j * M1 20) = M (pc + (j + 1) * M 20) := by
      intro j hj
      rw [e20, f _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun h => (hdis 0 (j + 1) (by omega) (by omega)).2 (by rw [← h]; ring))]
      congr 1; ring
    have ela : ∀ j, j < r → M1 (la + 2 + 2 * j) = M (la + 2 * (j + 1)) := by
      intro j hj
      rw [f _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      congr 1; ring
    obtain ⟨τ2, hτ2, r1, r2, r3, r4, r5⟩ := ih (w + 1) (pr + 2) (pc + M1 20) (la + 2) M1 R1
      (by omega) q16 q17 (by rw [q18, e20]) q21 e11 e12 e19 (by omega) (by omega) (by omega)
      (by
        intro j j' hj hj'
        have := hdis (j + 1) (j' + 1) (by omega) (by omega)
        rw [e20]
        constructor
        · intro h; exact this.1 (by omega)
        · intro h; exact this.2 (by rw [show (j' + 1) * M 20 = j' * M 20 + M 20 by ring]; omega))
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨r1, ?_, ?_, ?_, r5⟩
    · intro j hj
      rcases j with _ | j
      · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul]
        rw [r4 la (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega)]
        simpa using qla
      · have := r2 j (by omega)
        rw [show la + 2 * (j + 1) = la + 2 + 2 * j by ring, this, epr j (by omega), epc j (by omega),
          ela j (by omega), e14, show la + 2 + 2 * j = la + 2 * (j + 1) by ring]
    · rw [r3, q23]
      have htr : ∀ j, j < r →
          (((1 ≤ M1 (pr + 2 + 2 * j) ∨ 1 ≤ M1 (pc + M1 20 + j * M1 20)) ∧ M1 (la + 2 + 2 * j) = 0) ↔
          ((1 ≤ M (pr + 2 * (j + 1)) ∨ 1 ≤ M (pc + (j + 1) * M 20)) ∧ M (la + 2 * (j + 1)) = 0)) := by
        intro j hj; rw [epr j hj, epc j hj, ela j hj]
      by_cases h0 : (1 ≤ M pr ∨ 1 ≤ M pc) ∧ M la = 0
      · have hex : ∃ j, j < r + 1 ∧ (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 :=
          ⟨0, by omega, by simpa using h0⟩
        rw [if_pos hex]
        split_ifs <;> rfl
      · rw [if_neg h0]
        by_cases hex' : ∃ j, j < r ∧ (1 ≤ M1 (pr + 2 + 2 * j) ∨ 1 ≤ M1 (pc + M1 20 + j * M1 20)) ∧
            M1 (la + 2 + 2 * j) = 0
        · obtain ⟨j, hj, ht⟩ := hex'
          rw [if_pos ⟨j, hj, ht⟩, if_pos ⟨j + 1, by omega, (htr j hj).mp ht⟩]
        · rw [if_neg hex', if_neg]
          rintro ⟨j, hj, ht⟩
          rcases j with _ | j
          · exact h0 (by simpa using ht)
          · exact hex' ⟨j, by omega, (htr j (by omega)).mpr ht⟩
    · intro a a16 a17 a18 a21 a22 a23 hne
      rw [r4 a a16 a17 a18 a21 a22 a23 (fun j hj => by have := hne (j + 1) (by omega); omega)]
      exact f a a16 a17 a18 a21 a22 a23 (by have := hne 0 (by omega); omega)

end

end RW

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
      [natBranch 13 16 (b + 14) (b + 1), natLoad 22 17, natBranch 11 22 (b + 5) (b + 3), natLoad 22 18, natBranch 11 22 (b + 5) (b + 9), natLoad 22 21, natBranch 22 12 (b + 7) (b + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump b]) :
    ∀ (r w pr pc la : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = M 13 →
      M 16 = w → M 17 = pr → M 18 = pc → M 21 = la → M 11 = 1 → M 12 = 0 → M 19 = 2 →
      32 ≤ la → 32 ≤ pr → 32 ≤ pc →
      (∀ j j', j < r → j' < r → la + 2 * j ≠ pr + 2 * j' ∧ la + 2 * j ≠ pc + j' * M 20) →
      ∃ τ, τ ≤ 14 * r + 1 ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 14 ∧
        (∀ j, j < r → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (la + 2 * j) =
          if (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then M 14
          else M (la + 2 * j)) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem 23 =
          (if ∃ j, j < r ∧ (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then 1
            else M 23) ∧
        (∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → a ≠ 23 → (∀ j, j < r → a ≠ la + 2 * j) →
          (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R :=
  RW.row_loop p b hcode
