-- Prove2me | solution 1 for WilliamsonShmoys.planarRAMStep_eq_execInstr
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:46:51.601328+00:00
-- url     : https://prove2.me/submissions/e75d1989-e269-454f-940f-7d19c6912381

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace PK
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

lemma run_two (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 2 = planarRAMStep p (planarRAMStep p s) := rfl

/-- One "double cell 1, then add cell c" pair. -/
lemma pair_upd (p : List PlanarRAMInstruction) (M : ℕ → ℕ) (R : ℕ → ℝ) (v c pc : ℕ)
    (h0 : p[pc]? = some (natAdd 1 1 1)) (h1 : p[pc + 1]? = some (natAdd 1 1 c)) (hc : c ≠ 1) :
    planarRAMRun p ⟨pc, Function.update M 1 v, R⟩ 2 =
      ⟨pc + 2, Function.update M 1 (2 * v + M c), R⟩ := by
  rw [run_two, step_exec p ⟨pc, Function.update M 1 v, R⟩ _ h0,
    step_exec p (execInstr (natAdd 1 1 1) ⟨pc, Function.update M 1 v, R⟩) _
      (by simpa [execInstr] using h1)]
  simp only [execInstr, Function.update_self, Function.update_idem, Function.update_of_ne hc]
  congr 1
  all_goals first | omega | (congr 1; ring) | rfl

theorem pack_fragment (p : List PlanarRAMInstruction) (base : ℕ) (s : PlanarRAMState)
    (hcode : CodeAt p base
      [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7])
    (hpc : s.pc = base) :
    planarRAMRun p s 12 =
      { pc := base + 12,
        natMem := Function.update s.natMem 1
          (64 * s.natMem 1 + 32 * s.natMem 2 + 16 * s.natMem 3 + 8 * s.natMem 4 +
            4 * s.natMem 5 + 2 * s.natMem 6 + s.natMem 7),
        realMem := s.realMem } := by
  have h0 : p[base + 0]? = some (natAdd 1 1 1) := by simpa using hcode 0 (by norm_num)
  have h1 : p[base + 1]? = some (natAdd 1 1 2) := by simpa using hcode 1 (by norm_num)
  have h2 : p[base + 2]? = some (natAdd 1 1 1) := by simpa using hcode 2 (by norm_num)
  have h3 : p[base + 3]? = some (natAdd 1 1 3) := by simpa using hcode 3 (by norm_num)
  have h4 : p[base + 4]? = some (natAdd 1 1 1) := by simpa using hcode 4 (by norm_num)
  have h5 : p[base + 5]? = some (natAdd 1 1 4) := by simpa using hcode 5 (by norm_num)
  have h6 : p[base + 6]? = some (natAdd 1 1 1) := by simpa using hcode 6 (by norm_num)
  have h7 : p[base + 7]? = some (natAdd 1 1 5) := by simpa using hcode 7 (by norm_num)
  have h8 : p[base + 8]? = some (natAdd 1 1 1) := by simpa using hcode 8 (by norm_num)
  have h9 : p[base + 9]? = some (natAdd 1 1 6) := by simpa using hcode 9 (by norm_num)
  have h10 : p[base + 10]? = some (natAdd 1 1 1) := by simpa using hcode 10 (by norm_num)
  have h11 : p[base + 11]? = some (natAdd 1 1 7) := by simpa using hcode 11 (by norm_num)
  have hs : s = ⟨base + 0, Function.update s.natMem 1 (s.natMem 1), s.realMem⟩ := by
    cases s with
    | mk pc0 M0 R0 =>
      simp only at hpc
      subst hpc
      simp
  conv_lhs => rw [hs]
  rw [show (12 : ℕ) = 2 + 2 + 2 + 2 + 2 + 2 from rfl, run_add, run_add, run_add, run_add, run_add]
  rw [pair_upd p s.natMem s.realMem _ 2 (base + 0) h0 (by simpa using h1) (by norm_num)]
  rw [pair_upd p s.natMem s.realMem _ 3 (base + 2) h2 (by simpa using h3) (by norm_num)]
  rw [pair_upd p s.natMem s.realMem _ 4 (base + 4) h4 (by simpa using h5) (by norm_num)]
  rw [pair_upd p s.natMem s.realMem _ 5 (base + 6) h6 (by simpa using h7) (by norm_num)]
  rw [pair_upd p s.natMem s.realMem _ 6 (base + 8) h8 (by simpa using h9) (by norm_num)]
  rw [pair_upd p s.natMem s.realMem _ 7 (base + 10) h10 (by simpa using h11) (by norm_num)]
  congr 1
  all_goals first | omega | (congr 1; ring) | rfl | simp | (simp; ring)

end PK

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execInstr ins s :=
  PK.step_exec p s ins h
