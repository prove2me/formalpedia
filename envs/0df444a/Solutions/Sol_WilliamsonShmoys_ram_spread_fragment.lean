-- Prove2me | solution 1 for WilliamsonShmoys.ram_spread_fragment
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T12:21:10.896848+00:00
-- url     : https://prove2.me/submissions/35aeadaa-3f7c-424e-bc9c-a38e45ba0bb9

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace SP
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

section
variable (p : List PlanarRAMInstruction) (base : ℕ)
  (hcode : CodeAt p base
    [natConst 5 8, natConst 6 32, natBranch 2 5 (base + 9) (base + 3), natSub 2 2 4,
      natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (base + 2)])
include hcode

lemma code_at (i : ℕ) (hi : i < 9) :
    p[base + i]? = ([natConst 5 8, natConst 6 32, natBranch 2 5 (base + 9) (base + 3), natSub 2 2 4,
      natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (base + 2)] :
        List PlanarRAMInstruction)[i]? :=
  hcode i (by simpa using hi)

/-- One loop iteration: from the loop head with counter `c ≥ 9`. -/
lemma spread_iter (M : ℕ → ℕ) (R : ℕ → ℝ) (c : ℕ) (hc : 9 ≤ c) (h2 : M 2 = c) (h4 : M 4 = 1)
    (h5 : M 5 = 8) (h6 : M 6 = 32) :
    planarRAMRun p ⟨base + 2, M, R⟩ 7 =
      ⟨base + 2,
        Function.update
          (Function.update (Function.update (Function.update M 2 (c - 1)) 7 (2 * (c - 1) + 32)) 3
            (M (c - 1)))
          (2 * (c - 1) + 32) (M (c - 1)),
        R⟩ := by
  have hb : p[base + 2]? = some (natBranch 2 5 (base + 9) (base + 3)) := by
    simpa using code_at p base hcode 2 (by norm_num)
  have i3 : p[base + 3]? = some (natSub 2 2 4) := by simpa using code_at p base hcode 3 (by norm_num)
  have i4 : p[base + 4]? = some (natAdd 7 2 2) := by simpa using code_at p base hcode 4 (by norm_num)
  have i5 : p[base + 5]? = some (natAdd 7 7 6) := by simpa using code_at p base hcode 5 (by norm_num)
  have i6 : p[base + 6]? = some (natLoad 3 2) := by simpa using code_at p base hcode 6 (by norm_num)
  have i7 : p[base + 7]? = some (natStore 7 3) := by simpa using code_at p base hcode 7 (by norm_num)
  have i8 : p[base + 8]? = some (jump (base + 2)) := by simpa using code_at p base hcode 8 (by norm_num)
  have hlt : ¬ M 2 ≤ M 5 := by omega
  rw [show planarRAMRun p ⟨base + 2, M, R⟩ 7 =
      planarRAMRun p ⟨base + 2, M, R⟩ (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) from rfl,
    run_succ, step_exec p _ _ hb]
  simp only [execInstr, if_neg hlt]
  rw [run_succ, step_exec p _ _ i3, run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i4), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i5), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i6), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i7), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i8), run_zero]
  simp only [execInstr, Function.update_self, h2, h4, h6,
    Function.update_of_ne (show (4:ℕ) ≠ 2 by norm_num),
    Function.update_of_ne (show (2:ℕ) ≠ 7 by norm_num),
    Function.update_of_ne (show (6:ℕ) ≠ 7 by norm_num),
    Function.update_of_ne (show (6:ℕ) ≠ 2 by norm_num),
    Function.update_of_ne (show (7:ℕ) ≠ 3 by norm_num),
    Function.update_of_ne (show (3:ℕ) ≠ 7 by norm_num)]
  have hc7 : c - 1 ≠ 7 := by omega
  have hc2 : c - 1 ≠ 2 := by omega
  simp only [Function.update_of_ne hc7, Function.update_of_ne hc2, Function.update_idem]
  rw [show c - 1 + (c - 1) + 32 = 2 * (c - 1) + 32 by ring]

lemma spread_loop :
    ∀ (r c : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), c - 8 = r → M 2 = c → M 4 = 1 → M 5 = 8 → M 6 = 32 →
      (planarRAMRun p ⟨base + 2, M, R⟩ (7 * r + 1)).pc = base + 9 ∧
      (∀ c', 8 ≤ c' → c' < c → (planarRAMRun p ⟨base + 2, M, R⟩ (7 * r + 1)).natMem (2 * c' + 32) = M c') ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 7 → (∀ c', 8 ≤ c' → c' < c → a ≠ 2 * c' + 32) →
        (planarRAMRun p ⟨base + 2, M, R⟩ (7 * r + 1)).natMem a = M a) ∧
      (planarRAMRun p ⟨base + 2, M, R⟩ (7 * r + 1)).realMem = R := by
  intro r
  induction r with
  | zero =>
    intro c M R hr h2 h4 h5 h6
    have hb : p[base + 2]? = some (natBranch 2 5 (base + 9) (base + 3)) := by
      simpa using code_at p base hcode 2 (by norm_num)
    have hle : M 2 ≤ M 5 := by omega
    rw [show 7 * 0 + 1 = 0 + 1 from rfl, run_succ, run_zero, step_exec p _ _ hb]
    simp only [execInstr, if_pos hle]
    refine ⟨trivial, fun c' h1 h2' => by omega, fun a _ _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro c M R hr h2 h4 h5 h6
    have hc : 9 ≤ c := by omega
    rw [show 7 * (r + 1) + 1 = 7 + (7 * r + 1) by ring, run_add,
      spread_iter p base hcode M R c hc h2 h4 h5 h6]
    set M' := Function.update
          (Function.update (Function.update (Function.update M 2 (c - 1)) 7 (2 * (c - 1) + 32)) 3
            (M (c - 1)))
          (2 * (c - 1) + 32) (M (c - 1)) with hM'
    have hfr : ∀ a, a ≠ 2 → a ≠ 3 → a ≠ 7 → a ≠ 2 * (c - 1) + 32 → M' a = M a := by
      intro a a2 a3 a7 at'
      rw [hM', Function.update_of_ne at', Function.update_of_ne a3, Function.update_of_ne a7,
        Function.update_of_ne a2]
    have h2' : M' 2 = c - 1 := by
      rw [hM', Function.update_of_ne (by omega), Function.update_of_ne (by norm_num),
        Function.update_of_ne (by norm_num), Function.update_self]
    obtain ⟨r1, r2, r3, r4⟩ := ih (c - 1) M' R (by omega) h2'
      (by rw [hfr 4 (by norm_num) (by norm_num) (by norm_num) (by omega), h4])
      (by rw [hfr 5 (by norm_num) (by norm_num) (by norm_num) (by omega), h5])
      (by rw [hfr 6 (by norm_num) (by norm_num) (by norm_num) (by omega), h6])
    refine ⟨r1, ?_, ?_, r4⟩
    · intro c' hc'1 hc'2
      by_cases hlast : c' = c - 1
      · subst hlast
        rw [r3 (2 * (c - 1) + 32) (by omega) (by omega) (by omega) (fun c'' _ h => by omega)]
        rw [hM', Function.update_self]
      · rw [r2 c' hc'1 (by omega)]
        exact hfr c' (by omega) (by omega) (by omega) (by omega)
    · intro a a2 a3 a7 hne
      rw [r3 a a2 a3 a7 (fun c' h1 h2 => hne c' h1 (by omega))]
      exact hfr a a2 a3 a7 (hne (c - 1) (by omega) (by omega))

theorem spread_fragment (s : PlanarRAMState) (hpc : s.pc = base) (h4 : s.natMem 4 = 1) :
    let L := s.natMem 2
    let s' := planarRAMRun p s (2 + 7 * (L - 8) + 1)
    s'.pc = base + 9 ∧
      (∀ c, 8 ≤ c → c < L → s'.natMem (2 * c + 32) = s.natMem c) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 5 → a ≠ 6 → a ≠ 7 → (∀ c, 8 ≤ c → c < L → a ≠ 2 * c + 32) →
        s'.natMem a = s.natMem a) ∧
      s'.realMem = s.realMem := by
  intro L
  have c0 : p[base + 0]? = some (natConst 5 8) := by simpa using code_at p base hcode 0 (by norm_num)
  have c1 : p[base + 1]? = some (natConst 6 32) := by simpa using code_at p base hcode 1 (by norm_num)
  let M1 := Function.update (Function.update s.natMem 5 8) 6 32
  have e : planarRAMRun p s 2 = ⟨base + 2, M1, s.realMem⟩ := by
    rw [show planarRAMRun p s 2 = planarRAMRun p s (0 + 1 + 1) from rfl, run_succ,
      step_exec p _ _ (by rw [hpc]; simpa using c0), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c1), run_zero]
    simp only [execInstr, hpc, M1]
  have hM1 : ∀ a, a ≠ 5 → a ≠ 6 → M1 a = s.natMem a := by
    intro a h5 h6
    simp only [M1, Function.update_of_ne h6, Function.update_of_ne h5]
  rw [run_add, run_add, e]
  obtain ⟨r1, r2, r3, r4⟩ := spread_loop p base hcode (L - 8) L M1 s.realMem rfl
    (by rw [hM1 2 (by norm_num) (by norm_num)])
    (by rw [hM1 4 (by norm_num) (by norm_num), h4])
    (by simp [M1]) (by simp [M1])
  rw [← run_add]
  refine ⟨r1, fun c h1 h2 => ?_, fun a a2 a3 a5 a6 a7 hne => ?_, r4⟩
  · rw [r2 c h1 h2, hM1 c (by omega) (by omega)]
  · rw [r3 a a2 a3 a7 hne, hM1 a a5 a6]

end

end SP

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 5 8, natConst 6 32, natBranch 2 5 (base + 9) (base + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (base + 2)]) (s : PlanarRAMState) (hpc : s.pc = base) (h4 : s.natMem 4 = 1) :
    let L := s.natMem 2
    let s' := planarRAMRun p s (2 + 7 * (L - 8) + 1)
    s'.pc = base + 9 ∧
      (∀ c, 8 ≤ c → c < L → s'.natMem (2 * c + 32) = s.natMem c) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 5 → a ≠ 6 → a ≠ 7 → (∀ c, 8 ≤ c → c < L → a ≠ 2 * c + 32) →
        s'.natMem a = s.natMem a) ∧
      s'.realMem = s.realMem :=
  SP.spread_fragment p base hcode s hpc h4
