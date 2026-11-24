-- Prove2me | solution 1 for WilliamsonShmoys.ram_real_spread_fragment
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T15:29:07.177457+00:00
-- url     : https://prove2.me/submissions/d0d93c15-1187-467c-a349-d90c8f57fa96

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace RS
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

lemma run_succ_right (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMStep p (planarRAMRun p s t) := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply']

lemma run_zero (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 0 = s := rfl

section
variable (p : List PlanarRAMInstruction) (base : ℕ)
  (hcode : CodeAt p base
    [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0,
      natBranch 2 11 (base + 12) (base + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6,
      realLoad 0 2, realStore 7 0, jump (base + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0,
      realStore 3 0])
include hcode

lemma code_at (i : ℕ) (hi : i < 16) :
    p[base + i]? = ([natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0,
      natBranch 2 11 (base + 12) (base + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6,
      realLoad 0 2, realStore 7 0, jump (base + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0,
      realStore 3 0] : List PlanarRAMInstruction)[i]? :=
  hcode i (by simpa using hi)

/-- One loop iteration from the loop head with counter `c ≥ 2`. -/
lemma rs_iter (M : ℕ → ℕ) (R : ℕ → ℝ) (c : ℕ) (hc : 2 ≤ c) (h2 : M 2 = c) (h11 : M 11 = 1)
    (h6 : M 6 = 32) :
    planarRAMRun p ⟨base + 5, M, R⟩ 7 =
      ⟨base + 5,
        Function.update (Function.update M 2 (c - 1)) 7 (2 * (c - 1) + 32),
        Function.update (Function.update R 0 (R (c - 1))) (2 * (c - 1) + 32) (R (c - 1))⟩ := by
  have hb : p[base + 5]? = some (natBranch 2 11 (base + 12) (base + 6)) := by
    simpa using code_at p base hcode 5 (by norm_num)
  have i6 : p[base + 6]? = some (natSub 2 2 11) := by simpa using code_at p base hcode 6 (by norm_num)
  have i7 : p[base + 7]? = some (natAdd 7 2 2) := by simpa using code_at p base hcode 7 (by norm_num)
  have i8 : p[base + 8]? = some (natAdd 7 7 6) := by simpa using code_at p base hcode 8 (by norm_num)
  have i9 : p[base + 9]? = some (realLoad 0 2) := by simpa using code_at p base hcode 9 (by norm_num)
  have i10 : p[base + 10]? = some (realStore 7 0) := by simpa using code_at p base hcode 10 (by norm_num)
  have i11 : p[base + 11]? = some (jump (base + 5)) := by simpa using code_at p base hcode 11 (by norm_num)
  have hlt : ¬ M 2 ≤ M 11 := by omega
  rw [show planarRAMRun p ⟨base + 5, M, R⟩ 7 =
      planarRAMRun p ⟨base + 5, M, R⟩ (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) from rfl,
    run_succ, step_exec p _ _ hb]
  simp only [execInstr, if_neg hlt]
  rw [run_succ, step_exec p _ _ i6, run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i7), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i8), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i9), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i10), run_succ]
  simp only [execInstr]
  rw [step_exec p _ _ (by simpa using i11), run_zero]
  simp only [execInstr, Function.update_self, h2, h11, h6,
    Function.update_of_ne (show (11:ℕ) ≠ 2 by norm_num),
    Function.update_of_ne (show (2:ℕ) ≠ 7 by norm_num),
    Function.update_of_ne (show (6:ℕ) ≠ 7 by norm_num),
    Function.update_of_ne (show (6:ℕ) ≠ 2 by norm_num), Function.update_idem]
  rw [show c - 1 + (c - 1) + 32 = 2 * (c - 1) + 32 by ring]

lemma rs_loop :
    ∀ (r c : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), c - 1 = r → M 2 = c → M 11 = 1 → M 6 = 32 →
      (planarRAMRun p ⟨base + 5, M, R⟩ (7 * r + 1)).pc = base + 12 ∧
      (∀ c', 1 ≤ c' → c' < c → (planarRAMRun p ⟨base + 5, M, R⟩ (7 * r + 1)).realMem (2 * c' + 32) = R c') ∧
      (∀ a, a ≠ 0 → (∀ c', 1 ≤ c' → c' < c → a ≠ 2 * c' + 32) →
        (planarRAMRun p ⟨base + 5, M, R⟩ (7 * r + 1)).realMem a = R a) ∧
      (∀ a, a ≠ 2 → a ≠ 7 → (planarRAMRun p ⟨base + 5, M, R⟩ (7 * r + 1)).natMem a = M a) := by
  intro r
  induction r with
  | zero =>
    intro c M R hr h2 h11 h6
    have hb : p[base + 5]? = some (natBranch 2 11 (base + 12) (base + 6)) := by
      simpa using code_at p base hcode 5 (by norm_num)
    have hle : M 2 ≤ M 11 := by omega
    rw [show 7 * 0 + 1 = 0 + 1 from rfl, run_succ, run_zero, step_exec p _ _ hb]
    simp only [execInstr, if_pos hle]
    exact ⟨trivial, fun c' h1 h2' => by omega, fun a _ _ => trivial, fun a _ _ => trivial⟩
  | succ r ih =>
    intro c M R hr h2 h11 h6
    have hc : 2 ≤ c := by omega
    rw [show 7 * (r + 1) + 1 = 7 + (7 * r + 1) by ring, run_add, rs_iter p base hcode M R c hc h2 h11 h6]
    set M' := Function.update (Function.update M 2 (c - 1)) 7 (2 * (c - 1) + 32) with hM'
    set R' := Function.update (Function.update R 0 (R (c - 1))) (2 * (c - 1) + 32) (R (c - 1)) with hR'
    have hfr : ∀ a, a ≠ 2 → a ≠ 7 → M' a = M a := by
      intro a a2 a7; rw [hM', Function.update_of_ne a7, Function.update_of_ne a2]
    have hrf : ∀ a, a ≠ 0 → a ≠ 2 * (c - 1) + 32 → R' a = R a := by
      intro a a0 at'; rw [hR', Function.update_of_ne at', Function.update_of_ne a0]
    obtain ⟨r1, r2, r3, r4⟩ := ih (c - 1) M' R' (by omega)
      (by rw [hM', Function.update_of_ne (by norm_num), Function.update_self])
      (by rw [hfr 11 (by norm_num) (by norm_num), h11])
      (by rw [hfr 6 (by norm_num) (by norm_num), h6])
    refine ⟨r1, ?_, ?_, fun a a2 a7 => (r4 a a2 a7).trans (hfr a a2 a7)⟩
    · intro c' hc'1 hc'2
      by_cases hlast : c' = c - 1
      · subst hlast
        rw [r3 (2 * (c - 1) + 32) (by omega) (fun c'' _ h => by omega), hR', Function.update_self]
      · rw [r2 c' hc'1 (by omega)]
        exact hrf c' (by omega) (by omega)
    · intro a a0 hne
      rw [r3 a a0 (fun c' h1 h2 => hne c' h1 (by omega))]
      exact hrf a a0 (hne (c - 1) (by omega) (by omega))

theorem rspread_fragment (s : PlanarRAMState) (hpc : s.pc = base) (h11 : s.natMem 11 = 1)
    (h12 : s.natMem 12 = 0) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (5 + (7 * (n - 1) + 1) + 4)
    s'.pc = base + 16 ∧
      (∀ c, c < n → s'.realMem (2 * c + 32) = s.realMem c) ∧
      s'.realMem 0 = 0 ∧ s'.realMem (2 * n + 1) = 0 ∧
      (∀ a, a ≠ 0 → a ≠ 32 → a ≠ 2 * n + 1 → (∀ c, c < n → a ≠ 2 * c + 32) →
        s'.realMem a = s.realMem a) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 6 → a ≠ 7 → s'.natMem a = s.natMem a) := by
  intro n
  have c : ∀ i, i < 16 → p[base + i]? = ([natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0,
      natBranch 2 11 (base + 12) (base + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6,
      realLoad 0 2, realStore 7 0, jump (base + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0,
      realStore 3 0] : List PlanarRAMInstruction)[i]? :=
    fun i hi => code_at p base hcode i hi
  have c0 := c 0 (by norm_num); have c1 := c 1 (by norm_num); have c2 := c 2 (by norm_num)
  have c3 := c 3 (by norm_num); have c4 := c 4 (by norm_num); have c12 := c 12 (by norm_num)
  have c13 := c 13 (by norm_num); have c14 := c 14 (by norm_num); have c15 := c 15 (by norm_num)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, add_zero] at c0 c1 c2 c3 c4 c12 c13 c14 c15
  let M1 := Function.update (Function.update (Function.update (Function.update s.natMem 2 n) 6 32)
    3 (n + n)) 3 (n + n + 1)
  let R1 := Function.update s.realMem (n + n + 1) (s.realMem 0)
  have e : planarRAMRun p s 5 = ⟨base + 5, M1, R1⟩ := by
    rw [show planarRAMRun p s 5 = planarRAMRun p s (0 + 1 + 1 + 1 + 1 + 1) from rfl,
      run_succ, step_exec p _ _ (by rw [hpc]; exact c0), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c1), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c2), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c3), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c4), run_zero]
    simp only [execInstr, hpc, M1, R1, h12, add_zero, Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 2 by norm_num), Function.update_of_ne (show (0:ℕ) ≠ 6 by norm_num),
      Function.update_of_ne (show (11:ℕ) ≠ 3 by norm_num), Function.update_of_ne (show (11:ℕ) ≠ 6 by norm_num),
      Function.update_of_ne (show (11:ℕ) ≠ 2 by norm_num), h11]
    rfl
  have m2 : M1 2 = n := by simp [M1]
  have m11 : M1 11 = 1 := by simp [M1, h11]
  have m6 : M1 6 = 32 := by simp [M1]
  have m3 : M1 3 = n + n + 1 := by simp [M1]
  obtain ⟨r1, r2, r3, r4⟩ := rs_loop p base hcode (n - 1) n M1 R1 rfl m2 m11 m6
  rw [run_add p s (5 + (7 * (n - 1) + 1)) 4, run_add p s 5 (7 * (n - 1) + 1), e,
    show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
  set s2 := planarRAMRun p ⟨base + 5, M1, R1⟩ (7 * (n - 1) + 1) with hs2
  have q3 : s2.natMem 3 = n + n + 1 := by rw [r4 3 (by norm_num) (by norm_num), m3]
  have q6 : s2.natMem 6 = 32 := by rw [r4 6 (by norm_num) (by norm_num), m6]
  rw [run_succ, step_exec p s2 _ (by rw [r1]; exact c12)]
  rw [run_succ, step_exec p _ _ (by simp only [execInstr, r1]; exact c13)]
  rw [run_succ, step_exec p _ _ (by simp only [execInstr, r1]; exact c14)]
  rw [run_succ, step_exec p _ _ (by simp only [execInstr, r1]; exact c15), run_zero]
  simp only [execInstr, q3, q6]
  have hsave : s2.realMem (n + n + 1) = s.realMem 0 := by
    rw [r3 (n + n + 1) (by omega) (fun c' _ _ => by omega)]
    simp [R1]
  have hodd0 : (32 : ℕ) ≠ n + n + 1 := by omega
  have hsrc : ∀ c', 1 ≤ c' → c' < n → s2.realMem (2 * c' + 32) = s.realMem c' := by
    intro c' h1 h2
    rw [r2 c' h1 h2]
    simp only [R1]
    rw [Function.update_of_ne (by omega)]
  have hfr2 : ∀ a, a ≠ 0 → a ≠ n + n + 1 → (∀ c', 1 ≤ c' → c' < n → a ≠ 2 * c' + 32) →
      s2.realMem a = s.realMem a := by
    intro a a0 an hne
    rw [r3 a a0 hne]
    simp only [R1]
    rw [Function.update_of_ne an]
  refine ⟨by simp [r1], ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    by_cases h0 : c' = 0
    · subst h0
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [Function.update_of_ne hodd0, Function.update_of_ne (by norm_num), Function.update_self,
        Function.update_self, hsave]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsrc c' (by omega) hc']
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | ring
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | ring
  · intro a a0 a32 an hne
    simp only [Function.update_apply]
    split_ifs <;> first | omega | skip
    exact hfr2 a a0 (by omega) (fun c' h1 h2 => hne c' h2)
  · intro a a2 a3 a6 a7
    rw [r4 a a2 a7]
    simp only [M1, Function.update_of_ne a3, Function.update_of_ne a6, Function.update_of_ne a2]

end

end RS

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (base + 12) (base + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (base + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0]) (s : PlanarRAMState) (hpc : s.pc = base) (h11 : s.natMem 11 = 1)
    (h12 : s.natMem 12 = 0) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (5 + (7 * (n - 1) + 1) + 4)
    s'.pc = base + 16 ∧
      (∀ c, c < n → s'.realMem (2 * c + 32) = s.realMem c) ∧
      s'.realMem 0 = 0 ∧ s'.realMem (2 * n + 1) = 0 ∧
      (∀ a, a ≠ 0 → a ≠ 32 → a ≠ 2 * n + 1 → (∀ c, c < n → a ≠ 2 * c + 32) →
        s'.realMem a = s.realMem a) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 6 → a ≠ 7 → s'.natMem a = s.natMem a) :=
  RS.rspread_fragment p base hcode s hpc h11 h12
