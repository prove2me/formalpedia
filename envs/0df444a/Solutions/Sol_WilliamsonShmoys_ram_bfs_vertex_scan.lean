-- Prove2me | solution 1 for WilliamsonShmoys.ram_bfs_vertex_scan
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T02:11:11.072643+00:00
-- url     : https://prove2.me/submissions/b7ce756a-7242-424e-b1bf-5c99e5b3a8cb

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Theorems.Thm_WilliamsonShmoys_ram_bfs_row_scan

set_option autoImplicit false

namespace VS
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
variable (p : List PlanarRAMInstruction) (c : ℕ)
  (hcode : CodeAt p c
    [natBranch 13 24 (c + 27) (c + 1),
      natLoad 22 27,
      natBranch 22 15 (c + 3) (c + 22),
      natBranch 15 22 (c + 4) (c + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (c + 8 + 14) (c + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (c + 8 + 7) (c + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (c + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump c])
include hcode

lemma row_code : CodeAt p (c + 8)
    [natBranch 13 16 (c + 8 + 14) (c + 8 + 1), natLoad 22 17, natBranch 11 22 (c + 8 + 5) (c + 8 + 3),
      natLoad 22 18, natBranch 11 22 (c + 8 + 5) (c + 8 + 9), natLoad 22 21,
      natBranch 22 12 (c + 8 + 7) (c + 8 + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11,
      natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump (c + 8)] := by
  apply codeAt_sub p c 8 _ _ hcode
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

set_option maxHeartbeats 4000000 in
/-- One iteration of the vertex scan, from the loop head with `u < n`. -/
lemma vscan_iter (M : ℕ → ℕ) (R : ℕ → ℝ) (n u t LVB : ℕ) (hu : u < n) (ht : 1 ≤ t)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h24 : M 24 = u) (h25 : M 25 = 36 + 2 * u * n)
    (h26 : M 26 = 36 + 2 * u) (h27 : M 27 = LVB + 2 * u) (h28 : M 28 = LVB)
    (h11 : M 11 = 1) (h12 : M 12 = 0) (h19 : M 19 = 2) (h15 : M 15 = t) (h14 : M 14 = t + 1)
    (hLVB : 36 + 2 * n * n ≤ LVB) :
    ∃ τ, τ ≤ 14 * n + 14 ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).pc = c ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 24 = u + 1 ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 25 = 36 + 2 * (u + 1) * n ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 26 = 36 + 2 * (u + 1) ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 27 = LVB + 2 * (u + 1) ∧
      (∀ j, j < n → (planarRAMRun p ⟨c, M, R⟩ τ).natMem (LVB + 2 * j) =
        if M (LVB + 2 * u) = t ∧ (1 ≤ M (36 + 2 * u * n + 2 * j) ∨ 1 ≤ M (36 + 2 * u + j * (2 * n))) ∧
            M (LVB + 2 * j) = 0 then t + 1 else M (LVB + 2 * j)) ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 23 =
        (if M (LVB + 2 * u) = t ∧ ∃ j, j < n ∧
            (1 ≤ M (36 + 2 * u * n + 2 * j) ∨ 1 ≤ M (36 + 2 * u + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
          then 1 else M 23) ∧
      (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 15 → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨c, M, R⟩ τ).natMem 20 = 2 * n ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).natMem 28 = LVB ∧
      (planarRAMRun p ⟨c, M, R⟩ τ).realMem = R := by
  have c0 : p[c + 0]? = some (natBranch 13 24 (c + 27) (c + 1)) := by simpa using hcode 0 (by simp)
  have c1 : p[c + 1]? = some (natLoad 22 27) := by simpa using hcode 1 (by simp)
  have c2 : p[c + 2]? = some (natBranch 22 15 (c + 3) (c + 22)) := by simpa using hcode 2 (by simp)
  have c3 : p[c + 3]? = some (natBranch 15 22 (c + 4) (c + 22)) := by simpa using hcode 3 (by simp)
  have c4 : p[c + 4]? = some (natConst 16 0) := by simpa using hcode 4 (by simp)
  have c5 : p[c + 5]? = some (natAdd 17 25 12) := by simpa using hcode 5 (by simp)
  have c6 : p[c + 6]? = some (natAdd 18 26 12) := by simpa using hcode 6 (by simp)
  have c7 : p[c + 7]? = some (natAdd 21 28 12) := by simpa using hcode 7 (by simp)
  have c8 : p[c + 8]? = some (natBranch 13 16 (c + 8 + 14) (c + 8 + 1)) := by simpa using hcode 8 (by simp)
  have c9 : p[c + 9]? = some (natLoad 22 17) := by simpa using hcode 9 (by simp)
  have c10 : p[c + 10]? = some (natBranch 11 22 (c + 8 + 5) (c + 8 + 3)) := by simpa using hcode 10 (by simp)
  have c11 : p[c + 11]? = some (natLoad 22 18) := by simpa using hcode 11 (by simp)
  have c12 : p[c + 12]? = some (natBranch 11 22 (c + 8 + 5) (c + 8 + 9)) := by simpa using hcode 12 (by simp)
  have c13 : p[c + 13]? = some (natLoad 22 21) := by simpa using hcode 13 (by simp)
  have c14 : p[c + 14]? = some (natBranch 22 12 (c + 8 + 7) (c + 8 + 9)) := by simpa using hcode 14 (by simp)
  have c15 : p[c + 15]? = some (natStore 21 14) := by simpa using hcode 15 (by simp)
  have c16 : p[c + 16]? = some (natAdd 23 11 12) := by simpa using hcode 16 (by simp)
  have c17 : p[c + 17]? = some (natAdd 16 16 11) := by simpa using hcode 17 (by simp)
  have c18 : p[c + 18]? = some (natAdd 17 17 19) := by simpa using hcode 18 (by simp)
  have c19 : p[c + 19]? = some (natAdd 18 18 20) := by simpa using hcode 19 (by simp)
  have c20 : p[c + 20]? = some (natAdd 21 21 19) := by simpa using hcode 20 (by simp)
  have c21 : p[c + 21]? = some (jump (c + 8)) := by simpa using hcode 21 (by simp)
  have c22 : p[c + 22]? = some (natAdd 24 24 11) := by simpa using hcode 22 (by simp)
  have c23 : p[c + 23]? = some (natAdd 25 25 20) := by simpa using hcode 23 (by simp)
  have c24 : p[c + 24]? = some (natAdd 26 26 19) := by simpa using hcode 24 (by simp)
  have c25 : p[c + 25]? = some (natAdd 27 27 19) := by simpa using hcode 25 (by simp)
  have c26 : p[c + 26]? = some (jump c) := by simpa using hcode 26 (by simp)
  have hu36 : ∀ k, k ≤ 28 → LVB + 2 * u ≠ k := fun k hk => by omega
  have hLV : 36 ≤ LVB := by omega
  by_cases hv : M (LVB + 2 * u) = t
  · let M8 := Function.update (Function.update (Function.update (Function.update
        (Function.update M 22 t) 16 0) 17 (36 + 2 * u * n)) 18 (36 + 2 * u)) 21 LVB
    have e8 : planarRAMRun p ⟨c, M, R⟩ 8 = ⟨c + 8, M8, R⟩ := by
      rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p c 0 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c0]
      rw [run_succ, step_at p c 1 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c1]
      rw [run_succ, step_at p c 2 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c2]
      rw [run_succ, step_at p c 3 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c3]
      rw [run_succ, step_at p c 4 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c4]
      rw [run_succ, step_at p c 5 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c5]
      rw [run_succ, step_at p c 6 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c6]
      rw [run_succ, step_at p c 7 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]) c7]
      rw [run_zero]
      simp only [execInstr]
      congr 1
      · simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hu36]
      · funext a
        simp [M8, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv]
    have m8 : ∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → M8 a = M a := by
      intro a a16 a17 a18 a21 a22
      simp only [M8, Function.update_of_ne a16, Function.update_of_ne a17, Function.update_of_ne a18,
        Function.update_of_ne a21, Function.update_of_ne a22]
    have g : ∀ a, 28 < a → M8 a = M a := fun a ha => m8 a (by omega) (by omega) (by omega) (by omega) (by omega)
    have hdis : ∀ j j', j < n → j' < n → LVB + 2 * j ≠ 36 + 2 * u * n + 2 * j' ∧
        LVB + 2 * j ≠ 36 + 2 * u + j' * M8 20 := by
      intro j j' hj hj'
      rw [m8 20 (by omega) (by omega) (by omega) (by omega) (by omega), h20]
      constructor
      · have : 2 * u * n + 2 * j' < 2 * n * n := by nlinarith
        omega
      · have : 2 * u + j' * (2 * n) < 2 * n * n := by nlinarith
        omega
    obtain ⟨τr, hτr, r1, r2, r3, r4, r5⟩ := WilliamsonShmoys.ram_bfs_row_scan p (c + 8) (row_code p c hcode)
      n 0 (36 + 2 * u * n) (36 + 2 * u) LVB M8 R
      (by rw [m8 13 (by omega) (by omega) (by omega) (by omega) (by omega), h13]; omega)
      (by simp [M8]) (by simp [M8]) (by simp [M8]) (by simp [M8])
      (by rw [m8 11 (by omega) (by omega) (by omega) (by omega) (by omega), h11])
      (by rw [m8 12 (by omega) (by omega) (by omega) (by omega) (by omega), h12])
      (by rw [m8 19 (by omega) (by omega) (by omega) (by omega) (by omega), h19])
      (by omega) (by omega) (by omega) hdis
    refine ⟨8 + τr + 5, by omega, ?_⟩
    rw [run_add, run_add, e8]
    set S9 := planarRAMRun p ⟨c + 8, M8, R⟩ τr with hS9
    obtain ⟨pc9, M9, R9⟩ := S9
    simp only at r1 r2 r3 r4 r5
    subst r1; subst r5
    have gE : ∀ j, M8 (36 + 2 * u * n + 2 * j) = M (36 + 2 * u * n + 2 * j) := fun j => g _ (by omega)
    have gC : ∀ j, M8 (36 + 2 * u + j * M8 20) = M (36 + 2 * u + j * (2 * n)) := by
      intro j
      rw [m8 20 (by omega) (by omega) (by omega) (by omega) (by omega), h20]
      exact g _ (by omega)
    have gL : ∀ j, M8 (LVB + 2 * j) = M (LVB + 2 * j) := fun j => g _ (by omega)
    have g14 : M8 14 = t + 1 := by rw [m8 14 (by omega) (by omega) (by omega) (by omega) (by omega), h14]
    have g23 : M8 23 = M 23 := m8 23 (by omega) (by omega) (by omega) (by omega) (by omega)
    have f9 : ∀ a, (a ≤ 15 ∨ (23 < a ∧ ∀ j, j < n → a ≠ LVB + 2 * j)) → M9 a = M a := by
      intro a ha
      have hL : ∀ j, j < n → a ≠ LVB + 2 * j := by
        intro j hj; rcases ha with ha | ⟨_, ha⟩
        · omega
        · exact ha j hj
      rw [r4 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hL]
      exact m8 a (by omega) (by omega) (by omega) (by omega) (by omega)
    have q24 := f9 24 (Or.inr ⟨by omega, fun j _ => by omega⟩)
    have q25 := f9 25 (Or.inr ⟨by omega, fun j _ => by omega⟩)
    have q26 := f9 26 (Or.inr ⟨by omega, fun j _ => by omega⟩)
    have q27 := f9 27 (Or.inr ⟨by omega, fun j _ => by omega⟩)
    have q28 := f9 28 (Or.inr ⟨by omega, fun j _ => by omega⟩)
    have q11 := f9 11 (Or.inl (by omega))
    have q19 : M9 19 = 2 := by
      rw [r4 19 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega),
        m8 19 (by omega) (by omega) (by omega) (by omega) (by omega), h19]
    have q20 : M9 20 = 2 * n := by
      rw [r4 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega),
        m8 20 (by omega) (by omega) (by omega) (by omega) (by omega), h20]
    rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at p c 22 _ (by simp [execInstr]; try omega) c22]
    rw [run_succ, step_at p c 23 _ (by simp [execInstr]; try omega) c23]
    rw [run_succ, step_at p c 24 _ (by simp [execInstr]; try omega) c24]
    rw [run_succ, step_at p c 25 _ (by simp [execInstr]; try omega) c25]
    rw [run_succ, step_at p c 26 _ (by simp [execInstr]; try omega) c26]
    rw [run_zero]
    simp only [execInstr]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simp [q24, q11, h24, h11]
    · simp [q25, q20, h25]; ring
    · simp [q26, q19, h26]; ring
    · simp [q27, q19, h27]; ring
    · intro j hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), r2 j hj, gE, gC, gL, g14]
      simp [hv]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), r3, g23]
      simp only [gE, gC, gL, hv, true_and]
    · intro a ha hne
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact f9 a (Or.inr ⟨by omega, hne⟩)
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact f9 a (Or.inl ha)
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), q19]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), q20]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), q28, h28]
  · by_cases hle : M (LVB + 2 * u) ≤ t
    · have hge : ¬ t ≤ M (LVB + 2 * u) := by omega
      refine ⟨9, by omega, ?_⟩
      rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p c 0 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c0]
      rw [run_succ, step_at p c 1 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c1]
      rw [run_succ, step_at p c 2 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c2]
      rw [run_succ, step_at p c 3 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c3]
      rw [run_succ, step_at p c 22 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c22]
      rw [run_succ, step_at p c 23 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c23]
      rw [run_succ, step_at p c 24 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c24]
      rw [run_succ, step_at p c 25 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c25]
      rw [run_succ, step_at p c 26 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge, hu36]) c26]
      rw [run_zero]
      simp only [execInstr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro j hj; simp (disch := omega) only [Function.update_apply, if_neg]; simp [hv]; done)
        | (intro a ha hne; simp (disch := omega) only [Function.update_apply, if_neg]; done)
        | (intro a ha; simp (disch := omega) only [Function.update_apply, if_neg]; done)
        | (simp (disch := omega) only [Function.update_apply, if_neg]; simp [hv]; done)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge]; done)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge]; ring)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hge]; omega)
    · refine ⟨8, by omega, ?_⟩
      rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p c 0 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c0]
      rw [run_succ, step_at p c 1 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c1]
      rw [run_succ, step_at p c 2 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c2]
      rw [run_succ, step_at p c 22 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c22]
      rw [run_succ, step_at p c 23 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c23]
      rw [run_succ, step_at p c 24 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c24]
      rw [run_succ, step_at p c 25 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c25]
      rw [run_succ, step_at p c 26 _ (by simp [execInstr, Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle, hu36]) c26]
      rw [run_zero]
      simp only [execInstr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro j hj; simp (disch := omega) only [Function.update_apply, if_neg]; simp [hv]; done)
        | (intro a ha hne; simp (disch := omega) only [Function.update_apply, if_neg]; done)
        | (intro a ha; simp (disch := omega) only [Function.update_apply, if_neg]; done)
        | (simp (disch := omega) only [Function.update_apply, if_neg]; simp [hv]; done)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle]; done)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle]; ring)
        | (simp [Function.update_apply, h11, h12, h13, h14, h15, h19, h20, h24, h25, h26, h27, h28, hu, hv, hle]; omega)

open Classical in
lemma vscan_loop (n t LVB : ℕ) (ht : 1 ≤ t) (hLVB : 36 + 2 * n * n ≤ LVB) :
    ∀ (r u : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), u + r = n →
      M 13 = n → M 20 = 2 * n → M 24 = u → M 25 = 36 + 2 * u * n → M 26 = 36 + 2 * u →
      M 27 = LVB + 2 * u → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      ∃ τ, τ ≤ r * (14 * n + 14) + 1 ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).pc = c + 27 ∧
        (∀ j, j < n → (planarRAMRun p ⟨c, M, R⟩ τ).natMem (LVB + 2 * j) =
          if M (LVB + 2 * j) = 0 ∧ ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
          then t + 1 else M (LVB + 2 * j)) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 23 =
          (if ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
            then 1 else M 23) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 15 → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨c, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).realMem = R := by
  have c0 : p[c + 0]? = some (natBranch 13 24 (c + 27) (c + 1)) := by simpa using hcode 0 (by simp)
  intro r
  induction r with
  | zero =>
    intro u M R hu h13 h20 h24 h25 h26 h27 h28 h11 h12 h19 h15 h14
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p c 0 _ (by simp) c0, run_zero]
    have hle : M 13 ≤ M 24 := by omega
    simp only [execInstr, if_pos hle]
    refine ⟨trivial, fun j hj => ?_, ?_, fun a _ _ => trivial, fun a _ => trivial, h19, h20, h28, trivial⟩
    · rw [if_neg]; rintro ⟨_, v, hv1, hv2, _⟩; omega
    · rw [if_neg]; rintro ⟨v, hv1, hv2, _⟩; omega
  | succ r ih =>
    intro u M R hu h13 h20 h24 h25 h26 h27 h28 h11 h12 h19 h15 h14
    obtain ⟨τ1, hτ1, q1, q24, q25, q26, q27, qL, q23, qfr, qlo, q19, q20, q28, qr⟩ :=
      vscan_iter p c hcode M R n u t LVB (by omega) ht h13 h20 h24 h25 h26 h27 h28 h11 h12 h19 h15 h14 hLVB
    set S1 := planarRAMRun p ⟨c, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 q24 q25 q26 q27 qL q23 qfr qlo q19 q20 q28 qr
    subst q1; subst qr
    have e11 : M1 11 = 1 := (qlo 11 (by omega)).trans h11
    have e12 : M1 12 = 0 := (qlo 12 (by omega)).trans h12
    have e13 : M1 13 = n := (qlo 13 (by omega)).trans h13
    have e14 : M1 14 = t + 1 := (qlo 14 (by omega)).trans h14
    have e15 : M1 15 = t := (qlo 15 (by omega)).trans h15
    have eE : ∀ v j, v < n → j < n → M1 (36 + 2 * v * n + 2 * j) = M (36 + 2 * v * n + 2 * j) := by
      intro v j hv hj
      have h1 := Nat.mul_le_mul_right n (show v + 1 ≤ n by omega)
      have h2 : (v + 1) * n = v * n + n := by ring
      have h3 : 2 * v * n = 2 * (v * n) := by ring
      have : 2 * v * n + 2 * j < 2 * n * n := by rw [h3, Nat.mul_assoc]; omega
      exact qfr _ (by omega) (fun j' _ => by omega)
    have eC : ∀ v j, v < n → j < n → M1 (36 + 2 * v + j * (2 * n)) = M (36 + 2 * v + j * (2 * n)) := by
      intro v j hv hj
      have h1 := Nat.mul_le_mul_right (2 * n) (show j + 1 ≤ n by omega)
      have h2 : (j + 1) * (2 * n) = j * (2 * n) + 2 * n := by ring
      have h3 : n * (2 * n) = 2 * n * n := by ring
      have : 2 * v + j * (2 * n) < 2 * n * n := by omega
      exact qfr _ (by omega) (fun j' _ => by omega)
    obtain ⟨τ2, hτ2, r1, rL, r23, rfr, rlo, r19, r20, r28, rr⟩ :=
      ih (u + 1) M1 R1 (by omega) e13 q20 q24 q25 q26 q27 q28 e11 e12 q19 e15 e14
    have hrr : (r + 1) * (14 * n + 14) = r * (14 * n + 14) + (14 * n + 14) := by ring
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    -- label facts of M1 in terms of M
    have hL1 : ∀ j, j < n → (M1 (LVB + 2 * j) = t ↔ M (LVB + 2 * j) = t) := by
      intro j hj; rw [qL j hj]; split_ifs with h <;> omega
    have hL0 : ∀ j, j < n → (M1 (LVB + 2 * j) = 0 ↔ (M (LVB + 2 * j) = 0 ∧
        ¬ (M (LVB + 2 * u) = t ∧ (1 ≤ M (36 + 2 * u * n + 2 * j) ∨ 1 ≤ M (36 + 2 * u + j * (2 * n)))))) := by
      intro j hj; rw [qL j hj]; split_ifs with h <;> constructor <;> intro h' <;> first | omega | tauto
    refine ⟨r1, ?_, ?_, ?_, ?_, r19, r20, r28, rr⟩
    · intro j hj
      rw [rL j hj]
      have key : (∃ v, u + 1 ≤ v ∧ v < n ∧ M1 (LVB + 2 * v) = t ∧ (1 ≤ M1 (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M1 (36 + 2 * v + j * (2 * n)))) ↔
          (∃ v, u + 1 ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))) := by
        constructor
        · rintro ⟨v, a, b, c', d⟩
          exact ⟨v, a, b, (hL1 v b).1 c', by rwa [eE v j b hj, eC v j b hj] at d⟩
        · rintro ⟨v, a, b, c', d⟩
          exact ⟨v, a, b, (hL1 v b).2 c', by rwa [eE v j b hj, eC v j b hj]⟩
      by_cases hX : M (LVB + 2 * j) = 0
      · by_cases hU : M (LVB + 2 * u) = t ∧ (1 ≤ M (36 + 2 * u * n + 2 * j) ∨ 1 ≤ M (36 + 2 * u + j * (2 * n)))
        · have hm : M1 (LVB + 2 * j) = t + 1 := by rw [qL j hj, if_pos ⟨hU.1, hU.2, hX⟩]
          rw [if_neg (by rw [hm]; omega), hm, if_pos ⟨hX, u, le_refl _, by omega, hU.1, hU.2⟩]
        · have hm : M1 (LVB + 2 * j) = M (LVB + 2 * j) := by
            rw [qL j hj, if_neg (fun h => hU ⟨h.1, h.2.1⟩)]
          rw [hm]
          by_cases hE : ∃ v, u + 1 ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
          · obtain ⟨v, a, b, c', d⟩ := hE
            rw [if_pos ⟨hX, key.2 ⟨v, a, b, c', d⟩⟩, if_pos ⟨hX, v, by omega, b, c', d⟩]
          · rw [if_neg (fun h => hE (key.1 h.2)), if_neg]
            rintro ⟨_, v, a, b, c', d⟩
            rcases Nat.eq_or_lt_of_le a with e | e
            · subst e; exact hU ⟨c', d⟩
            · exact hE ⟨v, e, b, c', d⟩
      · have hm : M1 (LVB + 2 * j) = M (LVB + 2 * j) := by rw [qL j hj, if_neg (fun h => hX h.2.2)]
        rw [hm, if_neg (fun h => hX h.1), if_neg (fun h => hX h.1)]
    · rw [r23, q23]
      by_cases hPu : M (LVB + 2 * u) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * u * n + 2 * j) ∨ 1 ≤ M (36 + 2 * u + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
      · have hR : ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0 :=
          ⟨u, le_refl _, by omega, hPu⟩
        rw [if_pos hPu, if_pos hR]; split_ifs <;> rfl
      · rw [if_neg hPu]
        have hz : ∀ j, j < n → (M1 (LVB + 2 * j) = 0 ↔ M (LVB + 2 * j) = 0) := by
          intro j hj; rw [hL0 j hj]
          exact ⟨And.left, fun h => ⟨h, fun hh => hPu ⟨hh.1, j, hj, hh.2, h⟩⟩⟩
        have hiff : (∃ v, u + 1 ≤ v ∧ v < n ∧ M1 (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M1 (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M1 (36 + 2 * v + j * (2 * n))) ∧ M1 (LVB + 2 * j) = 0) ↔
            (∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) := by
          constructor
          · rintro ⟨v, a, b, c', j, hj, d, e⟩
            exact ⟨v, by omega, b, (hL1 v b).1 c', j, hj, by rwa [eE v j b hj, eC v j b hj] at d, (hz j hj).1 e⟩
          · rintro ⟨v, a, b, c', j, hj, d, e⟩
            rcases Nat.eq_or_lt_of_le a with h | h
            · subst h; exact absurd ⟨c', j, hj, d, e⟩ hPu
            · exact ⟨v, h, b, (hL1 v b).2 c', j, hj, by rwa [eE v j b hj, eC v j b hj], (hz j hj).2 e⟩
        by_cases hc : ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
        · rw [if_pos (hiff.2 hc), if_pos hc]
        · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]
    · intro a ha hne; rw [rfr a ha hne, qfr a ha hne]
    · intro a ha; rw [rlo a ha, qlo a ha]

end

end VS

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (c : ℕ)
    (hcode : CodeAt p c
    [natBranch 13 24 (c + 27) (c + 1),
      natLoad 22 27,
      natBranch 22 15 (c + 3) (c + 22),
      natBranch 15 22 (c + 4) (c + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (c + 8 + 14) (c + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (c + 8 + 7) (c + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (c + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump c])
    (n t LVB : ℕ) (ht : 1 ≤ t) (hLVB : 36 + 2 * n * n ≤ LVB) :
    ∀ (r u : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), u + r = n →
      M 13 = n → M 20 = 2 * n → M 24 = u → M 25 = 36 + 2 * u * n → M 26 = 36 + 2 * u →
      M 27 = LVB + 2 * u → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      ∃ τ, τ ≤ r * (14 * n + 14) + 1 ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).pc = c + 27 ∧
        (∀ j, j < n → (planarRAMRun p ⟨c, M, R⟩ τ).natMem (LVB + 2 * j) =
          if M (LVB + 2 * j) = 0 ∧ ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
          then t + 1 else M (LVB + 2 * j)) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 23 =
          (if ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
            then 1 else M 23) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 15 → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨c, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).realMem = R :=
  VS.vscan_loop p c hcode n t LVB ht hLVB
