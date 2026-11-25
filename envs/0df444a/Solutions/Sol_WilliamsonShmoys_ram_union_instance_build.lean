-- Prove2me | solution 1 for WilliamsonShmoys.ram_union_instance_build
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T07:11:43.605996+00:00
-- url     : https://prove2.me/submissions/7f9e00ab-40f8-4a95-9819-60ca964b9dd8

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace UB
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


lemma ex_const (d v pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (natConst d v) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := rfl

lemma ex_add (d l r pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l + M r = v) :
    execInstr (natAdd d l r) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_sub (d l r pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l - M r = v) :
    execInstr (natSub d l r) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_load (d a pc v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M (M a) = v) :
    execInstr (natLoad d a) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M d v, R⟩ := by
  rw [← h]; rfl

lemma ex_store (a src pc x v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (hv : M src = v) :
    execInstr (natStore a src) ⟨pc, M, R⟩ = ⟨pc + 1, Function.update M x v, R⟩ := by
  rw [← ha, ← hv]; rfl

lemma ex_rzero (d pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (realZero d) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d 0⟩ := rfl

lemma ex_rload (d a pc x : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (h : R x = v) :
    execInstr (realLoad d a) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d v⟩ := by
  rw [← h, ← ha]; rfl

lemma ex_rstore (a src pc x : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (ha : M a = x) (hv : R src = v) :
    execInstr (realStore a src) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R x v⟩ := by
  rw [← ha, ← hv]; rfl

lemma ex_brt (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : M l ≤ M r) :
    execInstr (natBranch l r y n) ⟨pc, M, R⟩ = ⟨y, M, R⟩ := by
  simp [execInstr, h]

lemma ex_brf (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : ¬ M l ≤ M r) :
    execInstr (natBranch l r y n) ⟨pc, M, R⟩ = ⟨n, M, R⟩ := by
  simp [execInstr, h]

lemma ex_jump (j pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) :
    execInstr (jump j) ⟨pc, M, R⟩ = ⟨j, M, R⟩ := rfl

lemma step_at' (p : List PlanarRAMInstruction) (b k pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (ins : PlanarRAMInstruction) (h1 : pc = b + k) (h2 : p[b + k]? = some ins) :
    planarRAMStep p ⟨pc, M, R⟩ = execInstr ins ⟨pc, M, R⟩ :=
  step_exec p _ ins (by simp only; rw [h1]; exact h2)

lemma tab_ne (OB N n v v' w w' : ℕ) (hn : n ≤ N) (hw : w < n) (hw' : w' < n) (h : v < v') :
    OB + 2 * v * N + 2 * w ≠ OB + 2 * v' * N + 2 * w' := by
  have h1 := Nat.mul_le_mul_right N (show v + 1 ≤ v' by omega)
  have e1 : 2 * v * N = 2 * (v * N) := by ring
  have e2 : 2 * v' * N = 2 * (v' * N) := by ring
  have e3 : (v + 1) * N = v * N + N := by ring
  omega

lemma tab_odd (OB N v w : ℕ) (hOB : OB % 2 = 1) : (OB + 2 * v * N + 2 * w) % 2 = 1 := by
  have e1 : 2 * v * N = 2 * (v * N) := by ring
  omega

lemma pos_ne (n k c c' v v' w w' : ℕ) (hc : c < c') (hc' : c' < k) (hv : v < n) (hw : w < n) :
    5 + 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v * (k * n) + 2 * w ≠
      5 + 2 * (c' * n) * (k * n) + 2 * (c' * n) + 2 * v' * (k * n) + 2 * w' := by
  have h1 : c * n + v < c' * n := by
    have := Nat.mul_le_mul_right n (show c + 1 ≤ c' by omega)
    have e : (c + 1) * n = c * n + n := by ring
    omega
  have h2 : c * n + w < k * n := by
    have := Nat.mul_le_mul_right n (show c + 1 ≤ k by omega)
    have e : (c + 1) * n = c * n + n := by ring
    omega
  have h3 := Nat.mul_le_mul_right (k * n) (show c * n + v + 1 ≤ c' * n + v' by omega)
  have e1 : 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v * (k * n) + 2 * w =
      2 * ((c * n + v) * (k * n) + (c * n + w)) := by ring
  have e2 : 2 * (c' * n) * (k * n) + 2 * (c' * n) + 2 * v' * (k * n) + 2 * w' =
      2 * ((c' * n + v') * (k * n) + (c' * n + w')) := by ring
  have e3 : (c * n + v + 1) * (k * n) = (c * n + v) * (k * n) + k * n := by ring
  omega

lemma pos_odd (n N c v w : ℕ) : (5 + 2 * (c * n) * N + 2 * (c * n) + 2 * v * N + 2 * w) % 2 = 1 := by
  have e1 : 2 * (c * n) * N + 2 * (c * n) + 2 * v * N + 2 * w = 2 * ((c * n) * N + c * n + v * N + w) := by ring
  omega

section
variable (p : List PlanarRAMInstruction) (b : ℕ)
  (hcode : CodeAt p b
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 26 32 32,
      natAdd 30 28 26,
      natConst 8 0,
      natConst 6 0,
      natBranch 34 6 (b + 11) (b + 8),
      natAdd 8 8 32,
      natAdd 6 6 2,
      jump (b + 7),
      natAdd 10 8 8,
      natSub 24 10 26,
      natConst 10 1,
      natStore 10 8,
      natAdd 8 34 34,
      natAdd 8 8 34,
      natConst 10 3,
      natStore 10 8,
      natConst 6 0,
      natConst 18 5,
      natConst 22 1,
      natBranch 34 6 (b + 54) (b + 23),
      natAdd 12 28 0,
      natConst 20 32,
      natConst 16 36,
      natBranch 30 12 (b + 51) (b + 27),
      natLoad 8 12,
      natBranch 8 6 (b + 29) (b + 30),
      natBranch 6 8 (b + 44) (b + 30),
      realLoad 0 20,
      realStore 22 0,
      natAdd 14 28 0,
      natBranch 30 14 (b + 46) (b + 34),
      natLoad 10 14,
      natBranch 10 6 (b + 36) (b + 37),
      natBranch 6 10 (b + 40) (b + 37),
      natLoad 10 16,
      natBranch 2 10 (b + 39) (b + 40),
      natStore 18 2,
      natAdd 14 14 4,
      natAdd 16 16 4,
      natAdd 18 18 4,
      jump (b + 33),
      natAdd 16 16 26,
      natAdd 18 18 26,
      natAdd 18 18 24,
      natAdd 12 12 4,
      natAdd 20 20 4,
      natAdd 22 22 4,
      jump (b + 26),
      natAdd 18 18 26,
      natAdd 6 6 2,
      jump (b + 22)])
include hcode

set_option maxHeartbeats 8000000 in
lemma w_loop (n LVB c EB : ℕ) (hLe : LVB % 2 = 0) (hEe : EB % 2 = 0) (hL : 36 ≤ LVB) (hEB : 36 ≤ EB) :
    ∀ (r w O : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = n → O % 2 = 1 →
      M 30 = LVB + 2 * n → M 14 = LVB + 2 * w → M 16 = EB + 2 * w → M 18 = O + 2 * w →
      M 6 = c → M 2 = 1 → M 4 = 2 →
      ∃ τ, τ ≤ 11 * r + 1 ∧ (planarRAMRun p ⟨b + 33, M, R⟩ τ).pc = b + 46 ∧
        (∀ j, w ≤ j → j < n → (planarRAMRun p ⟨b + 33, M, R⟩ τ).natMem (O + 2 * j) =
          if M (LVB + 2 * j) ≠ c ∧ 1 ≤ M (EB + 2 * j) then 1 else M (O + 2 * j)) ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ).natMem 14 = LVB + 2 * n ∧ (planarRAMRun p ⟨b + 33, M, R⟩ τ).natMem 16 = EB + 2 * n ∧ (planarRAMRun p ⟨b + 33, M, R⟩ τ).natMem 18 = O + 2 * n ∧
        (∀ a, a ≠ 10 → a ≠ 14 → a ≠ 16 → a ≠ 18 → (∀ j, w ≤ j → j < n → a ≠ O + 2 * j) →
          (planarRAMRun p ⟨b + 33, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ).realMem = R := by
  have c0 : p[b + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 26 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natAdd 30 28 26) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 8 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natBranch 34 6 (b + 11) (b + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 8 8 32) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (jump (b + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 10 8 8) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natSub 24 10 26) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natConst 10 1) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natStore 10 8) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 8 34 34) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 8 8 34) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natConst 10 3) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natStore 10 8) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natConst 6 0) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 18 5) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natConst 22 1) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natBranch 34 6 (b + 54) (b + 23)) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natAdd 12 28 0) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natConst 20 32) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natConst 16 36) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natBranch 30 12 (b + 51) (b + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (natLoad 8 12) := by simpa using hcode 27 (by simp)
  have c28 : p[b + 28]? = some (natBranch 8 6 (b + 29) (b + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[b + 29]? = some (natBranch 6 8 (b + 44) (b + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[b + 30]? = some (realLoad 0 20) := by simpa using hcode 30 (by simp)
  have c31 : p[b + 31]? = some (realStore 22 0) := by simpa using hcode 31 (by simp)
  have c32 : p[b + 32]? = some (natAdd 14 28 0) := by simpa using hcode 32 (by simp)
  have c33 : p[b + 33]? = some (natBranch 30 14 (b + 46) (b + 34)) := by simpa using hcode 33 (by simp)
  have c34 : p[b + 34]? = some (natLoad 10 14) := by simpa using hcode 34 (by simp)
  have c35 : p[b + 35]? = some (natBranch 10 6 (b + 36) (b + 37)) := by simpa using hcode 35 (by simp)
  have c36 : p[b + 36]? = some (natBranch 6 10 (b + 40) (b + 37)) := by simpa using hcode 36 (by simp)
  have c37 : p[b + 37]? = some (natLoad 10 16) := by simpa using hcode 37 (by simp)
  have c38 : p[b + 38]? = some (natBranch 2 10 (b + 39) (b + 40)) := by simpa using hcode 38 (by simp)
  have c39 : p[b + 39]? = some (natStore 18 2) := by simpa using hcode 39 (by simp)
  have c40 : p[b + 40]? = some (natAdd 14 14 4) := by simpa using hcode 40 (by simp)
  have c41 : p[b + 41]? = some (natAdd 16 16 4) := by simpa using hcode 41 (by simp)
  have c42 : p[b + 42]? = some (natAdd 18 18 4) := by simpa using hcode 42 (by simp)
  have c43 : p[b + 43]? = some (jump (b + 33)) := by simpa using hcode 43 (by simp)
  have c44 : p[b + 44]? = some (natAdd 16 16 26) := by simpa using hcode 44 (by simp)
  have c45 : p[b + 45]? = some (natAdd 18 18 26) := by simpa using hcode 45 (by simp)
  have c46 : p[b + 46]? = some (natAdd 18 18 24) := by simpa using hcode 46 (by simp)
  have c47 : p[b + 47]? = some (natAdd 12 12 4) := by simpa using hcode 47 (by simp)
  have c48 : p[b + 48]? = some (natAdd 20 20 4) := by simpa using hcode 48 (by simp)
  have c49 : p[b + 49]? = some (natAdd 22 22 4) := by simpa using hcode 49 (by simp)
  have c50 : p[b + 50]? = some (jump (b + 26)) := by simpa using hcode 50 (by simp)
  have c51 : p[b + 51]? = some (natAdd 18 18 26) := by simpa using hcode 51 (by simp)
  have c52 : p[b + 52]? = some (natAdd 6 6 2) := by simpa using hcode 52 (by simp)
  have c53 : p[b + 53]? = some (jump (b + 22)) := by simpa using hcode 53 (by simp)
  intro r
  induction r with
  | zero =>
    intro w O M R hw hO h30 h14 h16 h18 h6 h2 h4
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 33 _ rfl c33, run_zero]
    simp only [execInstr, show M 30 ≤ M 14 by omega, if_true]
    refine ⟨trivial, fun j h1 h2 => by omega, by rw [h14]; omega, by rw [h16]; omega, by rw [h18]; omega,
      fun a _ _ _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro w O M R hw hO h30 h14 h16 h18 h6 h2 h4
    have hlt : ¬ M 30 ≤ M 14 := by omega
    have hwn : w < n := by omega
    have hR : EB + 2 * w ≠ 10 ∧ LVB + 2 * w ≠ 10 ∧ EB + 2 * w ≠ 14 ∧ EB + 2 * w ≠ 16 ∧ EB + 2 * w ≠ 18 := by omega
    have hO1 : O + 2 * w ≠ 14 ∧ O + 2 * w ≠ 16 ∧ O + 2 * w ≠ 10 ∧ O + 2 * w ≠ 18 := by omega
    have hO3 : (14 : ℕ) ≠ O + 2 * w ∧ (16 : ℕ) ≠ O + 2 * w ∧ (10 : ℕ) ≠ O + 2 * w ∧ (18 : ℕ) ≠ O + 2 * w ∧ (4 : ℕ) ≠ O + 2 * w ∧ (2 : ℕ) ≠ O + 2 * w ∧ (6 : ℕ) ≠ O + 2 * w ∧ (30 : ℕ) ≠ O + 2 * w := by omega
    have hO2 : LVB + 2 * w ≠ O + 2 * w ∧ EB + 2 * w ≠ O + 2 * w := by omega
    have one : ∃ τ1, τ1 ≤ 11 ∧ (planarRAMRun p ⟨b + 33, M, R⟩ τ1).pc = b + 33 ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ1).natMem (O + 2 * w) =
          (if M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (EB + 2 * w) then 1 else M (O + 2 * w)) ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ1).natMem 14 = LVB + 2 * (w + 1) ∧ (planarRAMRun p ⟨b + 33, M, R⟩ τ1).natMem 16 = EB + 2 * (w + 1) ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ1).natMem 18 = O + 2 * (w + 1) ∧
        (∀ a, a ≠ 10 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ O + 2 * w → (planarRAMRun p ⟨b + 33, M, R⟩ τ1).natMem a = M a) ∧
        (planarRAMRun p ⟨b + 33, M, R⟩ τ1).realMem = R := by
      obtain ⟨md, hmd⟩ : ∃ md, M (LVB + 2 * w) = md := ⟨_, rfl⟩
      obtain ⟨E, hE⟩ : ∃ E, M (EB + 2 * w) = E := ⟨_, rfl⟩
      rw [hmd, hE]
      by_cases a1 : md ≤ c
      · by_cases a2 : c ≤ md
        · have hc : ¬ (md ≠ c ∧ 1 ≤ E) := by omega
          refine ⟨8, by omega, ?_⟩
          rw [show (8 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p b 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 34 _ _ _ _ (by omega) c34, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 35 _ _ _ _ (by omega) c35, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 36 _ _ _ _ (by omega) c36, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 42 _ _ _ _ (by omega) c42, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 43 _ _ _ _ (by omega) c43, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR, if_neg hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, if_neg hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, if_neg hc] <;> omega)
            | (simp [Function.update_apply, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, if_neg hc]; done)
            | (intro a a10 a14 a16 a18 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, a10, a14, a16, a18, aO, if_false])
        · by_cases a3 : 1 ≤ E
          · have hc : md ≠ c ∧ 1 ≤ E := ⟨by omega, a3⟩
            refine ⟨11, by omega, ?_⟩
            rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p b 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 34 _ _ _ _ (by omega) c34, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 35 _ _ _ _ (by omega) c35, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 36 _ _ _ _ (by omega) c36, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 37 _ _ _ _ (by omega) c37, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 38 _ _ _ _ (by omega) c38, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 39 _ _ _ _ (by omega) c39, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 42 _ _ _ _ (by omega) c42, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 43 _ _ _ _ (by omega) c43, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_pos hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_pos hc] <;> omega)
              | (simp [Function.update_apply, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_pos hc]; done)
              | (intro a a10 a14 a16 a18 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, a10, a14, a16, a18, aO, if_false])
          · have hc : ¬ (md ≠ c ∧ 1 ≤ E) := by omega
            refine ⟨10, by omega, ?_⟩
            rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p b 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 34 _ _ _ _ (by omega) c34, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 35 _ _ _ _ (by omega) c35, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 36 _ _ _ _ (by omega) c36, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 37 _ _ _ _ (by omega) c37, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 38 _ _ _ _ (by omega) c38, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 42 _ _ _ _ (by omega) c42, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 43 _ _ _ _ (by omega) c43, ex_jump]
            rw [run_zero]
            try rfl
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
            all_goals first
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR] <;> omega)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_neg hc]; done)
              | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_neg hc] <;> omega)
              | (simp [Function.update_apply, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a2, a3, if_neg hc]; done)
              | (intro a a10 a14 a16 a18 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, a10, a14, a16, a18, aO, if_false])
      · by_cases a3 : 1 ≤ E
        · have hc : md ≠ c ∧ 1 ≤ E := ⟨by omega, a3⟩
          refine ⟨10, by omega, ?_⟩
          rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p b 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 34 _ _ _ _ (by omega) c34, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 35 _ _ _ _ (by omega) c35, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 37 _ _ _ _ (by omega) c37, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 38 _ _ _ _ (by omega) c38, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 39 _ _ _ _ (by omega) c39, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 42 _ _ _ _ (by omega) c42, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 43 _ _ _ _ (by omega) c43, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_pos hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_pos hc] <;> omega)
            | (simp [Function.update_apply, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_pos hc]; done)
            | (intro a a10 a14 a16 a18 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, a10, a14, a16, a18, aO, if_false])
        · have hc : ¬ (md ≠ c ∧ 1 ≤ E) := by omega
          refine ⟨9, by omega, ?_⟩
          rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
          rw [run_succ, step_at' p b 33 _ _ _ _ (by omega) c33, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 34 _ _ _ _ (by omega) c34, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 35 _ _ _ _ (by omega) c35, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 37 _ _ _ _ (by omega) c37, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 38 _ _ _ _ (by omega) c38, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | trivial | omega)]
          rw [run_succ, step_at' p b 40 _ _ _ _ (by omega) c40, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 41 _ _ _ _ (by omega) c41, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 42 _ _ _ _ (by omega) c42, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3] <;> first | rfl | omega) | rfl)]
          rw [run_succ, step_at' p b 43 _ _ _ _ (by omega) c43, ex_jump]
          rw [run_zero]
          try rfl
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          all_goals first
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR, if_neg hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h14, h16, h18, h2, h4, h6, hO1, hO3, hR] <;> omega)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_neg hc]; done)
            | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_neg hc] <;> omega)
            | (simp [Function.update_apply, h30, h14, h16, h18, h6, h2, h4, hlt, hwn, hmd, hE, hO1, hO2, hR, hO3, a1, a3, if_neg hc]; done)
            | (intro a a10 a14 a16 a18 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, a10, a14, a16, a18, aO, if_false])
    obtain ⟨τ1, hτ1, m1, mO, m14, m16, m18, mfr, mr⟩ := one
    set S1 := planarRAMRun p ⟨b + 33, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at m1 mO m14 m16 m18 mfr mr
    subst m1; subst mr
    obtain ⟨τ2, hτ2, r1, rO, r14, r16, r18, rfr, rr⟩ := ih (w + 1) O M1 R1 (by omega) hO
      (by rw [mfr 30 (by omega) (by omega) (by omega) (by omega) (by omega), h30]) m14 m16 m18
      (by rw [mfr 6 (by omega) (by omega) (by omega) (by omega) (by omega), h6])
      (by rw [mfr 2 (by omega) (by omega) (by omega) (by omega) (by omega), h2])
      (by rw [mfr 4 (by omega) (by omega) (by omega) (by omega) (by omega), h4])
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    refine ⟨r1, fun j hj1 hj2 => ?_, r14, r16, r18, fun a a10 a14 a16 a18 aO => ?_, rr⟩
    · rcases Nat.eq_or_lt_of_le hj1 with h | h
      · subst h
        rw [rfr _ (by omega) (by omega) (by omega) (by omega) (fun j' h1 _ => by omega), mO]
      · rw [rO j h hj2, mfr (LVB + 2 * j) (by omega) (by omega) (by omega) (by omega) (by omega),
          mfr (EB + 2 * j) (by omega) (by omega) (by omega) (by omega) (by omega),
          mfr (O + 2 * j) (by omega) (by omega) (by omega) (by omega) (by omega)]
    · rw [rfr a a10 a14 a16 a18 (fun j h1 h2 => aO j (by omega) h2), mfr a a10 a14 a16 a18 (aO w le_rfl (by omega))]

set_option maxHeartbeats 16000000 in
lemma v_loop (n N LVB c OB D : ℕ) (hnN : n ≤ N) (hLe : LVB % 2 = 0) (hL36 : 36 + 2 * n * n ≤ LVB)
    (hOB : OB % 2 = 1) (hD : D % 2 = 1) :
    ∀ (r v : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), v + r = n →
      M 30 = LVB + 2 * n → M 12 = LVB + 2 * v → M 20 = 32 + 2 * v → M 22 = D + 2 * v →
      M 16 = 36 + 2 * v * n → M 18 = OB + 2 * v * N → M 24 = 2 * N - 2 * n → M 26 = 2 * n →
      M 28 = LVB → M 6 = c → M 2 = 1 → M 4 = 2 → M 0 = 0 →
      ∃ τ, τ ≤ (11 * n + 20) * r + 1 ∧ (planarRAMRun p ⟨b + 26, M, R⟩ τ).pc = b + 51 ∧
        (∀ v' w, v ≤ v' → v' < n → w < n → (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem (OB + 2 * v' * N + 2 * w) =
          if M (LVB + 2 * v') ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v' * n + 2 * w) then 1
          else M (OB + 2 * v' * N + 2 * w)) ∧
        (∀ v', v ≤ v' → v' < n → (planarRAMRun p ⟨b + 26, M, R⟩ τ).realMem (D + 2 * v') =
          if M (LVB + 2 * v') ≠ c then R (32 + 2 * v') else R (D + 2 * v')) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem 12 = LVB + 2 * n ∧ (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem 20 = 32 + 2 * n ∧ (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem 22 = D + 2 * n ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem 16 = 36 + 2 * n * n ∧ (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem 18 = OB + 2 * n * N ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ 20 → a ≠ 22 →
          (∀ v' w, v ≤ v' → v' < n → w < n → a ≠ OB + 2 * v' * N + 2 * w) → (planarRAMRun p ⟨b + 26, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≠ 0 → (∀ v', v ≤ v' → v' < n → a ≠ D + 2 * v') → (planarRAMRun p ⟨b + 26, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[b + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 26 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natAdd 30 28 26) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 8 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natBranch 34 6 (b + 11) (b + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 8 8 32) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (jump (b + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 10 8 8) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natSub 24 10 26) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natConst 10 1) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natStore 10 8) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 8 34 34) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 8 8 34) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natConst 10 3) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natStore 10 8) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natConst 6 0) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 18 5) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natConst 22 1) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natBranch 34 6 (b + 54) (b + 23)) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natAdd 12 28 0) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natConst 20 32) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natConst 16 36) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natBranch 30 12 (b + 51) (b + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (natLoad 8 12) := by simpa using hcode 27 (by simp)
  have c28 : p[b + 28]? = some (natBranch 8 6 (b + 29) (b + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[b + 29]? = some (natBranch 6 8 (b + 44) (b + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[b + 30]? = some (realLoad 0 20) := by simpa using hcode 30 (by simp)
  have c31 : p[b + 31]? = some (realStore 22 0) := by simpa using hcode 31 (by simp)
  have c32 : p[b + 32]? = some (natAdd 14 28 0) := by simpa using hcode 32 (by simp)
  have c33 : p[b + 33]? = some (natBranch 30 14 (b + 46) (b + 34)) := by simpa using hcode 33 (by simp)
  have c34 : p[b + 34]? = some (natLoad 10 14) := by simpa using hcode 34 (by simp)
  have c35 : p[b + 35]? = some (natBranch 10 6 (b + 36) (b + 37)) := by simpa using hcode 35 (by simp)
  have c36 : p[b + 36]? = some (natBranch 6 10 (b + 40) (b + 37)) := by simpa using hcode 36 (by simp)
  have c37 : p[b + 37]? = some (natLoad 10 16) := by simpa using hcode 37 (by simp)
  have c38 : p[b + 38]? = some (natBranch 2 10 (b + 39) (b + 40)) := by simpa using hcode 38 (by simp)
  have c39 : p[b + 39]? = some (natStore 18 2) := by simpa using hcode 39 (by simp)
  have c40 : p[b + 40]? = some (natAdd 14 14 4) := by simpa using hcode 40 (by simp)
  have c41 : p[b + 41]? = some (natAdd 16 16 4) := by simpa using hcode 41 (by simp)
  have c42 : p[b + 42]? = some (natAdd 18 18 4) := by simpa using hcode 42 (by simp)
  have c43 : p[b + 43]? = some (jump (b + 33)) := by simpa using hcode 43 (by simp)
  have c44 : p[b + 44]? = some (natAdd 16 16 26) := by simpa using hcode 44 (by simp)
  have c45 : p[b + 45]? = some (natAdd 18 18 26) := by simpa using hcode 45 (by simp)
  have c46 : p[b + 46]? = some (natAdd 18 18 24) := by simpa using hcode 46 (by simp)
  have c47 : p[b + 47]? = some (natAdd 12 12 4) := by simpa using hcode 47 (by simp)
  have c48 : p[b + 48]? = some (natAdd 20 20 4) := by simpa using hcode 48 (by simp)
  have c49 : p[b + 49]? = some (natAdd 22 22 4) := by simpa using hcode 49 (by simp)
  have c50 : p[b + 50]? = some (jump (b + 26)) := by simpa using hcode 50 (by simp)
  have c51 : p[b + 51]? = some (natAdd 18 18 26) := by simpa using hcode 51 (by simp)
  have c52 : p[b + 52]? = some (natAdd 6 6 2) := by simpa using hcode 52 (by simp)
  have c53 : p[b + 53]? = some (jump (b + 22)) := by simpa using hcode 53 (by simp)
  intro r
  induction r with
  | zero =>
    intro v M R hv h30 h12 h20 h22 h16 h18 h24 h26 h28 h6 h2 h4 h0
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 26 _ rfl c26, run_zero]
    simp only [execInstr, show M 30 ≤ M 12 by omega, if_true]
    refine ⟨trivial, fun v' w h1 h2 h3 => by omega, fun v' h1 h2 => by omega, by rw [h12]; omega,
      by rw [h20]; omega, by rw [h22]; omega, by rw [h16]; subst hv; ring_nf, by rw [h18]; subst hv; ring_nf,
      fun a _ _ _ _ _ _ _ _ _ => trivial, fun a _ _ => trivial⟩
  | succ r ih =>
    intro v M R hv h30 h12 h20 h22 h16 h18 h24 h26 h28 h6 h2 h4 h0
    have hlt : ¬ M 30 ≤ M 12 := by omega
    have hvn : v < n := by omega
    have hR1 : LVB + 2 * v ≠ 8 ∧ LVB + 2 * v ≠ 14 ∧ LVB + 2 * v ≠ 0 := by omega
    have hR2 : (0 : ℕ) ≠ D + 2 * v ∧ 32 + 2 * v ≠ 0 ∧ (0 : ℕ) ≠ 32 + 2 * v ∧ D + 2 * v ≠ 0 := by omega
    obtain ⟨md, hmd⟩ : ∃ md, M (LVB + 2 * v) = md := ⟨_, rfl⟩
    have hvN : (2 * v * N) % 2 = 0 := by rw [Nat.mul_assoc]; simp
    have hvN' : (v * N * 2) % 2 = 0 := by simp
    -- one iteration: ∃ τ1, run τ1 reaches b + 26 with the expected memory
    have one : ∃ τ1, τ1 ≤ 11 * n + 20 ∧ (planarRAMRun p ⟨b + 26, M, R⟩ τ1).pc = b + 26 ∧
        (∀ w, w < n → (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem (OB + 2 * v * N + 2 * w) =
          if md ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1
          else M (OB + 2 * v * N + 2 * w)) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).realMem (D + 2 * v) =
          (if md ≠ c then R (32 + 2 * v) else R (D + 2 * v)) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem 12 = LVB + 2 * (v + 1) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem 20 = 32 + 2 * (v + 1) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem 22 = D + 2 * (v + 1) ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem 16 = 36 + 2 * (v + 1) * n ∧
        (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem 18 = OB + 2 * (v + 1) * N ∧
        (∀ a, a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ 20 → a ≠ 22 →
          (∀ w, w < n → a ≠ OB + 2 * v * N + 2 * w) →
          (planarRAMRun p ⟨b + 26, M, R⟩ τ1).natMem a = M a) ∧
        (∀ a, a ≠ 0 → a ≠ D + 2 * v → (planarRAMRun p ⟨b + 26, M, R⟩ τ1).realMem a = R a) := by
      by_cases hS : md = c
      · -- skip path
        refine ⟨11, by omega, ?_⟩
        rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at' p b 26 _ _ _ _ (by omega) c26, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | trivial | omega)]
        rw [run_succ, step_at' p b 27 _ _ _ _ (by omega) c27, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 28 _ _ _ _ (by omega) c28, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | trivial | omega)]
        rw [run_succ, step_at' p b 29 _ _ _ _ (by omega) c29, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | trivial | omega)]
        rw [run_succ, step_at' p b 44 _ _ _ _ (by omega) c44, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 45 _ _ _ _ (by omega) c45, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 46 _ _ _ _ (by omega) c46, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 47 _ _ _ _ (by omega) c47, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 48 _ _ _ _ (by omega) c48, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 49 _ _ _ _ (by omega) c49, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS, le_refl] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 50 _ _ _ _ (by omega) c50, ex_jump]
        rw [run_zero]
        try rfl
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS]; done)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS] <;> omega)
          | (intro w hw; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS]; split_ifs <;> first | rfl | omega | (congr 1; ring))
          | (intro a a8 a10 a12 a14 a16 a18 a20 a22 aO; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a8, a10, a12, a14, a16, a18, a20, a22, if_false])
          | (intro a a0 aD; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, aD, if_false])
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS]; ring_nf; omega)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS]; ring)
          | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, hS]; omega)
      · -- process path: segment to b + 33
        obtain ⟨τs, hτs, e7⟩ : ∃ τs, τs ≤ 7 ∧ planarRAMRun p ⟨b + 26, M, R⟩ τs = ⟨b + 33, Function.update (Function.update M 8 md) 14 LVB, Function.update (Function.update R 0 (R (32 + 2 * v))) (D + 2 * v) (R (32 + 2 * v))⟩ := by
          by_cases a1 : md ≤ c
          · have a2 : ¬ c ≤ md := by omega
            refine ⟨7, le_rfl, ?_⟩
            rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p b 26 _ _ _ _ (by omega) c26, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 27 _ _ _ _ (by omega) c27, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 28 _ _ _ _ (by omega) c28, ex_brt _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 29 _ _ _ _ (by omega) c29, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 30 _ _ _ _ (by omega) c30, ex_rload _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 31 _ _ _ _ (by omega) c31, ex_rstore _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1, a2] <;> first | rfl | omega) | rfl)]
            rw [run_zero]
            try rfl
          · refine ⟨6, by omega, ?_⟩
            rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
            rw [run_succ, step_at' p b 26 _ _ _ _ (by omega) c26, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 27 _ _ _ _ (by omega) c27, ex_load _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 28 _ _ _ _ (by omega) c28, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | trivial | omega)]
            rw [run_succ, step_at' p b 30 _ _ _ _ (by omega) c30, ex_rload _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 31 _ _ _ _ (by omega) c31, ex_rstore _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl)]
            rw [run_succ, step_at' p b 32 _ _ _ _ (by omega) c32, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h30, h12, h20, h22, h16, h18, h24, h26, h28, h6, h2, h4, h0, hlt, hmd, hR1, hR2, a1] <;> first | rfl | omega) | rfl)]
            rw [run_zero]
            try rfl
        have m7 : ∀ a, a ≠ 8 → a ≠ 14 → (Function.update (Function.update M 8 md) 14 LVB) a = M a := fun a a8 a14 => by
          rw [Function.update_of_ne a14, Function.update_of_ne a8]
        have h7_30 := m7 30 (by omega) (by omega)
        have h7_6 := m7 6 (by omega) (by omega)
        have h7_2 := m7 2 (by omega) (by omega)
        have h7_4 := m7 4 (by omega) (by omega)
        have h7_12 := m7 12 (by omega) (by omega)
        have h7_20 := m7 20 (by omega) (by omega)
        have h7_22 := m7 22 (by omega) (by omega)
        have h7_24 := m7 24 (by omega) (by omega)
        have h7_26 := m7 26 (by omega) (by omega)
        have hEBe : (36 + 2 * v * n) % 2 = 0 := by rw [Nat.mul_assoc]; omega
        obtain ⟨τw, hτw, w1, wO, w14, w16, w18, wfr, wr⟩ :=
          w_loop p b hcode n LVB c (36 + 2 * v * n) hLe hEBe (by omega) (by omega) n 0 (OB + 2 * v * N)
            (Function.update (Function.update M 8 md) 14 LVB) (Function.update (Function.update R 0 (R (32 + 2 * v))) (D + 2 * v) (R (32 + 2 * v))) (by omega) (by omega)
            (by rw [h7_30, h30]) (by simp) (by rw [m7 16 (by omega) (by omega), h16]; ring)
            (by rw [m7 18 (by omega) (by omega), h18]; ring)
            (by rw [h7_6, h6]) (by rw [h7_2, h2]) (by rw [h7_4, h4])
        set Sw := planarRAMRun p ⟨b + 33, Function.update (Function.update M 8 md) 14 LVB, Function.update (Function.update R 0 (R (32 + 2 * v))) (D + 2 * v) (R (32 + 2 * v))⟩ τw with hSw
        obtain ⟨pcw, Mw, Rw⟩ := Sw
        simp only at w1 wO w14 w16 w18 wfr wr
        subst w1; subst wr
        have mw : ∀ a, a ≠ 8 → a ≠ 10 → a ≠ 14 → a ≠ 16 → a ≠ 18 → (∀ j, j < n → a ≠ OB + 2 * v * N + 2 * j) →
            Mw a = M a := fun a a8 a10 a14 a16 a18 aO =>
          (wfr a a10 a14 a16 a18 (fun j _ hj => aO j hj)).trans (m7 a a8 a14)
        refine ⟨τs + τw + 5, by omega, ?_⟩
        rw [run_add, run_add, e7, ← hSw]
        rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl]
        rw [run_succ, step_at' p b 46 _ _ _ _ (by omega) c46, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, w18, mw 24 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h24, mw 12 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h12, mw 20 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h20, mw 22 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h22, mw 4 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h4] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 47 _ _ _ _ (by omega) c47, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, w18, mw 24 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h24, mw 12 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h12, mw 20 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h20, mw 22 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h22, mw 4 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h4] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 48 _ _ _ _ (by omega) c48, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, w18, mw 24 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h24, mw 12 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h12, mw 20 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h20, mw 22 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h22, mw 4 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h4] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 49 _ _ _ _ (by omega) c49, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, w18, mw 24 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h24, mw 12 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h12, mw 20 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h20, mw 22 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h22, mw 4 (by omega) (by omega) (by omega) (by omega) (by omega) (fun j _ => by omega), h4] <;> first | rfl | omega) | rfl)]
        rw [run_succ, step_at' p b 50 _ _ _ _ (by omega) c50, ex_jump]
        rw [run_zero]
        try rfl
        refine ⟨rfl, fun w hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a a8 a10 a12 a14 a16 a18 a20 a22 aO => ?_, fun a a0 aD => ?_⟩
        · have e1 := wO w (Nat.zero_le _) hw
          simp only [Function.update_apply]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), e1,
            m7 _ (by omega) (by omega), m7 _ (by omega) (by omega), m7 _ (by omega) (by omega)]
          by_cases hc2 : M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w)
          · rw [if_pos hc2, if_pos ⟨hS, hc2⟩]
          · rw [if_neg hc2, if_neg (fun h => hc2 h.2)]
        · rw [if_pos hS]; simp [Function.update_apply]
        · simp only [Function.update_apply]; simp; omega
        · simp only [Function.update_apply]; simp; omega
        · simp only [Function.update_apply]; simp; omega
        · simp only [Function.update_apply]; simp [w16]; ring
        · simp only [Function.update_apply]; simp; ring_nf; omega
        · simp only [Function.update_apply]
          rw [if_neg a22, if_neg a20, if_neg a12, if_neg a18]
          exact mw a a8 a10 a14 a16 a18 aO
        · simp only [Function.update_apply, if_neg aD, if_neg a0]
    obtain ⟨τ1, hτ1, q1, qT, qRd, q12, q20, q22, q16, q18, qfr, qRfr⟩ := one
    set S1 := planarRAMRun p ⟨b + 26, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 qT qRd q12 q20 q22 q16 q18 qfr qRfr
    subst q1
    have ev : ∀ a, a % 2 = 0 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ 20 → a ≠ 22 →
        M1 a = M a := fun a hae a8 a10 a12 a14 a16 a18 a20 a22 =>
      qfr a a8 a10 a12 a14 a16 a18 a20 a22 (fun w _ h => by have := tab_odd OB N v w hOB; omega)
    obtain ⟨τ2, hτ2, r1, rT, rR, r12, r20, r22, r16, r18, rfr, rRfr⟩ :=
      ih (v + 1) M1 R1 (by omega)
        (by rw [ev 30 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h30])
        q12 q20 q22 q16 q18
        (by rw [ev 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h24])
        (by rw [ev 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h26])
        (by rw [ev 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h28])
        (by rw [ev 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h6])
        (by rw [ev 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h2])
        (by rw [ev 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h4])
        (by rw [ev 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0])
    have hm : (11 * n + 20) * (r + 1) = (11 * n + 20) * r + (11 * n + 20) := by ring
    refine ⟨τ1 + τ2, by omega, ?_⟩
    rw [run_add, ← hS1]
    have evL : ∀ j, M1 (LVB + 2 * j) = M (LVB + 2 * j) := fun j =>
      ev _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have evE : ∀ v' w, M1 (36 + 2 * v' * n + 2 * w) = M (36 + 2 * v' * n + 2 * w) := fun v' w => by
      have e1 : 2 * v' * n = 2 * (v' * n) := by ring
      exact ev _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨r1, fun v' w hv1 hv2 hw => ?_, fun v' hv1 hv2 => ?_, r12, r20, r22, r16, r18,
      fun a a8 a10 a12 a14 a16 a18 a20 a22 aO => ?_, fun a a0 aD => ?_⟩
    · rcases Nat.eq_or_lt_of_le hv1 with h | h
      · subst h
        rw [rfr _ (by have := tab_odd OB N v w hOB; omega) (by have := tab_odd OB N v w hOB; omega)
          (by have := tab_odd OB N v w hOB; omega) (by have := tab_odd OB N v w hOB; omega)
          (by have := tab_odd OB N v w hOB; omega) (by have := tab_odd OB N v w hOB; omega)
          (by have := tab_odd OB N v w hOB; omega) (by have := tab_odd OB N v w hOB; omega)
          (fun v'' w' h1 h2 h3 => tab_ne OB N n v v'' w w' hnN hw h3 (by omega)), qT w hw, hmd]
      · rw [rT v' w h hv2 hw, evL, evL, evE,
          qfr _ (by have := tab_odd OB N v' w hOB; omega) (by have := tab_odd OB N v' w hOB; omega)
          (by have := tab_odd OB N v' w hOB; omega) (by have := tab_odd OB N v' w hOB; omega)
          (by have := tab_odd OB N v' w hOB; omega) (by have := tab_odd OB N v' w hOB; omega)
          (by have := tab_odd OB N v' w hOB; omega) (by have := tab_odd OB N v' w hOB; omega)
          (fun w' hw' => (tab_ne OB N n v v' w' w hnN hw' hw h).symm)]
    · rcases Nat.eq_or_lt_of_le hv1 with h | h
      · subst h
        rw [rRfr _ (by omega) (fun v'' h1 _ => by omega), qRd, hmd]
      · rw [rR v' h hv2, evL, qRfr _ (by omega) (by omega), qRfr (D + 2 * v') (by omega) (by omega)]
    · rw [rfr a a8 a10 a12 a14 a16 a18 a20 a22 (fun v' w h1 h2 h3 => aO v' w (by omega) h2 h3),
        qfr a a8 a10 a12 a14 a16 a18 a20 a22 (fun w hw => aO v w le_rfl (by omega) hw)]
    · rw [rRfr a a0 (fun v' h1 h2 => aD v' (by omega) h2), qRfr a a0 (aD v le_rfl (by omega))]

set_option maxHeartbeats 16000000 in
lemma c_loop (n k LVB : ℕ) (hLe : LVB % 2 = 0) (hL36 : 36 + 2 * n * n ≤ LVB) :
    ∀ (r c : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), c + r = k →
      M 34 = k → M 6 = c → M 18 = 5 + 2 * (c * n) * (k * n) + 2 * (c * n) → M 22 = 1 + 2 * (c * n) →
      M 30 = LVB + 2 * n → M 24 = 2 * (k * n) - 2 * n → M 26 = 2 * n → M 28 = LVB →
      M 2 = 1 → M 4 = 2 → M 0 = 0 →
      ∃ τ, τ ≤ ((11 * n + 20) * n + 8) * r + 1 ∧ (planarRAMRun p ⟨b + 22, M, R⟩ τ).pc = b + 54 ∧
        (∀ c' v w, c ≤ c' → c' < k → v < n → w < n → (planarRAMRun p ⟨b + 22, M, R⟩ τ).natMem (5 + 2 * (c' * n) * (k * n) + 2 * (c' * n) + 2 * v * (k * n) + 2 * w) =
          if M (LVB + 2 * v) ≠ c' ∧ M (LVB + 2 * w) ≠ c' ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1
          else M (5 + 2 * (c' * n) * (k * n) + 2 * (c' * n) + 2 * v * (k * n) + 2 * w)) ∧
        (∀ c' v, c ≤ c' → c' < k → v < n → (planarRAMRun p ⟨b + 22, M, R⟩ τ).realMem (1 + 2 * (c' * n) + 2 * v) =
          if M (LVB + 2 * v) ≠ c' then R (32 + 2 * v) else R (1 + 2 * (c' * n) + 2 * v)) ∧
        (∀ a, a % 2 = 0 → 32 ≤ a → (planarRAMRun p ⟨b + 22, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a % 2 = 1 → (∀ c' v w, c ≤ c' → c' < k → v < n → w < n → a ≠ 5 + 2 * (c' * n) * (k * n) + 2 * (c' * n) + 2 * v * (k * n) + 2 * w) → (planarRAMRun p ⟨b + 22, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≠ 0 → (∀ c' v, c ≤ c' → c' < k → v < n → a ≠ 1 + 2 * (c' * n) + 2 * v) → (planarRAMRun p ⟨b + 22, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[b + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 26 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natAdd 30 28 26) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 8 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natBranch 34 6 (b + 11) (b + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 8 8 32) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (jump (b + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 10 8 8) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natSub 24 10 26) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natConst 10 1) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natStore 10 8) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 8 34 34) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 8 8 34) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natConst 10 3) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natStore 10 8) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natConst 6 0) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 18 5) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natConst 22 1) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natBranch 34 6 (b + 54) (b + 23)) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natAdd 12 28 0) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natConst 20 32) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natConst 16 36) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natBranch 30 12 (b + 51) (b + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (natLoad 8 12) := by simpa using hcode 27 (by simp)
  have c28 : p[b + 28]? = some (natBranch 8 6 (b + 29) (b + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[b + 29]? = some (natBranch 6 8 (b + 44) (b + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[b + 30]? = some (realLoad 0 20) := by simpa using hcode 30 (by simp)
  have c31 : p[b + 31]? = some (realStore 22 0) := by simpa using hcode 31 (by simp)
  have c32 : p[b + 32]? = some (natAdd 14 28 0) := by simpa using hcode 32 (by simp)
  have c33 : p[b + 33]? = some (natBranch 30 14 (b + 46) (b + 34)) := by simpa using hcode 33 (by simp)
  have c34 : p[b + 34]? = some (natLoad 10 14) := by simpa using hcode 34 (by simp)
  have c35 : p[b + 35]? = some (natBranch 10 6 (b + 36) (b + 37)) := by simpa using hcode 35 (by simp)
  have c36 : p[b + 36]? = some (natBranch 6 10 (b + 40) (b + 37)) := by simpa using hcode 36 (by simp)
  have c37 : p[b + 37]? = some (natLoad 10 16) := by simpa using hcode 37 (by simp)
  have c38 : p[b + 38]? = some (natBranch 2 10 (b + 39) (b + 40)) := by simpa using hcode 38 (by simp)
  have c39 : p[b + 39]? = some (natStore 18 2) := by simpa using hcode 39 (by simp)
  have c40 : p[b + 40]? = some (natAdd 14 14 4) := by simpa using hcode 40 (by simp)
  have c41 : p[b + 41]? = some (natAdd 16 16 4) := by simpa using hcode 41 (by simp)
  have c42 : p[b + 42]? = some (natAdd 18 18 4) := by simpa using hcode 42 (by simp)
  have c43 : p[b + 43]? = some (jump (b + 33)) := by simpa using hcode 43 (by simp)
  have c44 : p[b + 44]? = some (natAdd 16 16 26) := by simpa using hcode 44 (by simp)
  have c45 : p[b + 45]? = some (natAdd 18 18 26) := by simpa using hcode 45 (by simp)
  have c46 : p[b + 46]? = some (natAdd 18 18 24) := by simpa using hcode 46 (by simp)
  have c47 : p[b + 47]? = some (natAdd 12 12 4) := by simpa using hcode 47 (by simp)
  have c48 : p[b + 48]? = some (natAdd 20 20 4) := by simpa using hcode 48 (by simp)
  have c49 : p[b + 49]? = some (natAdd 22 22 4) := by simpa using hcode 49 (by simp)
  have c50 : p[b + 50]? = some (jump (b + 26)) := by simpa using hcode 50 (by simp)
  have c51 : p[b + 51]? = some (natAdd 18 18 26) := by simpa using hcode 51 (by simp)
  have c52 : p[b + 52]? = some (natAdd 6 6 2) := by simpa using hcode 52 (by simp)
  have c53 : p[b + 53]? = some (jump (b + 22)) := by simpa using hcode 53 (by simp)
  intro r
  induction r with
  | zero =>
    intro c M R hc h34 h6 h18 h22 h30 h24 h26 h28 h2 h4 h0
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 22 _ rfl c22, run_zero]
    simp only [execInstr, show M 34 ≤ M 6 by omega, if_true]
    exact ⟨trivial, fun c' v w h1 h2 _ _ => by omega, fun c' v h1 h2 _ => by omega,
      fun a _ _ => trivial, fun a _ _ => trivial, fun a _ _ => trivial⟩
  | succ r ih =>
    intro c M R hc h34 h6 h18 h22 h30 h24 h26 h28 h2 h4 h0
    have hlt : ¬ M 34 ≤ M 6 := by omega
    have hnN : n ≤ k * n := Nat.le_mul_of_pos_left n (by omega)
    obtain ⟨τs, hτs, e4⟩ : ∃ τs, τs ≤ 4 ∧ planarRAMRun p ⟨b + 22, M, R⟩ τs =
        ⟨b + 26, Function.update (Function.update (Function.update M 12 LVB) 20 32) 16 36, R⟩ := by
      refine ⟨4, le_rfl, ?_⟩
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at' p b 22 _ _ _ _ (by omega) c22, ex_brf _ _ _ _ _ _ _ (by simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, h34, h6, h28, h0, hlt] <;> first | trivial | omega)]
      rw [run_succ, step_at' p b 23 _ _ _ _ (by omega) c23, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h34, h6, h28, h0, hlt] <;> first | rfl | omega) | rfl)]
      rw [run_succ, step_at' p b 24 _ _ _ _ (by omega) c24, ex_const]
      rw [run_succ, step_at' p b 25 _ _ _ _ (by omega) c25, ex_const]
      rw [run_zero]
      try rfl
    have m4 : ∀ a, a ≠ 12 → a ≠ 20 → a ≠ 16 →
        (Function.update (Function.update (Function.update M 12 LVB) 20 32) 16 36) a = M a :=
      fun a a12 a20 a16 => by rw [Function.update_of_ne a16, Function.update_of_ne a20, Function.update_of_ne a12]
    have hOBo : (5 + 2 * (c * n) * (k * n) + 2 * (c * n)) % 2 = 1 := by
      have := pos_odd n (k * n) c 0 0; simpa using this
    obtain ⟨τv, hτv, v1, vT, vR, v12, v20, v22, v16, v18, vfr, vRfr⟩ :=
      v_loop p b hcode n (k * n) LVB c (5 + 2 * (c * n) * (k * n) + 2 * (c * n)) (1 + 2 * (c * n)) hnN hLe hL36
        hOBo (by omega) n 0 (Function.update (Function.update (Function.update M 12 LVB) 20 32) 16 36) R (by omega)
        (by rw [m4 30 (by omega) (by omega) (by omega), h30]) (by simp) (by simp)
        (by rw [m4 22 (by omega) (by omega) (by omega), h22]; ring) (by simp)
        (by rw [m4 18 (by omega) (by omega) (by omega), h18]; ring)
        (by rw [m4 24 (by omega) (by omega) (by omega), h24]) (by rw [m4 26 (by omega) (by omega) (by omega), h26])
        (by rw [m4 28 (by omega) (by omega) (by omega), h28]) (by rw [m4 6 (by omega) (by omega) (by omega), h6])
        (by rw [m4 2 (by omega) (by omega) (by omega), h2]) (by rw [m4 4 (by omega) (by omega) (by omega), h4])
        (by rw [m4 0 (by omega) (by omega) (by omega), h0])
    set Sv := planarRAMRun p ⟨b + 26, (Function.update (Function.update (Function.update M 12 LVB) 20 32) 16 36), R⟩ τv with hSv
    obtain ⟨pcv, Mv, Rv⟩ := Sv
    simp only at v1 vT vR v12 v20 v22 v16 v18 vfr vRfr
    subst v1
    have ev : ∀ a, a % 2 = 0 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ 20 → a ≠ 22 →
        Mv a = M a := fun a hae a8 a10 a12 a14 a16 a18 a20 a22 =>
      (vfr a a8 a10 a12 a14 a16 a18 a20 a22 (fun v' w _ _ _ h => by
        have := pos_odd n (k * n) c v' w
        have e : 5 + 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v' * (k * n) + 2 * w = 5 + 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v' * (k * n) + 2 * w := rfl
        omega)).trans (m4 a a12 a20 a16)
    have mv26 : Mv 26 = 2 * n := by rw [ev 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h26]
    have mv6 : Mv 6 = c := by rw [ev 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h6]
    have mv2 : Mv 2 = 1 := by rw [ev 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h2]
    obtain ⟨M2, e3, f18, f6, ffr⟩ : ∃ M2, planarRAMRun p ⟨b + 51, Mv, Rv⟩ 3 = ⟨b + 22, M2, Rv⟩ ∧
        M2 18 = 5 + 2 * ((c + 1) * n) * (k * n) + 2 * ((c + 1) * n) ∧ M2 6 = c + 1 ∧
        (∀ a, a ≠ 18 → a ≠ 6 → M2 a = Mv a) := by
      refine ⟨Function.update (Function.update Mv 18 (Mv 18 + Mv 26)) 6 (Mv 6 + Mv 2), ?_, ?_, ?_, ?_⟩
      · rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at' p b 51 _ _ _ _ (by omega) c51,
          ex_add _ _ _ _ _ _ _ rfl, run_succ, step_at' p b 52 _ _ _ _ (by omega) c52,
          ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl),
          run_succ, step_at' p b 53 _ _ _ _ (by omega) c53, ex_jump, run_zero]
      · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, v18, mv26]; ring
      · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, mv6, mv2]
      · intro a a18 a6; simp only [Function.update_apply, a18, a6, if_false]
    have ev2 : ∀ a, a % 2 = 0 → a ≠ 8 → a ≠ 10 → a ≠ 12 → a ≠ 14 → a ≠ 16 → a ≠ 18 → a ≠ 20 → a ≠ 22 → a ≠ 6 →
        M2 a = M a := fun a hae a8 a10 a12 a14 a16 a18 a20 a22 a6 =>
      (ffr a a18 a6).trans (ev a hae a8 a10 a12 a14 a16 a18 a20 a22)
    obtain ⟨τ2, hτ2, r1, rT, rR, rev, rodd, rRfr⟩ := ih (c + 1) M2 Rv (by omega)
      (by rw [ev2 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h34])
      f6 f18 (by rw [ffr 22 (by omega) (by omega), v22]; ring)
      (by rw [ev2 30 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h30])
      (by rw [ev2 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h24])
      (by rw [ev2 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h26])
      (by rw [ev2 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h28])
      (by rw [ev2 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h2])
      (by rw [ev2 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h4])
      (by rw [ev2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0])
    have hm : ((11 * n + 20) * n + 8) * (r + 1) = ((11 * n + 20) * n + 8) * r + ((11 * n + 20) * n + 8) := by ring
    have hτv' : τv ≤ (11 * n + 20) * n + 1 := by simpa using hτv
    refine ⟨τs + τv + 3 + τ2, by omega, ?_⟩
    rw [run_add, run_add, run_add, e4, ← hSv, e3]
    have evL : ∀ j, M (LVB + 2 * j) = (if True then M (LVB + 2 * j) else 0) := fun j => rfl
    refine ⟨r1, fun c' v w hc1 hc2 hv hw => ?_, fun c' v hc1 hc2 hv => ?_, fun a ha h32 => ?_,
      fun a ha aT => ?_, fun a a0 aD => ?_⟩
    · rcases Nat.eq_or_lt_of_le hc1 with h | h
      · subst h
        have hp := pos_odd n (k * n) c v w
        rw [rodd _ hp (fun c'' v' w' h1 h2 h3 h4 => (pos_ne n k c c'' v v' w w' (by omega) h2 hv hw)),
          ffr _ (by omega) (by omega), vT v w (Nat.zero_le _) hv hw]
        rw [m4 _ (by omega) (by omega) (by omega), m4 _ (by omega) (by omega) (by omega)]
        have e1 : 2 * v * n = 2 * (v * n) := by ring
        rw [m4 (36 + 2 * v * n + 2 * w) (by omega) (by omega) (by omega)]
        rw [m4 _ (by have := pos_odd n (k * n) c v w; omega) (by have := pos_odd n (k * n) c v w; omega)
          (by have := pos_odd n (k * n) c v w; omega)]
      · have hp := pos_odd n (k * n) c' v w
        have e1 : 2 * v * n = 2 * (v * n) := by ring
        rw [rT c' v w h hc2 hv hw, ev2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega), ev2 _ (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega), ev2 (36 + 2 * v * n + 2 * w) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          ffr _ (by omega) (by omega),
          vfr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (fun v' w' _ hv' hw' => (pos_ne n k c c' v' v w' w h hc2 hv' hw').symm),
          m4 _ (by omega) (by omega) (by omega)]
    · rcases Nat.eq_or_lt_of_le hc1 with h | h
      · subst h
        rw [rRfr _ (by omega) (fun c'' v' h1 h2 h3 => by
              have := Nat.mul_le_mul_right n (show c + 1 ≤ c'' by omega)
              have e : (c + 1) * n = c * n + n := by ring
              omega),
          vR v (Nat.zero_le _) hv, m4 _ (by omega) (by omega) (by omega)]
      · rw [rR c' v h hc2 hv, ev2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega),
          vRfr (32 + 2 * v) (by omega) (fun v' _ _ => by omega),
          vRfr (1 + 2 * (c' * n) + 2 * v) (by omega) (fun v' _ hv' => by
            have := Nat.mul_le_mul_right n (show c + 1 ≤ c' by omega)
            have e : (c + 1) * n = c * n + n := by ring
            omega)]
    · rw [rev a ha h32, ev2 a ha (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
    · rw [rodd a ha (fun c' v w h1 h2 h3 h4 => aT c' v w (by omega) h2 h3 h4), ffr a (by omega) (by omega),
        vfr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun v w _ hv hw => aT c v w le_rfl (by omega) hv hw), m4 a (by omega) (by omega) (by omega)]
    · rw [rRfr a a0 (fun c' v h1 h2 h3 => aD c' v (by omega) h2 h3),
        vRfr a a0 (fun v _ hv => by have := aD c v le_rfl (by omega) hv; simpa using this)]

set_option maxHeartbeats 4000000 in
lemma mul_loop (n k : ℕ) :
    ∀ (r i acc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + r = k →
      M 34 = k → M 32 = n → M 2 = 1 → M 6 = i → M 8 = acc →
      ∃ τ, τ ≤ 4 * r + 1 ∧ (planarRAMRun p ⟨b + 7, M, R⟩ τ).pc = b + 11 ∧
        (planarRAMRun p ⟨b + 7, M, R⟩ τ).natMem 8 = acc + r * n ∧
        (∀ a, a ≠ 6 → a ≠ 8 → (planarRAMRun p ⟨b + 7, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b + 7, M, R⟩ τ).realMem = R := by
  have c0 : p[b + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 26 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natAdd 30 28 26) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 8 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natBranch 34 6 (b + 11) (b + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 8 8 32) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (jump (b + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 10 8 8) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natSub 24 10 26) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natConst 10 1) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natStore 10 8) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 8 34 34) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 8 8 34) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natConst 10 3) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natStore 10 8) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natConst 6 0) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 18 5) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natConst 22 1) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natBranch 34 6 (b + 54) (b + 23)) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natAdd 12 28 0) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natConst 20 32) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natConst 16 36) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natBranch 30 12 (b + 51) (b + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (natLoad 8 12) := by simpa using hcode 27 (by simp)
  have c28 : p[b + 28]? = some (natBranch 8 6 (b + 29) (b + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[b + 29]? = some (natBranch 6 8 (b + 44) (b + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[b + 30]? = some (realLoad 0 20) := by simpa using hcode 30 (by simp)
  have c31 : p[b + 31]? = some (realStore 22 0) := by simpa using hcode 31 (by simp)
  have c32 : p[b + 32]? = some (natAdd 14 28 0) := by simpa using hcode 32 (by simp)
  have c33 : p[b + 33]? = some (natBranch 30 14 (b + 46) (b + 34)) := by simpa using hcode 33 (by simp)
  have c34 : p[b + 34]? = some (natLoad 10 14) := by simpa using hcode 34 (by simp)
  have c35 : p[b + 35]? = some (natBranch 10 6 (b + 36) (b + 37)) := by simpa using hcode 35 (by simp)
  have c36 : p[b + 36]? = some (natBranch 6 10 (b + 40) (b + 37)) := by simpa using hcode 36 (by simp)
  have c37 : p[b + 37]? = some (natLoad 10 16) := by simpa using hcode 37 (by simp)
  have c38 : p[b + 38]? = some (natBranch 2 10 (b + 39) (b + 40)) := by simpa using hcode 38 (by simp)
  have c39 : p[b + 39]? = some (natStore 18 2) := by simpa using hcode 39 (by simp)
  have c40 : p[b + 40]? = some (natAdd 14 14 4) := by simpa using hcode 40 (by simp)
  have c41 : p[b + 41]? = some (natAdd 16 16 4) := by simpa using hcode 41 (by simp)
  have c42 : p[b + 42]? = some (natAdd 18 18 4) := by simpa using hcode 42 (by simp)
  have c43 : p[b + 43]? = some (jump (b + 33)) := by simpa using hcode 43 (by simp)
  have c44 : p[b + 44]? = some (natAdd 16 16 26) := by simpa using hcode 44 (by simp)
  have c45 : p[b + 45]? = some (natAdd 18 18 26) := by simpa using hcode 45 (by simp)
  have c46 : p[b + 46]? = some (natAdd 18 18 24) := by simpa using hcode 46 (by simp)
  have c47 : p[b + 47]? = some (natAdd 12 12 4) := by simpa using hcode 47 (by simp)
  have c48 : p[b + 48]? = some (natAdd 20 20 4) := by simpa using hcode 48 (by simp)
  have c49 : p[b + 49]? = some (natAdd 22 22 4) := by simpa using hcode 49 (by simp)
  have c50 : p[b + 50]? = some (jump (b + 26)) := by simpa using hcode 50 (by simp)
  have c51 : p[b + 51]? = some (natAdd 18 18 26) := by simpa using hcode 51 (by simp)
  have c52 : p[b + 52]? = some (natAdd 6 6 2) := by simpa using hcode 52 (by simp)
  have c53 : p[b + 53]? = some (jump (b + 22)) := by simpa using hcode 53 (by simp)
  intro r
  induction r with
  | zero =>
    intro i acc M R hi h34 h32 h2 h6 h8
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p b 7 _ rfl c7, run_zero]
    simp only [execInstr, show M 34 ≤ M 6 by omega, if_true]
    exact ⟨trivial, by simp [h8], fun a _ _ => trivial, trivial⟩
  | succ r ih =>
    intro i acc M R hi h34 h32 h2 h6 h8
    have hlt : ¬ M 34 ≤ M 6 := by omega
    obtain ⟨τ2, hτ2, r1, r8, rfr, rr⟩ := ih (i + 1) (acc + n)
      (Function.update (Function.update M 8 (acc + n)) 6 (i + 1)) R (by omega)
      (by simp [Function.update_apply, h34]) (by simp [Function.update_apply, h32])
      (by simp [Function.update_apply, h2]) (by simp) (by simp [Function.update_apply])
    refine ⟨4 + τ2, by omega, ?_⟩
    have e4 : planarRAMRun p ⟨b + 7, M, R⟩ 4 =
        ⟨b + 7, Function.update (Function.update M 8 (acc + n)) 6 (i + 1), R⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at' p b 7 _ _ _ _ (by omega) c7,
        ex_brf _ _ _ _ _ _ _ hlt, run_succ, step_at' p b 8 _ _ _ _ (by omega) c8,
        ex_add _ _ _ _ _ _ _ (by rw [h8, h32]), run_succ, step_at' p b 9 _ _ _ _ (by omega) c9,
        ex_add _ _ _ _ _ _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, h6, h2]; rfl),
        run_succ, step_at' p b 10 _ _ _ _ (by omega) c10, ex_jump, run_zero]
    rw [run_add, e4]
    refine ⟨r1, by rw [r8]; ring, fun a a6 a8 => ?_, rr⟩
    rw [rfr a a6 a8, Function.update_of_ne a6, Function.update_of_ne a8]

set_option maxHeartbeats 16000000 in
lemma union_build (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL36 : 36 + 2 * n * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 20 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 54 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = k * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 3 = 3 * k ∧
      (∀ c v w, c < k → v < n → w < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
        if M (LVB + 2 * v) ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1
        else M (5 + 2 * ((c * n + v) * (k * n) + (c * n + w)))) ∧
      (∀ c v, c < k → v < n → (planarRAMRun p ⟨b, M, R⟩ τ).realMem (2 * (c * n + v) + 1) =
        if M (LVB + 2 * v) ≠ c then R (32 + 2 * v) else R (2 * (c * n + v) + 1)) ∧
      (∀ a, a % 2 = 0 → 32 ≤ a → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 → (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) →
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) →
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[b + 0]? = some (natConst 0 0) := by simpa using hcode 0 (by simp)
  have c1 : p[b + 1]? = some (natConst 2 1) := by simpa using hcode 1 (by simp)
  have c2 : p[b + 2]? = some (natConst 4 2) := by simpa using hcode 2 (by simp)
  have c3 : p[b + 3]? = some (natAdd 26 32 32) := by simpa using hcode 3 (by simp)
  have c4 : p[b + 4]? = some (natAdd 30 28 26) := by simpa using hcode 4 (by simp)
  have c5 : p[b + 5]? = some (natConst 8 0) := by simpa using hcode 5 (by simp)
  have c6 : p[b + 6]? = some (natConst 6 0) := by simpa using hcode 6 (by simp)
  have c7 : p[b + 7]? = some (natBranch 34 6 (b + 11) (b + 8)) := by simpa using hcode 7 (by simp)
  have c8 : p[b + 8]? = some (natAdd 8 8 32) := by simpa using hcode 8 (by simp)
  have c9 : p[b + 9]? = some (natAdd 6 6 2) := by simpa using hcode 9 (by simp)
  have c10 : p[b + 10]? = some (jump (b + 7)) := by simpa using hcode 10 (by simp)
  have c11 : p[b + 11]? = some (natAdd 10 8 8) := by simpa using hcode 11 (by simp)
  have c12 : p[b + 12]? = some (natSub 24 10 26) := by simpa using hcode 12 (by simp)
  have c13 : p[b + 13]? = some (natConst 10 1) := by simpa using hcode 13 (by simp)
  have c14 : p[b + 14]? = some (natStore 10 8) := by simpa using hcode 14 (by simp)
  have c15 : p[b + 15]? = some (natAdd 8 34 34) := by simpa using hcode 15 (by simp)
  have c16 : p[b + 16]? = some (natAdd 8 8 34) := by simpa using hcode 16 (by simp)
  have c17 : p[b + 17]? = some (natConst 10 3) := by simpa using hcode 17 (by simp)
  have c18 : p[b + 18]? = some (natStore 10 8) := by simpa using hcode 18 (by simp)
  have c19 : p[b + 19]? = some (natConst 6 0) := by simpa using hcode 19 (by simp)
  have c20 : p[b + 20]? = some (natConst 18 5) := by simpa using hcode 20 (by simp)
  have c21 : p[b + 21]? = some (natConst 22 1) := by simpa using hcode 21 (by simp)
  have c22 : p[b + 22]? = some (natBranch 34 6 (b + 54) (b + 23)) := by simpa using hcode 22 (by simp)
  have c23 : p[b + 23]? = some (natAdd 12 28 0) := by simpa using hcode 23 (by simp)
  have c24 : p[b + 24]? = some (natConst 20 32) := by simpa using hcode 24 (by simp)
  have c25 : p[b + 25]? = some (natConst 16 36) := by simpa using hcode 25 (by simp)
  have c26 : p[b + 26]? = some (natBranch 30 12 (b + 51) (b + 27)) := by simpa using hcode 26 (by simp)
  have c27 : p[b + 27]? = some (natLoad 8 12) := by simpa using hcode 27 (by simp)
  have c28 : p[b + 28]? = some (natBranch 8 6 (b + 29) (b + 30)) := by simpa using hcode 28 (by simp)
  have c29 : p[b + 29]? = some (natBranch 6 8 (b + 44) (b + 30)) := by simpa using hcode 29 (by simp)
  have c30 : p[b + 30]? = some (realLoad 0 20) := by simpa using hcode 30 (by simp)
  have c31 : p[b + 31]? = some (realStore 22 0) := by simpa using hcode 31 (by simp)
  have c32 : p[b + 32]? = some (natAdd 14 28 0) := by simpa using hcode 32 (by simp)
  have c33 : p[b + 33]? = some (natBranch 30 14 (b + 46) (b + 34)) := by simpa using hcode 33 (by simp)
  have c34 : p[b + 34]? = some (natLoad 10 14) := by simpa using hcode 34 (by simp)
  have c35 : p[b + 35]? = some (natBranch 10 6 (b + 36) (b + 37)) := by simpa using hcode 35 (by simp)
  have c36 : p[b + 36]? = some (natBranch 6 10 (b + 40) (b + 37)) := by simpa using hcode 36 (by simp)
  have c37 : p[b + 37]? = some (natLoad 10 16) := by simpa using hcode 37 (by simp)
  have c38 : p[b + 38]? = some (natBranch 2 10 (b + 39) (b + 40)) := by simpa using hcode 38 (by simp)
  have c39 : p[b + 39]? = some (natStore 18 2) := by simpa using hcode 39 (by simp)
  have c40 : p[b + 40]? = some (natAdd 14 14 4) := by simpa using hcode 40 (by simp)
  have c41 : p[b + 41]? = some (natAdd 16 16 4) := by simpa using hcode 41 (by simp)
  have c42 : p[b + 42]? = some (natAdd 18 18 4) := by simpa using hcode 42 (by simp)
  have c43 : p[b + 43]? = some (jump (b + 33)) := by simpa using hcode 43 (by simp)
  have c44 : p[b + 44]? = some (natAdd 16 16 26) := by simpa using hcode 44 (by simp)
  have c45 : p[b + 45]? = some (natAdd 18 18 26) := by simpa using hcode 45 (by simp)
  have c46 : p[b + 46]? = some (natAdd 18 18 24) := by simpa using hcode 46 (by simp)
  have c47 : p[b + 47]? = some (natAdd 12 12 4) := by simpa using hcode 47 (by simp)
  have c48 : p[b + 48]? = some (natAdd 20 20 4) := by simpa using hcode 48 (by simp)
  have c49 : p[b + 49]? = some (natAdd 22 22 4) := by simpa using hcode 49 (by simp)
  have c50 : p[b + 50]? = some (jump (b + 26)) := by simpa using hcode 50 (by simp)
  have c51 : p[b + 51]? = some (natAdd 18 18 26) := by simpa using hcode 51 (by simp)
  have c52 : p[b + 52]? = some (natAdd 6 6 2) := by simpa using hcode 52 (by simp)
  have c53 : p[b + 53]? = some (jump (b + 22)) := by simpa using hcode 53 (by simp)
  have sA : (planarRAMRun p ⟨b, M, R⟩ 7).pc = b + 7 ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 0 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 2 = 1 ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 4 = 2 ∧
      (planarRAMRun p ⟨b, M, R⟩ 7).natMem 26 = 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 30 = LVB + 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 8 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ 7).natMem 6 = 0 ∧
      (∀ a, a ≠ 0 → a ≠ 2 → a ≠ 4 → a ≠ 26 → a ≠ 30 → a ≠ 8 → a ≠ 6 → (planarRAMRun p ⟨b, M, R⟩ 7).natMem a = M a) ∧ (planarRAMRun p ⟨b, M, R⟩ 7).realMem = R := by
    rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p b 0 _ _ _ _ (by omega) c0, ex_const]
    rw [run_succ, step_at' p b 1 _ _ _ _ (by omega) c1, ex_const]
    rw [run_succ, step_at' p b 2 _ _ _ _ (by omega) c2, ex_const]
    rw [run_succ, step_at' p b 3 _ _ _ _ (by omega) c3, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h34, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 4 _ _ _ _ (by omega) c4, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, h32, h34, h28] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 5 _ _ _ _ (by omega) c5, ex_const]
    rw [run_succ, step_at' p b 6 _ _ _ _ (by omega) c6, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, h32, h34, h28]; ring1)
      | (intro a a0 a2 a4 a26 a30 a8 a6; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a0, a2, a4, a26, a30, a8, a6])
  obtain ⟨a1, a0, a2, a4, a26, a30, a8, a6, afr, ar⟩ := sA
  set S7 := planarRAMRun p ⟨b, M, R⟩ 7 with hS7
  obtain ⟨pc7, M7, R7⟩ := S7
  simp only at a1 a0 a2 a4 a26 a30 a8 a6 afr ar
  subst a1; subst R7
  have f7 : ∀ a, 32 ≤ a → M7 a = M a := fun a ha => afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨τm, hτm, m1, m8, mfr, mr⟩ := mul_loop p b hcode n k k 0 0 M7 R (by omega)
    (by rw [f7 34 (by omega), h34]) (by rw [f7 32 (by omega), h32]) a2 a6 a8
  set S8 := planarRAMRun p ⟨b + 7, M7, R⟩ τm with hS8
  obtain ⟨pc8, M8, R8⟩ := S8
  simp only at m1 m8 mfr mr
  subst m1; subst R8
  have g8 : M8 8 = k * n := by rw [m8]; ring
  have g32 : M8 32 = n := by rw [mfr 32 (by omega) (by omega), f7 32 (by omega), h32]
  have g34 : M8 34 = k := by rw [mfr 34 (by omega) (by omega), f7 34 (by omega), h34]
  have g26 : M8 26 = 2 * n := by rw [mfr 26 (by omega) (by omega), a26]
  have sB : (planarRAMRun p ⟨b + 11, M8, R⟩ 11).pc = b + 22 ∧ (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 24 = 2 * (k * n) - 2 * n ∧ (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 1 = k * n ∧
      (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 3 = 3 * k ∧ (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 6 = 0 ∧ (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 18 = 5 + 2 * (0 * n) * (k * n) + 2 * (0 * n) ∧
      (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem 22 = 1 + 2 * (0 * n) ∧
      (∀ a, a ≠ 10 → a ≠ 24 → a ≠ 1 → a ≠ 8 → a ≠ 3 → a ≠ 6 → a ≠ 18 → a ≠ 22 → (planarRAMRun p ⟨b + 11, M8, R⟩ 11).natMem a = M8 a) ∧ (planarRAMRun p ⟨b + 11, M8, R⟩ 11).realMem = R := by
    rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at' p b 11 _ _ _ _ (by omega) c11, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 12 _ _ _ _ (by omega) c12, ex_sub _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 13 _ _ _ _ (by omega) c13, ex_const]
    rw [run_succ, step_at' p b 14 _ _ _ _ (by omega) c14, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 15 _ _ _ _ (by omega) c15, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 16 _ _ _ _ (by omega) c16, ex_add _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 17 _ _ _ _ (by omega) c17, ex_const]
    rw [run_succ, step_at' p b 18 _ _ _ _ (by omega) c18, ex_store _ _ _ _ _ _ _ (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl) (by first | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, add_zero, g8, g32, g34, g26] <;> first | rfl | omega) | rfl)]
    rw [run_succ, step_at' p b 19 _ _ _ _ (by omega) c19, ex_const]
    rw [run_succ, step_at' p b 20 _ _ _ _ (by omega) c20, ex_const]
    rw [run_succ, step_at' p b 21 _ _ _ _ (by omega) c21, ex_const]
    rw [run_zero]
    try rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals first
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, g8, g32, g34, g26]; done)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, g8, g32, g34, g26] <;> omega)
      | (simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, g8, g32, g34, g26]; ring1)
      | (intro a a10 a24 a1 a8 a3 a6 a18 a22; simp only [Function.update_apply, ite_true, ite_false, Nat.reduceEqDiff, ↓reduceIte, eq_self_iff_true, if_true, add_zero, ne_eq, not_true_eq_false, false_and, if_false, a10, a24, a1, a8, a3, a6, a18, a22])
  obtain ⟨b1, b24, b1n, b3, b6, b18, b22, bfr, br⟩ := sB
  set S9 := planarRAMRun p ⟨b + 11, M8, R⟩ 11 with hS9
  obtain ⟨pc9, M9, R9⟩ := S9
  simp only at b1 b24 b1n b3 b6 b18 b22 bfr br
  subst b1; subst R9
  have e9 : ∀ a, a ≠ 10 → a ≠ 24 → a ≠ 1 → a ≠ 8 → a ≠ 3 → a ≠ 6 → a ≠ 18 → a ≠ 22 → a ≠ 0 → a ≠ 2 →
      a ≠ 4 → a ≠ 26 → a ≠ 30 → M9 a = M a := fun a a10 a24 a1 a8 a3 a6 a18 a22 a0 a2 a4 a26 a30 => by
    rw [bfr a a10 a24 a1 a8 a3 a6 a18 a22, mfr a a6 a8, afr a a0 a2 a4 a26 a30 a8 a6]
  have k9 : ∀ a, a ≠ 10 → a ≠ 24 → a ≠ 1 → a ≠ 8 → a ≠ 3 → a ≠ 6 → a ≠ 18 → a ≠ 22 → M9 a = M8 a := bfr
  obtain ⟨τc, hτc, c1, cT, cR, cev, codd, cRfr⟩ := c_loop p b hcode n k LVB hLe hL36 k 0 M9 R (by omega)
    (by rw [k9 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g34])
    b6 b18 b22
    (by rw [k9 30 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 30 (by omega) (by omega), a30])
    b24
    (by rw [k9 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g26])
    (by rw [e9 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), h28])
    (by rw [k9 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 2 (by omega) (by omega), a2])
    (by rw [k9 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 4 (by omega) (by omega), a4])
    (by rw [k9 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 0 (by omega) (by omega), a0])
  have hposeq : ∀ c v w, 5 + 2 * ((c * n + v) * (k * n) + (c * n + w)) =
      5 + 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v * (k * n) + 2 * w := fun c v w => by ring
  have hdeq : ∀ c v, 2 * (c * n + v) + 1 = 1 + 2 * (c * n) + 2 * v := fun c v => by ring
  refine ⟨7 + τm + 11 + τc, by nlinarith, ?_⟩
  rw [run_add, run_add, run_add, ← hS7, ← hS8, ← hS9]
  refine ⟨c1, ?_, ?_, fun c v w hc hv hw => ?_, fun c v hc hv => ?_, fun a ha h32' => ?_,
    fun a ha a1 a3 aT => ?_, fun a a0 aD => ?_⟩
  · rw [codd 1 (by omega) (fun c' v w _ _ _ _ => by omega), b1n]
  · rw [codd 3 (by omega) (fun c' v w _ _ _ _ => by omega), b3]
  · have hp := pos_odd n (k * n) c v w
    rw [hposeq, cT c v w (Nat.zero_le _) hc hv hw]
    have e1 : 2 * v * n = 2 * (v * n) := by ring
    rw [e9 (LVB + 2 * v) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega),
      e9 (LVB + 2 * w) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega),
      e9 (36 + 2 * v * n + 2 * w) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      e9 (5 + 2 * (c * n) * (k * n) + 2 * (c * n) + 2 * v * (k * n) + 2 * w) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [hdeq, cR c v (Nat.zero_le _) hc hv,
      e9 (LVB + 2 * v) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [cev a ha h32', e9 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [codd a ha (fun c v w _ hc hv hw h => aT c v w hc hv hw (by rw [hposeq]; exact h)),
      e9 a (by omega) (by omega) a1 (by omega) a3 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  · rw [cRfr a a0 (fun c v _ hc hv h => aD c v hc hv (by rw [hdeq]; exact h))]

end

end UB

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 26 32 32,
      natAdd 30 28 26,
      natConst 8 0,
      natConst 6 0,
      natBranch 34 6 (b + 11) (b + 8),
      natAdd 8 8 32,
      natAdd 6 6 2,
      jump (b + 7),
      natAdd 10 8 8,
      natSub 24 10 26,
      natConst 10 1,
      natStore 10 8,
      natAdd 8 34 34,
      natAdd 8 8 34,
      natConst 10 3,
      natStore 10 8,
      natConst 6 0,
      natConst 18 5,
      natConst 22 1,
      natBranch 34 6 (b + 54) (b + 23),
      natAdd 12 28 0,
      natConst 20 32,
      natConst 16 36,
      natBranch 30 12 (b + 51) (b + 27),
      natLoad 8 12,
      natBranch 8 6 (b + 29) (b + 30),
      natBranch 6 8 (b + 44) (b + 30),
      realLoad 0 20,
      realStore 22 0,
      natAdd 14 28 0,
      natBranch 30 14 (b + 46) (b + 34),
      natLoad 10 14,
      natBranch 10 6 (b + 36) (b + 37),
      natBranch 6 10 (b + 40) (b + 37),
      natLoad 10 16,
      natBranch 2 10 (b + 39) (b + 40),
      natStore 18 2,
      natAdd 14 14 4,
      natAdd 16 16 4,
      natAdd 18 18 4,
      jump (b + 33),
      natAdd 16 16 26,
      natAdd 18 18 26,
      natAdd 18 18 24,
      natAdd 12 12 4,
      natAdd 20 20 4,
      natAdd 22 22 4,
      jump (b + 26),
      natAdd 18 18 26,
      natAdd 6 6 2,
      jump (b + 22)])
    (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL36 : 36 + 2 * n * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 20 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 54 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = k * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 3 = 3 * k ∧
      (∀ c v w, c < k → v < n → w < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
        if M (LVB + 2 * v) ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1
        else M (5 + 2 * ((c * n + v) * (k * n) + (c * n + w)))) ∧
      (∀ c v, c < k → v < n → (planarRAMRun p ⟨b, M, R⟩ τ).realMem (2 * (c * n + v) + 1) =
        if M (LVB + 2 * v) ≠ c then R (32 + 2 * v) else R (2 * (c * n + v) + 1)) ∧
      (∀ a, a % 2 = 0 → 32 ≤ a → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 → (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) →
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) →
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem a = R a) :=
  UB.union_build p b hcode n k LVB hk hLe hL36 M R h32 h34 h28
