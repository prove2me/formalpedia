-- Prove2me | solution 1 for WilliamsonShmoys.ram_baker_seg_output
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:27:53.771025+00:00
-- url     : https://prove2.me/submissions/359c5449-96b2-4905-a3f1-e63f2d78072f

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Theorems.Thm_WilliamsonShmoys_ram_best_copy_select
import Theorems.Thm_WilliamsonShmoys_ram_output_bitmap_write

set_option autoImplicit false

namespace SG4
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

lemma ex_radd (d l r pc : ℕ) (v : ℝ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : R l + R r = v) :
    execInstr (realAdd d l r) ⟨pc, M, R⟩ = ⟨pc + 1, M, Function.update R d v⟩ := by
  rw [← h]; rfl

lemma ex_rbrt (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : R l ≤ R r) :
    execInstr (realBranch l r y n) ⟨pc, M, R⟩ = ⟨y, M, R⟩ := by
  simp [execInstr, h]

lemma ex_rbrf (l r y n pc : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h : ¬ R l ≤ R r) :
    execInstr (realBranch l r y n) ⟨pc, M, R⟩ = ⟨n, M, R⟩ := by
  simp [execInstr, h]

set_option maxHeartbeats 8000000 in
lemma seg4 (p : List PlanarRAMInstruction) (X : ℕ)
    (hca : CodeAt p X [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 24 32 32, natAdd 18 28 24, natConst 26 0, natConst 6 0, natBranch 34 6 (X + 11) (X + 8), natAdd 26 26 32, natAdd 6 6 2, jump (X + 7), natConst 30 0, natConst 6 0, natBranch 26 6 (X + 17) (X + 14), natAdd 30 30 26, natAdd 6 6 2, jump (X + 13), natAdd 30 30 30, natConst 8 5, natAdd 14 30 8, natConst 6 0, natConst 20 0, natAdd 22 14 0, realZero 4, natBranch 34 6 (X + 50) (X + 25), realZero 2, natAdd 10 28 0, natConst 16 32, natAdd 12 14 0, natBranch 18 10 (X + 41) (X + 30), natLoad 8 12, natBranch 2 8 (X + 32) (X + 37), natLoad 8 10, natBranch 8 6 (X + 34) (X + 35), natBranch 6 8 (X + 37) (X + 35), realLoad 0 16, realAdd 2 2 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 16 16 4, jump (X + 29), natBranch 6 0 (X + 43) (X + 42), realBranch 2 4 (X + 47) (X + 43), realZero 4, realAdd 4 4 2, natAdd 20 6 0, natAdd 22 14 0, natAdd 14 14 24, natAdd 6 6 2, jump (X + 24)])
    (hg4 : CodeAt p (X + 50) [natConst 0 0, natAdd 32 40 0, natAdd 28 42 0])
    (hcb : CodeAt p (X + 53) [natConst 0 0, natConst 2 1, natConst 4 2, natConst 36 16, natAdd 24 32 32, natAdd 18 28 24, natConst 30 0, natConst 6 0, natBranch 32 6 (X + 53 + 12) (X + 53 + 9), natAdd 30 30 32, natAdd 6 6 2, jump (X + 53 + 8), natAdd 26 30 0, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natConst 8 32, natAdd 38 30 8, natAdd 10 28 0, natAdd 12 22 0, natBranch 18 10 (X + 53 + 34) (X + 53 + 22), natLoad 8 12, natBranch 2 8 (X + 53 + 24) (X + 53 + 29), natLoad 8 10, natBranch 8 20 (X + 53 + 26) (X + 53 + 27), natBranch 20 8 (X + 53 + 29) (X + 53 + 27), natStore 38 2, jump (X + 53 + 30), natStore 38 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 38 38 36, jump (X + 53 + 21), natAdd 0 26 32, natAdd 0 0 2, natAdd 8 30 36, natStore 8 8, natAdd 1 0 0, natAdd 1 1 1, natAdd 1 1 1, natAdd 1 1 1, natLoad 1 1, natBranch 0 1 (X + 53 + 48) (X + 53 + 44), natStore 0 1, natConst 1 1, natSub 0 0 1, jump (X + 53 + 38)])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h40 : M 40 = n) (h42 : M 42 = (16 * (n * n) + 16 * n + 48)) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 26 * n + 52 ∧ (planarRAMRun p ⟨X, M, R⟩ τ).pc = X + 101 ∧
      ∃ cs, cs < k ∧ (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ cs then R (32 + 2 * j) else 0)) ∧
        ∀ v, v < n → (planarRAMRun p ⟨X, M, R⟩ τ).natMem (2 + n * n + v) =
          if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * v) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * v) ≠ cs then 1 else 0 := by
  set LVB := (16 * (n * n) + 16 * n + 48) with hLVB
  obtain ⟨τa, hτa, a1, a20, a22, aW, afr, aRfr⟩ :=
    ram_best_copy_select p X hca n k LVB hk (by rw [hLVB]; omega) (by rw [hLVB]; omega) M R h32 h34 h28
  set S1 := planarRAMRun p ⟨X, M, R⟩ τa with hS1
  obtain ⟨pc1, M1, R1⟩ := S1
  simp only at a1 a20 a22 aW afr aRfr
  subst a1
  have g0 : p[X + 50 + 0]? = some (natConst 0 0) := by simpa using hg4 0 (by simp)
  have g1 : p[X + 50 + 1]? = some (natAdd 32 40 0) := by simpa using hg4 1 (by simp)
  have g2 : p[X + 50 + 2]? = some (natAdd 28 42 0) := by simpa using hg4 2 (by simp)
  have m40 : M1 40 = n := by rw [afr 40 (Or.inr (by omega)), h40]
  have m42 : M1 42 = LVB := by rw [afr 42 (Or.inr (by omega)), h42]
  have eg : planarRAMRun p ⟨X + 50, M1, R1⟩ 3 =
      ⟨X + 53, Function.update (Function.update (Function.update M1 0 0) 32 n) 28 LVB, R1⟩ := by
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at' p (X + 50) 0 _ _ _ _ (by omega) g0, ex_const,
      run_succ, step_at' p (X + 50) 1 _ _ _ _ (by omega) g1,
      ex_add _ _ _ _ n _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, m40, add_zero]),
      run_succ, step_at' p (X + 50) 2 _ _ _ _ (by omega) g2,
      ex_add _ _ _ _ LVB _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, m42, add_zero]),
      run_zero]
  set M2 := Function.update (Function.update (Function.update M1 0 0) 32 n) 28 LVB with hM2
  have k2 : ∀ a, a ≠ 0 → a ≠ 32 → a ≠ 28 → M2 a = M1 a := fun a a0 a32 a28 => by
    rw [hM2, Function.update_of_ne a28, Function.update_of_ne a32, Function.update_of_ne a0]
  have hBo : (5 + 2 * (k * n) * (k * n) + 2 * M1 20 * n) % 2 = 1 := by
    have e1 : 2 * (k * n) * (k * n) = 2 * ((k * n) * (k * n)) := by ring
    have e2 : 2 * M1 20 * n = 2 * (M1 20 * n) := by ring
    omega
  obtain ⟨τb, hτb, b1, bO⟩ := ram_output_bitmap_write p (X + 53) hcb n LVB (5 + 2 * (k * n) * (k * n) + 2 * M1 20 * n)
    (M1 20) (by rw [hLVB]; omega) hBo (by rw [hLVB]; nlinarith) M2 R1
    (by rw [hM2]; simp) (by rw [hM2]; simp) (by rw [k2 20 (by omega) (by omega) (by omega)])
    (by rw [k2 22 (by omega) (by omega) (by omega), a22])
  refine ⟨τa + 3 + τb, by omega, ?_⟩
  rw [run_add, run_add, ← hS1, eg]
  refine ⟨by rw [b1], M1 20, a20, aW, fun v hv => ?_⟩
  rw [bO v hv]
  have e1 : (5 + 2 * (k * n) * (k * n) + 2 * M1 20 * n + 2 * v) % 2 = 1 := by
    have e2 : 2 * v = 2 * v := rfl
    omega
  rw [k2 _ (by omega) (by omega) (by omega), afr _ (Or.inl e1),
    k2 (LVB + 2 * v) (by rw [hLVB]; omega) (by rw [hLVB]; omega) (by rw [hLVB]; omega),
    afr (LVB + 2 * v) (Or.inr (by rw [hLVB]; omega))]

end SG4

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (X : ℕ)
    (hca : CodeAt p X [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 24 32 32, natAdd 18 28 24, natConst 26 0, natConst 6 0, natBranch 34 6 (X + 11) (X + 8), natAdd 26 26 32, natAdd 6 6 2, jump (X + 7), natConst 30 0, natConst 6 0, natBranch 26 6 (X + 17) (X + 14), natAdd 30 30 26, natAdd 6 6 2, jump (X + 13), natAdd 30 30 30, natConst 8 5, natAdd 14 30 8, natConst 6 0, natConst 20 0, natAdd 22 14 0, realZero 4, natBranch 34 6 (X + 50) (X + 25), realZero 2, natAdd 10 28 0, natConst 16 32, natAdd 12 14 0, natBranch 18 10 (X + 41) (X + 30), natLoad 8 12, natBranch 2 8 (X + 32) (X + 37), natLoad 8 10, natBranch 8 6 (X + 34) (X + 35), natBranch 6 8 (X + 37) (X + 35), realLoad 0 16, realAdd 2 2 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 16 16 4, jump (X + 29), natBranch 6 0 (X + 43) (X + 42), realBranch 2 4 (X + 47) (X + 43), realZero 4, realAdd 4 4 2, natAdd 20 6 0, natAdd 22 14 0, natAdd 14 14 24, natAdd 6 6 2, jump (X + 24)])
    (hg4 : CodeAt p (X + 50) [natConst 0 0, natAdd 32 40 0, natAdd 28 42 0])
    (hcb : CodeAt p (X + 53) [natConst 0 0, natConst 2 1, natConst 4 2, natConst 36 16, natAdd 24 32 32, natAdd 18 28 24, natConst 30 0, natConst 6 0, natBranch 32 6 (X + 53 + 12) (X + 53 + 9), natAdd 30 30 32, natAdd 6 6 2, jump (X + 53 + 8), natAdd 26 30 0, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natConst 8 32, natAdd 38 30 8, natAdd 10 28 0, natAdd 12 22 0, natBranch 18 10 (X + 53 + 34) (X + 53 + 22), natLoad 8 12, natBranch 2 8 (X + 53 + 24) (X + 53 + 29), natLoad 8 10, natBranch 8 20 (X + 53 + 26) (X + 53 + 27), natBranch 20 8 (X + 53 + 29) (X + 53 + 27), natStore 38 2, jump (X + 53 + 30), natStore 38 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 38 38 36, jump (X + 53 + 21), natAdd 0 26 32, natAdd 0 0 2, natAdd 8 30 36, natStore 8 8, natAdd 1 0 0, natAdd 1 1 1, natAdd 1 1 1, natAdd 1 1 1, natLoad 1 1, natBranch 0 1 (X + 53 + 48) (X + 53 + 44), natStore 0 1, natConst 1 1, natSub 0 0 1, jump (X + 53 + 38)])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h40 : M 40 = n) (h42 : M 42 = (16 * (n * n) + 16 * n + 48)) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 26 * n + 52 ∧ (planarRAMRun p ⟨X, M, R⟩ τ).pc = X + 101 ∧
      ∃ cs, cs < k ∧ (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ cs then R (32 + 2 * j) else 0)) ∧
        ∀ v, v < n → (planarRAMRun p ⟨X, M, R⟩ τ).natMem (2 + n * n + v) =
          if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * v) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * v) ≠ cs then 1 else 0 :=
  SG4.seg4 p X hca hg4 hcb n k hk M R h32 h34 h28 h40 h42
