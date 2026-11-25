-- Prove2me | solution 1 for WilliamsonShmoys.ram_zero_odd_cells
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T06:03:09.653806+00:00
-- url     : https://prove2.me/submissions/4e8015e2-7ea5-4432-b819-48a310045657

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace ZO
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
variable (p : List PlanarRAMInstruction) (z : ℕ)
  (hcode : CodeAt p z
    [natConst 0 1,
      natConst 4 2,
      natConst 6 0,
      realZero 0,
      natBranch 2 0 (z + 9) (z + 5),
      natStore 0 6,
      realStore 0 0,
      natAdd 0 0 4,
      jump (z + 4)])
include hcode

lemma zero_loop (K : ℕ) :
    ∀ (r m : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), m + r = K →
      M 0 = 2 * m + 1 → M 2 = 2 * K + 1 → M 4 = 2 → M 6 = 0 → R 0 = 0 →
      ∃ τ, τ ≤ 5 * r + 1 ∧ (planarRAMRun p ⟨z + 4, M, R⟩ τ).pc = z + 9 ∧
        (∀ i, m ≤ i → i < K → (planarRAMRun p ⟨z + 4, M, R⟩ τ).natMem (2 * i + 1) = 0 ∧ (planarRAMRun p ⟨z + 4, M, R⟩ τ).realMem (2 * i + 1) = 0) ∧
        (∀ a, a ≠ 0 → (∀ i, m ≤ i → i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z + 4, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, (∀ i, m ≤ i → i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z + 4, M, R⟩ τ).realMem a = R a) ∧
        (planarRAMRun p ⟨z + 4, M, R⟩ τ).natMem 0 = 2 * K + 1 := by
  have c0 : p[z + 0]? = some (natConst 0 1) := by simpa using hcode 0 (by simp)
  have c1 : p[z + 1]? = some (natConst 4 2) := by simpa using hcode 1 (by simp)
  have c2 : p[z + 2]? = some (natConst 6 0) := by simpa using hcode 2 (by simp)
  have c3 : p[z + 3]? = some (realZero 0) := by simpa using hcode 3 (by simp)
  have c4 : p[z + 4]? = some (natBranch 2 0 (z + 9) (z + 5)) := by simpa using hcode 4 (by simp)
  have c5 : p[z + 5]? = some (natStore 0 6) := by simpa using hcode 5 (by simp)
  have c6 : p[z + 6]? = some (realStore 0 0) := by simpa using hcode 6 (by simp)
  have c7 : p[z + 7]? = some (natAdd 0 0 4) := by simpa using hcode 7 (by simp)
  have c8 : p[z + 8]? = some (jump (z + 4)) := by simpa using hcode 8 (by simp)
  intro r
  induction r with
  | zero =>
    intro m M R hm h0 h2 h4 h6 hR0
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p z 4 _ rfl c4, run_zero]
    simp only [execInstr, show M 2 ≤ M 0 by omega, if_true]
    exact ⟨trivial, fun i h1 h2 => by omega, fun a _ _ => trivial, fun a _ => trivial, by omega⟩
  | succ r ih =>
    intro m M R hm h0 h2 h4 h6 hR0
    have hlt : ¬ M 2 ≤ M 0 := by omega
    set M1 := Function.update (Function.update M (2 * m + 1) 0) 0 (2 * (m + 1) + 1) with hM1
    set R1 := Function.update R (2 * m + 1) 0 with hR1
    have e4 : planarRAMRun p ⟨z + 4, M, R⟩ 5 = ⟨z + 4, M1, R1⟩ := by
      rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at p z 4 _ rfl c4,
        run_succ, step_at p z 5 _ (by simp [execInstr, hlt]) c5,
        run_succ, step_at p z 6 _ (by simp [execInstr, hlt]) c6,
        run_succ, step_at p z 7 _ (by simp [execInstr, hlt]) c7,
        run_succ, step_at p z 8 _ (by simp [execInstr, hlt]) c8, run_zero]
      simp only [execInstr]
      congr 1
      · rw [hM1]; funext a; simp only [Function.update_apply, h0, h4, h6]
        split_ifs <;> first | rfl | omega | contradiction
      · rw [hR1]; funext a; simp only [Function.update_apply, h0, hR0]
        split_ifs <;> first | rfl | omega | contradiction
    have fM : ∀ a, a ≠ 0 → a ≠ 2 * m + 1 → M1 a = M a := fun a a0 a1 => by
      rw [hM1, Function.update_of_ne a0, Function.update_of_ne a1]
    obtain ⟨τ, hτ, r1, rz, rfr, rfrR, r0⟩ := ih (m + 1) M1 R1 (by omega) (by rw [hM1]; simp)
      (by rw [fM 2 (by omega) (by omega), h2]) (by rw [fM 4 (by omega) (by omega), h4])
      (by rw [fM 6 (by omega) (by omega), h6]) (by rw [hR1, Function.update_of_ne (by omega), hR0])
    refine ⟨5 + τ, by omega, ?_⟩
    rw [run_add, e4]
    refine ⟨r1, fun i hi1 hi2 => ?_, fun a a0 ha => ?_, fun a ha => ?_, r0⟩
    · rcases Nat.eq_or_lt_of_le hi1 with h | h
      · subst h
        rw [rfr _ (by omega) (fun i' h1 _ => by omega), rfrR _ (fun i' h1 _ => by omega)]
        exact ⟨by rw [hM1, Function.update_of_ne (by omega), Function.update_self],
          by rw [hR1, Function.update_self]⟩
      · exact rz i h hi2
    · rw [rfr a a0 (fun i h1 h2 => ha i (by omega) h2), fM a a0 (ha m le_rfl (by omega))]
    · rw [rfrR a (fun i h1 h2 => ha i (by omega) h2), hR1, Function.update_of_ne (ha m le_rfl (by omega))]

lemma zero_sweep (K : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h2 : M 2 = 2 * K + 1) :
    ∃ τ, τ ≤ 5 * K + 5 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).pc = z + 9 ∧
      (∀ i, i < K → (planarRAMRun p ⟨z, M, R⟩ τ).natMem (2 * i + 1) = 0 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).realMem (2 * i + 1) = 0) ∧
      (∀ a, a ≠ 0 → a ≠ 4 → a ≠ 6 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).realMem a = R a) := by
  have c0 : p[z + 0]? = some (natConst 0 1) := by simpa using hcode 0 (by simp)
  have c1 : p[z + 1]? = some (natConst 4 2) := by simpa using hcode 1 (by simp)
  have c2 : p[z + 2]? = some (natConst 6 0) := by simpa using hcode 2 (by simp)
  have c3 : p[z + 3]? = some (realZero 0) := by simpa using hcode 3 (by simp)
  have c4 : p[z + 4]? = some (natBranch 2 0 (z + 9) (z + 5)) := by simpa using hcode 4 (by simp)
  have c5 : p[z + 5]? = some (natStore 0 6) := by simpa using hcode 5 (by simp)
  have c6 : p[z + 6]? = some (realStore 0 0) := by simpa using hcode 6 (by simp)
  have c7 : p[z + 7]? = some (natAdd 0 0 4) := by simpa using hcode 7 (by simp)
  have c8 : p[z + 8]? = some (jump (z + 4)) := by simpa using hcode 8 (by simp)
  set M4 := Function.update (Function.update (Function.update M 0 1) 4 2) 6 0 with hM4
  set R4 := Function.update R 0 0 with hR4
  have e4 : planarRAMRun p ⟨z, M, R⟩ 4 = ⟨z + 4, M4, R4⟩ := by
    rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at p z 0 _ (by simp) c0,
      run_succ, step_at p z 1 _ (by simp [execInstr]) c1,
      run_succ, step_at p z 2 _ (by simp [execInstr]) c2,
      run_succ, step_at p z 3 _ (by simp [execInstr]) c3, run_zero]
    rfl
  have fM : ∀ a, a ≠ 0 → a ≠ 4 → a ≠ 6 → M4 a = M a := fun a a0 a4 a6 => by
    rw [hM4, Function.update_of_ne a6, Function.update_of_ne a4, Function.update_of_ne a0]
  obtain ⟨τ, hτ, r1, rz, rfr, rfrR, -⟩ := zero_loop p z hcode K K 0 M4 R4 (by omega) (by rw [hM4]; simp)
    (by rw [fM 2 (by omega) (by omega) (by omega), h2]) (by rw [hM4]; simp) (by rw [hM4]; simp)
    (by rw [hR4]; simp)
  refine ⟨4 + τ, by omega, ?_⟩
  rw [run_add, e4]
  refine ⟨r1, fun i hi => rz i (Nat.zero_le _) hi, fun a a0 a4 a6 ha => ?_, fun a a0 ha => ?_⟩
  · rw [rfr a a0 (fun i _ h => ha i h), fM a a0 a4 a6]
  · rw [rfrR a (fun i _ h => ha i h), hR4, Function.update_of_ne a0]

end

end ZO

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (z : ℕ)
    (hcode : CodeAt p z
    [natConst 0 1,
      natConst 4 2,
      natConst 6 0,
      realZero 0,
      natBranch 2 0 (z + 9) (z + 5),
      natStore 0 6,
      realStore 0 0,
      natAdd 0 0 4,
      jump (z + 4)])
    (K : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h2 : M 2 = 2 * K + 1) :
    ∃ τ, τ ≤ 5 * K + 5 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).pc = z + 9 ∧
      (∀ i, i < K → (planarRAMRun p ⟨z, M, R⟩ τ).natMem (2 * i + 1) = 0 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).realMem (2 * i + 1) = 0) ∧
      (∀ a, a ≠ 0 → a ≠ 4 → a ≠ 6 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).realMem a = R a) :=
  ZO.zero_sweep p z hcode K M R h2
