-- Prove2me | solution 1 for WilliamsonShmoys.ram_level_mod_sweep
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T05:58:02.209931+00:00
-- url     : https://prove2.me/submissions/7432a7bc-c6d8-4a44-87de-5babf8e33fde

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace MK
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
variable (p : List PlanarRAMInstruction) (h : ℕ)
  (hcode : CodeAt p h
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (h + 12) (h + 3),
      natLoad 22 27,
      natSub 22 22 17,
      natBranch 16 22 (h + 6) (h + 8),
      natSub 22 22 16,
      jump (h + 5),
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (h + 2)])
include hcode

lemma mod_loop (k : ℕ) (hk : 0 < k) :
    ∀ (q x : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), x / k ≤ q → M 16 = k → M 22 = x →
      ∃ τ, τ ≤ 3 * (x / k) + 1 ∧ (planarRAMRun p ⟨h + 5, M, R⟩ τ).pc = h + 8 ∧ (planarRAMRun p ⟨h + 5, M, R⟩ τ).natMem 22 = x % k ∧
        (∀ a, a ≠ 22 → (planarRAMRun p ⟨h + 5, M, R⟩ τ).natMem a = M a) ∧ (planarRAMRun p ⟨h + 5, M, R⟩ τ).realMem = R := by
  have c0 : p[h + 0]? = some (natConst 24 0) := by simpa using hcode 0 (by simp)
  have c1 : p[h + 1]? = some (natAdd 27 28 12) := by simpa using hcode 1 (by simp)
  have c2 : p[h + 2]? = some (natBranch 13 24 (h + 12) (h + 3)) := by simpa using hcode 2 (by simp)
  have c3 : p[h + 3]? = some (natLoad 22 27) := by simpa using hcode 3 (by simp)
  have c4 : p[h + 4]? = some (natSub 22 22 17) := by simpa using hcode 4 (by simp)
  have c5 : p[h + 5]? = some (natBranch 16 22 (h + 6) (h + 8)) := by simpa using hcode 5 (by simp)
  have c6 : p[h + 6]? = some (natSub 22 22 16) := by simpa using hcode 6 (by simp)
  have c7 : p[h + 7]? = some (jump (h + 5)) := by simpa using hcode 7 (by simp)
  have c8 : p[h + 8]? = some (natStore 27 22) := by simpa using hcode 8 (by simp)
  have c9 : p[h + 9]? = some (natAdd 24 24 11) := by simpa using hcode 9 (by simp)
  have c10 : p[h + 10]? = some (natAdd 27 27 19) := by simpa using hcode 10 (by simp)
  have c11 : p[h + 11]? = some (jump (h + 2)) := by simpa using hcode 11 (by simp)
  intro q
  induction q with
  | zero =>
    intro x M R hq h16 h22
    have hx : x < k := by
      by_contra hc; push_neg at hc
      have := Nat.div_pos hc hk; omega
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p h 5 _ rfl c5, run_zero]
    simp only [execInstr, h16, h22, show ¬ k ≤ x by omega, if_false]
    exact ⟨trivial, (Nat.mod_eq_of_lt hx).symm, fun a _ => trivial, trivial⟩
  | succ q ih =>
    intro x M R hq h16 h22
    by_cases hx : k ≤ x
    · obtain ⟨τ, hτ, r1, r22, rfr, rr⟩ := ih (x - k) (Function.update M 22 (x - k)) R
        (by rw [Nat.div_eq_sub_div hk hx] at hq; omega) (by simp [Function.update_apply, h16])
        (by simp)
      refine ⟨3 + τ, ?_, ?_⟩
      · rw [Nat.div_eq_sub_div hk hx]; omega
      rw [run_add, show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at p h 5 _ rfl c5,
        run_succ, step_at p h 6 _ (by simp [execInstr, h16, h22, hx]) c6,
        run_succ, step_at p h 7 _ (by simp [execInstr, h16, h22, hx]) c7, run_zero]
      have e : (execInstr (jump (h + 5)) (execInstr (natSub 22 22 16)
          (execInstr (natBranch 16 22 (h + 6) (h + 8)) ⟨h + 5, M, R⟩))) =
          ⟨h + 5, Function.update M 22 (x - k), R⟩ := by
        simp [execInstr, h16, h22, hx]
      rw [e]
      refine ⟨r1, ?_, fun a ha => ?_, rr⟩
      · rw [r22, Nat.mod_eq_sub_mod hx]
      · rw [rfr a ha, Function.update_of_ne ha]
    · have hxk : x < k := by omega
      refine ⟨1, by omega, ?_⟩
      rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p h 5 _ rfl c5, run_zero]
      simp only [execInstr, h16, h22, hx, if_false]
      exact ⟨trivial, (Nat.mod_eq_of_lt hxk).symm, fun a _ => trivial, trivial⟩

set_option maxHeartbeats 4000000 in
lemma modv_loop (n k LVB : ℕ) (hk : 0 < k) (hLVB : 36 ≤ LVB) :
    ∀ (r w : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = n →
      M 13 = n → M 16 = k → M 17 = n + 2 → M 24 = w → M 27 = LVB + 2 * w → M 11 = 1 → M 19 = 2 →
      (∀ j, w ≤ j → j < n → n + 2 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ 2 * n + 2) →
      ∃ τ, τ ≤ (3 * n + 9) * r + 1 ∧
        (planarRAMRun p ⟨h + 2, M, R⟩ τ).pc = h + 12 ∧
        (∀ j, w ≤ j → j < n → (planarRAMRun p ⟨h + 2, M, R⟩ τ).natMem (LVB + 2 * j) = (M (LVB + 2 * j) - (n + 2)) % k) ∧
        (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, w ≤ j → j < n → a ≠ LVB + 2 * j) →
          (planarRAMRun p ⟨h + 2, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨h + 2, M, R⟩ τ).realMem = R := by
  have c0 : p[h + 0]? = some (natConst 24 0) := by simpa using hcode 0 (by simp)
  have c1 : p[h + 1]? = some (natAdd 27 28 12) := by simpa using hcode 1 (by simp)
  have c2 : p[h + 2]? = some (natBranch 13 24 (h + 12) (h + 3)) := by simpa using hcode 2 (by simp)
  have c3 : p[h + 3]? = some (natLoad 22 27) := by simpa using hcode 3 (by simp)
  have c4 : p[h + 4]? = some (natSub 22 22 17) := by simpa using hcode 4 (by simp)
  have c5 : p[h + 5]? = some (natBranch 16 22 (h + 6) (h + 8)) := by simpa using hcode 5 (by simp)
  have c6 : p[h + 6]? = some (natSub 22 22 16) := by simpa using hcode 6 (by simp)
  have c7 : p[h + 7]? = some (jump (h + 5)) := by simpa using hcode 7 (by simp)
  have c8 : p[h + 8]? = some (natStore 27 22) := by simpa using hcode 8 (by simp)
  have c9 : p[h + 9]? = some (natAdd 24 24 11) := by simpa using hcode 9 (by simp)
  have c10 : p[h + 10]? = some (natAdd 27 27 19) := by simpa using hcode 10 (by simp)
  have c11 : p[h + 11]? = some (jump (h + 2)) := by simpa using hcode 11 (by simp)
  intro r
  induction r with
  | zero =>
    intro w M R hw h13 h16 h17 h24 h27 h11 h19 hb
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p h 2 _ rfl c2, run_zero]
    simp only [execInstr, show M 13 ≤ M 24 by omega, if_true]
    exact ⟨trivial, fun j hj1 hj2 => by omega, fun a _ _ _ _ => trivial, trivial⟩
  | succ r ih =>
    intro w M R hw h13 h16 h17 h24 h27 h11 h19 hb
    have hlt : ¬ M 13 ≤ M 24 := by omega
    obtain ⟨hb1, hb2⟩ := hb w le_rfl (by omega)
    set x := M (LVB + 2 * w) - (n + 2) with hxdef
    have hxn : x ≤ n := by omega
    -- three set-up steps to the inner loop head
    set M3 := Function.update M 22 x with hM3
    have e3 : planarRAMRun p ⟨h + 2, M, R⟩ 3 = ⟨h + 5, M3, R⟩ := by
      rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at p h 2 _ rfl c2,
        run_succ, step_at p h 3 _ (by simp [execInstr, hlt]) c3,
        run_succ, step_at p h 4 _ (by simp [execInstr, hlt]) c4, run_zero]
      simp only [execInstr, hlt, if_false]
      congr 1
      rw [hM3]; funext a; simp only [Function.update_apply]; split_ifs <;> simp_all
    obtain ⟨τm, hτm, m1, m22, mfr, mr⟩ := mod_loop p h hcode k hk (x / k) x M3 R le_rfl
      (by rw [hM3, Function.update_of_ne (by omega), h16]) (by rw [hM3, Function.update_self])
    set S1 := planarRAMRun p ⟨h + 5, M3, R⟩ τm with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at m1 m22 mfr mr
    subst m1; subst mr
    have f1 : ∀ a, a ≠ 22 → M1 a = M a := fun a ha => (mfr a ha).trans (by rw [hM3, Function.update_of_ne ha])
    have n22 : LVB + 2 * w ≠ 22 := by omega
    set M2 := Function.update (Function.update (Function.update M1 (LVB + 2 * w) (x % k)) 24 (w + 1)) 27
      (LVB + 2 * (w + 1)) with hM2
    have e4 : planarRAMRun p ⟨h + 8, M1, R1⟩ 4 = ⟨h + 2, M2, R1⟩ := by
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, run_succ, step_at p h 8 _ rfl c8,
        run_succ, step_at p h 9 _ (by simp [execInstr]) c9,
        run_succ, step_at p h 10 _ (by simp [execInstr]) c10,
        run_succ, step_at p h 11 _ (by simp [execInstr]) c11, run_zero]
      simp only [execInstr]
      congr 1
      rw [hM2]; funext a
      simp only [Function.update_apply, f1 27 (by omega), f1 24 (by omega), f1 11 (by omega),
        f1 19 (by omega), h27, h24, h11, h19, m22]
      split_ifs <;> omega
    have hM2fr : ∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → a ≠ LVB + 2 * w → M2 a = M a := by
      intro a a22 a24 a27 aL
      rw [hM2, Function.update_of_ne a27, Function.update_of_ne a24, Function.update_of_ne aL, f1 a a22]
    obtain ⟨τ2, hτ2, r1, rL, rfr, rr⟩ := ih (w + 1) M2 R1 (by omega)
      (by rw [hM2fr 13 (by omega) (by omega) (by omega) (by omega), h13])
      (by rw [hM2fr 16 (by omega) (by omega) (by omega) (by omega), h16])
      (by rw [hM2fr 17 (by omega) (by omega) (by omega) (by omega), h17])
      (by rw [hM2]; simp) (by rw [hM2]; simp)
      (by rw [hM2fr 11 (by omega) (by omega) (by omega) (by omega), h11])
      (by rw [hM2fr 19 (by omega) (by omega) (by omega) (by omega), h19])
      (fun j hj1 hj2 => by rw [hM2fr _ (by omega) (by omega) (by omega) (by omega)]; exact hb j (by omega) hj2)
    have hdiv : x / k ≤ n := (Nat.div_le_self x k).trans hxn
    refine ⟨3 + τm + 4 + τ2, by nlinarith, ?_⟩
    rw [run_add, run_add, run_add, e3, ← hS1, e4]
    refine ⟨r1, fun j hj1 hj2 => ?_, fun a a22 a24 a27 aL => ?_, rr⟩
    · rcases Nat.eq_or_lt_of_le hj1 with hj | hj
      · subst hj
        rw [rfr _ (by omega) (by omega) (by omega) (fun j' h1 _ => by omega), hM2,
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      · rw [rL j hj hj2, hM2fr _ (by omega) (by omega) (by omega) (by omega)]
    · rw [rfr a a22 a24 a27 (fun j h1 h2 => aL j (by omega) h2),
        hM2fr a a22 a24 a27 (aL w le_rfl (by omega))]

lemma mod_sweep (n k LVB : ℕ) (hk : 0 < k) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h16 : M 16 = k) (h17 : M 17 = n + 2) (h28 : M 28 = LVB) (h11 : M 11 = 1)
    (h12 : M 12 = 0) (h19 : M 19 = 2)
    (hb : ∀ j, j < n → n + 2 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ 2 * n + 2) :
    ∃ τ, τ ≤ (3 * n + 9) * n + 3 ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).pc = h + 12 ∧
      (∀ j, j < n → (planarRAMRun p ⟨h, M, R⟩ τ).natMem (LVB + 2 * j) = (M (LVB + 2 * j) - (n + 2)) % k) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨h, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).realMem = R := by
  have c0 : p[h + 0]? = some (natConst 24 0) := by simpa using hcode 0 (by simp)
  have c1 : p[h + 1]? = some (natAdd 27 28 12) := by simpa using hcode 1 (by simp)
  have e2 : planarRAMRun p ⟨h, M, R⟩ 2 = ⟨h + 2, Function.update (Function.update M 24 0) 27 LVB, R⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, run_succ, step_at p h 0 _ (by simp) c0,
      run_succ, step_at p h 1 _ (by simp [execInstr]) c1, run_zero]
    simp [execInstr, Function.update_apply, h28, h12]
  have hu : ∀ a, a ≠ 24 → a ≠ 27 → (Function.update (Function.update M 24 0) 27 LVB) a = M a :=
    fun a a24 a27 => by rw [Function.update_of_ne a27, Function.update_of_ne a24]
  obtain ⟨τ, hτ, r1, rL, rfr, rr⟩ := modv_loop p h hcode n k LVB hk hLVB n 0
    (Function.update (Function.update M 24 0) 27 LVB) R (by omega)
    (by rw [hu 13 (by omega) (by omega), h13]) (by rw [hu 16 (by omega) (by omega), h16])
    (by rw [hu 17 (by omega) (by omega), h17]) (by simp) (by simp)
    (by rw [hu 11 (by omega) (by omega), h11]) (by rw [hu 19 (by omega) (by omega), h19])
    (fun j _ hj => by rw [hu _ (by omega) (by omega)]; exact hb j hj)
  refine ⟨2 + τ, by omega, ?_⟩
  rw [run_add, e2]
  refine ⟨r1, fun j hj => ?_, fun a a22 a24 a27 aL => ?_, rr⟩
  · rw [rL j (Nat.zero_le _) hj, hu _ (by omega) (by omega)]
  · rw [rfr a a22 a24 a27 (fun j _ hj => aL j hj), hu a a24 a27]

end

end MK

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (h : ℕ)
    (hcode : CodeAt p h
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (h + 12) (h + 3),
      natLoad 22 27,
      natSub 22 22 17,
      natBranch 16 22 (h + 6) (h + 8),
      natSub 22 22 16,
      jump (h + 5),
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (h + 2)])
    (n k LVB : ℕ) (hk : 0 < k) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h16 : M 16 = k) (h17 : M 17 = n + 2) (h28 : M 28 = LVB) (h11 : M 11 = 1)
    (h12 : M 12 = 0) (h19 : M 19 = 2)
    (hb : ∀ j, j < n → n + 2 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ 2 * n + 2) :
    ∃ τ, τ ≤ (3 * n + 9) * n + 3 ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).pc = h + 12 ∧
      (∀ j, j < n → (planarRAMRun p ⟨h, M, R⟩ τ).natMem (LVB + 2 * j) = (M (LVB + 2 * j) - (n + 2)) % k) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨h, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).realMem = R :=
  MK.mod_sweep p h hcode n k LVB hk hLVB M R h13 h16 h17 h28 h11 h12 h19 hb
