-- Prove2me | solution 1 for WilliamsonShmoys.ram_baker_seg_input
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:17:47.179811+00:00
-- url     : https://prove2.me/submissions/88a28f16-15f2-4c03-9cb9-38e203ccddc5

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Theorems.Thm_WilliamsonShmoys_ram_pack_low_cells
import Theorems.Thm_WilliamsonShmoys_ram_square_fragment
import Theorems.Thm_WilliamsonShmoys_ram_spread_fragment
import Theorems.Thm_WilliamsonShmoys_ram_unpack_low_cells
import Theorems.Thm_WilliamsonShmoys_ram_real_spread_fragment

set_option autoImplicit false

namespace SG1
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


section
variable {n k : ℕ} (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ)

lemma inp0 : (planarRAMInput n k edge weight).natMem 0 = n := by simp [planarRAMInput]
lemma inp1 : (planarRAMInput n k edge weight).natMem 1 = k := by simp [planarRAMInput]
lemma inpb (a : ℕ) (ha : 2 ≤ a) : (planarRAMInput n k edge weight).natMem a ≤ 1 := by
  simp only [planarRAMInput, if_neg (show a ≠ 0 by omega), if_neg (show a ≠ 1 by omega)]
  split_ifs <;> omega
lemma inpZ (a : ℕ) (ha : 2 + n * n ≤ a) : (planarRAMInput n k edge weight).natMem a = 0 := by
  simp only [planarRAMInput, if_neg (show a ≠ 0 by omega), if_neg (show a ≠ 1 by omega)]
  have hn : ¬ (a - 2) / n < n := by
    intro h
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h
    · rw [Nat.div_lt_iff_lt_mul h0] at h; omega
  rw [dif_neg hn]
lemma inpE (v w : Fin n) : (planarRAMInput n k edge weight).natMem (2 + v.val * n + w.val) =
    if edge v w then 1 else 0 := by
  have hn : 0 < n := by have := v.isLt; omega
  have e1 : (2 + v.val * n + w.val - 2) / n = v.val := by
    rw [show 2 + v.val * n + w.val - 2 = w.val + v.val * n by omega, Nat.add_mul_div_right _ _ hn,
      Nat.div_eq_of_lt w.isLt, Nat.zero_add]
  have e2 : (2 + v.val * n + w.val - 2) % n = w.val := by
    rw [show 2 + v.val * n + w.val - 2 = w.val + v.val * n by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt w.isLt]
  simp only [planarRAMInput, if_neg (show 2 + v.val * n + w.val ≠ 0 by omega),
    if_neg (show 2 + v.val * n + w.val ≠ 1 by omega)]
  rw [dif_pos (by rw [e1]; exact v.isLt), dif_pos (by rw [e2]; exact w.isLt)]
  have h1 : (⟨(2 + v.val * n + w.val - 2) / n, by rw [e1]; exact v.isLt⟩ : Fin n) = v := Fin.ext e1
  have h2 : (⟨(2 + v.val * n + w.val - 2) % n, by rw [e2]; exact w.isLt⟩ : Fin n) = w := Fin.ext e2
  rw [h1, h2]
lemma inpR (v : Fin n) : (planarRAMInput n k edge weight).realMem v.val = weight v := by
  simp [planarRAMInput, v.isLt]
lemma inpRZ (a : ℕ) (ha : n ≤ a) : (planarRAMInput n k edge weight).realMem a = 0 := by
  simp [planarRAMInput, show ¬ a < n by omega]
end

set_option maxHeartbeats 4000000 in
lemma seg1 (p : List PlanarRAMInstruction)
    (hc1 : CodeAt p 0 [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7])
    (hc2 : CodeAt p 12 [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (12 + 7) (12 + 4), natAdd 2 2 0, natAdd 3 3 4, jump (12 + 3)])
    (hc3 : CodeAt p 19 [natConst 5 8, natConst 6 32, natBranch 2 5 (19 + 9) (19 + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (19 + 2)])
    (hc4 : CodeAt p 28 [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (28 + 7) (28 + 10), natSub 8 8 10, natAdd 9 9 11, jump (28 + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 14) (28 + 17), natSub 8 8 10, natAdd 9 9 11, jump (28 + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 21) (28 + 24), natSub 8 8 10, natAdd 9 9 11, jump (28 + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 28) (28 + 31), natSub 8 8 10, natAdd 9 9 11, jump (28 + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 35) (28 + 38), natSub 8 8 10, natAdd 9 9 11, jump (28 + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 42) (28 + 45), natSub 8 8 10, natAdd 9 9 11, jump (28 + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12])
    (hg : CodeAt p 76 [natConst 10 2, natConst 11 1, natConst 12 0])
    (hc5 : CodeAt p 79 [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (79 + 12) (79 + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (79 + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0])
    (n k : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ) :
    ∃ τ, τ ≤ 800 * k + 8 * (n + 1) * (n + 1) + 900 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).pc = 95 ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 0 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 32 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 34 = k ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 10 = 2 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 11 = 1 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 12 = 0 ∧
      (∀ v w : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0) ∧
      (∀ a, 48 + 2 * (n * n) ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem a = 0) ∧
      (∀ v : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem (32 + 2 * v.val) = weight v) ∧
      (∀ a, a % 2 = 1 → n ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem a = 0) := by
  set s0 := planarRAMInput n k edge weight with hs0
  have h0pc : s0.pc = 0 := rfl
  -- P1
  have e1 := ram_pack_low_cells p 0 s0 hc1 h0pc
  set s1 := planarRAMRun p s0 12 with hs1
  -- P2
  have h2 := ram_square_fragment p 12 hc2 s1 (by rw [e1])
  dsimp only at h2
  have s1_0 : s1.natMem 0 = n := by rw [e1]; simp only [Function.update_apply, if_neg (show (0:ℕ) ≠ 1 by omega)]; exact inp0 edge weight
  rw [s1_0] at h2
  obtain ⟨p2, c2, c3, c4, f2, r2⟩ := h2
  set s2 := planarRAMRun p s1 (4 * n + 4) with hs2
  -- P3
  have h3 := ram_spread_fragment p 19 hc3 s2 p2 c4
  dsimp only at h3
  rw [c2] at h3
  obtain ⟨p3, m3, f3, r3⟩ := h3
  set s3 := planarRAMRun p s2 (2 + 7 * (2 + n * n - 8) + 1) with hs3
  -- facts about cell 1 and low cells
  have s0b : ∀ a, 2 ≤ a → s0.natMem a ≤ 1 := fun a ha => inpb edge weight a ha
  have s3_1 : s3.natMem 1 = 64 * k + 32 * s0.natMem 2 + 16 * s0.natMem 3 + 8 * s0.natMem 4 +
      4 * s0.natMem 5 + 2 * s0.natMem 6 + s0.natMem 7 := by
    rw [f3 1 (by omega) (by omega) (by omega) (by omega) (by omega) (fun c h1 h2 => by omega),
      f2 1 (by omega) (by omega) (by omega), e1]
    simp only [Function.update_apply, eq_self_iff_true, ite_true]
    rw [inp1 edge weight]
  -- P4
  obtain ⟨τ4, hτ4, p4, u32, u34, u36, u38, u40, u42, u44, u46, f4, r4⟩ :=
    ram_unpack_low_cells p 28 hc4 s3 p3 k (s0.natMem 2) (s0.natMem 3) (s0.natMem 4) (s0.natMem 5)
      (s0.natMem 6) (s0.natMem 7) (s0b 2 (by omega)) (s0b 3 (by omega)) (s0b 4 (by omega)) (s0b 5 (by omega))
      (s0b 6 (by omega)) (s0b 7 (by omega)) s3_1
  set s4 := planarRAMRun p s3 τ4 with hs4
  obtain ⟨pc4, M4, R4⟩ := s4
  simp only at p4 u32 u34 u36 u38 u40 u42 u44 u46 f4 r4
  subst p4
  have g0 : p[76 + 0]? = some (natConst 10 2) := by simpa using hg 0 (by simp)
  have g1 : p[76 + 1]? = some (natConst 11 1) := by simpa using hg 1 (by simp)
  have g2 : p[76 + 2]? = some (natConst 12 0) := by simpa using hg 2 (by simp)
  have e3 : planarRAMRun p ⟨28 + 48, M4, R4⟩ 3 =
      ⟨79, Function.update (Function.update (Function.update M4 10 2) 11 1) 12 0, R4⟩ := by
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at' p 76 0 _ _ _ _ (by omega) g0, ex_const,
      run_succ, step_at' p 76 1 _ _ _ _ (by omega) g1, ex_const,
      run_succ, step_at' p 76 2 _ _ _ _ (by omega) g2, ex_const, run_zero]
  set M5 := Function.update (Function.update (Function.update M4 10 2) 11 1) 12 0 with hM5
  have m5 : ∀ a, a ≠ 10 → a ≠ 11 → a ≠ 12 → M5 a = M4 a := fun a a10 a11 a12 => by
    rw [hM5, Function.update_of_ne a12, Function.update_of_ne a11, Function.update_of_ne a10]
  have h5 := ram_real_spread_fragment p 79 hc5 ⟨79, M5, R4⟩ rfl (by rw [hM5]; simp) (by rw [hM5]; simp)
  dsimp only at h5
  have M5_0 : M5 0 = n := by
    rw [m5 0 (by omega) (by omega) (by omega), f4 0 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      f3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (fun c h1 h2 => by omega),
      f2 0 (by omega) (by omega) (by omega), s1_0]
  rw [M5_0] at h5
  obtain ⟨p5, w5, r50, r5n, rf5, nf5⟩ := h5
  set S := planarRAMRun p ⟨79, M5, R4⟩ (5 + (7 * (n - 1) + 1) + 4) with hS
  -- relocation of the input
  have s1n : ∀ a, a ≠ 1 → s1.natMem a = s0.natMem a := fun a ha => by
    rw [e1]; simp only [Function.update_apply, if_neg ha]
  have reloc : ∀ c, 2 ≤ c → c < 2 + n * n → M4 (2 * c + 32) = s0.natMem c := by
    intro c hc1 hc2
    rcases (show c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ 8 ≤ c by omega) with h | h | h | h | h | h | h
    · subst h; exact u36
    · subst h; exact u38
    · subst h; exact u40
    · subst h; exact u42
    · subst h; exact u44
    · subst h; exact u46
    · rw [f4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), m3 c h hc2, f2 c (by omega) (by omega) (by omega),
        s1n c (by omega)]
  have hm1 : (n - 1) + 1 ≤ n + 1 := by omega
  have hτ4' : τ4 ≤ 768 * k + 786 := by
    have := s0b 2 (by omega); have := s0b 3 (by omega); have := s0b 4 (by omega)
    have := s0b 5 (by omega); have := s0b 6 (by omega); have := s0b 7 (by omega)
    rw [s3_1] at hτ4; omega
  have hτ3 : 2 + 7 * (2 + n * n - 8) + 1 ≤ 7 * (n * n) + 3 := by omega
  refine ⟨12 + (4 * n + 4) + (2 + 7 * (2 + n * n - 8) + 1) + τ4 + 3 + (5 + (7 * (n - 1) + 1) + 4), ?_, ?_⟩
  · have : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    have e8 : 8 * (n + 1) * (n + 1) = 8 * ((n + 1) * (n + 1)) := by ring
    omega
  rw [run_add p s0 (12 + (4 * n + 4) + (2 + 7 * (2 + n * n - 8) + 1) + τ4 + 3) (5 + (7 * (n - 1) + 1) + 4), run_add p s0 (12 + (4 * n + 4) + (2 + 7 * (2 + n * n - 8) + 1) + τ4) 3,
    run_add p s0 (12 + (4 * n + 4) + (2 + 7 * (2 + n * n - 8) + 1)) τ4, run_add p s0 (12 + (4 * n + 4)) (2 + 7 * (2 + n * n - 8) + 1), run_add p s0 12 (4 * n + 4),
    ← hs1, ← hs2, ← hs3, ← hs4, e3, ← hS]
  refine ⟨p5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nf5 0 (by omega) (by omega) (by omega) (by omega), M5_0]
  · rw [nf5 32 (by omega) (by omega) (by omega) (by omega), m5 32 (by omega) (by omega) (by omega), u32,
      f3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (fun c h1 h2 => by omega),
      f2 0 (by omega) (by omega) (by omega), s1_0]
  · rw [nf5 34 (by omega) (by omega) (by omega) (by omega), m5 34 (by omega) (by omega) (by omega), u34]
  · rw [nf5 10 (by omega) (by omega) (by omega) (by omega), hM5]; simp
  · rw [nf5 11 (by omega) (by omega) (by omega) (by omega), hM5]; simp
  · rw [nf5 12 (by omega) (by omega) (by omega) (by omega), hM5]; simp
  · intro v w
    have hv := v.isLt; have hw := w.isLt
    have hlt : 2 + v.val * n + w.val < 2 + n * n := by
      have := Nat.mul_le_mul_right n (show v.val + 1 ≤ n by omega)
      have e : (v.val + 1) * n = v.val * n + n := by ring
      omega
    have ea : 36 + 2 * v.val * n + 2 * w.val = 2 * (2 + v.val * n + w.val) + 32 := by ring
    rw [nf5 _ (by omega) (by omega) (by omega) (by omega), m5 _ (by omega) (by omega) (by omega), ea,
      reloc _ (by omega) hlt, inpE]
  · intro a ha
    rw [nf5 a (by omega) (by omega) (by omega) (by omega), m5 a (by omega) (by omega) (by omega),
      f4 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      f3 a (by omega) (by omega) (by omega) (by omega) (by omega) (fun c h1 h2 => by omega),
      f2 a (by omega) (by omega) (by omega), s1n a (by omega), inpZ edge weight a (by omega)]
  · intro v
    have hr : ∀ a, R4 a = s0.realMem a := fun a => by rw [r4, r3, r2, e1]
    rw [show 32 + 2 * v.val = 2 * v.val + 32 by ring, w5 v.val v.isLt]
    exact (hr _).trans (inpR edge weight v)
  · intro a ha hna
    have hr : ∀ a, R4 a = s0.realMem a := fun a => by rw [r4, r3, r2, e1]
    by_cases h2n : a = 2 * n + 1
    · subst h2n; exact r5n
    · rw [rf5 a (by omega) (by omega) h2n (fun c _ => by omega)]
      exact (hr _).trans (inpRZ edge weight a hna)

end SG1

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction)
    (hc1 : CodeAt p 0 [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7])
    (hc2 : CodeAt p 12 [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (12 + 7) (12 + 4), natAdd 2 2 0, natAdd 3 3 4, jump (12 + 3)])
    (hc3 : CodeAt p 19 [natConst 5 8, natConst 6 32, natBranch 2 5 (19 + 9) (19 + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (19 + 2)])
    (hc4 : CodeAt p 28 [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (28 + 7) (28 + 10), natSub 8 8 10, natAdd 9 9 11, jump (28 + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 14) (28 + 17), natSub 8 8 10, natAdd 9 9 11, jump (28 + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 21) (28 + 24), natSub 8 8 10, natAdd 9 9 11, jump (28 + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 28) (28 + 31), natSub 8 8 10, natAdd 9 9 11, jump (28 + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 35) (28 + 38), natSub 8 8 10, natAdd 9 9 11, jump (28 + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 42) (28 + 45), natSub 8 8 10, natAdd 9 9 11, jump (28 + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12])
    (hg : CodeAt p 76 [natConst 10 2, natConst 11 1, natConst 12 0])
    (hc5 : CodeAt p 79 [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (79 + 12) (79 + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (79 + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0])
    (n k : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ) :
    ∃ τ, τ ≤ 800 * k + 8 * (n + 1) * (n + 1) + 900 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).pc = 95 ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 0 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 32 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 34 = k ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 10 = 2 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 11 = 1 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 12 = 0 ∧
      (∀ v w : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0) ∧
      (∀ a, 48 + 2 * (n * n) ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem a = 0) ∧
      (∀ v : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem (32 + 2 * v.val) = weight v) ∧
      (∀ a, a % 2 = 1 → n ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem a = 0) :=
  SG1.seg1 p hc1 hc2 hc3 hc4 hg hc5 n k edge weight
