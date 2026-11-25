-- Prove2me | solution 2 for WilliamsonShmoys.ram_baker_seg_levels
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T13:27:47.794807+00:00
-- url     : https://prove2.me/submissions/a4e51d96-4606-409e-bbe0-e8bcd80a653b

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Theorems.Thm_WilliamsonShmoys_ram_bfs_baker_levels
import Theorems.Thm_WilliamsonShmoys_ram_level_mod_sweep
import Theorems.Thm_WilliamsonShmoys_ram_zero_odd_cells

set_option autoImplicit false

namespace SG3A
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

lemma bakerRoot_spec {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.Reachable (bakerRoot G v) v ∧ bakerRoot G v ≤ v ∧ ∀ u, G.Reachable u v → bakerRoot G v ≤ u := by
  classical
  have hmem := Finset.min'_mem (Finset.univ.filter (fun u => G.Reachable u v))
    ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl (G := G) v⟩⟩
  have hdef : bakerRoot G v = (Finset.univ.filter (fun u => G.Reachable u v)).min'
      ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl (G := G) v⟩⟩ := by
    unfold bakerRoot; congr
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef]; exact (Finset.mem_filter.1 hmem).2
  · rw [hdef]; exact Finset.min'_le (Finset.univ.filter (fun u => G.Reachable u v)) _ (Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl (G := G) v⟩)
  · intro u hu; rw [hdef]; exact Finset.min'_le (Finset.univ.filter (fun u => G.Reachable u v)) _ (Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩)

lemma bakerRoot_eq_of_reach {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) (h : G.Reachable a b) :
    bakerRoot G a = bakerRoot G b := by
  obtain ⟨ra, -, ma⟩ := bakerRoot_spec G a
  obtain ⟨rb, -, mb⟩ := bakerRoot_spec G b
  exact le_antisymm (ma _ (rb.trans h.symm)) (mb _ (ra.trans h))

/-- If `u` is its own root, the vertices with root `u` are exactly those reachable from `u`. -/
lemma root_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u j : Fin n) (hu : bakerRoot G u = u) :
    bakerRoot G j = u ↔ G.Reachable u j := by
  constructor
  · intro h; rw [← h]; exact (bakerRoot_spec G j).1
  · intro h; rw [← bakerRoot_eq_of_reach G u j h, hu]


lemma dist_lt_card {n : ℕ} (G : SimpleGraph (Fin n)) (r j : Fin n) (h : G.Reachable r j) :
    G.dist r j < n := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist
  have := (q.isPath_of_length_eq_dist hq).length_lt
  simpa [hq] using this

lemma level_lt {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) : bakerLevel G j < n :=
  dist_lt_card G _ j (bakerRoot_spec G j).1

set_option maxHeartbeats 8000000 in
lemma seg3a (p : List PlanarRAMInstruction)
    (hc6 : CodeAt p 123 [natConst 29 0, natAdd 30 28 12, natBranch 13 29 (123 + 58) (123 + 3), natLoad 22 30, natBranch 22 12 (123 + 5) (123 + 55), natStore 30 11, natConst 15 1, natConst 14 2, natConst 23 0, natConst 24 0, natConst 25 36, natConst 26 36, natAdd 27 28 12, natBranch 13 24 (123 + 8 + 5 + 27) (123 + 8 + 5 + 1), natLoad 22 27, natBranch 22 15 (123 + 8 + 5 + 3) (123 + 8 + 5 + 22), natBranch 15 22 (123 + 8 + 5 + 4) (123 + 8 + 5 + 22), natConst 16 0, natAdd 17 25 12, natAdd 18 26 12, natAdd 21 28 12, natBranch 13 16 (123 + 8 + 5 + 8 + 14) (123 + 8 + 5 + 8 + 1), natLoad 22 17, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 3), natLoad 22 18, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 9), natLoad 22 21, natBranch 22 12 (123 + 8 + 5 + 8 + 7) (123 + 8 + 5 + 8 + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump (123 + 8 + 5 + 8), natAdd 24 24 11, natAdd 25 25 20, natAdd 26 26 19, natAdd 27 27 19, jump (123 + 8 + 5), natBranch 11 23 (123 + 8 + 33) (123 + 8 + 36), natAdd 15 15 11, natAdd 14 14 11, jump (123 + 8), natConst 24 0, natAdd 27 28 12, natBranch 13 24 (123 + 44 + 11) (123 + 44 + 3), natLoad 22 27, natBranch 22 12 (123 + 44 + 8) (123 + 44 + 5), natBranch 22 31 (123 + 44 + 6) (123 + 44 + 8), natAdd 22 22 31, natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (123 + 44 + 2), natAdd 29 29 11, natAdd 30 30 19, jump (123 + 2)])
    (hg1 : CodeAt p 181 [natAdd 16 34 12, natAdd 17 13 10])
    (hc7 : CodeAt p 183 [natConst 24 0, natAdd 27 28 12, natBranch 13 24 (183 + 12) (183 + 3), natLoad 22 27, natSub 22 22 17, natBranch 16 22 (183 + 6) (183 + 8), natSub 22 22 16, jump (183 + 5), natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (183 + 2)])
    (hg2 : CodeAt p 195 [natAdd 2 1 1, natConst 5 97, natAdd 2 2 5])
    (hc8 : CodeAt p 198 [natConst 0 1, natConst 4 2, natConst 6 0, realZero 0, natBranch 2 0 (198 + 9) (198 + 5), natStore 0 6, realStore 0 0, natAdd 0 0 4, jump (198 + 4)])
    (n k : ℕ) (hk : 0 < k) (edge : Fin n → Fin n → Bool) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) (h13 : M 13 = n) (h19 : M 19 = 2)
    (h20 : M 20 = 2 * n) (h31 : M 31 = n + 1) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h1 : M 1 = n * n)
    (h32 : M 32 = n) (h34 : M 34 = k)
    (hE : ∀ v w : Fin n, v ≠ w → M (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0)
    (hD : ∀ v, v < n → M (36 + v * (2 * n + 2)) = 0)
    (hZ : ∀ a, 48 + 2 * (n * n) ≤ a → M a = 0)
    (hRo : ∀ a, a % 2 = 1 → n ≤ a → R a = 0) :
    ∃ τ, τ ≤ 40 * (n + 1) * (n + 1) + 260 ∧ (planarRAMRun p ⟨123, M, R⟩ τ).pc = 207 ∧
      (planarRAMRun p ⟨123, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ j : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem ((16 * (n * n) + 16 * n + 48) + 2 * j.val) =
        bakerLevel (SimpleGraph.fromRel (fun u v => edge u v = true)) j % k) ∧
      (∀ v w : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem (36 + 2 * v.val * n + 2 * w.val) = M (36 + 2 * v.val * n + 2 * w.val)) ∧
      (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).natMem a = 0) ∧ (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = 0) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = R a) := by
  set G := SimpleGraph.fromRel (fun u v : Fin n => edge u v = true) with hG
  set LVB := (16 * (n * n) + 16 * n + 48) with hLVB
  have hL36 : 36 + 2 * n * n ≤ LVB := by rw [hLVB]; nlinarith
  have hadj : ∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨
      1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j := by
    intro v j
    rw [hG, SimpleGraph.fromRel_adj]
    by_cases hvj : v = j
    · subst hvj
      have e1 : 36 + 2 * (v : ℕ) * n + 2 * (v : ℕ) = 36 + v.val * (2 * n + 2) := by ring
      have e2 : 36 + 2 * (v : ℕ) + (v : ℕ) * (2 * n) = 36 + v.val * (2 * n + 2) := by ring
      rw [e1, e2, hD v.val v.isLt]
      simp
    · have e2 : 36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n) = 36 + 2 * j.val * n + 2 * v.val := by ring
      rw [e2, hE v j hvj, hE j v (Ne.symm hvj)]
      constructor
      · rintro (h | h)
        · exact ⟨hvj, Or.inl (by by_contra hc; simp [hc] at h)⟩
        · exact ⟨hvj, Or.inr (by by_contra hc; simp [hc] at h)⟩
      · rintro ⟨-, h | h⟩
        · left; simp [h]
        · right; simp [h]
  have hzero : ∀ j, j < n → M (LVB + 2 * j) = 0 := fun j _ => hZ _ (by rw [hLVB]; nlinarith)
  -- P6
  obtain ⟨τ6, hτ6, q1, qL, qfr, qlo, q19, q20, q28, qr⟩ :=
    ram_bfs_baker_levels p 123 hc6 n LVB hL36 G M R h13 h20 h28 h11 h12 h19 h31 hadj hzero
  set S6 := planarRAMRun p ⟨123, M, R⟩ τ6 with hS6
  obtain ⟨pc6, M6, R6⟩ := S6
  simp only at q1 qL qfr qlo q19 q20 q28 qr
  subst R6
  have e6 : pc6 = 181 := by omega
  subst e6
  have nl : ∀ a, 30 < a → a < LVB → M6 a = M a := fun a h1 h2 => qfr a h1 (fun j _ => by omega)
  -- G1
  have g10 : p[181 + 0]? = some (natAdd 16 34 12) := by simpa using hg1 0 (by simp)
  have g11 : p[181 + 1]? = some (natAdd 17 13 10) := by simpa using hg1 1 (by simp)
  have m34 : M6 34 = k := by rw [nl 34 (by omega) (by rw [hLVB]; omega), h34]
  have m12 : M6 12 = 0 := by rw [qlo 12 (by omega), h12]
  have m13 : M6 13 = n := by rw [qlo 13 (by omega), h13]
  have m10 : M6 10 = 2 := by rw [qlo 10 (by omega), h10]
  have eg1 : planarRAMRun p ⟨181, M6, R⟩ 2 = ⟨183, Function.update (Function.update M6 16 k) 17 (n + 2), R⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, run_succ, step_at' p 181 0 _ _ _ _ (by omega) g10,
      ex_add _ _ _ _ k _ _ (by rw [m34, m12, Nat.add_zero]), run_succ, step_at' p 181 1 _ _ _ _ (by omega) g11,
      ex_add _ _ _ _ (n + 2) _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, m13, m10]), run_zero]
  set M7 := Function.update (Function.update M6 16 k) 17 (n + 2) with hM7
  have k7 : ∀ a, a ≠ 16 → a ≠ 17 → M7 a = M6 a := fun a a16 a17 => by
    rw [hM7, Function.update_of_ne a17, Function.update_of_ne a16]
  -- P7a
  have hb : ∀ j, j < n → n + 2 ≤ M7 (LVB + 2 * j) ∧ M7 (LVB + 2 * j) ≤ 2 * n + 2 := by
    intro j hj
    rw [k7 _ (by rw [hLVB]; omega) (by rw [hLVB]; omega), qL ⟨j, hj⟩]
    have := level_lt G ⟨j, hj⟩
    omega
  obtain ⟨τ7, hτ7, w1, wL, wfr, wr⟩ := ram_level_mod_sweep p 183 hc7 n k LVB hk (by rw [hLVB]; omega) M7 R
    (by rw [k7 13 (by omega) (by omega), m13]) (by rw [hM7]; simp) (by rw [hM7]; simp)
    (by rw [k7 28 (by omega) (by omega), q28]) (by rw [k7 11 (by omega) (by omega), qlo 11 (by omega), h11])
    (by rw [k7 12 (by omega) (by omega), m12]) (by rw [k7 19 (by omega) (by omega), q19]) hb
  set S7 := planarRAMRun p ⟨183, M7, R⟩ τ7 with hS7
  obtain ⟨pc7, M8, R7⟩ := S7
  simp only at w1 wL wfr wr
  subst R7
  have e7 : pc7 = 195 := by omega
  subst e7
  -- G2
  have g20 : p[195 + 0]? = some (natAdd 2 1 1) := by simpa using hg2 0 (by simp)
  have g21 : p[195 + 1]? = some (natConst 5 97) := by simpa using hg2 1 (by simp)
  have g22 : p[195 + 2]? = some (natAdd 2 2 5) := by simpa using hg2 2 (by simp)
  have m1 : M8 1 = n * n := by
    rw [wfr 1 (by omega) (by omega) (by omega) (fun j _ => by rw [hLVB]; omega), k7 1 (by omega) (by omega),
      qlo 1 (by omega), h1]
  have eg2 : planarRAMRun p ⟨195, M8, R⟩ 3 =
      ⟨198, Function.update (Function.update (Function.update M8 2 (n * n + n * n)) 5 97) 2 (2 * (n * n + 48) + 1), R⟩ := by
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, run_succ, step_at' p 195 0 _ _ _ _ (by omega) g20,
      ex_add _ _ _ _ (n * n + n * n) _ _ (by rw [m1]), run_succ, step_at' p 195 1 _ _ _ _ (by omega) g21, ex_const,
      run_succ, step_at' p 195 2 _ _ _ _ (by omega) g22,
      ex_add _ _ _ _ (2 * (n * n + 48) + 1) _ _ (by simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]; ring),
      run_zero]
  set M9 := Function.update (Function.update (Function.update M8 2 (n * n + n * n)) 5 97) 2 (2 * (n * n + 48) + 1) with hM9
  have k9 : ∀ a, a ≠ 2 → a ≠ 5 → M9 a = M8 a := fun a a2 a5 => by
    rw [hM9, Function.update_of_ne a2, Function.update_of_ne a5, Function.update_of_ne a2]
  -- P8
  obtain ⟨τ8, hτ8, z1, zz, zfr, zRfr⟩ := ram_zero_odd_cells p 198 hc8 (n * n + 48) M9 R (by rw [hM9]; simp)
  set S8 := planarRAMRun p ⟨198, M9, R⟩ τ8 with hS8
  obtain ⟨pc8, M10, R10⟩ := S8
  simp only at z1 zz zfr zRfr
  subst z1
  have ev : ∀ a, a % 2 = 0 → a ≠ 0 → a ≠ 4 → a ≠ 6 → M10 a = M9 a := fun a he a0 a4 a6 =>
    zfr a a0 a4 a6 (fun i _ => by omega)
  have chainE : ∀ a, a % 2 = 0 → 30 < a → a < LVB → M10 a = M a := fun a he h30 hL => by
    rw [ev a he (by omega) (by omega) (by omega), k9 a (by omega) (by omega),
      wfr a (by omega) (by omega) (by omega) (fun j _ => by omega), k7 a (by omega) (by omega), nl a h30 hL]
  refine ⟨τ6 + 2 + τ7 + 3 + τ8, ?_, ?_⟩
  · have : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    have e40 : 40 * (n + 1) * (n + 1) = 40 * ((n + 1) * (n + 1)) := by ring
    have e1 : (3 * n + 9) * n = 3 * (n * n) + 9 * n := by ring
    have e2 : 32 * n * n = 32 * (n * n) := by ring
    omega
  rw [run_add, run_add, run_add, run_add, ← hS6, eg1, ← hS7, eg2, ← hS8]
  refine ⟨rfl, ?_, ?_, ?_, fun j => ?_, fun v w => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha a0 => ?_⟩
  · exact (chainE 32 (by omega) (by omega) (by rw [hLVB]; omega)).trans h32
  · exact (chainE 34 (by omega) (by omega) (by rw [hLVB]; omega)).trans h34
  · change M10 28 = LVB
    rw [ev 28 (by omega) (by omega) (by omega) (by omega), k9 28 (by omega) (by omega),
      wfr 28 (by omega) (by omega) (by omega) (fun j _ => by rw [hLVB]; omega), k7 28 (by omega) (by omega), q28]
  · change M10 (LVB + 2 * j.val) = _
    rw [ev _ (by rw [hLVB]; omega) (by rw [hLVB]; omega) (by rw [hLVB]; omega) (by rw [hLVB]; omega),
      k9 _ (by rw [hLVB]; omega) (by rw [hLVB]; omega), wL j.val j.isLt,
      k7 _ (by rw [hLVB]; omega) (by rw [hLVB]; omega), qL j]
    congr 1; omega
  · change M10 _ = _
    have hv := v.isLt; have hw := w.isLt
    have hlt : 2 * v.val * n + 2 * w.val < 2 * (n * n) := by
      have := Nat.mul_le_mul_right n (show v.val + 1 ≤ n by omega)
      have e : (v.val + 1) * n = v.val * n + n := by ring
      have e2 : 2 * v.val * n = 2 * (v.val * n) := by ring
      omega
    have e2 : 2 * v.val * n = 2 * (v.val * n) := by ring
    exact chainE _ (by omega) (by omega) (by rw [hLVB]; nlinarith)
  · change M10 a = 0
    by_cases hs : a < 2 * (n * n + 48) + 1
    · obtain ⟨i, rfl⟩ : ∃ i, a = 2 * i + 1 := ⟨a / 2, by omega⟩
      exact (zz i (by omega)).1
    · rw [zfr a (by omega) (by omega) (by omega) (fun i hi => by omega), k9 a (by omega) (by omega),
        wfr a (by omega) (by omega) (by omega) (fun j _ => by omega), k7 a (by omega) (by omega),
        qfr a (by omega) (fun j _ => by omega), hZ a (by omega)]
  · change R10 a = 0
    by_cases hs : a < 2 * (n * n + 48) + 1
    · obtain ⟨i, rfl⟩ : ∃ i, a = 2 * i + 1 := ⟨a / 2, by omega⟩
      exact (zz i (by omega)).2
    · rw [zRfr a (by omega) (fun i hi => by omega), hRo a ha (by nlinarith)]
  · change R10 a = R a
    exact zRfr a a0 (fun i _ => by omega)

end SG3A

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction)
    (hc6 : CodeAt p 123 [natConst 29 0, natAdd 30 28 12, natBranch 13 29 (123 + 58) (123 + 3), natLoad 22 30, natBranch 22 12 (123 + 5) (123 + 55), natStore 30 11, natConst 15 1, natConst 14 2, natConst 23 0, natConst 24 0, natConst 25 36, natConst 26 36, natAdd 27 28 12, natBranch 13 24 (123 + 8 + 5 + 27) (123 + 8 + 5 + 1), natLoad 22 27, natBranch 22 15 (123 + 8 + 5 + 3) (123 + 8 + 5 + 22), natBranch 15 22 (123 + 8 + 5 + 4) (123 + 8 + 5 + 22), natConst 16 0, natAdd 17 25 12, natAdd 18 26 12, natAdd 21 28 12, natBranch 13 16 (123 + 8 + 5 + 8 + 14) (123 + 8 + 5 + 8 + 1), natLoad 22 17, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 3), natLoad 22 18, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 9), natLoad 22 21, natBranch 22 12 (123 + 8 + 5 + 8 + 7) (123 + 8 + 5 + 8 + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump (123 + 8 + 5 + 8), natAdd 24 24 11, natAdd 25 25 20, natAdd 26 26 19, natAdd 27 27 19, jump (123 + 8 + 5), natBranch 11 23 (123 + 8 + 33) (123 + 8 + 36), natAdd 15 15 11, natAdd 14 14 11, jump (123 + 8), natConst 24 0, natAdd 27 28 12, natBranch 13 24 (123 + 44 + 11) (123 + 44 + 3), natLoad 22 27, natBranch 22 12 (123 + 44 + 8) (123 + 44 + 5), natBranch 22 31 (123 + 44 + 6) (123 + 44 + 8), natAdd 22 22 31, natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (123 + 44 + 2), natAdd 29 29 11, natAdd 30 30 19, jump (123 + 2)])
    (hg1 : CodeAt p 181 [natAdd 16 34 12, natAdd 17 13 10])
    (hc7 : CodeAt p 183 [natConst 24 0, natAdd 27 28 12, natBranch 13 24 (183 + 12) (183 + 3), natLoad 22 27, natSub 22 22 17, natBranch 16 22 (183 + 6) (183 + 8), natSub 22 22 16, jump (183 + 5), natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (183 + 2)])
    (hg2 : CodeAt p 195 [natAdd 2 1 1, natConst 5 97, natAdd 2 2 5])
    (hc8 : CodeAt p 198 [natConst 0 1, natConst 4 2, natConst 6 0, realZero 0, natBranch 2 0 (198 + 9) (198 + 5), natStore 0 6, realStore 0 0, natAdd 0 0 4, jump (198 + 4)])
    (n k : ℕ) (hk : 0 < k) (edge : Fin n → Fin n → Bool) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) (h13 : M 13 = n) (h19 : M 19 = 2)
    (h20 : M 20 = 2 * n) (h31 : M 31 = n + 1) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h1 : M 1 = n * n)
    (h32 : M 32 = n) (h34 : M 34 = k)
    (hE : ∀ v w : Fin n, v ≠ w → M (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0)
    (hD : ∀ v, v < n → M (36 + v * (2 * n + 2)) = 0)
    (hZ : ∀ a, 48 + 2 * (n * n) ≤ a → M a = 0)
    (hRo : ∀ a, a % 2 = 1 → n ≤ a → R a = 0) :
    ∃ τ, τ ≤ 40 * (n + 1) * (n + 1) + 260 ∧ (planarRAMRun p ⟨123, M, R⟩ τ).pc = 207 ∧
      (planarRAMRun p ⟨123, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ j : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem ((16 * (n * n) + 16 * n + 48) + 2 * j.val) =
        bakerLevel (SimpleGraph.fromRel (fun u v => edge u v = true)) j % k) ∧
      (∀ v w : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem (36 + 2 * v.val * n + 2 * w.val) = M (36 + 2 * v.val * n + 2 * w.val)) ∧
      (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).natMem a = 0) ∧ (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = 0) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = R a) :=
  SG3A.seg3a p hc6 hg1 hc7 hg2 hc8 n k hk edge M R h0 h10 h11 h12 h13 h19 h20 h31 h28 h1 h32 h34 hE hD hZ hRo
