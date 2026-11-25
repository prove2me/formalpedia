-- Prove2me | solution 1 for WilliamsonShmoys.ram_bfs_baker_levels
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T02:51:52.369144+00:00
-- url     : https://prove2.me/submissions/c7b5816b-7a62-4487-954f-38652c86c7c5

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Theorems.Thm_WilliamsonShmoys_ram_bfs_layer_loop
import Theorems.Thm_WilliamsonShmoys_ram_bfs_finalize_sweep

set_option autoImplicit false

namespace RL
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

lemma edge_lt1 (n v j : ℕ) (hv : v < n) (hj : j < n) : 2 * v * n + 2 * j < 2 * n * n := by
  have h1 := Nat.mul_le_mul_right n (show v + 1 ≤ n by omega)
  have h2 : (v + 1) * n = v * n + n := by ring
  have h3 : 2 * v * n = 2 * (v * n) := by ring
  rw [h3, Nat.mul_assoc]; omega

lemma edge_lt2 (n v j : ℕ) (hv : v < n) (hj : j < n) : 2 * v + j * (2 * n) < 2 * n * n := by
  have h1 := Nat.mul_le_mul_right (2 * n) (show j + 1 ≤ n by omega)
  have h2 : (j + 1) * (2 * n) = j * (2 * n) + 2 * n := by ring
  have h3 : n * (2 * n) = 2 * n * n := by ring
  omega

lemma card_split {n : ℕ} (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (h : ∀ j, P j ↔ Q j ∨ R j) (hd : ∀ j, ¬ (Q j ∧ R j)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card + (Finset.univ.filter R).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have := h j; have := hd j
  by_cases hq : Q j <;> by_cases hr : R j <;> simp_all

lemma loop_arith (n c c2 r τ1 τ2 : ℕ) (h1 : τ1 ≤ (23 * n + 24) * c + 9 * n + 12)
    (h2 : τ2 ≤ (23 * n + 24) * c2 + (9 * n + 12) * r + 1) :
    τ1 + τ2 ≤ (23 * n + 24) * (c + c2) + (9 * n + 12) * (r + 1) + 1 := by nlinarith

section
variable (p : List PlanarRAMInstruction) (e : ℕ)
  (hcode : CodeAt p e
    [natConst 29 0,
      natAdd 30 28 12,
      natBranch 13 29 (e + 58) (e + 3),
      natLoad 22 30,
      natBranch 22 12 (e + 5) (e + 55),
      natStore 30 11,
      natConst 15 1,
      natConst 14 2,
      natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (e + 8 + 5 + 27) (e + 8 + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (e + 8 + 5 + 3) (e + 8 + 5 + 22),
      natBranch 15 22 (e + 8 + 5 + 4) (e + 8 + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (e + 8 + 5 + 8 + 14) (e + 8 + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (e + 8 + 5 + 8 + 7) (e + 8 + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (e + 8 + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (e + 8 + 5),
      natBranch 11 23 (e + 8 + 33) (e + 8 + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump (e + 8),
      natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (e + 44 + 11) (e + 44 + 3),
      natLoad 22 27,
      natBranch 22 12 (e + 44 + 8) (e + 44 + 5),
      natBranch 22 31 (e + 44 + 6) (e + 44 + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (e + 44 + 2),
      natAdd 29 29 11,
      natAdd 30 30 19,
      jump (e + 2)])
include hcode

lemma lay_code : CodeAt p (e + 8)
    [natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (e + 8 + 5 + 27) (e + 8 + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (e + 8 + 5 + 3) (e + 8 + 5 + 22),
      natBranch 15 22 (e + 8 + 5 + 4) (e + 8 + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (e + 8 + 5 + 8 + 14) (e + 8 + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (e + 8 + 5 + 8 + 7) (e + 8 + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (e + 8 + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (e + 8 + 5),
      natBranch 11 23 (e + 8 + 33) (e + 8 + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump (e + 8)] := by
  apply codeAt_sub p e 8 _ _ hcode
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

lemma fin_code : CodeAt p (e + 44)
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (e + 44 + 11) (e + 44 + 3),
      natLoad 22 27,
      natBranch 22 12 (e + 44 + 8) (e + 44 + 5),
      natBranch 22 31 (e + 44 + 6) (e + 44 + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (e + 44 + 2)] := by
  apply codeAt_sub p e 44 _ _ hcode
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

open Classical in
set_option maxHeartbeats 8000000 in
lemma root_iter (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n))
    (u : ℕ) (hu : u < n) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0)
    (h19 : M 19 = 2) (h29 : M 29 = u) (h30 : M 30 = LVB + 2 * u) (h31 : M 31 = n + 1)
    (hadj : ∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j)
    (hinv : ∀ j : Fin n, M (LVB + 2 * (j : ℕ)) = if ((bakerRoot G j : Fin n) : ℕ) < u then n + 2 + bakerLevel G j else 0) :
    ∃ τ, τ ≤ (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => ((bakerRoot G j : Fin n) : ℕ) = u)).card + 9 * n + 12 ∧
      (planarRAMRun p ⟨e + 2, M, R⟩ τ).pc = e + 2 ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 29 = u + 1 ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 30 = LVB + 2 * (u + 1) ∧
      (∀ j : Fin n, (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) =
        if ((bakerRoot G j : Fin n) : ℕ) < u + 1 then n + 2 + bakerLevel G j else 0) ∧
      (∀ a, 30 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 13 → (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 28 = LVB ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).realMem = R := by
  have c2 : p[e + 2]? = some (natBranch 13 29 (e + 58) (e + 3)) := by simpa using hcode 2 (by simp)
  have c3 : p[e + 3]? = some (natLoad 22 30) := by simpa using hcode 3 (by simp)
  have c4 : p[e + 4]? = some (natBranch 22 12 (e + 5) (e + 55)) := by simpa using hcode 4 (by simp)
  have c5 : p[e + 5]? = some (natStore 30 11) := by simpa using hcode 5 (by simp)
  have c6 : p[e + 6]? = some (natConst 15 1) := by simpa using hcode 6 (by simp)
  have c7 : p[e + 7]? = some (natConst 14 2) := by simpa using hcode 7 (by simp)
  have c55 : p[e + 55]? = some (natAdd 29 29 11) := by simpa using hcode 55 (by simp)
  have c56 : p[e + 56]? = some (natAdd 30 30 19) := by simpa using hcode 56 (by simp)
  have c57 : p[e + 57]? = some (jump (e + 2)) := by simpa using hcode 57 (by simp)
  have hLV : 36 ≤ LVB := by omega
  have hlt : ¬ M 13 ≤ M 29 := by omega
  have hwn : u < n := hu
  obtain ⟨U, hU⟩ : ∃ U : Fin n, (U : ℕ) = u := ⟨⟨u, hu⟩, rfl⟩
  have hbr := bakerRoot_spec G U
  have hinvU := hinv U
  rw [hU] at hinvU
  have hJU : ∀ j : Fin n, (j : ℕ) = u → j = U := fun j h => Fin.ext (by rw [h, hU])
  by_cases hz : M (LVB + 2 * u) ≤ 0
  · -- u is a new root
    have hz0 : M (LVB + 2 * u) = 0 := by omega
    have hbU : bakerRoot G U = U := by
      rw [hz0] at hinvU
      have h2 : ¬ ((bakerRoot G U : Fin n) : ℕ) < u := by
        intro hh; rw [if_pos hh] at hinvU; omega
      apply Fin.ext
      have := hbr.2.1
      rw [Fin.le_def, hU] at this
      rw [hU]
      omega
    set M6 := Function.update (Function.update (Function.update (Function.update M 22 0) (LVB + 2 * u) 1) 15 1) 14 2
      with hM6def
    have e6 : planarRAMRun p ⟨e + 2, M, R⟩ 6 = ⟨e + 8, M6, R⟩ := by
      rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
      rw [run_succ, step_at p e 2 _ rfl c2]
      rw [run_succ, step_at p e 3 _ (by simp [execInstr, hlt]) c3]
      rw [run_succ, step_at p e 4 _ (by simp [execInstr, hlt]) c4]
      rw [run_succ, step_at p e 5 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz0, h12]) c5]
      rw [run_succ, step_at p e 6 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz0, h12]) c6]
      rw [run_succ, step_at p e 7 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz0, h12]) c7]
      rw [run_zero]
      simp only [execInstr]
      congr 1
      · simp [hlt, Function.update_apply, h30, hz0, h12]
      · rw [hM6def]; funext a; simp [Function.update_apply, h30, hz0, h11]
    have hM6' : ∀ a, a ≠ 14 → a ≠ 15 → a ≠ 22 → a ≠ LVB + 2 * u → M6 a = M a := by
      intro a a14 a15 a22 aL
      rw [hM6def, Function.update_of_ne a14, Function.update_of_ne a15, Function.update_of_ne aL,
        Function.update_of_ne a22]
    have hM6L : ∀ j : Fin n, M6 (LVB + 2 * (j : ℕ)) = if (j : ℕ) = u then 1 else M (LVB + 2 * (j : ℕ)) := by
      intro j
      by_cases hj : (j : ℕ) = u
      · rw [if_pos hj, hM6def, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hj,
          Function.update_self]
      · rw [if_neg hj, hM6' _ (by omega) (by omega) (by omega) (by omega)]
    have hadj6 : ∀ v j : Fin n, (1 ≤ M6 (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨
        1 ≤ M6 (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j := by
      intro v j
      have e1 := edge_lt1 n v j v.isLt j.isLt
      have e2 := edge_lt2 n v j v.isLt j.isLt
      rw [hM6' _ (by omega) (by omega) (by omega) (by omega), hM6' _ (by omega) (by omega) (by omega) (by omega)]
      exact hadj v j
    have hinv6 : ∀ j : Fin n, if G.Reachable U j then
        M6 (LVB + 2 * (j : ℕ)) = (if G.dist U j + 1 ≤ 1 then G.dist U j + 1 else 0)
        else (M6 (LVB + 2 * (j : ℕ)) = 0 ∨ n + 2 ≤ M6 (LVB + 2 * (j : ℕ))) := by
      intro j
      rw [hM6L j]
      by_cases hr : G.Reachable U j
      · rw [if_pos hr]
        by_cases hj : (j : ℕ) = u
        · rw [if_pos hj, hJU j hj, SimpleGraph.dist_self]; rfl
        · rw [if_neg hj]
          have hd : G.dist U j ≠ 0 := by
            intro h0
            have := (hr.dist_eq_zero_iff).1 h0
            apply hj; rw [← this, hU]
          rw [if_neg (by omega), hinv j, if_neg]
          rw [← bakerRoot_eq_of_reach G U j hr, hbU, hU]; omega
      · rw [if_neg hr]
        have hj : (j : ℕ) ≠ u := fun h => hr (by rw [hJU j h])
        rw [if_neg hj, hinv j]
        split_ifs <;> omega
    obtain ⟨τL, hτL, l1, lL, lfr, llo, l19, l20, l28, lr⟩ :=
      WilliamsonShmoys.ram_bfs_layer_loop p (e + 8) (lay_code p e hcode) n LVB hLVB G U n 1 M6 R (by omega)
        le_rfl (by omega)
        (by rw [hM6' 13 (by omega) (by omega) (by omega) (by omega), h13])
        (by rw [hM6' 20 (by omega) (by omega) (by omega) (by omega), h20])
        (by rw [hM6' 28 (by omega) (by omega) (by omega) (by omega), h28])
        (by rw [hM6' 11 (by omega) (by omega) (by omega) (by omega), h11])
        (by rw [hM6' 12 (by omega) (by omega) (by omega) (by omega), h12])
        (by rw [hM6' 19 (by omega) (by omega) (by omega) (by omega), h19])
        (by rw [hM6def, Function.update_of_ne (by omega), Function.update_self])
        (by rw [hM6def, Function.update_self])
        hadj6 ⟨U, SimpleGraph.Reachable.refl U, by rw [SimpleGraph.dist_self]⟩ hinv6
    have hcard : (Finset.univ.filter (fun j : Fin n => G.Reachable U j ∧ 1 ≤ G.dist U j + 1)).card =
        (Finset.univ.filter (fun j : Fin n => ((bakerRoot G j : Fin n) : ℕ) = u)).card := by
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro j _
      constructor
      · rintro ⟨hr, -⟩; rw [(root_iff G U j hbU).2 hr, hU]
      · intro h
        exact ⟨(root_iff G U j hbU).1 (Fin.ext (by rw [h, hU])), by omega⟩
    rw [hcard] at hτL
    set SL := planarRAMRun p ⟨e + 8, M6, R⟩ τL with hSL
    obtain ⟨pcL, ML, RL⟩ := SL
    simp only at l1 lL lfr llo l19 l20 l28 lr
    have hpcL : pcL = e + 44 := by omega
    subst hpcL
    have hML : ∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → a ≠ 14 → a ≠ 15 → a ≠ 22 → ML a = M a :=
      fun a ha hne a14 a15 a22 => (lfr a ha hne).trans (hM6' a a14 a15 a22 (hne u hu))
    have hMLlo : ∀ a, a ≤ 13 → ML a = M a :=
      fun a ha => (llo a ha).trans (hM6' a (by omega) (by omega) (by omega) (by omega))
    obtain ⟨τF, hτF, f1, fL, ffr, fr⟩ :=
      WilliamsonShmoys.ram_bfs_finalize_sweep p (e + 44) (fin_code p e hcode) n LVB hLV ML RL
        ((hMLlo 13 le_rfl).trans h13) l28 ((hMLlo 11 (by omega)).trans h11) ((hMLlo 12 (by omega)).trans h12) l19
        ((hML 31 (by omega) (fun j _ => by omega) (by omega) (by omega) (by omega)).trans h31)
    set SF := planarRAMRun p ⟨e + 44, ML, RL⟩ τF with hSF
    obtain ⟨pcF, MF, RF⟩ := SF
    simp only at f1 fL ffr fr
    subst fr; subst lr
    have hMF : ∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) → MF a = ML a := ffr
    have mf29 : MF 29 = u := by
      rw [hMF 29 (by omega) (by omega) (by omega) (fun j _ => by omega),
        hML 29 (by omega) (fun j _ => by omega) (by omega) (by omega) (by omega), h29]
    have mf30 : MF 30 = LVB + 2 * u := by
      rw [hMF 30 (by omega) (by omega) (by omega) (fun j _ => by omega),
        hML 30 (by omega) (fun j _ => by omega) (by omega) (by omega) (by omega), h30]
    have mf11 : MF 11 = 1 := by
      rw [hMF 11 (by omega) (by omega) (by omega) (fun j _ => by omega), hMLlo 11 (by omega), h11]
    have mf19 : MF 19 = 2 := by
      rw [hMF 19 (by omega) (by omega) (by omega) (fun j _ => by omega), l19]
    refine ⟨6 + τL + τF + 3, by omega, ?_⟩
    rw [run_add, run_add, run_add, e6, ← hSL, ← hSF]
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at p e 55 _ (by simp [f1]) c55]
    rw [run_succ, step_at p e 56 _ (by simp [execInstr, f1]) c56]
    rw [run_succ, step_at p e 57 _ (by simp [execInstr, f1]) c57]
    rw [run_zero]
    simp only [execInstr]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simp [Function.update_apply, mf29, mf11]
    · simp [Function.update_apply, mf30, mf19]; ring
    · intro j
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), fL j j.isLt, lL j]
      by_cases hr : G.Reachable U j
      · have hbj : bakerRoot G j = U := (root_iff G U j hbU).2 hr
        have hlev : bakerLevel G j = G.dist U j := by unfold bakerLevel; rw [hbj]
        have hdl := dist_lt_card G U j hr
        rw [if_pos hr, if_pos ⟨by omega, by omega⟩, if_pos (by rw [hbj, hU]; omega), hlev]
        ring
      · have hbj : bakerRoot G j ≠ U := fun h => hr ((root_iff G U j hbU).1 h)
        have hj : (j : ℕ) ≠ u := fun h => hr (by rw [hJU j h])
        have hbj' : ((bakerRoot G j : Fin n) : ℕ) ≠ u := fun h => hbj (hJU _ h)
        rw [if_neg hr, hM6L j, if_neg hj, hinv j]
        by_cases hb : ((bakerRoot G j : Fin n) : ℕ) < u
        · rw [if_pos hb, if_neg (by omega), if_pos (by omega)]
        · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
    · intro a ha hne
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hMF a (by omega) (by omega) (by omega) hne, hML a (by omega) hne (by omega) (by omega) (by omega)]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hMF a (by omega) (by omega) (by omega) (fun j _ => by omega), hMLlo a ha]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), mf19]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hMF 20 (by omega) (by omega) (by omega) (fun j _ => by omega), l20]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hMF 28 (by omega) (by omega) (by omega) (fun j _ => by omega), l28]
  · -- u already labelled: skip
    have hbu : ((bakerRoot G U : Fin n) : ℕ) < u := by
      by_contra hc; rw [if_neg hc] at hinvU; omega
    have hne : ∀ j : Fin n, ((bakerRoot G j : Fin n) : ℕ) ≠ u := by
      intro j h
      have hbj : bakerRoot G j = U := hJU _ h
      have hr : G.Reachable U j := by rw [← hbj]; exact (bakerRoot_spec G j).1
      have := bakerRoot_eq_of_reach G U j hr
      rw [this, hbj, hU] at hbu
      omega
    have n22 : LVB + 2 * u ≠ 22 := by omega
    refine ⟨6, by omega, ?_⟩
    rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at p e 2 _ rfl c2]
    rw [run_succ, step_at p e 3 _ (by simp [execInstr, hlt]) c3]
    rw [run_succ, step_at p e 4 _ (by simp [execInstr, hlt]) c4]
    rw [run_succ, step_at p e 55 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz, h12]) c55]
    rw [run_succ, step_at p e 56 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz, h12]) c56]
    rw [run_succ, step_at p e 57 _ (by simp [execInstr, hlt, Function.update_apply, h30, hz, h12]) c57]
    rw [run_zero]
    simp only [execInstr]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simp [Function.update_apply, h29, h11]
    · simp [Function.update_apply, h30, h19]; ring
    · intro j
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hinv j]
      have := hne j
      by_cases hb : ((bakerRoot G j : Fin n) : ℕ) < u
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb, if_neg (by omega)]
    · intro a ha hne'
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simp [Function.update_apply, h19]
    · simp [Function.update_apply, h20]
    · simp [Function.update_apply, h28]

open Classical in
lemma root_loop (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) :
    ∀ (r u : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), u + r = n →
      M 13 = n → M 20 = 2 * n → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 29 = u →
      M 30 = LVB + 2 * u → M 31 = n + 1 →
      (∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j) →
      (∀ j : Fin n, M (LVB + 2 * (j : ℕ)) = if ((bakerRoot G j : Fin n) : ℕ) < u then n + 2 + bakerLevel G j else 0) →
      ∃ τ, τ ≤ (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => u ≤ ((bakerRoot G j : Fin n) : ℕ))).card + (9 * n + 12) * r + 1 ∧
        (planarRAMRun p ⟨e + 2, M, R⟩ τ).pc = e + 58 ∧
        (∀ j : Fin n, (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) = n + 2 + bakerLevel G j) ∧
        (∀ a, 30 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 13 → (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).natMem 28 = LVB ∧ (planarRAMRun p ⟨e + 2, M, R⟩ τ).realMem = R := by
  have c2 : p[e + 2]? = some (natBranch 13 29 (e + 58) (e + 3)) := by simpa using hcode 2 (by simp)
  intro r
  induction r with
  | zero =>
    intro u M R hu h13 h20 h28 h11 h12 h19 h29 h30 h31 hadj hinv
    refine ⟨1, by omega, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_at p e 2 _ rfl c2, run_zero]
    simp only [execInstr, show M 13 ≤ M 29 by omega, if_true]
    refine ⟨trivial, fun j => ?_, fun a _ _ => trivial, fun a _ => trivial, h19, h20, h28, trivial⟩
    rw [hinv j, if_pos (by have := j.isLt; have : ((bakerRoot G j : Fin n) : ℕ) < n := (bakerRoot G j).isLt; omega)]
  | succ r ih =>
    intro u M R hu h13 h20 h28 h11 h12 h19 h29 h30 h31 hadj hinv
    obtain ⟨τ1, hτ1, q1, q29, q30, qL, qfr, qlo, q19, q20, q28, qr⟩ :=
      root_iter p e hcode n LVB hLVB G u (by omega) M R h13 h20 h28 h11 h12 h19 h29 h30 h31 hadj hinv
    set S1 := planarRAMRun p ⟨e + 2, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 q29 q30 qL qfr qlo q19 q20 q28 qr
    subst q1; subst qr
    have hadj1 : ∀ v j : Fin n, (1 ≤ M1 (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨
        1 ≤ M1 (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j := by
      intro v j
      have e1 := edge_lt1 n v j v.isLt j.isLt
      have e2 := edge_lt2 n v j v.isLt j.isLt
      rw [qfr _ (by omega) (fun j' _ => by omega), qfr _ (by omega) (fun j' _ => by omega)]
      exact hadj v j
    obtain ⟨τ2, hτ2, r1, rL, rfr, rlo, r19, r20, r28, rr⟩ :=
      ih (u + 1) M1 R1 (by omega) ((qlo 13 le_rfl).trans h13) q20 q28 ((qlo 11 (by omega)).trans h11)
        ((qlo 12 (by omega)).trans h12) q19 q29 q30 ((qfr 31 (by omega) (fun j _ => by omega)).trans h31) hadj1 qL
    have hsplit := card_split (fun j : Fin n => u ≤ ((bakerRoot G j : Fin n) : ℕ)) (fun j : Fin n => ((bakerRoot G j : Fin n) : ℕ) = u)
      (fun j : Fin n => u + 1 ≤ ((bakerRoot G j : Fin n) : ℕ)) (fun j => by omega) (fun j => by omega)
    refine ⟨τ1 + τ2, ?_, ?_⟩
    · rw [hsplit]; exact loop_arith n _ _ r τ1 τ2 hτ1 hτ2
    rw [run_add, ← hS1]
    refine ⟨r1, rL, ?_, ?_, r19, r20, r28, rr⟩
    · intro a ha hne; rw [rfr a ha hne, qfr a ha hne]
    · intro a ha; rw [rlo a ha, qlo a ha]

open Classical in
lemma root_entry (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0)
    (h19 : M 19 = 2) (h31 : M 31 = n + 1)
    (hadj : ∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j)
    (hzero : ∀ j, j < n → M (LVB + 2 * j) = 0) :
    ∃ τ, τ ≤ 32 * n * n + 36 * n + 3 ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).pc = e + 58 ∧
      (∀ j : Fin n, (planarRAMRun p ⟨e, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) = n + 2 + bakerLevel G j) ∧
      (∀ a, 30 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 13 → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 28 = LVB ∧ (planarRAMRun p ⟨e, M, R⟩ τ).realMem = R := by
  have c0 : p[e + 0]? = some (natConst 29 0) := by simpa using hcode 0 (by simp)
  have c1 : p[e + 1]? = some (natAdd 30 28 12) := by simpa using hcode 1 (by simp)
  have e2 : planarRAMRun p ⟨e, M, R⟩ 2 = ⟨e + 2, Function.update (Function.update M 29 0) 30 LVB, R⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, run_succ, step_at p e 0 _ (by simp) c0,
      run_succ, step_at p e 1 _ (by simp [execInstr]) c1, run_zero]
    simp [execInstr, Function.update_apply, h28, h12]
  have hu : ∀ a, a ≠ 29 → a ≠ 30 → (Function.update (Function.update M 29 0) 30 LVB) a = M a :=
    fun a a29 a30 => by rw [Function.update_of_ne a30, Function.update_of_ne a29]
  have hLV : 36 ≤ LVB := by omega
  obtain ⟨τ, hτ, r1, rL, rfr, rlo, r19, r20, r28, rr⟩ :=
    root_loop p e hcode n LVB hLVB G n 0 (Function.update (Function.update M 29 0) 30 LVB) R (by omega)
      (by rw [hu 13 (by omega) (by omega), h13]) (by rw [hu 20 (by omega) (by omega), h20])
      (by rw [hu 28 (by omega) (by omega), h28]) (by rw [hu 11 (by omega) (by omega), h11])
      (by rw [hu 12 (by omega) (by omega), h12]) (by rw [hu 19 (by omega) (by omega), h19])
      (by simp) (by simp) (by rw [hu 31 (by omega) (by omega), h31])
      (fun v j => by
        have e1 := edge_lt1 n v j v.isLt j.isLt
        have e2 := edge_lt2 n v j v.isLt j.isLt
        rw [hu _ (by omega) (by omega), hu _ (by omega) (by omega)]; exact hadj v j)
      (fun j => by rw [hu _ (by omega) (by omega), hzero j j.isLt, if_neg (by omega)])
  have hcard : (Finset.univ.filter (fun j : Fin n => 0 ≤ ((bakerRoot G j : Fin n) : ℕ))).card ≤ n :=
    (Finset.card_filter_le _ _).trans (by simp)
  refine ⟨2 + τ, ?_, ?_⟩
  · have : (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => 0 ≤ ((bakerRoot G j : Fin n) : ℕ))).card ≤
        (23 * n + 24) * n := Nat.mul_le_mul_left _ hcard
    nlinarith
  rw [run_add, e2]
  refine ⟨r1, rL, fun a ha hne => ?_, fun a ha => ?_, r19, r20, r28, rr⟩
  · rw [rfr a ha hne, hu a (by omega) (by omega)]
  · rw [rlo a ha, hu a (by omega) (by omega)]

end

end RL

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (e : ℕ)
    (hcode : CodeAt p e
    [natConst 29 0,
      natAdd 30 28 12,
      natBranch 13 29 (e + 58) (e + 3),
      natLoad 22 30,
      natBranch 22 12 (e + 5) (e + 55),
      natStore 30 11,
      natConst 15 1,
      natConst 14 2,
      natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (e + 8 + 5 + 27) (e + 8 + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (e + 8 + 5 + 3) (e + 8 + 5 + 22),
      natBranch 15 22 (e + 8 + 5 + 4) (e + 8 + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (e + 8 + 5 + 8 + 14) (e + 8 + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (e + 8 + 5 + 8 + 7) (e + 8 + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (e + 8 + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (e + 8 + 5),
      natBranch 11 23 (e + 8 + 33) (e + 8 + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump (e + 8),
      natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (e + 44 + 11) (e + 44 + 3),
      natLoad 22 27,
      natBranch 22 12 (e + 44 + 8) (e + 44 + 5),
      natBranch 22 31 (e + 44 + 6) (e + 44 + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (e + 44 + 2),
      natAdd 29 29 11,
      natAdd 30 30 19,
      jump (e + 2)])
    (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0)
    (h19 : M 19 = 2) (h31 : M 31 = n + 1)
    (hadj : ∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j)
    (hzero : ∀ j, j < n → M (LVB + 2 * j) = 0) :
    ∃ τ, τ ≤ 32 * n * n + 36 * n + 3 ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).pc = e + 58 ∧
      (∀ j : Fin n, (planarRAMRun p ⟨e, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) = n + 2 + bakerLevel G j) ∧
      (∀ a, 30 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 13 → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 28 = LVB ∧ (planarRAMRun p ⟨e, M, R⟩ τ).realMem = R :=
  RL.root_entry p e hcode n LVB hLVB G M R h13 h20 h28 h11 h12 h19 h31 hadj hzero
