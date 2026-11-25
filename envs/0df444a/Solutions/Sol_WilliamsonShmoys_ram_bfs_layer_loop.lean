-- Prove2me | solution 1 for WilliamsonShmoys.ram_bfs_layer_loop
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T02:41:39.540261+00:00
-- url     : https://prove2.me/submissions/7844accd-2aed-46b8-8015-1db542527bf7

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Theorems.Thm_WilliamsonShmoys_ram_bfs_vertex_scan_counted
import Theorems.Thm_WilliamsonShmoys_bfs_layer_step


set_option autoImplicit false

namespace BM

lemma dist_lt_card {n : ℕ} (G : SimpleGraph (Fin n)) (r j : Fin n) (h : G.Reachable r j) :
    G.dist r j < n := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  have := (p.isPath_of_length_eq_dist hp).length_lt
  simpa [hp] using this

lemma layer_down {V : Type} (G : SimpleGraph V) (r : V) (t : ℕ) :
    ∀ m j, G.Reachable r j → G.dist r j = t + m → ∃ w, G.Reachable r w ∧ G.dist r w = t := by
  intro m
  induction m with
  | zero => intro j hj hd; exact ⟨j, hj, by simpa using hd⟩
  | succ m ih =>
    intro j hj hd
    have hw : ¬ (G.Reachable r j ∧ G.dist r j ≤ t + m) := by omega
    obtain ⟨u, hu, hdu, -⟩ := (WilliamsonShmoys.bfs_layer_step G r j (t + m) hw).1 ⟨hj, by omega⟩
    exact ih u hu hdu

lemma no_layer_below {V : Type} (G : SimpleGraph V) (r : V) (t : ℕ)
    (h : ¬ ∃ w, G.Reachable r w ∧ G.dist r w = t) (j : V) (hj : G.Reachable r j) : G.dist r j < t := by
  by_contra hc
  exact h (layer_down G r t (G.dist r j - t) j hj (by omega))

end BM

namespace LL
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

lemma sum_range_fin (n : ℕ) (g : ℕ → ℕ) (P : Fin n → Prop) [DecidablePred P] (hg : ∀ v : Fin n, g v = if P v then 1 else 0) :
    ∑ v ∈ Finset.range n, g v = (Finset.univ.filter P).card := by
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun v _ => hg v)

lemma card_split {n : ℕ} (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (h : ∀ j, P j ↔ Q j ∨ R j) (hd : ∀ j, ¬ (Q j ∧ R j)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card + (Finset.univ.filter R).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have := h j; have := hd j
  by_cases hq : Q j <;> by_cases hr : R j <;> simp_all

lemma card_mono {n : ℕ} (Q P : Fin n → Prop) [DecidablePred Q] [DecidablePred P] (h : ∀ j, Q j → P j) :
    (Finset.univ.filter Q).card ≤ (Finset.univ.filter P).card :=
  Finset.card_le_card (fun j => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h j)

lemma time_arith (n c c2 τ1 τ2 : ℕ) (hc : 1 ≤ c) (h1 : τ1 ≤ 9 * n + 10 + (14 * n + 14) * c)
    (h2 : τ2 ≤ (23 * n + 24) * c2) : τ1 + τ2 ≤ (23 * n + 24) * (c + c2) := by nlinarith

lemma time_arith0 (n c C τ1 : ℕ) (hc : 1 ≤ c) (hcC : c ≤ C) (h1 : τ1 ≤ 9 * n + 10 + (14 * n + 14) * c) :
    τ1 ≤ (23 * n + 24) * C := by nlinarith

section
variable (p : List PlanarRAMInstruction) (d : ℕ)
  (hcode : CodeAt p d
    [natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (d + 5 + 27) (d + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (d + 5 + 3) (d + 5 + 22),
      natBranch 15 22 (d + 5 + 4) (d + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (d + 5 + 8 + 14) (d + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (d + 5 + 8 + 7) (d + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (d + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (d + 5),
      natBranch 11 23 (d + 33) (d + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump d])
include hcode

lemma vs_code : CodeAt p (d + 5)
    [natBranch 13 24 (d + 5 + 27) (d + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (d + 5 + 3) (d + 5 + 22),
      natBranch 15 22 (d + 5 + 4) (d + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (d + 5 + 8 + 14) (d + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (d + 5 + 8 + 7) (d + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (d + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (d + 5)] := by
  apply codeAt_sub p d 5 _ _ hcode
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

open Classical in
set_option maxHeartbeats 4000000 in
lemma layer_pass (M : ℕ → ℕ) (R : ℕ → ℝ) (n t LVB : ℕ) (ht : 1 ≤ t) (hLVB : 36 + 2 * n * n ≤ LVB)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0)
    (h19 : M 19 = 2) (h15 : M 15 = t) (h14 : M 14 = t + 1) :
    ∃ τ, τ ≤ 9 * n + 10 + (14 * n + 14) * ∑ v ∈ Finset.range n, (if M (LVB + 2 * v) = t then 1 else 0) ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).pc = (if (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) then d else d + 36) ∧
      (∀ j, j < n → (planarRAMRun p ⟨d, M, R⟩ τ).natMem (LVB + 2 * j) =
        if M (LVB + 2 * j) = 0 ∧ ∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
        then t + 1 else M (LVB + 2 * j)) ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).natMem 15 = (if (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) then t + 1 else t) ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).natMem 14 = (if (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) then t + 2 else t + 1) ∧
      (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 13 → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨d, M, R⟩ τ).natMem 20 = 2 * n ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).natMem 28 = LVB ∧
      (planarRAMRun p ⟨d, M, R⟩ τ).realMem = R := by
  have hLV : 36 ≤ LVB := by omega
  have c0 : p[d + 0]? = some (natConst 23 0) := by simpa using hcode 0 (by simp)
  have c1 : p[d + 1]? = some (natConst 24 0) := by simpa using hcode 1 (by simp)
  have c2 : p[d + 2]? = some (natConst 25 36) := by simpa using hcode 2 (by simp)
  have c3 : p[d + 3]? = some (natConst 26 36) := by simpa using hcode 3 (by simp)
  have c4 : p[d + 4]? = some (natAdd 27 28 12) := by simpa using hcode 4 (by simp)
  have c32 : p[d + 32]? = some (natBranch 11 23 (d + 33) (d + 36)) := by simpa using hcode 32 (by simp)
  have c33 : p[d + 33]? = some (natAdd 15 15 11) := by simpa using hcode 33 (by simp)
  have c34 : p[d + 34]? = some (natAdd 14 14 11) := by simpa using hcode 34 (by simp)
  have c35 : p[d + 35]? = some (jump d) := by simpa using hcode 35 (by simp)
  set M5 := Function.update (Function.update (Function.update (Function.update
      (Function.update M 23 0) 24 0) 25 36) 26 36) 27 LVB with hM5def
  have e5 : planarRAMRun p ⟨d, M, R⟩ 5 = ⟨d + 5, M5, R⟩ := by
    rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at p d 0 _ (by simp) c0]
    rw [run_succ, step_at p d 1 _ (by simp [execInstr]) c1]
    rw [run_succ, step_at p d 2 _ (by simp [execInstr]) c2]
    rw [run_succ, step_at p d 3 _ (by simp [execInstr]) c3]
    rw [run_succ, step_at p d 4 _ (by simp [execInstr]) c4]
    rw [run_zero]
    simp only [execInstr]
    congr 1
    rw [hM5def]; simp [Function.update_apply, h12, h28]
  have hM5 : ∀ a, 28 < a → M5 a = M a := by
    intro a ha
    rw [hM5def, Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hM5l : ∀ a, a ≤ 22 → M5 a = M a := by
    intro a ha
    rw [hM5def, Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  obtain ⟨τv, hτv, v1, vL, v23, vfr, vlo, v19, v20, v28, vr⟩ :=
    WilliamsonShmoys.ram_bfs_vertex_scan_counted p (d + 5) (vs_code p d hcode) n t LVB ht hLVB n 0 M5 R (by omega)
      (by rw [hM5l 13 (by omega), h13]) (by rw [hM5l 20 (by omega), h20]) (by simp [hM5def])
      (by simp [hM5def]) (by simp [hM5def]) (by simp [hM5def]) (by simp [hM5def, h28])
      (by rw [hM5l 11 (by omega), h11]) (by rw [hM5l 12 (by omega), h12]) (by rw [hM5l 19 (by omega), h19])
      (by rw [hM5l 15 (by omega), h15]) (by rw [hM5l 14 (by omega), h14])
  have hsum : ∑ v ∈ Finset.range n, (if M5 (LVB + 2 * (0 + v)) = t then 1 else 0) =
      ∑ v ∈ Finset.range n, (if M (LVB + 2 * v) = t then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.zero_add, hM5 _ (by omega)]
  rw [hsum] at hτv
  have hFC : (∃ v, 0 ≤ v ∧ v < n ∧ M5 (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M5 (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M5 (36 + 2 * v + j * (2 * n))) ∧ M5 (LVB + 2 * j) = 0) ↔ (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) := by
    constructor
    · rintro ⟨v, -, hv, a, j, hj, b, c⟩
      exact ⟨v, hv, by rwa [hM5 _ (by omega)] at a, j, hj, by rwa [hM5 _ (by omega), hM5 _ (by omega)] at b,
        by rwa [hM5 _ (by omega)] at c⟩
    · rintro ⟨v, hv, a, j, hj, b, c⟩
      exact ⟨v, Nat.zero_le _, hv, by rwa [hM5 _ (by omega)], j, hj, by rwa [hM5 _ (by omega), hM5 _ (by omega)],
        by rwa [hM5 _ (by omega)]⟩
  have hLab : ∀ j, j < n → ((∃ v, 0 ≤ v ∧ v < n ∧ M5 (LVB + 2 * v) = t ∧ (1 ≤ M5 (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M5 (36 + 2 * v + j * (2 * n)))) ↔
      (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))))) := by
    intro j hj
    constructor
    · rintro ⟨v, -, hv, a, b⟩
      exact ⟨v, hv, by rwa [hM5 _ (by omega)] at a, by rwa [hM5 _ (by omega), hM5 _ (by omega)] at b⟩
    · rintro ⟨v, hv, a, b⟩
      exact ⟨v, Nat.zero_le _, hv, by rwa [hM5 _ (by omega)], by rwa [hM5 _ (by omega), hM5 _ (by omega)]⟩
  rw [hFC] at v23
  have h23 : M5 23 = 0 := by simp [hM5def]
  rw [h23] at v23
  set S1 := planarRAMRun p ⟨d + 5, M5, R⟩ τv with hS1
  obtain ⟨pc1, M1, R1⟩ := S1
  simp only at v1 vL v23 vfr vlo v19 v20 v28 vr
  subst vr
  have L1 : ∀ j, j < n → M1 (LVB + 2 * j) = if M (LVB + 2 * j) = 0 ∧ ∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
      then t + 1 else M (LVB + 2 * j) := by
    intro j hj
    rw [vL j hj, hM5 _ (by omega)]
    simp only [hLab j hj]
  have F1 : ∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → M1 a = M a := fun a ha hne => (vfr a ha hne).trans (hM5 a ha)
  have lo1 : ∀ a, a ≤ 15 → M1 a = M a := fun a ha => (vlo a ha).trans (hM5l a (by omega))
  by_cases hc : (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧ (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0)
  · rw [if_pos hc] at v23
    refine ⟨5 + τv + 4, by omega, ?_⟩
    rw [run_add, run_add, e5, ← hS1]
    rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
    rw [run_succ, step_at p d 32 _ (by simp [v1]; try omega) c32]
    rw [run_succ, step_at p d 33 _ (by simp [execInstr, v23, lo1 11 (by omega), h11]) c33]
    rw [run_succ, step_at p d 34 _ (by simp [execInstr, v23, lo1 11 (by omega), h11]) c34]
    rw [run_succ, step_at p d 35 _ (by simp [execInstr, v23, lo1 11 (by omega), h11]) c35]
    rw [run_zero]
    simp only [execInstr, if_pos hc]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · intro j hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), L1 j hj]
    · simp [Function.update_apply, lo1 15 (by omega), lo1 11 (by omega), h15, h11]
    · simp [Function.update_apply, lo1 14 (by omega), lo1 11 (by omega), h14, h11]
    · intro a ha hne
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), F1 a ha hne]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), lo1 a (by omega)]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v19]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v20]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), v28]
  · rw [if_neg hc] at v23
    refine ⟨5 + τv + 1, by omega, ?_⟩
    rw [run_add, run_add, e5, ← hS1]
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    rw [run_succ, step_at p d 32 _ (by simp [v1]; try omega) c32]
    rw [run_zero]
    simp only [execInstr, if_neg hc]
    refine ⟨by simp [v23, lo1 11 (by omega), h11], L1, ?_, ?_, F1, fun a ha => lo1 a (by omega), v19, v20, v28, trivial⟩
    · rw [lo1 15 (by omega), h15]
    · rw [lo1 14 (by omega), h14]

open Classical in
lemma layer_loop (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (r : Fin n) :
    ∀ (f t : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), n + 1 ≤ t + f → 1 ≤ t → t ≤ n →
      M 13 = n → M 20 = 2 * n → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      (∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j) →
      (∃ w, G.Reachable r w ∧ G.dist r w + 1 = t) →
      (∀ j : Fin n, if G.Reachable r j then
          M (LVB + 2 * (j : ℕ)) = (if G.dist r j + 1 ≤ t then G.dist r j + 1 else 0)
        else (M (LVB + 2 * (j : ℕ)) = 0 ∨ n + 2 ≤ M (LVB + 2 * (j : ℕ)))) →
      ∃ τ, τ ≤ (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => G.Reachable r j ∧ t ≤ G.dist r j + 1)).card ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).pc = d + 36 ∧
        (∀ j : Fin n, (planarRAMRun p ⟨d, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) =
          if G.Reachable r j then G.dist r j + 1 else M (LVB + 2 * (j : ℕ))) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 13 → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨d, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).realMem = R := by
  intro f
  induction f with
  | zero => intro t M R hf ht1 htn; exfalso; omega
  | succ f ih =>
    intro t M R hf ht1 htn h13 h20 h28 h11 h12 h19 h15 h14 hadj hroot hinv
    obtain ⟨τ1, hτ1, q1, qL, q15, q14, qfr, qlo, q19, q20, q28, qr⟩ :=
      layer_pass p d hcode M R n t LVB ht1 hLVB h13 h20 h28 h11 h12 h19 h15 h14
    have K1 : ∀ v : Fin n, M (LVB + 2 * (v : ℕ)) = t ↔ G.Reachable r v ∧ G.dist r v + 1 = t := by
      intro v
      have hv := hinv v
      by_cases hr : G.Reachable r v
      · rw [if_pos hr] at hv; rw [hv]
        by_cases hle : G.dist r v + 1 ≤ t
        · rw [if_pos hle]; exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩
        · rw [if_neg hle]; constructor
          · intro h; omega
          · rintro ⟨-, h⟩; omega
      · rw [if_neg hr] at hv; constructor
        · intro h; rcases hv with hv | hv <;> omega
        · rintro ⟨h, -⟩; exact absurd h hr
    have K0 : ∀ j : Fin n, G.Reachable r j →
        (M (LVB + 2 * (j : ℕ)) = 0 ↔ ¬ (G.Reachable r j ∧ G.dist r j ≤ t - 1)) := by
      intro j hr
      have hv := hinv j; rw [if_pos hr] at hv; rw [hv]
      by_cases hle : G.dist r j + 1 ≤ t
      · rw [if_pos hle]; constructor
        · intro h; omega
        · intro h; exact absurd ⟨hr, by omega⟩ h
      · rw [if_neg hle]; constructor
        · intro _ h; omega
        · intro _; rfl
    have KE : ∀ j : Fin n, (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧
          (1 ≤ M (36 + 2 * v * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * v + (j : ℕ) * (2 * n)))) ↔
        ∃ u, G.Reachable r u ∧ G.dist r u = t - 1 ∧ G.Adj u j := by
      intro j; constructor
      · rintro ⟨v, hv, a, b⟩
        obtain ⟨hr, hd⟩ := (K1 ⟨v, hv⟩).1 a
        exact ⟨⟨v, hv⟩, hr, by omega, (hadj ⟨v, hv⟩ j).1 b⟩
      · rintro ⟨u, hr, hd, ha⟩
        exact ⟨u, u.isLt, (K1 u).2 ⟨hr, by omega⟩, (hadj u j).2 ha⟩
    have NL : ∀ j : Fin n, (planarRAMRun p ⟨d, M, R⟩ τ1).natMem (LVB + 2 * (j : ℕ)) =
        if G.Reachable r j then (if G.dist r j + 1 ≤ t + 1 then G.dist r j + 1 else 0)
        else M (LVB + 2 * (j : ℕ)) := by
      intro j
      rw [qL j j.isLt]
      by_cases hr : G.Reachable r j
      · rw [if_pos hr]
        have hv := hinv j; rw [if_pos hr] at hv
        by_cases hle : G.dist r j + 1 ≤ t
        · rw [if_neg (fun h => by have := h.1; rw [hv, if_pos hle] at this; omega), hv, if_pos hle,
            if_pos (by omega)]
        · have h0 : M (LVB + 2 * (j : ℕ)) = 0 := by rw [hv, if_neg hle]
          have hw : ¬ (G.Reachable r j ∧ G.dist r j ≤ t - 1) := fun h => hle (by omega)
          have BL := WilliamsonShmoys.bfs_layer_step G r j (t - 1) hw
          by_cases hd : G.dist r j = t
          · rw [if_pos ⟨h0, (KE j).2 (BL.1 ⟨hr, by omega⟩)⟩, if_pos (by omega)]; omega
          · rw [if_neg (fun h => hd (by have := (BL.2 ((KE j).1 h.2)).2; omega)), h0, if_neg (by omega)]
      · rw [if_neg hr, if_neg]
        rintro ⟨-, hex⟩
        obtain ⟨u, hu, -, ha⟩ := (KE j).1 hex
        exact hr (hu.trans ha.reachable)
    have FCiff : (∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
          (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0) ↔
        ∃ j : Fin n, G.Reachable r j ∧ G.dist r j = t := by
      constructor
      · rintro ⟨v, hv, a, j, hj, b, c⟩
        obtain ⟨hr, hd⟩ := (K1 ⟨v, hv⟩).1 a
        have hA := (hadj ⟨v, hv⟩ ⟨j, hj⟩).1 b
        have hrj := hr.trans hA.reachable
        have hw := (K0 ⟨j, hj⟩ hrj).1 c
        have := (WilliamsonShmoys.bfs_layer_step G r ⟨j, hj⟩ (t - 1) hw).2 ⟨⟨v, hv⟩, hr, by omega, hA⟩
        exact ⟨⟨j, hj⟩, this.1, by omega⟩
      · rintro ⟨j, hr, hd⟩
        have hw : ¬ (G.Reachable r j ∧ G.dist r j ≤ t - 1) := fun h => by omega
        obtain ⟨u, hu, hdu, ha⟩ := (WilliamsonShmoys.bfs_layer_step G r j (t - 1) hw).1 ⟨hr, by omega⟩
        exact ⟨u, u.isLt, (K1 u).2 ⟨hu, by omega⟩, j, j.isLt, (hadj u j).2 ha, (K0 j hr).2 hw⟩
    have hcnt : ∑ v ∈ Finset.range n, (if M (LVB + 2 * v) = t then 1 else 0) =
        (Finset.univ.filter (fun j : Fin n => G.Reachable r j ∧ G.dist r j + 1 = t)).card :=
      sum_range_fin n (fun v => if M (LVB + 2 * v) = t then 1 else 0)
        (fun j : Fin n => G.Reachable r j ∧ G.dist r j + 1 = t) (fun v => by
        show (if M (LVB + 2 * (v : ℕ)) = t then 1 else 0) = _
        by_cases h : M (LVB + 2 * (v : ℕ)) = t
        · rw [if_pos h, if_pos ((K1 v).1 h)]
        · rw [if_neg h, if_neg (fun h' => h ((K1 v).2 h'))])
    rw [hcnt] at hτ1
    have hc1 : 1 ≤ (Finset.univ.filter (fun j : Fin n => G.Reachable r j ∧ G.dist r j + 1 = t)).card := by
      obtain ⟨w, hw1, hw2⟩ := hroot
      exact Finset.card_pos.2 ⟨w, by simp [hw1, hw2]⟩
    have hsplit := card_split (fun j : Fin n => G.Reachable r j ∧ t ≤ G.dist r j + 1)
      (fun j => G.Reachable r j ∧ G.dist r j + 1 = t) (fun j => G.Reachable r j ∧ t + 1 ≤ G.dist r j + 1)
      (fun j => by constructor
                   · rintro ⟨a, b⟩; rcases Nat.eq_or_lt_of_le b with h | h
                     · exact Or.inl ⟨a, h.symm⟩
                     · exact Or.inr ⟨a, h⟩
                   · rintro (⟨a, b⟩ | ⟨a, b⟩) <;> exact ⟨a, by omega⟩)
      (fun j => by rintro ⟨⟨-, a⟩, ⟨-, b⟩⟩; omega)
    have hmono := card_mono (fun j : Fin n => G.Reachable r j ∧ G.dist r j + 1 = t)
      (fun j : Fin n => G.Reachable r j ∧ t ≤ G.dist r j + 1) (fun j h => ⟨h.1, by omega⟩)
    set S1 := planarRAMRun p ⟨d, M, R⟩ τ1 with hS1
    obtain ⟨pc1, M1, R1⟩ := S1
    simp only at q1 qL q15 q14 qfr qlo q19 q20 q28 qr NL
    subst qr
    have hadj1 : ∀ v j : Fin n, (1 ≤ M1 (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M1 (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j := by
      intro v j
      have e1 := edge_lt1 n v j v.isLt j.isLt
      have e2 := edge_lt2 n v j v.isLt j.isLt
      rw [qfr _ (by omega) (fun j' _ => by omega), qfr _ (by omega) (fun j' _ => by omega)]
      exact hadj v j
    by_cases hc : ∃ v, v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
          (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
    · rw [if_pos hc] at q1 q15 q14
      obtain ⟨j0, hr0, hd0⟩ := FCiff.1 hc
      have htn' : t + 1 ≤ n := by have := BM.dist_lt_card G r j0 hr0; omega
      subst q1
      have hinv1 : ∀ j : Fin n, if G.Reachable r j then
          M1 (LVB + 2 * (j : ℕ)) = (if G.dist r j + 1 ≤ t + 1 then G.dist r j + 1 else 0)
          else (M1 (LVB + 2 * (j : ℕ)) = 0 ∨ n + 2 ≤ M1 (LVB + 2 * (j : ℕ))) := by
        intro j
        rw [NL j]
        by_cases hr : G.Reachable r j
        · rw [if_pos hr, if_pos hr]
        · rw [if_neg hr, if_neg hr]
          have := hinv j; rw [if_neg hr] at this; exact this
      obtain ⟨τ2, hτ2, r1, rL, rfr, rlo, r19, r20, r28, rr⟩ :=
        ih (t + 1) M1 R1 (by omega) (by omega) htn' ((qlo 13 (by omega)).trans h13) q20 q28
          ((qlo 11 (by omega)).trans h11) ((qlo 12 (by omega)).trans h12) q19 q15 q14 hadj1
          ⟨j0, hr0, by omega⟩ hinv1
      refine ⟨τ1 + τ2, ?_, ?_⟩
      · rw [hsplit]; exact time_arith n _ _ τ1 τ2 hc1 hτ1 hτ2
      rw [run_add, ← hS1]
      refine ⟨r1, ?_, ?_, ?_, r19, r20, r28, rr⟩
      · intro j
        rw [rL j]
        by_cases hr : G.Reachable r j
        · rw [if_pos hr, if_pos hr]
        · rw [if_neg hr, if_neg hr, NL j, if_neg hr]
      · intro a ha hne; rw [rfr a ha hne, qfr a ha hne]
      · intro a ha; rw [rlo a ha, qlo a ha]
    · rw [if_neg hc] at q1
      have hnone : ¬ ∃ w, G.Reachable r w ∧ G.dist r w = t := fun h => hc (FCiff.2 h)
      refine ⟨τ1, time_arith0 n _ _ τ1 hc1 hmono hτ1, ?_⟩
      rw [← hS1]
      refine ⟨q1, ?_, qfr, qlo, q19, q20, q28, rfl⟩
      intro j
      show M1 (LVB + 2 * (j : ℕ)) = _
      rw [NL j]
      by_cases hr : G.Reachable r j
      · have := BM.no_layer_below G r t hnone j hr
        rw [if_pos hr, if_pos hr, if_pos (by omega)]
      · rw [if_neg hr, if_neg hr]

end

end LL

open WilliamsonShmoys PlanarRAMInstruction
open Classical in
theorem solution (p : List PlanarRAMInstruction) (d : ℕ)
    (hcode : CodeAt p d
    [natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (d + 5 + 27) (d + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (d + 5 + 3) (d + 5 + 22),
      natBranch 15 22 (d + 5 + 4) (d + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (d + 5 + 8 + 14) (d + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (d + 5 + 8 + 7) (d + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (d + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (d + 5),
      natBranch 11 23 (d + 33) (d + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump d])
    (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (r : Fin n) :
    ∀ (f t : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), n + 1 ≤ t + f → 1 ≤ t → t ≤ n →
      M 13 = n → M 20 = 2 * n → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      (∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j) →
      (∃ w, G.Reachable r w ∧ G.dist r w + 1 = t) →
      (∀ j : Fin n, if G.Reachable r j then
          M (LVB + 2 * (j : ℕ)) = (if G.dist r j + 1 ≤ t then G.dist r j + 1 else 0)
        else (M (LVB + 2 * (j : ℕ)) = 0 ∨ n + 2 ≤ M (LVB + 2 * (j : ℕ)))) →
      ∃ τ, τ ≤ (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => G.Reachable r j ∧ t ≤ G.dist r j + 1)).card ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).pc = d + 36 ∧
        (∀ j : Fin n, (planarRAMRun p ⟨d, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) =
          if G.Reachable r j then G.dist r j + 1 else M (LVB + 2 * (j : ℕ))) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 13 → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨d, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).realMem = R :=
  LL.layer_loop p d hcode n LVB hLVB G r
