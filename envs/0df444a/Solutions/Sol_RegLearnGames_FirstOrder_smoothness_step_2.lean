-- Prove2me | solution 2 for RegLearnGames.FirstOrder.smoothness_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:13:04.414777+00:00
-- url     : https://prove2.me/submissions/84df8e6b-afd8-49f2-9817-77a2d64161d2

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting
set_option autoImplicit false

open Finset RegLearnGames.FirstOrder

lemma oo_pp_update {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d)
    (s : Fin n → Fin d) :
    AGT.profileProb (Function.update w i (Pi.single a 1)) s
      = (if s i = a then 1 else 0) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  congr 1
  · simp [Pi.single_apply]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma oo_pp {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (s : Fin n → Fin d) :
    AGT.profileProb w s = w i (s i) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]


lemma oo_R_update {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d)
    (s : Fin n → Fin d) :
    ∏ j ∈ univ.erase i, w j (Function.update s i a j) = ∏ j ∈ univ.erase i, w j (s j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma oo_costVec {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (i : Fin n) (hl : ∑ b, w i b = 1) (a : Fin d) :
    costVec c w i a = ∑ s, AGT.profileProb w s * c i (Function.update s i a) := by
  unfold costVec AGT.expectedPayoff
  simp only [oo_pp_update]
  have h1 : ∑ s : Fin n → Fin d, (if s i = a then 1 else 0) * (∏ j ∈ univ.erase i, w j (s j)) * c i s
      = ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = a),
          (∏ j ∈ univ.erase i, w j (s j)) * c i s := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s i = a <;> simp [h]
  rw [h1]
  rw [← Finset.sum_fiberwise univ (fun s : Fin n → Fin d => s i)
    (fun s => AGT.profileProb w s * c i (Function.update s i a))]
  have h2 : ∀ b : Fin d, ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = b),
      AGT.profileProb w s * c i (Function.update s i a)
      = w i b * ∑ s ∈ univ.filter (fun s : Fin n → Fin d => s i = a),
          (∏ j ∈ univ.erase i, w j (s j)) * c i s := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun s => Function.update s i a) (fun s => Function.update s i b)
      ?_ ?_ ?_ ?_ ?_
    · intro s hs; simp
    · intro s hs; simp
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp [hs]
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp [hs]
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [oo_pp w i s, hs, oo_R_update]
      ring
  rw [Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.sum_mul, hl, one_mul]

theorem solution {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (hw : AGT.IsMixedProfile w)
    (lam mu : ℝ) (sstar : Fin n → Fin d)
    (hsmooth : ∀ s : Fin n → Fin d,
      (∑ i, c i (Function.update s i (sstar i))) ≤
        lam * optCost c + mu * socialCostPure c s) :
    (∑ i, costVec c w i (sstar i)) ≤
      lam * optCost c + mu * socialCost c w := by
  have hP : ∀ s, 0 ≤ AGT.profileProb w s := fun s =>
    Finset.prod_nonneg (fun i _ => (hw i).1 (s i))
  have hone : ∑ s : Fin n → Fin d, AGT.profileProb w s = 1 := by
    unfold AGT.profileProb
    rw [← Fintype.prod_sum (fun i a => w i a)]
    simp [fun i => (hw i).2]
  calc ∑ i, costVec c w i (sstar i)
      = ∑ i, ∑ s, AGT.profileProb w s * c i (Function.update s i (sstar i)) :=
        Finset.sum_congr rfl (fun i _ => oo_costVec c w i (hw i).2 (sstar i))
    _ = ∑ s, AGT.profileProb w s * ∑ i, c i (Function.update s i (sstar i)) := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
    _ ≤ ∑ s, AGT.profileProb w s * (lam * optCost c + mu * socialCostPure c s) :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hsmooth s) (hP s))
    _ = lam * optCost c + mu * socialCost c w := by
        unfold socialCost
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [show ∑ s : Fin n → Fin d, AGT.profileProb w s * (lam * optCost c) = lam * optCost c by
          rw [← Finset.sum_mul, hone, one_mul]]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
