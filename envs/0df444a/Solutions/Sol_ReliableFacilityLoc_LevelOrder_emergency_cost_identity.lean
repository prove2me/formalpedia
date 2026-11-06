-- Prove2me | solution 1 for ReliableFacilityLoc.LevelOrder.emergency_cost_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:49:09.168898+00:00
-- url     : https://prove2.me/submissions/d2ebb0e3-4da3-40c7-83a7-18dd97a6dfbb

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL
import Definitions.Def_ReliableFacilityLoc_LevelOrder_Moves

open Finset
open ReliableFacilityLoc.LevelOrder

namespace RFL2Aux

variable {I J R : ℕ} (D : Instance I J R)

lemma qExt_last : D.qExt (Fin.last J) = 0 := by simp [Instance.qExt]
lemma qExt_cs (j : Fin J) : D.qExt j.castSucc = D.q j := by simp [Instance.qExt]
lemma dExt_last (i : Fin I) : D.dExt i (Fin.last J) = D.phi i := by simp [Instance.dExt]
lemma dExt_cs (i : Fin I) (j : Fin J) : D.dExt i j.castSucc = D.d i j := by simp [Instance.dExt]

lemma tp_zero (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (j : Fin (J + 1)) :
    D.transProb Y i j 0 = 1 - D.qExt j := by
  simp [Instance.transProb]

lemma tp_succ (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (j : Fin (J + 1))
    (r : Fin R) : D.transProb Y i j r.succ = (1 - D.qExt j) * ∑ k : Fin J,
      D.q k / (1 - D.q k) * D.transProb Y i k.castSucc r.castSucc * Y i k.castSucc r.castSucc := by
  simp [Instance.transProb, Fin.induction_succ]

lemma P_eq_tp {X : Fin J → ℝ} {Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ}
    (hf : D.IsFeasible X Y P) : P = D.transProb Y := by
  funext i j s
  induction s using Fin.induction generalizing j with
  | zero => rw [hf.prob_zero, tp_zero]
  | succ t ih => rw [hf.prob_succ, tp_succ]; simp only [ih]

lemma tp_congr_lt (Y Y' : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (s : Fin (R + 1))
    (h : ∀ l (t : Fin (R + 1)), t < s → Y' i l t = Y i l t) :
    ∀ l, D.transProb Y' i l s = D.transProb Y i l s := by
  induction s using Fin.induction with
  | zero => intro l; rw [tp_zero, tp_zero]
  | succ t ih =>
    intro l
    rw [tp_succ, tp_succ]
    have ht : t.castSucc < t.succ := Fin.castSucc_lt_succ
    have ih' := ih (fun l u hu => h l u (lt_trans hu ht))
    simp only [ih', h _ _ ht]

lemma tp_feas {X : Fin J → ℝ} {Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ}
    (lv : ∀ i r, ∑ j, Y i j r + ∑ s ∈ Iio r, Y i (Fin.last J) s = 1)
    (oo : ∀ i (j : Fin J), ∑ r ∈ Iio (Fin.last R), Y i j.castSucc r ≤ X j)
    (eo : ∀ i, ∑ r, Y i (Fin.last J) r = 1)
    (xb : ∀ j, X j = 0 ∨ X j = 1) (yb : ∀ i j r, Y i j r = 0 ∨ Y i j r = 1) :
    D.IsFeasible X Y (D.transProb Y) :=
  ⟨lv, oo, eo, fun i j => tp_zero D Y i j, fun i j r => tp_succ D Y i j r, xb, yb⟩

lemma P_factor {X : Fin J → ℝ} {Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ}
    (hf : D.IsFeasible X Y P) (i : Fin I) (l : Fin (J + 1)) (s : Fin (R + 1)) :
    P i l s = (1 - D.qExt l) * P i (Fin.last J) s := by
  induction s using Fin.cases with
  | zero => rw [hf.prob_zero, hf.prob_zero, qExt_last]; ring
  | succ t => rw [hf.prob_succ, hf.prob_succ i (Fin.last J), qExt_last]; ring

section feas
variable {D}
variable {X : Fin J → ℝ} {Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ}

lemma Y_nn (hf : D.IsFeasible X Y P) (i l s) : 0 ≤ Y i l s := by
  rcases hf.Y_binary i l s with h | h <;> rw [h] <;> norm_num

lemma Y_unique (hf : D.IsFeasible X Y P) (i : Fin I) (a b : Fin (J + 1)) (s : Fin (R + 1))
    (ha : Y i a s = 1) (hab : b ≠ a) : Y i b s = 0 := by
  have h1 := hf.level_one i s
  have h2 : 0 ≤ ∑ t ∈ Iio s, Y i (Fin.last J) t := sum_nonneg (fun t _ => Y_nn hf _ _ _)
  have h3 : ∑ l ∈ ({a, b} : Finset _), Y i l s ≤ ∑ l, Y i l s :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun l _ _ => Y_nn hf _ _ _)
  rw [sum_pair (Ne.symm hab)] at h3
  linarith [Y_nn hf i b s]

lemma Y_after_emerg (hf : D.IsFeasible X Y P) (i : Fin I) (t s : Fin (R + 1))
    (ht : Y i (Fin.last J) t = 1) (hts : t < s) (l : Fin (J + 1)) : Y i l s = 0 := by
  have h1 := hf.level_one i s
  have h2 : Y i (Fin.last J) t ≤ ∑ u ∈ Iio s, Y i (Fin.last J) u :=
    single_le_sum (f := fun u => Y i (Fin.last J) u) (fun u _ => Y_nn hf _ _ _) (Finset.mem_Iio.mpr hts)
  have h3 : Y i l s ≤ ∑ l, Y i l s := single_le_sum (f := fun l => Y i l s) (fun l _ => Y_nn hf _ _ _) (mem_univ l)
  linarith [Y_nn hf i l s]

/-- no regular facility at the last level `R` -/
lemma Y_last_level (hf : D.IsFeasible X Y P) (i : Fin I) (k : Fin J) :
    Y i k.castSucc (Fin.last R) = 0 := by
  have h1 := hf.level_one i (Fin.last R)
  have h2 := hf.emergency_once i
  have hu : (insert (Fin.last R) (Iio (Fin.last R)) : Finset (Fin (R + 1))) = univ := by
    ext x; by_cases hx : x = Fin.last R
    · simp [hx]
    · simp only [mem_insert, mem_Iio, mem_univ, iff_true]; exact Or.inr (Fin.lt_last_iff_ne_last.mpr hx)
  rw [← hu, sum_insert (by simp)] at h2
  have h3 : ∑ l ∈ ({k.castSucc, Fin.last J} : Finset _), Y i l (Fin.last R) ≤
      ∑ l, Y i l (Fin.last R) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun l _ _ => Y_nn hf _ _ _)
  rw [sum_pair (Fin.castSucc_ne_last k)] at h3
  linarith [Y_nn hf i k.castSucc (Fin.last R)]
end feas

end RFL2Aux

open RFL2Aux in
theorem solution {I J R : ℕ} (D : Instance I J R) (X : Fin J → ℝ)
    (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (hfeas : D.IsFeasible X Y P)
    (i : Fin I) (j : Fin J) (r : Fin R)
    (hj : Y i j.castSucc r.castSucc = 1) (hJ : Y i (Fin.last J) r.succ = 1) :
    D.IsFeasible X (emergencyUpY i j.castSucc r Y)
        (D.transProb (emergencyUpY i j.castSucc r Y)) ∧
      D.objective X (emergencyUpY i j.castSucc r Y)
          (D.transProb (emergencyUpY i j.castSucc r Y)) - D.objective X Y P =
        D.lam i * P i j.castSucc r.castSucc * (D.phi i - D.d i j) := by
  have hP := P_eq_tp D hfeas
  subst hP
  have hrr : r.castSucc < r.succ := Fin.castSucc_lt_succ
  have hrne : r.castSucc ≠ r.succ := ne_of_lt hrr
  have hjL : j.castSucc ≠ Fin.last J := Fin.castSucc_ne_last j
  have F1 : Y i (Fin.last J) r.castSucc = 0 := Y_unique hfeas i _ _ _ hj (Ne.symm hjL)
  have F2 : ∀ l, l ≠ Fin.last J → Y i l r.succ = 0 := fun l hl => Y_unique hfeas i _ _ _ hJ hl
  have F3 : ∀ l s, r.succ < s → Y i l s = 0 := fun l s hs => Y_after_emerg hfeas i _ _ hJ hs l
  set δ : Fin (J + 1) → Fin (R + 1) → ℝ := fun l s =>
    (if l = Fin.last J then (if s = r.castSucc then 1 else 0) else 0)
    - (if l = j.castSucc then (if s = r.castSucc then 1 else 0) else 0)
    - (if l = Fin.last J then (if s = r.succ then 1 else 0) else 0) with hδ
  have hYd : ∀ h l s, emergencyUpY i j.castSucc r Y h l s = Y h l s + (if h = i then δ l s else 0) := by
    intro h l s
    by_cases hh : h = i
    · subst hh
      by_cases hl : l = Fin.last J
      · subst hl
        by_cases hs : s = r.castSucc
        · subst hs; simp [emergencyUpY, hδ, F1, hjL.symm, hrne]
        · by_cases hs2 : s = r.succ
          · subst hs2; simp [emergencyUpY, hδ, hJ, hjL.symm, hrne.symm]
          · simp [emergencyUpY, hδ, hs, hs2, hjL.symm]
      · by_cases hl2 : l = j.castSucc
        · subst hl2
          by_cases hs : s = r.castSucc
          · subst hs; simp [emergencyUpY, hδ, hj, hjL]
          · simp [emergencyUpY, hδ, hs, hjL]
        · simp [emergencyUpY, hδ, hl, hl2]
    · simp [emergencyUpY, hh]
  have hYb : ∀ h l s, emergencyUpY i j.castSucc r Y h l s = 0 ∨
      emergencyUpY i j.castSucc r Y h l s = 1 := by
    intro h l s
    simp only [emergencyUpY]
    split_ifs
    · right; rfl
    · left; rfl
    · exact hfeas.Y_binary h l s
  have hfe : D.IsFeasible X (emergencyUpY i j.castSucc r Y)
      (D.transProb (emergencyUpY i j.castSucc r Y)) := by
    refine tp_feas D ?_ ?_ ?_ hfeas.X_binary hYb
    · intro h s
      by_cases hh : h = i
      · subst hh
        simp only [hYd, if_true, sum_add_distrib]
        have e1 : ∑ l, δ l s = (if s = r.castSucc then 1 else 0) - (if s = r.castSucc then 1 else 0)
            - (if s = r.succ then 1 else 0) := by
          simp [hδ, sum_sub_distrib]
        have e2 : ∑ t ∈ Iio s, δ (Fin.last J) t =
            (if r.castSucc < s then 1 else 0) - (if r.succ < s then 1 else 0) := by
          simp [hδ, sum_sub_distrib, hjL.symm, sum_ite_eq']
        rw [e1, e2]
        have h0 := hfeas.level_one h s
        have key : (if r.castSucc < s then (1:ℝ) else 0) = (if s = r.succ then 1 else 0)
            + (if r.succ < s then 1 else 0) := by
          simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
          split_ifs <;> first | (exfalso; omega) | norm_num
        linarith
      · simpa [hYd, hh] using hfeas.level_one h s
    · intro h l
      refine le_trans (sum_le_sum fun t _ => ?_) (hfeas.open_only h l)
      rw [hYd]
      split_ifs with hh
      · have : δ l.castSucc t ≤ 0 := by
          simp only [hδ, Fin.castSucc_ne_last, if_false]
          split_ifs <;> norm_num
        linarith
      · simp
    · intro h
      by_cases hh : h = i
      · subst hh
        simp only [hYd, if_true, sum_add_distrib, hfeas.emergency_once]
        simp [hδ, sum_sub_distrib, hjL.symm]
      · simpa [hYd, hh] using hfeas.emergency_once h
  refine ⟨hfe, ?_⟩
  have hA : D.objective X (emergencyUpY i j.castSucc r Y)
      (D.transProb (emergencyUpY i j.castSucc r Y))
      = D.objective X (emergencyUpY i j.castSucc r Y) (D.transProb Y) := by
    unfold Instance.objective
    congr 1
    refine sum_congr rfl fun h _ => sum_congr rfl fun l _ => sum_congr rfl fun s _ => ?_
    by_cases hh : h = i
    · subst hh
      by_cases hs : s ≤ r.castSucc
      · rw [tp_congr_lt D Y (emergencyUpY h j.castSucc r Y) h s ?_ l]
        intro l' t ht
        rw [hYd]
        have h1 : t ≠ r.castSucc := ne_of_lt (lt_of_lt_of_le ht hs)
        have h2 : t ≠ r.succ := ne_of_lt (lt_trans (lt_of_lt_of_le ht hs) hrr)
        simp [hδ, h1, h2]
      · have hY0 : emergencyUpY h j.castSucc r Y h l s = 0 := by
          rw [hYd]
          push_neg at hs
          have h1 : s ≠ r.castSucc := ne_of_gt hs
          have h3 : r.succ ≤ s := Fin.castSucc_lt_iff_succ_le.mp hs
          rcases eq_or_lt_of_le h3 with h4 | h4
          · subst h4
            by_cases hl : l = Fin.last J
            · subst hl; simp [hδ, hJ, hrne.symm]
            · simp [hδ, F2 l hl, hl, hrne.symm]
          · have h2 : s ≠ r.succ := ne_of_gt h4
            simp [hδ, F3 l s h4, h1, h2]
        rw [hY0]; simp
    · rw [tp_congr_lt D Y (emergencyUpY i j.castSucc r Y) h s (fun l t _ => by rw [hYd]; simp [hh]) l]
  have hB : D.objective X (emergencyUpY i j.castSucc r Y) (D.transProb Y)
      - D.objective X Y (D.transProb Y)
      = ∑ l, ∑ s, D.lam i * D.dExt i l * D.transProb Y i l s * δ l s := by
    unfold Instance.objective
    rw [show ∀ a b c : ℝ, (a + b) - (a + c) = b - c from fun _ _ _ => by ring,
      ← sum_sub_distrib, sum_eq_single i]
    · simp only [← sum_sub_distrib]
      refine sum_congr rfl fun l _ => sum_congr rfl fun s _ => ?_
      rw [hYd]; simp only [if_true]; ring
    · intro h _ hh
      simp [hYd, hh]
    · simp
  rw [hA, hB]
  simp only [hδ, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_irrel,
    sum_const_zero, sum_ite_eq', mem_univ, if_true]
  rw [dExt_last, dExt_cs, tp_succ, qExt_last,
    sum_eq_single j (fun k _ hk => by
      rw [Y_unique hfeas i _ _ _ hj (fun h => hk (Fin.castSucc_injective _ h))]; ring)
      (by simp), hj, P_factor D hfeas i j.castSucc r.castSucc, qExt_cs]
  have hq1 : 1 - D.q j ≠ 0 := by linarith [D.q_lt_one j]
  field_simp
  ring
