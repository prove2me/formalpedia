-- Prove2me | solution 1 for ReliableFacilityLoc.LevelOrder.swap_cost_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:52:57.131484+00:00
-- url     : https://prove2.me/submissions/90be60da-7d46-4bb9-9d12-633e8dacf3a4

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
    (i : Fin I) (j k : Fin J) (r : Fin R)
    (hj : Y i j.castSucc r.castSucc = 1) (hk : Y i k.castSucc r.succ = 1) :
    D.IsFeasible X (swapY i j.castSucc k.castSucc r Y)
        (D.transProb (swapY i j.castSucc k.castSucc r Y)) ∧
      D.objective X (swapY i j.castSucc k.castSucc r Y)
          (D.transProb (swapY i j.castSucc k.castSucc r Y)) - D.objective X Y P =
        D.lam i * (1 - D.q k) * (D.d i k - D.d i j) * P i j.castSucc r.castSucc := by
  have hP := P_eq_tp D hfeas
  subst hP
  have hrr : r.castSucc < r.succ := Fin.castSucc_lt_succ
  have hrne : r.castSucc ≠ r.succ := ne_of_lt hrr
  have hjL : j.castSucc ≠ Fin.last J := Fin.castSucc_ne_last j
  have hkL : k.castSucc ≠ Fin.last J := Fin.castSucc_ne_last k
  have hRs : r.succ ≠ Fin.last R := by
    intro h
    have := Y_last_level hfeas i k
    rw [← h, hk] at this
    norm_num at this
  have hrsL : r.succ < Fin.last R := Fin.lt_last_iff_ne_last.mpr hRs
  have hrcL : r.castSucc < Fin.last R := lt_trans hrr hrsL
  have hjk : j.castSucc ≠ k.castSucc := by
    intro h
    have h1 := hfeas.open_only i j
    have h2 : ∑ t ∈ ({r.castSucc, r.succ} : Finset _), Y i j.castSucc t ≤
        ∑ t ∈ Iio (Fin.last R), Y i j.castSucc t :=
      sum_le_sum_of_subset_of_nonneg (by
        intro t ht; simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact mem_Iio.mpr hrcL
        · exact mem_Iio.mpr hrsL) (fun t _ _ => Y_nn hfeas _ _ _)
    have hk' : Y i j.castSucc r.succ = 1 := by rw [h]; exact hk
    rw [sum_pair hrne, hj, hk'] at h2
    rcases hfeas.X_binary j with hx | hx <;> rw [hx] at h1 <;> linarith
  have rowY0 : ∀ m, Y i m r.castSucc = if m = j.castSucc then 1 else 0 := fun m => by
    split_ifs with hm
    · rw [hm, hj]
    · exact Y_unique hfeas i _ _ _ hj hm
  have rowY1 : ∀ m, Y i m r.succ = if m = k.castSucc then 1 else 0 := fun m => by
    split_ifs with hm
    · rw [hm, hk]
    · exact Y_unique hfeas i _ _ _ hk hm
  set δ : Fin (J + 1) → Fin (R + 1) → ℝ := fun l s =>
    (if l = k.castSucc then (if s = r.castSucc then 1 else 0) else 0)
    + (if l = j.castSucc then (if s = r.succ then 1 else 0) else 0)
    - (if l = j.castSucc then (if s = r.castSucc then 1 else 0) else 0)
    - (if l = k.castSucc then (if s = r.succ then 1 else 0) else 0) with hδ
  set Y' := swapY i j.castSucc k.castSucc r Y with hY'
  have hYd : ∀ h l s, Y' h l s = Y h l s + (if h = i then δ l s else 0) := by
    intro h l s
    by_cases hh : h = i
    · subst hh
      by_cases hl : l = k.castSucc
      · subst hl
        by_cases hs : s = r.castSucc
        · subst hs; simp [hY', swapY, hδ, rowY0, hjk.symm, hrne]
        · by_cases hs2 : s = r.succ
          · subst hs2; simp [hY', swapY, hδ, hk, hjk.symm, hrne.symm]
          · simp [hY', swapY, hδ, hs, hs2, hjk.symm]
      · by_cases hl2 : l = j.castSucc
        · subst hl2
          by_cases hs : s = r.castSucc
          · subst hs; simp [hY', swapY, hδ, hj, hjk, hrne]
          · by_cases hs2 : s = r.succ
            · subst hs2; simp [hY', swapY, hδ, rowY1, hjk, hrne.symm]
            · simp [hY', swapY, hδ, hs, hs2, hjk]
        · simp [hY', swapY, hδ, hl, hl2]
    · simp [hY', swapY, hh]
  have hYb : ∀ h l s, Y' h l s = 0 ∨ Y' h l s = 1 := by
    intro h l s
    simp only [hY', swapY]
    split_ifs
    · right; rfl
    · left; rfl
    · exact hfeas.Y_binary h l s
  have hfe : D.IsFeasible X Y' (D.transProb Y') := by
    refine tp_feas D ?_ ?_ ?_ hfeas.X_binary hYb
    · intro h s
      by_cases hh : h = i
      · subst hh
        simp only [hYd, if_true, sum_add_distrib]
        have e1 : ∑ l, δ l s = 0 := by
          simp [hδ, sum_sub_distrib, sum_add_distrib]
        have e2 : ∑ t ∈ Iio s, δ (Fin.last J) t = 0 := by
          simp [hδ, hjL.symm, hkL.symm]
        rw [e1, e2]
        linarith [hfeas.level_one h s]
      · simpa [hYd, hh] using hfeas.level_one h s
    · intro h l
      by_cases hh : h = i
      · subst hh
        simp only [hYd, if_true, sum_add_distrib]
        have e : ∑ t ∈ Iio (Fin.last R), δ l.castSucc t = 0 := by
          have hex : ∃ a : Fin R, a.castSucc = r.succ := ⟨r.succ.castPred hRs, Fin.castSucc_castPred _ _⟩
          simp [hδ, sum_sub_distrib, sum_add_distrib, sum_ite_irrel, sum_ite_eq', hrcL, hrsL, hex]
        rw [e, add_zero]; exact hfeas.open_only h l
      · simpa [hYd, hh] using hfeas.open_only h l
    · intro h
      by_cases hh : h = i
      · subst hh
        simp only [hYd, if_true, sum_add_distrib, hfeas.emergency_once]
        simp [hδ, hjL.symm, hkL.symm]
      · simpa [hYd, hh] using hfeas.emergency_once h
  refine ⟨hfe, ?_⟩
  have rowY'0 : ∀ m, Y' i m r.castSucc = if m = k.castSucc then 1 else 0 := fun m => by
    rw [hYd, if_pos rfl, rowY0]
    by_cases h1 : m = k.castSucc
    · subst h1; simp [hδ, hjk.symm, hrne]
    · by_cases h2 : m = j.castSucc
      · subst h2; simp [hδ, hjk, hrne]
      · simp [hδ, h1, h2]
  have rowY'1 : ∀ m, Y' i m r.succ = if m = j.castSucc then 1 else 0 := fun m => by
    rw [hYd, if_pos rfl, rowY1]
    by_cases h1 : m = k.castSucc
    · subst h1; simp [hδ, hjk.symm, hrne.symm]
    · by_cases h2 : m = j.castSucc
      · subst h2; simp [hδ, hjk, hrne.symm]
      · simp [hδ, h1, h2]
  have hsame : ∀ l t, t ≠ r.castSucc → t ≠ r.succ → Y' i l t = Y i l t := fun l t h1 h2 => by
    rw [hYd]; simp [hδ, h1, h2]
  have E1 : ∀ s, s ≤ r.castSucc → ∀ l, D.transProb Y' i l s = D.transProb Y i l s := by
    intro s hs
    refine tp_congr_lt D Y Y' i s (fun l t ht => hsame l t ?_ ?_)
    · exact ne_of_lt (lt_of_lt_of_le ht hs)
    · exact ne_of_lt (lt_trans (lt_of_lt_of_le ht hs) hrr)
  set T := D.transProb Y i (Fin.last J) r.castSucc with hT
  have hq1 : ∀ m : Fin J, 1 - D.q m ≠ 0 := fun m => by linarith [D.q_lt_one m]
  have E2 : ∀ l, D.transProb Y' i l r.succ = (1 - D.qExt l) * (D.q k * T) := by
    intro l
    rw [tp_succ]
    simp only [E1 r.castSucc le_rfl, rowY'0, Fin.castSucc_inj, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, if_true]
    rw [P_factor D hfeas i k.castSucc r.castSucc, qExt_cs]
    field_simp [hq1 k]
    rfl
  have E3 : ∀ l, D.transProb Y i l r.succ = (1 - D.qExt l) * (D.q j * T) := by
    intro l
    rw [tp_succ]
    simp only [rowY0, Fin.castSucc_inj, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      if_true]
    rw [P_factor D hfeas i j.castSucc r.castSucc, qExt_cs]
    field_simp [hq1 j]
    rfl
  have E4 : ∀ s, r.succ < s → ∀ l, D.transProb Y' i l s = D.transProb Y i l s := by
    intro s
    induction s using Fin.induction with
    | zero => intro h; exact absurd h (Fin.not_lt_zero _)
    | succ t ih =>
      intro hlt l
      rw [tp_succ, tp_succ]
      by_cases ht : t.castSucc = r.succ
      · rw [ht]
        simp only [E2, E3, rowY1, rowY'1, Fin.castSucc_inj, mul_ite, mul_one, mul_zero,
          sum_ite_eq', mem_univ, if_true, qExt_cs]
        field_simp [hq1 j, hq1 k]
      · have hlt' : r.succ < t.castSucc := by
          rw [Fin.lt_iff_val_lt_val] at hlt ⊢
          have : (t.castSucc : ℕ) ≠ r.succ := fun h => ht (Fin.ext h)
          simp only [Fin.val_succ, Fin.coe_castSucc] at hlt this ⊢
          omega
        have hne1 : t.castSucc ≠ r.castSucc := ne_of_gt (lt_trans hrr hlt')
        simp only [ih hlt', hsame _ _ hne1 ht]
  have hA : D.objective X Y' (D.transProb Y') - D.objective X Y' (D.transProb Y)
      = D.lam i * D.dExt i j.castSucc *
        (D.transProb Y' i j.castSucc r.succ - D.transProb Y i j.castSucc r.succ) := by
    unfold Instance.objective
    rw [show ∀ a b c : ℝ, (a + b) - (a + c) = b - c from fun _ _ _ => by ring,
      ← sum_sub_distrib, sum_eq_single i]
    · simp only [← sum_sub_distrib]
      have hz : ∀ l s, ¬(l = j.castSucc ∧ s = r.succ) →
          D.lam i * D.dExt i l * D.transProb Y' i l s * Y' i l s
            - D.lam i * D.dExt i l * D.transProb Y i l s * Y' i l s = 0 := by
        intro l s hls
        rcases lt_trichotomy s r.succ with hs | hs | hs
        · rw [E1 s (Fin.le_castSucc_iff.mpr hs)]; ring
        · subst hs
          have hl : l ≠ j.castSucc := fun h => hls ⟨h, rfl⟩
          rw [rowY'1, if_neg hl]; ring
        · rw [E4 s hs]; ring
      rw [sum_eq_single j.castSucc, sum_eq_single r.succ]
      · rw [rowY'1, if_pos rfl]; ring
      · intro s _ hs; exact hz _ _ (fun h => hs h.2)
      · simp
      · intro l _ hl; exact sum_eq_zero (fun s _ => hz _ _ (fun h => hl h.1))
      · simp
    · intro h _ hh
      rw [← sum_sub_distrib]
      refine sum_eq_zero fun l _ => ?_
      rw [← sum_sub_distrib]
      refine sum_eq_zero fun s _ => ?_
      rw [tp_congr_lt D Y Y' h s (fun l t _ => by rw [hYd]; simp [hh]) l]; ring
    · simp
  have hB : D.objective X Y' (D.transProb Y) - D.objective X Y (D.transProb Y)
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
  rw [show D.objective X Y' (D.transProb Y') - D.objective X Y (D.transProb Y) =
    (D.objective X Y' (D.transProb Y') - D.objective X Y' (D.transProb Y)) +
    (D.objective X Y' (D.transProb Y) - D.objective X Y (D.transProb Y)) by ring, hA, hB]
  simp only [hδ, mul_add, mul_sub, mul_ite, mul_one, mul_zero, sum_add_distrib, sum_sub_distrib,
    sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, if_true]
  rw [E2, E3, E3, P_factor D hfeas i j.castSucc r.castSucc,
    P_factor D hfeas i k.castSucc r.castSucc, dExt_cs, dExt_cs, qExt_cs, qExt_cs]
  ring
