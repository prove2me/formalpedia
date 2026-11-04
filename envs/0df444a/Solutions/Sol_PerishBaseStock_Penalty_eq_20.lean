-- Prove2me | solution 1 for PerishBaseStock.Penalty.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:25:35.255497+00:00
-- url     : https://prove2.me/submissions/5f6a210c-88e1-4b29-9866-f7e73316b3fb

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyEq20Aux
open PerishBaseStock.Penalty PerishBaseStock.Lifetime

variable {m : ℕ}

lemma level_lt (x : State m) (q q' : ℝ≥0) {i : ℕ} (him : i < m) :
    level x q i = level x q' i := by
  by_cases h0 : i = 0
  · simp [level, h0]
  · simp [level, h0, him]

lemma level_top (x : State m) (q : ℝ≥0) (hm : 1 ≤ m) : level x q m = topLevel x + q := by
  rw [level, dif_neg (by omega), dif_neg (lt_irrefl m)]

lemma topLevel_eq (x : State m) (q : ℝ≥0) (hm : 2 ≤ m) : topLevel x = level x q (m - 1) := by
  rw [level, dif_neg (by omega : m - 1 ≠ 0), dif_pos (by omega : m - 1 < m), topLevel,
    dif_pos (by omega : 0 < m - 1)]
  exact congrArg x (Fin.ext (by simp only; omega))

lemma firstLevel_eq (x : State m) (q : ℝ≥0) (hm : 1 ≤ m) : firstLevel x q = level x q 1 := by
  by_cases h : 0 < m - 1
  · rw [firstLevel, dif_pos h, level, dif_neg (by omega), dif_pos (by omega : 1 < m)]
  · rw [firstLevel, dif_neg h, level, dif_neg (by omega), dif_neg (by omega : ¬ 1 < m)]
    rfl

lemma outdate_eq (x : State m) (q d : ℝ≥0) (hm : 1 ≤ m) :
    outdate x q d = max (level x q 1 - d) 0 := by
  unfold outdate
  rw [firstLevel_eq x q hm]

lemma level_step (x : State m) (q q' d : ℝ≥0) {i : ℕ} (hi1 : 1 ≤ i) (him : i < m) :
    level (step x q d) q' i = max (level x q (i + 1) - max (level x q 1) d) 0 := by
  have hm : 1 ≤ m := by omega
  have hab : level x q (i + 1) = levelAbove x q ⟨i - 1, by omega⟩ := by
    by_cases h : i + 1 < m
    · rw [level, dif_neg (by omega), dif_pos h, levelAbove, dif_pos (by simp only; omega)]
      exact congrArg x (Fin.ext (by simp only; omega))
    · rw [level, dif_neg (by omega), dif_neg h, levelAbove, dif_neg (by simp only; omega)]
      rfl
  have hlev : level (step x q d) q' i = step x q d ⟨i - 1, by omega⟩ := by
    rw [level, dif_neg (by omega), dif_pos him]
  rw [hlev, hab]
  unfold step
  rw [outdate_eq x q d hm]
  congr 1
  rcases le_total (level x q 1) d with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring


lemma g_inc_le {u w : ℝ} (hw : 0 ≤ w) : max (u + w) 0 - max u 0 ≤ w := by
  rcases le_total u 0 with h | h <;> rcases le_total (u + w) 0 with h' | h' <;>
    simp [max_eq_left, max_eq_right, h, h'] <;> linarith

lemma g_inc_nonneg {u w : ℝ} (hw : 0 ≤ w) : 0 ≤ max (u + w) 0 - max u 0 := by
  have : max u 0 ≤ max (u + w) 0 := max_le_max (by linarith) le_rfl
  linarith

lemma g_inc_mono {u u' w w' : ℝ} (hu : u ≤ u') (hw : 0 ≤ w) (hww : w ≤ w') :
    max (u + w) 0 - max u 0 ≤ max (u' + w') 0 - max u' 0 := by
  rcases le_total u 0 with h1 | h1 <;> rcases le_total (u + w) 0 with h2 | h2 <;>
    rcases le_total u' 0 with h3 | h3 <;> rcases le_total (u' + w') 0 with h4 | h4 <;>
    simp only [max_eq_left, max_eq_right, h1, h2, h3, h4] <;> linarith

lemma max_sub_max_le {a b d : ℝ} (h : a ≤ b) : max b d - max a d ≤ b - a := by
  rcases le_total a d with h1 | h1 <;> rcases le_total b d with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith

lemma max_sub_max_nonneg {a b d : ℝ} (h : a ≤ b) : 0 ≤ max b d - max a d := by
  have : max a d ≤ max b d := max_le_max h le_rfl
  linarith

/-- `x^S_{t,i}` along the path `d` under the base-stock policy `π_S`. -/
def A (m : ℕ) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t i : ℕ) : ℝ :=
  level (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t)
    (orderQty (baseStockPolicy m S) d t) i

lemma A_top (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    A m S d t m = max (S : ℝ) (topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t)) := by
  unfold A
  rw [level_top _ _ hm]
  have hq : ((orderQty (baseStockPolicy m S) d t : ℝ≥0) : ℝ) =
      max ((S : ℝ) - topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t)) 0 :=
    Real.coe_toNNReal' _
  rw [hq]
  rcases le_total (S : ℝ) (topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t)) with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

lemma A_succ (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i < m) :
    A m S d (t + 1) i = max (A m S d t (i + 1) - max (A m S d t 1) (d t)) 0 := by
  unfold A
  exact level_step _ _ _ _ hi1 him

lemma A_zero (S : ℝ≥0) (d : CappedBaseStock.DemandPath) {i : ℕ} (him : i < m) :
    A m S d 0 i = 0 := by
  unfold A
  by_cases h0 : i = 0
  · simp [level, h0]
  · simp [level, h0, him, PerishBaseStock.Penalty.run, emptyState]

lemma top_zero (S : ℝ≥0) (d : CappedBaseStock.DemandPath) :
    topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d 0) = 0 := by
  simp only [topLevel, PerishBaseStock.Penalty.run, emptyState]
  split_ifs <;> rfl

lemma top_succ_le (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m)
    (hS : A m S d t m = S) :
    topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d (t + 1)) ≤ S := by
  by_cases h2 : 2 ≤ m
  · rw [topLevel_eq _ (orderQty (baseStockPolicy m S) d (t + 1)) h2]
    have := A_succ (m := m) S d t (i := m - 1) (by omega) (by omega)
    unfold A at this
    rw [this, show m - 1 + 1 = m by omega]
    unfold A at hS
    rw [hS]
    apply max_le _ (NNReal.coe_nonneg S)
    have : (0 : ℝ) ≤ max (level (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t)
      (orderQty (baseStockPolicy m S) d t) 1) (d t) :=
      le_trans (NNReal.coe_nonneg _) (le_max_right _ _)
    linarith
  · simp only [topLevel]
    rw [dif_neg (by omega)]
    exact NNReal.coe_nonneg S

/-- Single-policy invariant: `x_{t,m-1} ≤ S` and the levels are nondecreasing. -/
lemma inv (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (hm : 1 ≤ m) : ∀ t : ℕ,
    topLevel (PerishBaseStock.Penalty.run (baseStockPolicy m S) d t) ≤ S ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ m → A m S d t i ≤ A m S d t j := by
  intro t
  induction t with
  | zero =>
    refine ⟨by rw [top_zero]; exact NNReal.coe_nonneg S, fun i j hi hij hj => ?_⟩
    have htop : A m S d 0 m = S := by rw [A_top S d 0 hm, top_zero]; simp
    rcases Nat.lt_or_ge j m with hjm | hjm
    · rw [A_zero S d (by omega), A_zero S d hjm]
    · rw [show j = m by omega, htop]
      rcases Nat.lt_or_ge i m with him | him
      · rw [A_zero S d him]; exact NNReal.coe_nonneg S
      · rw [show i = m by omega, htop]
  | succ t ih =>
    obtain ⟨htop, hmono⟩ := ih
    have hSt : A m S d t m = S := by rw [A_top S d t hm]; exact max_eq_left htop
    have htop' := top_succ_le S d t hm hSt
    have hSt' : A m S d (t + 1) m = S := by rw [A_top S d (t + 1) hm]; exact max_eq_left htop'
    have hM : (0 : ℝ) ≤ max (A m S d t 1) (d t) :=
      le_trans (NNReal.coe_nonneg _) (le_max_right _ _)
    refine ⟨htop', fun i j hi hij hj => ?_⟩
    rcases Nat.lt_or_ge j m with hjm | hjm
    · rw [A_succ S d t hi (by omega), A_succ S d t (by omega) hjm]
      exact max_le_max (by linarith [hmono (i + 1) (j + 1) (by omega) (by omega) (by omega)]) le_rfl
    · rw [show j = m by omega, hSt']
      rcases Nat.lt_or_ge i m with him | him
      · rw [A_succ S d t hi him]
        apply max_le _ (NNReal.coe_nonneg S)
        have := hmono (i + 1) m (by omega) (by omega) le_rfl
        linarith
      · rw [show i = m by omega, hSt']



lemma gg {a b : ℝ} (hb : 0 ≤ b) : max (max a 0 - b) 0 = max (a - b) 0 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h]

lemma gg2 {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    max (max a 0 - b - c) 0 = max (a - b - c) 0 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h]

lemma max_eq_add_g (a d : ℝ) : max a d = d + max (a - d) 0 := by
  rcases le_total a d with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- `x^π_{t,i}` along the path `d`. -/
def Lv (π : Policy m) (d : CappedBaseStock.DemandPath) (t i : ℕ) : ℝ :=
  level (PerishBaseStock.Penalty.run π d t) (orderQty π d t) i

/-- `o^π_t`. -/
abbrev o (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  PerishBaseStock.Penalty.outdated π d t

lemma o_eq (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    o π d t = max (Lv π d t 1 - d t) 0 := by
  unfold o PerishBaseStock.Penalty.outdated Lv
  exact outdate_eq _ _ _ hm

lemma o_nonneg (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : 0 ≤ o π d t := by
  unfold o PerishBaseStock.Penalty.outdated outdate
  exact le_max_right _ _

lemma Lv_succ (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i < m) :
    Lv π d (t + 1) i = max (Lv π d t (i + 1) - d t - o π d t) 0 := by
  have hm : 1 ≤ m := by omega
  unfold Lv
  rw [show PerishBaseStock.Penalty.run π d (t + 1) = step (PerishBaseStock.Penalty.run π d t)
    (orderQty π d t) (d t) from rfl, level_step _ _ _ _ hi1 him]
  have := o_eq π d t hm
  unfold Lv at this
  rw [this, max_eq_add_g (level (PerishBaseStock.Penalty.run π d t) (orderQty π d t) 1) (d t)]
  congr 1; ring

lemma totalLevel_eq (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    totalLevel π d t = Lv π d t m := by
  unfold Lv totalLevel
  rw [level_top _ _ hm]
  rfl

/-- Iterating the FIFO recursion along one cohort. -/
lemma iter (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ∀ k, 1 ≤ k → k ≤ m - 1 → Lv π d (t + k) (m - k) =
      max (Lv π d t m - ∑ i ∈ Finset.range k, (d (t + i) : ℝ) -
        ∑ j ∈ Finset.range k, o π d (t + j)) 0 := by
  intro k hk1 hkm
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [Lv_succ π d t (by omega) (by omega), show m - (0 + 1) + 1 = m by omega]
      simp
    · have ih' := ih hpos (by omega)
      rw [show t + (k + 1) = (t + k) + 1 by ring,
        Lv_succ π d (t + k) (by omega) (by omega), show m - (k + 1) + 1 = m - k by omega, ih',
        Finset.sum_range_succ, Finset.sum_range_succ]
      rw [gg2 (NNReal.coe_nonneg (d (t + k))) (o_nonneg π d (t + k))]
      congr 1; ring

/-- Recursion (19). -/
lemma rec19 (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    o π d (t + (m - 1)) = max (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) -
      ∑ j ∈ Finset.range (m - 1), o π d (t + j)) 0 := by
  rw [o_eq π d _ hm]
  by_cases h2 : 2 ≤ m
  · have := iter π d t (m - 1) (by omega) le_rfl
    rw [show m - (m - 1) = 1 by omega] at this
    rw [this, gg (NNReal.coe_nonneg _)]
    have hs : ∑ i ∈ Finset.range m, (d (t + i) : ℝ) =
        ∑ i ∈ Finset.range (m - 1), (d (t + i) : ℝ) + (d (t + (m - 1)) : ℝ) := by
      rw [← Finset.sum_range_succ (fun i => (d (t + i) : ℝ)), show m - 1 + 1 = m by omega]
    rw [hs]
    congr 1; ring
  · have h1 : m = 1 := by omega
    subst h1
    simp

/-- Starting empty, nothing outdates before period `m - 1`. -/
lemma early (π : Policy m) (d : CappedBaseStock.DemandPath) :
    ∀ t i, 1 ≤ i → i + t ≤ m - 1 → Lv π d t i = 0 := by
  intro t
  induction t with
  | zero =>
    intro i hi hit
    unfold Lv
    have him : i < m := by omega
    simp [level, show i ≠ 0 by omega, him, PerishBaseStock.Penalty.run, emptyState]
  | succ t ih =>
    intro i hi hit
    rw [Lv_succ π d t hi (by omega), ih (i + 1) (by omega) (by omega)]
    have := o_nonneg π d t
    have := NNReal.coe_nonneg (d t)
    rw [max_eq_right (by linarith)]

lemma o_early (π : Policy m) (d : CappedBaseStock.DemandPath) (hm : 1 ≤ m) (t : ℕ)
    (ht : t + 1 < m) : o π d t = 0 := by
  rw [o_eq π d t hm, early π d t 1 le_rfl (by omega)]
  have := NNReal.coe_nonneg (d t)
  rw [max_eq_right (by linarith)]

/-- The cumulative-outdating recursion. -/
lemma F_succ (π : Policy m) (d : CappedBaseStock.DemandPath) (hm : 1 ≤ m) (t : ℕ) :
    ∑ j ∈ Finset.range (t + (m - 1) + 1), o π d j =
      max (∑ j ∈ Finset.range (t + (m - 1)), o π d j)
        (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) + ∑ j ∈ Finset.range t, o π d j) := by
  rw [Finset.sum_range_succ, rec19 π d t hm]
  have hsplit := Finset.sum_range_add (o π d) t (m - 1)
  rw [hsplit]
  set A := ∑ j ∈ Finset.range t, o π d j
  set B := ∑ j ∈ Finset.range (m - 1), o π d (t + j)
  rcases le_total (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) - B) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

end PerishPenaltyEq20Aux

open PerishBaseStock.Penalty PerishPenaltyEq20Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (hπ : ∀ t : ℕ, (floorLevel c P : ℝ) ≤ totalLevel π d t)
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, outdated (baseStockPolicy c.m (floorLevel c P)) d t ≤
      ∑ t ∈ Finset.range T, outdated π d t := by
  have hm := hc.one_le_m
  set Sl := floorLevel c P
  have hσ : ∀ t, Lv (baseStockPolicy c.m Sl) d t c.m = Sl := by
    intro t
    show A c.m Sl d t c.m = Sl
    rw [A_top Sl d t hm]
    exact max_eq_left (inv Sl d hm t).1
  have hπ' : ∀ t, (Sl : ℝ) ≤ Lv π d t c.m := fun t => by
    rw [← totalLevel_eq π d t hm]; exact hπ t
  have key : ∀ n, ∑ j ∈ Finset.range n, o (baseStockPolicy c.m Sl) d j ≤
      ∑ j ∈ Finset.range n, o π d j := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | k
      · simp
      · by_cases hk : k + 1 < c.m
        · have h0 : ∑ j ∈ Finset.range (k + 1), o (baseStockPolicy c.m Sl) d j = 0 :=
            Finset.sum_eq_zero (fun j hj => o_early _ d hm j
              (by have := Finset.mem_range.1 hj; omega))
          rw [h0]
          exact Finset.sum_nonneg (fun j _ => o_nonneg π d j)
        · obtain ⟨t, rfl⟩ : ∃ t, k = t + (c.m - 1) := ⟨k - (c.m - 1), by omega⟩
          rw [F_succ _ d hm t, F_succ π d hm t, hσ t]
          have h1 := ih (t + (c.m - 1)) (by omega)
          have h2 := ih t (by omega)
          have h3 := hπ' t
          exact max_le_max h1 (by linarith)
  exact key T
