-- Prove2me | solution 1 for PerishBaseStock.Lifetime.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:56:25.999178+00:00
-- url     : https://prove2.me/submissions/d2eb7416-af0e-499f-88bc-fbb8a296d0a4

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishLifetimeProp2Aux
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


lemma topLevel_cont : Continuous (fun x : State m => topLevel x) := by
  unfold topLevel
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma outdate_cont :
    Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => outdate p.1 p.2.1 p.2.2) := by
  unfold outdate firstLevel orderUpTo
  split_ifs
  · exact ((((continuous_apply _).comp continuous_fst).sub
      (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).max continuous_const)
  · exact ((((topLevel_cont.comp continuous_fst).add
      (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd))).sub
      (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).max continuous_const)

lemma step_cont :
    Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => step p.1 p.2.1 p.2.2) := by
  refine continuous_pi (fun j => ?_)
  have hla : Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => levelAbove p.1 p.2.1 j) := by
    unfold levelAbove orderUpTo
    split_ifs
    · exact (continuous_apply _).comp continuous_fst
    · exact (topLevel_cont.comp continuous_fst).add
        (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd))
  exact ((hla.sub (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).sub
    outdate_cont).max continuous_const

lemma run_meas (π : Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => PerishBaseStock.Penalty.run π d t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h : Measurable (fun d : CappedBaseStock.DemandPath =>
        (PerishBaseStock.Penalty.run π d t, π.φ t (PerishBaseStock.Penalty.run π d t), d t)) :=
      ih.prodMk (((π.measurable_φ t).comp ih).prodMk (measurable_pi_apply t))
    exact step_cont.measurable.comp h

lemma outdated_meas (π : Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => PerishBaseStock.Penalty.outdated π d t) := by
  have h : Measurable (fun d : CappedBaseStock.DemandPath =>
      (PerishBaseStock.Penalty.run π d t, π.φ t (PerishBaseStock.Penalty.run π d t), d t)) :=
    (run_meas π t).prodMk (((π.measurable_φ t).comp (run_meas π t)).prodMk (measurable_pi_apply t))
  exact outdate_cont.measurable.comp h


/-! ### Bridge to the `Lifetime` formalization -/

lemma run_eq (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    PerishBaseStock.Penalty.run π d t = PerishBaseStock.Lifetime.run π d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (PerishBaseStock.Penalty.run π d t) (π.φ t (PerishBaseStock.Penalty.run π d t)) (d t) =
      step (runFrom (emptyState m) π d t) (π.φ t (runFrom (emptyState m) π d t)) (d t)
    rw [ih]; rfl

lemma upTo_eq (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    upTo π d t = Lv π d t m := by
  rw [← totalLevel_eq π d t hm]
  unfold upTo totalLevel orderQty
  rw [run_eq]

lemma outdated_eq' (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    PerishBaseStock.Lifetime.outdated π d t = o π d t := by
  unfold PerishBaseStock.Lifetime.outdated outdateFrom o PerishBaseStock.Penalty.outdated orderQty
  rw [run_eq]
  rfl

/-! ### Pathwise inequalities (15)-(16) -/

lemma eq15 (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    max (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0 ≤
      ∑ j ∈ Finset.range m, o π d (t + j) := by
  have h := rec19 π d t hm
  have hs : ∑ j ∈ Finset.range m, o π d (t + j) =
      ∑ j ∈ Finset.range (m - 1), o π d (t + j) + o π d (t + (m - 1)) := by
    rw [← Finset.sum_range_succ (fun j => o π d (t + j)), show m - 1 + 1 = m by omega]
  rw [hs, h]
  have hB : 0 ≤ ∑ j ∈ Finset.range (m - 1), o π d (t + j) :=
    Finset.sum_nonneg (fun j _ => o_nonneg π d _)
  apply max_le
  · have := le_max_left (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) -
      ∑ j ∈ Finset.range (m - 1), o π d (t + j)) 0
    linarith
  · have := le_max_right (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) -
      ∑ j ∈ Finset.range (m - 1), o π d (t + j)) 0
    linarith

lemma eq16 (π : Policy m) (d : CappedBaseStock.DemandPath) (T : ℕ) (hm : 1 ≤ m) :
    ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range m, o π d (t + j) ≤
      (m : ℝ) * ∑ n ∈ Finset.range (T + (m - 1)), o π d n := by
  rw [Finset.sum_comm]
  calc ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range T, o π d (t + j)
      ≤ ∑ _j ∈ Finset.range m, ∑ n ∈ Finset.range (T + (m - 1)), o π d n := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.1 hj
        have h1 := Finset.sum_range_add (o π d) j T
        have h2 : ∑ t ∈ Finset.range T, o π d (t + j) = ∑ t ∈ Finset.range T, o π d (j + t) :=
          Finset.sum_congr rfl (fun t _ => by rw [add_comm])
        have h3 : 0 ≤ ∑ n ∈ Finset.range j, o π d n := Finset.sum_nonneg (fun n _ => o_nonneg π d n)
        have h4 : ∑ n ∈ Finset.range (j + T), o π d n ≤ ∑ n ∈ Finset.range (T + (m - 1)), o π d n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            (fun n _ _ => o_nonneg π d n)
        linarith
    _ = (m : ℝ) * ∑ n ∈ Finset.range (T + (m - 1)), o π d n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Real-valued period cost `C_t`. -/
def cr (h p θ : ℝ) (π : Policy m) (d : CappedBaseStock.DemandPath) (n : ℕ) : ℝ :=
  h * max (Lv π d n m - d n) 0 + p * max ((d n : ℝ) - Lv π d n m) 0 + θ * o π d n

/-- The integrand of (17). -/
def phi (h p θ : ℝ) (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  h * max (Lv π d t m - d t) 0 + p * max ((d t : ℝ) - Lv π d t m) 0 +
    θ / m * max (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0

lemma phi_nonneg {h p θ : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (π : Policy m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) : 0 ≤ phi h p θ π d t := by
  unfold phi
  have := mul_nonneg hh (le_max_right (Lv π d t m - d t) 0)
  have := mul_nonneg hp (le_max_right ((d t : ℝ) - Lv π d t m) 0)
  have := mul_nonneg (div_nonneg hθ (Nat.cast_nonneg m))
    (le_max_right (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0)
  linarith

lemma cr_nonneg {h p θ : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (π : Policy m)
    (d : CappedBaseStock.DemandPath) (n : ℕ) : 0 ≤ cr h p θ π d n := by
  unfold cr
  have := mul_nonneg hh (le_max_right (Lv π d n m - d n) 0)
  have := mul_nonneg hp (le_max_right ((d n : ℝ) - Lv π d n m) 0)
  have := mul_nonneg hθ (o_nonneg π d n)
  linarith

/-- Pathwise form of (17). -/
lemma path17 {h p θ : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (π : Policy m)
    (d : CappedBaseStock.DemandPath) (T : ℕ) (hm : 1 ≤ m) :
    ∑ t ∈ Finset.range T, phi h p θ π d t ≤ ∑ n ∈ Finset.range (T + (m - 1)), cr h p θ π d n := by
  set a : ℕ → ℝ := fun n => h * max (Lv π d n m - d n) 0 + p * max ((d n : ℝ) - Lv π d n m) 0
  have ha : ∀ n, 0 ≤ a n := fun n => by
    have := mul_nonneg hh (le_max_right (Lv π d n m - d n) 0)
    have := mul_nonneg hp (le_max_right ((d n : ℝ) - Lv π d n m) 0)
    simp only [a]; linarith
  have hphi : ∀ t, phi h p θ π d t = a t + θ / m *
      max (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0 := fun t => rfl
  have hcr : ∀ n, cr h p θ π d n = a n + θ * o π d n := fun n => rfl
  simp only [hphi, hcr, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ t ∈ Finset.range T, a t ≤ ∑ n ∈ Finset.range (T + (m - 1)), a n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun n _ _ => ha n)
  have h2 : ∑ t ∈ Finset.range T, max (Lv π d t m - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0 ≤
      (m : ℝ) * ∑ n ∈ Finset.range (T + (m - 1)), o π d n :=
    (Finset.sum_le_sum (fun t _ => eq15 π d t hm)).trans (eq16 π d T hm)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : θ / m * ∑ t ∈ Finset.range T, max (Lv π d t m - ∑ i ∈ Finset.range m,
      (d (t + i) : ℝ)) 0 ≤ θ * ∑ n ∈ Finset.range (T + (m - 1)), o π d n := by
    have := mul_le_mul_of_nonneg_left h2 (div_nonneg hθ hmR.le)
    calc _ ≤ θ / m * ((m : ℝ) * ∑ n ∈ Finset.range (T + (m - 1)), o π d n) := this
      _ = _ := by field_simp
  linarith


/-! ### Dependence on the past only -/

lemma run_congr (π : Policy m) (t : ℕ) (d e : CappedBaseStock.DemandPath)
    (h : ∀ i < t, d i = e i) :
    PerishBaseStock.Penalty.run π d t = PerishBaseStock.Penalty.run π e t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (PerishBaseStock.Penalty.run π d t) (π.φ t (PerishBaseStock.Penalty.run π d t)) (d t) =
      step (PerishBaseStock.Penalty.run π e t) (π.φ t (PerishBaseStock.Penalty.run π e t)) (e t)
    rw [ih (fun i hi => h i (by omega)), h t (by omega)]

/-- Complete a history of length `t` by zeros. -/
def ext (t : ℕ) (u : (Finset.range t) → ℝ≥0) : CappedBaseStock.DemandPath :=
  fun i => if hi : i ∈ Finset.range t then u ⟨i, hi⟩ else 0

lemma ext_meas (t : ℕ) : Measurable (ext t) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  unfold ext
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma Lv_top_eq (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    Lv π d t m = topLevel (PerishBaseStock.Penalty.run π d t) +
      ((π.φ t (PerishBaseStock.Penalty.run π d t) : ℝ≥0) : ℝ) := by
  unfold Lv; rw [level_top _ _ hm]; rfl

lemma Lv_meas (π : Policy m) (t : ℕ) (hm : 1 ≤ m) :
    Measurable (fun d : CappedBaseStock.DemandPath => Lv π d t m) := by
  have : (fun d : CappedBaseStock.DemandPath => Lv π d t m) = fun d =>
      topLevel (PerishBaseStock.Penalty.run π d t) +
        ((π.φ t (PerishBaseStock.Penalty.run π d t) : ℝ≥0) : ℝ) := by
    funext d; exact Lv_top_eq π d t hm
  rw [this]
  exact (topLevel_cont.measurable.comp (run_meas π t)).add
    (measurable_coe_nnreal_real.comp ((π.measurable_φ t).comp (run_meas π t)))

lemma run_nonneg (π : Policy m) (d : CappedBaseStock.DemandPath) :
    ∀ t j, 0 ≤ PerishBaseStock.Penalty.run π d t j := by
  intro t
  induction t with
  | zero => intro j; exact le_rfl
  | succ t _ =>
    intro j
    show 0 ≤ step _ _ _ j
    unfold step
    exact le_max_right _ _

lemma Lv_nonneg (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    0 ≤ Lv π d t m := by
  rw [Lv_top_eq π d t hm]
  have h1 : 0 ≤ topLevel (PerishBaseStock.Penalty.run π d t) := by
    unfold topLevel
    split_ifs
    · exact run_nonneg π d t _
    · exact le_rfl
  have := NNReal.coe_nonneg (π.φ t (PerishBaseStock.Penalty.run π d t))
  linarith

lemma Lv_congr (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lv π d t m = Lv π (ext t ((Finset.range t).restrict d)) t m := by
  have h := run_congr π t d (ext t ((Finset.range t).restrict d)) (fun i hi => by
    simp [ext, Finset.mem_range.2 hi, Finset.restrict])
  unfold Lv orderQty
  rw [h]

end PerishLifetimeProp2Aux

namespace PerishLifetimeProp2Aux2
open PerishBaseStock.Penalty PerishBaseStock.Lifetime PerishLifetimeProp2Aux

lemma memIco (c : PerishBaseStock.Lifetime.Params) (t : ℕ) : t ∈ Finset.Ico t (t + c.m) :=
  Finset.mem_Ico.2 ⟨le_rfl, by have := c.one_le_m; omega⟩

/-- The integrand of (17) as a function of the order-up-to level and the next `m` demands. -/
def Psi (c : PerishBaseStock.Lifetime.Params) (t : ℕ) (x : ℝ)
    (y : (Finset.Ico t (t + c.m)) → ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (x - y ⟨t, memIco c t⟩) 0 + c.p * max ((y ⟨t, memIco c t⟩ : ℝ) - x) 0 +
    c.θ / c.m * max (x - ∑ i, (y i : ℝ)) 0)

lemma Psi_cont (c : PerishBaseStock.Lifetime.Params) (t : ℕ) :
    Continuous (fun q : ℝ × ((Finset.Ico t (t + c.m)) → ℝ≥0) => Psi c t q.1 q.2) := by
  unfold Psi
  apply ENNReal.continuous_ofReal.comp
  have hy : Continuous (fun q : ℝ × ((Finset.Ico t (t + c.m)) → ℝ≥0) =>
      ((q.2 ⟨t, memIco c t⟩ : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp ((continuous_apply _).comp continuous_snd)
  have hs : Continuous (fun q : ℝ × ((Finset.Ico t (t + c.m)) → ℝ≥0) =>
      ∑ i, ((q.2 i : ℝ≥0) : ℝ)) :=
    continuous_finsetSum _ (fun i _ => NNReal.continuous_coe.comp ((continuous_apply i).comp continuous_snd))
  exact (((continuous_const.mul ((continuous_fst.sub hy).max continuous_const)).add
    (continuous_const.mul ((hy.sub continuous_fst).max continuous_const))).add
    (continuous_const.mul ((continuous_fst.sub hs).max continuous_const)))

lemma Psi_meas (c : PerishBaseStock.Lifetime.Params) (t : ℕ) {α : Type*} [MeasurableSpace α]
    {X : α → ℝ} {Y : α → ((Finset.Ico t (t + c.m)) → ℝ≥0)} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun a => Psi c t (X a) (Y a)) := by
  unfold Psi
  have hy : Measurable (fun a => ((Y a ⟨t, memIco c t⟩ : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp ((measurable_pi_apply _).comp hY)
  have hs : Measurable (fun a => ∑ i, ((Y a i : ℝ≥0) : ℝ)) :=
    Finset.measurable_sum _ (fun i _ => measurable_coe_nnreal_real.comp ((measurable_pi_apply i).comp hY))
  exact ENNReal.measurable_ofReal.comp
    (((measurable_const.mul ((hX.sub hy).max measurable_const)).add
    (measurable_const.mul ((hy.sub hX).max measurable_const))).add
    (measurable_const.mul ((hX.sub hs).max measurable_const)))

lemma phi_eq_Psi (c : PerishBaseStock.Lifetime.Params) (π : Policy c.m) (d : CappedBaseStock.DemandPath)
    (t : ℕ) :
    ENNReal.ofReal (phi c.h c.p c.θ π d t) =
      Psi c t (Lv π d t c.m) ((Finset.Ico t (t + c.m)).restrict d) := by
  unfold phi Psi
  congr 3
  have : ∑ i : (Finset.Ico t (t + c.m)), (((Finset.Ico t (t + c.m)).restrict d i : ℝ≥0) : ℝ) =
      ∑ i ∈ Finset.Ico t (t + c.m), (d i : ℝ) := by
    simp only [Finset.restrict]
    exact Finset.sum_coe_sort (Finset.Ico t (t + c.m)) (fun i => (d i : ℝ))
  rw [this, Finset.sum_Ico_eq_sum_range, show t + c.m - t = c.m by omega]

lemma int_hold' (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun x : ℝ≥0 => max (s - (x : ℝ)) 0) μ := by
  refine Integrable.mono' (integrable_const |s|) ?_ (Eventually.of_forall (fun x => ?_))
  · exact ((continuous_const.sub NNReal.continuous_coe).max continuous_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := NNReal.coe_nonneg x; have := le_abs_self s; linarith) (abs_nonneg s)

lemma leadTimeLaw_prob' (P : CappedBaseStock.DemandLaw) (τ : ℕ) :
    IsProbabilityMeasure (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P τ) := by
  unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
  exact Measure.isProbabilityMeasure_map
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)).aemeasurable

/-- `∫⁻ ofReal (a * g(D_t))` over the path law. -/
lemma coord_lint (P : CappedBaseStock.DemandLaw) (t : ℕ) (a : ℝ) (ha : 0 ≤ a) (g : ℝ≥0 → ℝ)
    (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (hgi : Integrable g P.law) :
    ∫⁻ d, ENNReal.ofReal (a * g (d t)) ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (a * ∫ y, g y ∂P.law) := by
  have hmeas : Measurable (fun y : ℝ≥0 => ENNReal.ofReal (a * g y)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hg)
  unfold CappedBaseStock.demandPathLaw
  have hcm := (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t).lintegral_comp hmeas
  dsimp only [Function.eval] at hcm
  rw [hcm, ← ofReal_integral_eq_lintegral_ofReal (hgi.const_mul a)
    (Eventually.of_forall (fun y => mul_nonneg ha (hg0 y))), integral_const_mul]

lemma inner (c : PerishBaseStock.Lifetime.Params) (P : CappedBaseStock.DemandLaw) (t : ℕ) (x : ℝ)
    (hx : 0 ≤ x) :
    ∫⁻ d, Psi c t x ((Finset.Ico t (t + c.m)).restrict d) ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P c x.toNNReal) := by
  have hm := c.one_le_m
  have := leadTimeLaw_prob' P (c.m - 1)
  have hθm : 0 ≤ c.θ / (c.m : ℝ) := div_nonneg c.θ_nonneg (Nat.cast_nonneg _)
  have hsum : ∀ d : CappedBaseStock.DemandPath,
      ∑ i : (Finset.Ico t (t + c.m)), (((Finset.Ico t (t + c.m)).restrict d i : ℝ≥0) : ℝ) =
      ∑ k ∈ Finset.range c.m, (d (t + k) : ℝ) := by
    intro d
    simp only [Finset.restrict]
    rw [Finset.sum_coe_sort (Finset.Ico t (t + c.m)) (fun i => (d i : ℝ)),
      Finset.sum_Ico_eq_sum_range, show t + c.m - t = c.m by omega]
  have hsplit : ∀ d : CappedBaseStock.DemandPath, Psi c t x ((Finset.Ico t (t + c.m)).restrict d) =
      ENNReal.ofReal (c.h * max (x - d t) 0) + ENNReal.ofReal (c.p * max ((d t : ℝ) - x) 0) +
      ENNReal.ofReal (c.θ / c.m * max (x - ∑ k ∈ Finset.range c.m, (d (t + k) : ℝ)) 0) := by
    intro d
    unfold Psi
    rw [hsum d, ENNReal.ofReal_add (add_nonneg (mul_nonneg c.h_pos.le (le_max_right _ _))
      (mul_nonneg c.p_pos.le (le_max_right _ _))) (mul_nonneg hθm (le_max_right _ _)),
      ENNReal.ofReal_add (mul_nonneg c.h_pos.le (le_max_right _ _))
      (mul_nonneg c.p_pos.le (le_max_right _ _))]
    rfl
  simp_rw [hsplit]
  rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
  have e1 := coord_lint P t c.h c.h_pos.le (fun y : ℝ≥0 => max (x - (y : ℝ)) 0) (by fun_prop)
    (fun _ => le_max_right _ _) (int_hold' P.law x)
  have e2 := coord_lint P t c.p c.p_pos.le (fun y : ℝ≥0 => max ((y : ℝ) - x) 0) (by fun_prop)
    (fun _ => le_max_right _ _) ((P.finiteMean.sub (integrable_const x)).pos_part)
  rw [e1, e2]
  -- the lead-time term, via the shift `d ↦ (d (t + k))_k`
  have hshift : (CappedBaseStock.demandPathLaw P).map
      (fun ω : CappedBaseStock.DemandPath => fun k => ω (t + k)) = CappedBaseStock.demandPathLaw P := by
    unfold CappedBaseStock.demandPathLaw
    exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => by simpa using h)
  have hF : Measurable (fun e : CappedBaseStock.DemandPath =>
      ENNReal.ofReal (c.θ / c.m * max (x - ∑ k ∈ Finset.range c.m, (e k : ℝ)) 0)) := by
    fun_prop
  have h3 : ∫⁻ d, ENNReal.ofReal (c.θ / c.m * max (x - ∑ k ∈ Finset.range c.m, (d (t + k) : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ e, ENNReal.ofReal (c.θ / c.m * max (x - ∑ k ∈ Finset.range c.m, (e k : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P := by
    conv_rhs => rw [← hshift]
    rw [lintegral_map hF (by fun_prop)]
  have hG : Measurable (fun y : ℝ≥0 => ENNReal.ofReal (c.θ / c.m * max (x - (y : ℝ)) 0)) := by
    fun_prop
  have h4 : ∫⁻ e, ENNReal.ofReal (c.θ / c.m * max (x - ∑ k ∈ Finset.range c.m, (e k : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ y, ENNReal.ofReal (c.θ / c.m * max (x - (y : ℝ)) 0)
      ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) := by
    unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
    rw [lintegral_map hG (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)),
      show c.m - 1 + 1 = c.m by omega]
    push_cast
    rfl
  rw [h3, h4, ← ofReal_integral_eq_lintegral_ofReal ((int_hold' _ x).const_mul _)
    (Eventually.of_forall (fun y => mul_nonneg hθm (le_max_right _ _))), integral_const_mul]
  have n1 : 0 ≤ c.h * ∫ y : ℝ≥0, max (x - (y : ℝ)) 0 ∂P.law :=
    mul_nonneg c.h_pos.le (integral_nonneg (fun _ => le_max_right _ _))
  have n2 : 0 ≤ c.p * ∫ y : ℝ≥0, max ((y : ℝ) - x) 0 ∂P.law :=
    mul_nonneg c.p_pos.le (integral_nonneg (fun _ => le_max_right _ _))
  have n3 : 0 ≤ c.θ / c.m * ∫ y : ℝ≥0, max (x - (y : ℝ)) 0
      ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) :=
    mul_nonneg hθm (integral_nonneg (fun _ => le_max_right _ _))
  rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3]
  congr 1
  unfold PerishBaseStock.Lifetime.heuristicCost LostSalesOrderUpTo.Asymptotic.backorderCost
    LostSalesOrderUpTo.Asymptotic.expectedHolding LostSalesOrderUpTo.Asymptotic.expectedShortfall
  rw [Real.coe_toNNReal x hx]


lemma exp_phi_ge (c : PerishBaseStock.Lifetime.Params) (P : CappedBaseStock.DemandLaw)
    (π : Policy c.m) (t : ℕ) (S : ℝ≥0) (hS : PerishBaseStock.Lifetime.IsHeuristicLevel P c S) :
    ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P c S) ≤
      ∫⁻ d, ENNReal.ofReal (phi c.h c.p c.θ π d t) ∂CappedBaseStock.demandPathLaw P := by
  have hm := c.one_le_m
  set μ := CappedBaseStock.demandPathLaw P with hμ
  set rR : CappedBaseStock.DemandPath → ((Finset.range t) → ℝ≥0) := fun d i => d i with hrRdef
  set rI : CappedBaseStock.DemandPath → ((Finset.Ico t (t + c.m)) → ℝ≥0) := fun d i => d i
    with hrIdef
  set G : ((Finset.range t) → ℝ≥0) → ℝ := fun u => Lv π (ext t u) t c.m with hGdef
  have hG : Measurable G := (Lv_meas π t hm).comp (ext_meas t)
  have hrR : Measurable rR := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hrI : Measurable rI := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hphi : ∀ d, ENNReal.ofReal (phi c.h c.p c.θ π d t) = Psi c t (G (rR d)) (rI d) := by
    intro d
    rw [phi_eq_Psi, Lv_congr π d t]
    rfl
  simp_rw [hphi]
  have hind : IndepFun rR rI μ := by
    have h := (iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ (ω : ℝ≥0) => ω)
      (fun _ => measurable_id)).indepFun_finset (Finset.range t) (Finset.Ico t (t + c.m))
      (by
        rw [Finset.disjoint_left]
        intro i hi hi'
        simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'
        omega)
      (fun i => measurable_pi_apply i)
    exact h
  have hpair := hind.map_prod_eq_prod_map_map hrR.aemeasurable hrI.aemeasurable
  have hF : Measurable (fun q : ((Finset.range t) → ℝ≥0) × ((Finset.Ico t (t + c.m)) → ℝ≥0) =>
      Psi c t (G q.1) q.2) :=
    Psi_meas c t (hG.comp measurable_fst) measurable_snd
  have := Measure.isProbabilityMeasure_map (μ := μ) hrR.aemeasurable
  calc ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P c S)
      = ∫⁻ _u, ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P c S) ∂(μ.map rR) := by
        simp
    _ ≤ ∫⁻ u, ∫⁻ y, Psi c t (G u) y ∂(μ.map rI) ∂(μ.map rR) := by
        apply lintegral_mono
        intro u
        dsimp only
        have hm2 : Measurable (fun y : (Finset.Ico t (t + c.m)) → ℝ≥0 => Psi c t (G u) y) :=
          Psi_meas c t (X := fun _ => G u) (Y := fun y => y) measurable_const measurable_id
        rw [lintegral_map hm2 hrI]
        have hin := inner c P t (G u) (Lv_nonneg π _ t hm)
        exact (ENNReal.ofReal_le_ofReal (hS _)).trans_eq hin.symm
    _ = ∫⁻ q, Psi c t (G q.1) q.2 ∂((μ.map rR).prod (μ.map rI)) :=
        (lintegral_prod _ hF.aemeasurable).symm
    _ = ∫⁻ q, Psi c t (G q.1) q.2 ∂(μ.map (fun d => (rR d, rI d))) := by rw [hpair]
    _ = ∫⁻ d, Psi c t (G (rR d)) (rI d) ∂μ := lintegral_map hF (hrR.prodMk hrI)

lemma sum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ℕ)
    (f : ℕ → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    simp_rw [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

end PerishLifetimeProp2Aux2

namespace PerishLemma2Aux
open PerishBaseStock.Penalty PerishBaseStock.Lifetime PerishLifetimeProp2Aux PerishLifetimeProp2Aux2

variable {m : ℕ}

lemma bs_eq (S : ℝ≥0) : baseStock m S = baseStockPolicy m S := rfl

lemma outdateFrom_eq (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdateFrom (emptyState m) (baseStock m S) d t = o (baseStockPolicy m S) d t := by
  rw [bs_eq]
  exact outdated_eq' _ d t

lemma hσ (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    Lv (baseStockPolicy m S) d t m = S := by
  show A m S d t m = S
  rw [A_top S d t hm]
  exact max_eq_left (inv S d hm t).1

/-- The potential `Φ_t = max_{1 ≤ i ≤ m} (x_{t,i} - i S/m)`. -/
def Phi (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  (Finset.range m).sup' (Finset.nonempty_range_iff.2 (by omega))
    (fun i => Lv (baseStockPolicy m S) d t (i + 1) - ((i : ℝ) + 1) * ((S : ℝ) / m))

lemma Phi_ge (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t j : ℕ) (hj1 : 1 ≤ j)
    (hjm : j ≤ m) :
    Lv (baseStockPolicy m S) d t j - (j : ℝ) * ((S : ℝ) / m) ≤ Phi hm S d t := by
  have h := Finset.le_sup' (fun i => Lv (baseStockPolicy m S) d t (i + 1) -
    ((i : ℝ) + 1) * ((S : ℝ) / m)) (Finset.mem_range.2 (show j - 1 < m by omega))
  rw [show j - 1 + 1 = j by omega] at h
  have hc : ((j - 1 : ℕ) : ℝ) + 1 = j := by
    rw [Nat.cast_sub hj1]; ring
  rw [hc] at h
  exact h

lemma Phi_nonneg (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    0 ≤ Phi hm S d t := by
  have h := Phi_ge hm S d t m hm le_rfl
  rw [hσ S d t hm] at h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have : (m : ℝ) * ((S : ℝ) / m) = S := by field_simp
  linarith

lemma Phi_zero (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) : Phi hm S d 0 ≤ 0 := by
  unfold Phi
  apply Finset.sup'_le
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ (S : ℝ) / m := div_nonneg (NNReal.coe_nonneg S) hmR.le
  rcases Nat.lt_or_ge (i + 1) m with h | h
  · rw [show Lv (baseStockPolicy m S) d 0 (i + 1) = A m S d 0 (i + 1) from rfl, A_zero S d h]
    have : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((S : ℝ) / m) := by positivity
    linarith
  · have him : i + 1 = m := by omega
    rw [him, hσ S d 0 hm]
    have : ((i : ℝ) + 1) = m := by exact_mod_cast him
    rw [this]
    have : (m : ℝ) * ((S : ℝ) / m) = S := by field_simp
    linarith

/-- One-step drift of the potential. -/
lemma Phi_step (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    o (baseStockPolicy m S) d t + Phi hm S d (t + 1) ≤
      Phi hm S d t + max ((S : ℝ) / m - d t) 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha0 : 0 ≤ (S : ℝ) / m := div_nonneg (NNReal.coe_nonneg S) hmR.le
  have hPn := Phi_nonneg hm S d t
  have hP1 := Phi_ge hm S d t 1 le_rfl hm
  rw [Nat.cast_one, one_mul] at hP1
  have ho := o_eq (baseStockPolicy m S) d t hm
  have hd := NNReal.coe_nonneg (d t)
  have hga : (S : ℝ) / m - d t ≤ max ((S : ℝ) / m - d t) 0 := le_max_left _ _
  have hga0 : 0 ≤ max ((S : ℝ) / m - d t) 0 := le_max_right _ _
  have hoB : o (baseStockPolicy m S) d t ≤ Phi hm S d t + max ((S : ℝ) / m - d t) 0 := by
    rw [ho]
    apply max_le
    · linarith
    · linarith
  have key : Phi hm S d (t + 1) ≤
      Phi hm S d t + max ((S : ℝ) / m - d t) 0 - o (baseStockPolicy m S) d t := by
    refine Finset.sup'_le _ _ (fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    have hpos : 0 ≤ ((i : ℝ) + 1) * ((S : ℝ) / m) := by positivity
    rcases Nat.lt_or_ge (i + 1) m with h | h
    · rw [Lv_succ (baseStockPolicy m S) d t (by omega) h]
      have hPi := Phi_ge hm S d t (i + 1 + 1) (by omega) (by omega)
      have hci : ((i + 1 + 1 : ℕ) : ℝ) = (i : ℝ) + 1 + 1 := by push_cast; ring
      rw [hci] at hPi
      rcases le_total (Lv (baseStockPolicy m S) d t (i + 1 + 1) - d t -
          o (baseStockPolicy m S) d t) 0 with hc | hc
      · rw [max_eq_right hc]
        rw [ho]
        rcases le_total (Lv (baseStockPolicy m S) d t 1 - d t) 0 with h1 | h1
        · rw [max_eq_right h1]; linarith
        · rw [max_eq_left h1]; linarith
      · rw [max_eq_left hc]
        have e : ((i : ℝ) + 1 + 1) * ((S : ℝ) / m) = ((i : ℝ) + 1) * ((S : ℝ) / m) + (S : ℝ) / m := by
          ring
        linarith
    · have him : i + 1 = m := by omega
      rw [him, hσ S d (t + 1) hm]
      have : ((i : ℝ) + 1) = m := by exact_mod_cast him
      rw [this]
      have : (m : ℝ) * ((S : ℝ) / m) = S := by field_simp
      linarith
  linarith

lemma cum_bound (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (N : ℕ) :
    ∑ n ∈ Finset.range N, o (baseStockPolicy m S) d n ≤
      ∑ n ∈ Finset.range N, max ((S : ℝ) / m - d n) 0 := by
  have h : ∀ N, ∑ n ∈ Finset.range N, o (baseStockPolicy m S) d n + Phi hm S d N ≤
      ∑ n ∈ Finset.range N, max ((S : ℝ) / m - d n) 0 := by
    intro N
    induction N with
    | zero => simpa using Phi_zero hm S d
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := Phi_step hm S d N
      linarith
  have := h N
  have := Phi_nonneg hm S d N
  linarith

/-- `E[ofReal (κ (x - Σ_{i<m} D_{t+i})^+)]` via the shift invariance of the path law. -/
lemma shift_lint (P : CappedBaseStock.DemandLaw) (hm : 1 ≤ m) (t : ℕ) (x κ : ℝ) (hκ : 0 ≤ κ) :
    ∫⁻ d, ENNReal.ofReal (κ * max (x - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (κ * ∫ y : ℝ≥0, max (x - (y : ℝ)) 0
        ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) := by
  have := leadTimeLaw_prob' P (m - 1)
  have hshift : (CappedBaseStock.demandPathLaw P).map
      (fun ω : CappedBaseStock.DemandPath => fun k => ω (t + k)) = CappedBaseStock.demandPathLaw P := by
    unfold CappedBaseStock.demandPathLaw
    exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => by simpa using h)
  have hF : Measurable (fun e : CappedBaseStock.DemandPath =>
      ENNReal.ofReal (κ * max (x - ∑ k ∈ Finset.range m, (e k : ℝ)) 0)) := by
    fun_prop
  have h3 : ∫⁻ d, ENNReal.ofReal (κ * max (x - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ e, ENNReal.ofReal (κ * max (x - ∑ k ∈ Finset.range m, (e k : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P := by
    conv_rhs => rw [← hshift]
    rw [lintegral_map hF (by fun_prop)]
  have hG : Measurable (fun y : ℝ≥0 => ENNReal.ofReal (κ * max (x - (y : ℝ)) 0)) := by
    fun_prop
  have h4 : ∫⁻ e, ENNReal.ofReal (κ * max (x - ∑ k ∈ Finset.range m, (e k : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ y, ENNReal.ofReal (κ * max (x - (y : ℝ)) 0)
      ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1) := by
    unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
    rw [lintegral_map hG (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)),
      show m - 1 + 1 = m by omega]
    push_cast
    rfl
  rw [h3, h4, ← ofReal_integral_eq_lintegral_ofReal ((int_hold' _ x).const_mul _)
    (Eventually.of_forall (fun y => mul_nonneg hκ (le_max_right _ _))), integral_const_mul]

end PerishLemma2Aux

open PerishBaseStock.Lifetime PerishLifetimeProp2Aux PerishLifetimeProp2Aux2 PerishLemma2Aux in
theorem solution (P : CappedBaseStock.DemandLaw) (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) :
    ENNReal.ofReal ((1 / (m : ℝ)) * LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) ≤ avgOutdate P m S ∧
      avgOutdate P m S ≤
        ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (S / (m : ℝ≥0))) ∧
      avgOutdate P m S ≤ ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hAvg : ∀ T, avgOutdateFrom P m S (emptyState m) T =
      (∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (o (PerishBaseStock.Penalty.baseStockPolicy m S) d t)
        ∂CappedBaseStock.demandPathLaw P) / ((T : ℝ≥0∞) + 1) := by
    intro T
    unfold avgOutdateFrom
    simp_rw [outdateFrom_eq]
  have hmeas : ∀ t, Measurable (fun d => ENNReal.ofReal (o (PerishBaseStock.Penalty.baseStockPolicy m S) d t)) :=
    fun t => (outdated_meas (PerishBaseStock.Penalty.baseStockPolicy m S) t).ennreal_ofReal
  have hnn : ∀ d t, 0 ≤ o (PerishBaseStock.Penalty.baseStockPolicy m S) d t := fun d t => o_nonneg _ d t
  have hSL : ∀ t, ∫⁻ d, ENNReal.ofReal (1 * max ((S : ℝ) - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P = ENNReal.ofReal (1 *
        LostSalesOrderUpTo.Asymptotic.expectedHolding
          (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) :=
    fun t => shift_lint P hm t S 1 zero_le_one
  have hT0 : ∀ T : ℕ, ((T : ℝ≥0∞) + 1) ≠ 0 := fun T => by positivity
  have hTt : ∀ T : ℕ, ((T : ℝ≥0∞) + 1) ≠ ⊤ := fun T => by simp
  have hconst : ∀ (T : ℕ) (c : ℝ≥0∞), (∑ _t ∈ Finset.range (T + 1), c) / ((T : ℝ≥0∞) + 1) = c := by
    intro T c
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    rw [mul_comm]; exact ENNReal.mul_div_cancel_right (hT0 T) (hTt T)
  refine ⟨?_, ?_, ?_⟩
  · -- lower bound
    set c0 := ENNReal.ofReal ((1 / (m : ℝ)) * LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) with hc0
    have hsumN : ∀ N : ℕ, ((N + 2 - m : ℕ) : ℝ≥0∞) * c0 ≤
        ∑ n ∈ Finset.range (N + 1), ∫⁻ d, ENNReal.ofReal (o (PerishBaseStock.Penalty.baseStockPolicy m S) d n)
          ∂CappedBaseStock.demandPathLaw P := by
      intro N
      by_cases hN : N + 2 ≤ m
      · rw [show N + 2 - m = 0 by omega]; simp
      · have hT : (N + 2 - m) + (m - 1) = N + 1 := by omega
        rw [← hT, ← lintegral_finsetSum _ (fun n _ => hmeas n)]
        have hc0' : ∀ t, ∫⁻ d, ENNReal.ofReal ((1 / (m : ℝ)) *
            max ((S : ℝ) - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
            ∂CappedBaseStock.demandPathLaw P = c0 :=
          fun t => shift_lint P hm t S _ (by positivity)
        calc ((N + 2 - m : ℕ) : ℝ≥0∞) * c0 = ∑ _t ∈ Finset.range (N + 2 - m), c0 := by simp
          _ = ∑ t ∈ Finset.range (N + 2 - m), ∫⁻ d, ENNReal.ofReal ((1 / (m : ℝ)) *
                max ((S : ℝ) - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
                ∂CappedBaseStock.demandPathLaw P := by simp_rw [hc0']
          _ ≤ ∫⁻ d, ∑ t ∈ Finset.range (N + 2 - m), ENNReal.ofReal ((1 / (m : ℝ)) *
                max ((S : ℝ) - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0)
                ∂CappedBaseStock.demandPathLaw P := sum_lintegral_le _ _ _
          _ ≤ _ := by
              apply lintegral_mono
              intro d
              dsimp only
              rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (by positivity)
                (le_max_right _ _)), ← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn d n)]
              apply ENNReal.ofReal_le_ofReal
              have h1 : ∑ t ∈ Finset.range (N + 2 - m),
                  max ((S : ℝ) - ∑ k ∈ Finset.range m, (d (t + k) : ℝ)) 0 ≤
                  (m : ℝ) * ∑ n ∈ Finset.range (N + 2 - m + (m - 1)), o (PerishBaseStock.Penalty.baseStockPolicy m S) d n := by
                refine le_trans (Finset.sum_le_sum (fun t _ => ?_)) (eq16 _ d _ hm)
                have := eq15 (PerishBaseStock.Penalty.baseStockPolicy m S) d t hm
                rwa [hσ S d t hm] at this
              rw [← Finset.mul_sum]
              have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))
              calc _ ≤ 1 / (m : ℝ) * ((m : ℝ) * ∑ n ∈ Finset.range (N + 2 - m + (m - 1)),
                    o (PerishBaseStock.Penalty.baseStockPolicy m S) d n) := h2
                _ = _ := by field_simp
    have hr : Tendsto (fun N : ℕ => ((N + 2 - m : ℕ) : ℝ≥0∞) / ((N : ℝ≥0∞) + 1)) atTop (𝓝 1) := by
      have hreal : Tendsto (fun N : ℕ => 1 - ((m : ℝ) - 1) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun N : ℕ => ((m : ℝ) - 1) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
          have := (tendsto_const_div_atTop_nhds_zero_nat ((m : ℝ) - 1)).comp
            (tendsto_add_atTop_nat 1)
          refine this.congr (fun N => ?_)
          simp [Function.comp]
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
      have h2 := (ENNReal.tendsto_ofReal hreal)
      rw [ENNReal.ofReal_one] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop m] with N hN
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [show ((N : ℝ≥0∞) + 1) = ENNReal.ofReal ((N : ℝ) + 1) by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one],
        show (((N + 2 - m : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((N + 2 - m : ℕ) : ℝ) by
          rw [ENNReal.ofReal_natCast],
        ← ENNReal.ofReal_div_of_pos hpos]
      congr 1
      rw [Nat.cast_sub (by omega)]
      push_cast
      field_simp
      ring
    have hv : Tendsto (fun N : ℕ => ((N + 2 - m : ℕ) : ℝ≥0∞) * c0 / ((N : ℝ≥0∞) + 1)) atTop
        (𝓝 c0) := by
      have := ENNReal.Tendsto.const_mul hr (Or.inl one_ne_zero) (a := c0)
      rw [mul_one] at this
      refine this.congr (fun N => ?_)
      simp only [div_eq_mul_inv]
      ring
    unfold avgOutdate
    rw [← hv.limsup_eq]
    refine limsup_le_limsup (Eventually.of_forall (fun N => ?_)) (by isBoundedDefault)
      (by isBoundedDefault)
    rw [hAvg]
    exact ENNReal.div_le_div_right (hsumN N) _
  · -- upper bound `E[(S/m - D)^+]`
    unfold avgOutdate
    apply limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (fun T => ?_))
    rw [hAvg]
    have hcoe : (((S / (m : ℝ≥0)) : ℝ≥0) : ℝ) = (S : ℝ) / m := by push_cast; rfl
    have hc : ∀ t, ∫⁻ d, ENNReal.ofReal (max ((S : ℝ) / m - d t) 0)
        ∂CappedBaseStock.demandPathLaw P =
        ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (S / (m : ℝ≥0))) := by
      intro t
      have h := coord_lint P t 1 zero_le_one (fun y : ℝ≥0 => max ((S : ℝ) / m - (y : ℝ)) 0)
        (by fun_prop) (fun _ => le_max_right _ _) (int_hold' P.law _)
      simp only [one_mul] at h
      rw [h]
      unfold LostSalesOrderUpTo.Asymptotic.expectedHolding
      rw [hcoe]
    rw [← hconst T (ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding P.law
      (S / (m : ℝ≥0))))]
    apply ENNReal.div_le_div_right
    rw [← lintegral_finsetSum _ (fun n _ => hmeas n)]
    have hsum : ∑ _t ∈ Finset.range (T + 1), ENNReal.ofReal
        (LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (S / (m : ℝ≥0))) =
        ∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (max ((S : ℝ) / m - d t) 0)
          ∂CappedBaseStock.demandPathLaw P := Finset.sum_congr rfl (fun t _ => (hc t).symm)
    rw [hsum, ← lintegral_finsetSum _ (fun n _ => by fun_prop)]
    apply lintegral_mono
    intro d
    dsimp only
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn d n),
      ← ENNReal.ofReal_sum_of_nonneg (fun n _ => le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal (cum_bound hm S d (T + 1))
  · -- upper bound `E[(S - Σ D_i)^+]`
    unfold avgOutdate
    apply limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (fun T => ?_))
    rw [hAvg]
    rw [← hconst T (ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S))]
    apply ENNReal.div_le_div_right
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : t + 1 < m
    · have : (fun d => ENNReal.ofReal (o (PerishBaseStock.Penalty.baseStockPolicy m S) d t)) = fun _ => 0 := by
        funext d; rw [o_early _ d hm t ht, ENNReal.ofReal_zero]
      rw [this, lintegral_zero]
      exact zero_le
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + (m - 1) := ⟨t - (m - 1), by omega⟩
      have h := hSL s
      rw [one_mul] at h
      rw [← h]
      apply lintegral_mono
      intro d
      apply ENNReal.ofReal_le_ofReal
      rw [one_mul, rec19 _ d s hm, hσ S d s hm]
      have : 0 ≤ ∑ j ∈ Finset.range (m - 1), o (PerishBaseStock.Penalty.baseStockPolicy m S) d (s + j) :=
        Finset.sum_nonneg (fun j _ => hnn d _)
      exact max_le_max (by linarith) le_rfl
