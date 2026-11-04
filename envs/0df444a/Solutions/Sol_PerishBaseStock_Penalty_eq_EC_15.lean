-- Prove2me | solution 1 for PerishBaseStock.Penalty.eq_EC_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:11:57.501887+00:00
-- url     : https://prove2.me/submissions/2c5e4add-3edf-42e2-884b-4a52e384f496

import Definitions.Def_PerishBaseStock_Penalty_Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyEC15Aux
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


lemma joint {S₁ S₂ : ℝ≥0} (h12 : S₁ ≤ S₂) (d : CappedBaseStock.DemandPath) (hm : 1 ≤ m) :
    ∀ t : ℕ, (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ m →
      A m S₂ d t i - A m S₁ d t i ≤ A m S₂ d t j - A m S₁ d t j) ∧
      0 ≤ A m S₂ d t 1 - A m S₁ d t 1 := by
  have h12' : (S₁ : ℝ) ≤ S₂ := by exact_mod_cast h12
  have hS : ∀ (S : ℝ≥0) t, A m S d t m = S := fun S t => by
    rw [A_top S d t hm]; exact max_eq_left (inv S d hm t).1
  intro t
  induction t with
  | zero =>
    have hD : ∀ i, 1 ≤ i → i ≤ m → 0 ≤ A m S₂ d 0 i - A m S₁ d 0 i ∧
        A m S₂ d 0 i - A m S₁ d 0 i ≤ S₂ - S₁ := by
      intro i hi him
      rcases Nat.lt_or_ge i m with h | h
      · rw [A_zero S₂ d h, A_zero S₁ d h]; constructor <;> linarith
      · rw [show i = m by omega, hS, hS]; constructor <;> linarith
    refine ⟨fun i j hi hij hj => ?_, (hD 1 le_rfl hm).1⟩
    rcases Nat.lt_or_ge j m with h | h
    · rw [A_zero S₂ d (by omega : i < m), A_zero S₁ d (by omega : i < m), A_zero S₂ d h,
        A_zero S₁ d h]
    · rw [show j = m by omega, hS, hS]; exact (hD i hi (by omega)).2
  | succ t ih =>
    obtain ⟨hDm, hD1⟩ := ih
    have hmono1 := (inv S₁ d hm t).2
    set M1 := max (A m S₁ d t 1) (d t) with hM1
    set M2 := max (A m S₂ d t 1) (d t) with hM2
    have he0 : 0 ≤ M2 - M1 := max_sub_max_nonneg (by linarith)
    have he1 : M2 - M1 ≤ A m S₂ d t 1 - A m S₁ d t 1 := max_sub_max_le (by linarith)
    have hDtop : ∀ i, 1 ≤ i → i ≤ m → A m S₂ d t i - A m S₁ d t i ≤ S₂ - S₁ := by
      intro i hi him
      have := hDm i m hi him le_rfl
      rw [hS, hS] at this; exact this
    have hform : ∀ i, 1 ≤ i → i < m → A m S₂ d (t + 1) i - A m S₁ d (t + 1) i =
        max ((A m S₁ d t (i + 1) - M1) + ((A m S₂ d t (i + 1) - A m S₁ d t (i + 1)) - (M2 - M1))) 0 -
          max (A m S₁ d t (i + 1) - M1) 0 := by
      intro i hi him
      rw [A_succ S₂ d t hi him, A_succ S₁ d t hi him]
      congr 2
      ring
    have hw : ∀ i, 1 ≤ i → i < m →
        0 ≤ (A m S₂ d t (i + 1) - A m S₁ d t (i + 1)) - (M2 - M1) := by
      intro i hi him
      have := hDm 1 (i + 1) le_rfl (by omega) (by omega)
      linarith
    refine ⟨fun i j hi hij hj => ?_, ?_⟩
    · rcases Nat.lt_or_ge j m with hjm | hjm
      · rw [hform i hi (by omega), hform j (by omega) hjm]
        exact g_inc_mono (by linarith [hmono1 (i + 1) (j + 1) (by omega) (by omega) (by omega)])
          (hw i hi (by omega)) (by linarith [hDm (i + 1) (j + 1) (by omega) (by omega) (by omega)])
      · rw [show j = m by omega, hS, hS]
        rcases Nat.lt_or_ge i m with him | him
        · rw [hform i hi him]
          have := g_inc_le (u := A m S₁ d t (i + 1) - M1) (hw i hi him)
          have := hDtop (i + 1) (by omega) (by omega)
          linarith
        · rw [show i = m by omega, hS, hS]
    · by_cases h1 : 1 < m
      · rw [hform 1 le_rfl h1]; exact g_inc_nonneg (hw 1 le_rfl h1)
      · have : m = 1 := by omega
        subst this
        have h := hS S₂ (t + 1); have h' := hS S₁ (t + 1)
        rw [h, h']; linarith

lemma outdated_eq (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) (hm : 1 ≤ m) :
    PerishBaseStock.Penalty.outdated (baseStockPolicy m S) d t = max (A m S d t 1 - d t) 0 := by
  unfold PerishBaseStock.Penalty.outdated A
  exact outdate_eq _ _ _ hm

/-- Pathwise form of (EC.15): `o^{S₂}_t ≤ o^{S₁}_t + S₂ - S₁`. -/
lemma outdated_le {S₁ S₂ : ℝ≥0} (h12 : S₁ ≤ S₂) (d : CappedBaseStock.DemandPath) (hm : 1 ≤ m)
    (t : ℕ) : PerishBaseStock.Penalty.outdated (baseStockPolicy m S₂) d t ≤ PerishBaseStock.Penalty.outdated (baseStockPolicy m S₁) d t + (S₂ - S₁) := by
  rw [outdated_eq S₂ d t hm, outdated_eq S₁ d t hm]
  obtain ⟨hDm, hD1⟩ := joint h12 d hm t
  have hS : ∀ (S : ℝ≥0), A m S d t m = S := fun S => by
    rw [A_top S d t hm]; exact max_eq_left (inv S d hm t).1
  have h1m := hDm 1 m le_rfl hm le_rfl
  rw [hS, hS] at h1m
  have := g_inc_le (u := A m S₁ d t 1 - d t) hD1
  have e : A m S₂ d t 1 - d t = (A m S₁ d t 1 - d t) + (A m S₂ d t 1 - A m S₁ d t 1) := by ring
  rw [e]
  linarith

end PerishPenaltyEC15Aux

open PerishBaseStock.Penalty PerishPenaltyEC15Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (S₁ S₂ : ℝ≥0) (h12 : S₁ ≤ S₂) :
    avgOutdating c P S₂ ≤ avgOutdating c P S₁ + ENNReal.ofReal ((S₂ : ℝ) - S₁) := by
  unfold avgOutdating longRunAverage
  set Δ := ENNReal.ofReal ((S₂ : ℝ) - S₁)
  rw [← limsup_add_const atTop _ Δ (by isBoundedDefault) (by isBoundedDefault)]
  apply limsup_le_limsup (Eventually.of_forall (fun T => ?_)) (by isBoundedDefault)
    (by isBoundedDefault)
  have hpt : ∀ t (d : CappedBaseStock.DemandPath),
      ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₂) d t) ≤
        ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₁) d t) + Δ := fun t d =>
    (ENNReal.ofReal_le_ofReal (outdated_le h12 d hc.one_le_m t)).trans ENNReal.ofReal_add_le
  have hint : ∀ t, ∫⁻ d, ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₂) d t)
        ∂CappedBaseStock.demandPathLaw P ≤
      ∫⁻ d, ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₁) d t)
        ∂CappedBaseStock.demandPathLaw P + Δ := by
    intro t
    calc _ ≤ ∫⁻ d, (ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₁) d t) + Δ)
          ∂CappedBaseStock.demandPathLaw P := lintegral_mono (fun d => hpt t d)
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range (T + 1)) => hint t)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hT0 : ((T : ℝ≥0∞) + 1) ≠ 0 := by positivity
  have hTt : ((T : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  calc _ ≤ (∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S₁) d t)
          ∂CappedBaseStock.demandPathLaw P + ((T + 1 : ℕ) : ℝ≥0∞) * Δ) / ((T : ℝ≥0∞) + 1) :=
        ENNReal.div_le_div_right hsum _
    _ = _ := by
        rw [ENNReal.add_div]
        congr 1
        push_cast
        rw [mul_comm]; exact ENNReal.mul_div_cancel_right hT0 hTt
