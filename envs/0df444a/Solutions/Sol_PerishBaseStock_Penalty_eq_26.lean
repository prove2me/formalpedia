-- Prove2me | solution 1 for PerishBaseStock.Penalty.eq_26
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:17:03.761679+00:00
-- url     : https://prove2.me/submissions/49fd4455-5dd4-4212-bd85-3a0b25b84a75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PerishBaseStock_Penalty_proposition_3
import Theorems.Thm_PerishBaseStock_Penalty_eq_EC_13
import Theorems.Thm_PerishBaseStock_Penalty_eq_EC_15
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyEq26Aux
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



lemma int_hold (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun x : ℝ≥0 => max (s - (x : ℝ)) 0) μ := by
  refine Integrable.mono' (integrable_const |s|) ?_ (Eventually.of_forall (fun x => ?_))
  · exact ((continuous_const.sub NNReal.continuous_coe).max continuous_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := NNReal.coe_nonneg x; have := le_abs_self s; linarith) (abs_nonneg s)

lemma int_short (P : CappedBaseStock.DemandLaw) (s : ℝ) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - s) 0) P.law :=
  (P.finiteMean.sub (integrable_const s)).pos_part

lemma hold_mono (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {s t : ℝ} (h : s ≤ t) :
    ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂μ ≤ ∫ x : ℝ≥0, max (t - (x : ℝ)) 0 ∂μ :=
  integral_mono (int_hold μ s) (int_hold μ t) (fun x => max_le_max (by linarith) le_rfl)

lemma hold_sub_le (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (s t : ℝ) :
    ∫ x : ℝ≥0, max (t - (x : ℝ)) 0 ∂μ - ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂μ ≤ |t - s| := by
  have h : ∫ x : ℝ≥0, (max (t - (x : ℝ)) 0 - max (s - (x : ℝ)) 0) ∂μ ≤
      ∫ _x : ℝ≥0, |t - s| ∂μ :=
    integral_mono ((int_hold μ t).sub (int_hold μ s)) (integrable_const _) (fun x => by
      have h1 := abs_max_sub_max_le_abs (t - (x : ℝ)) (s - x) 0
      have h2 : (t - (x : ℝ)) - (s - x) = t - s := by ring
      rw [h2] at h1
      exact (le_abs_self _).trans h1)
  rw [integral_sub (int_hold μ t) (int_hold μ s)] at h
  simpa using h

lemma short_gap (P : CappedBaseStock.DemandLaw) {M : ℝ} {M' : ℝ≥0} (h : M ≤ M') :
    (∫ x : ℝ≥0, max ((x : ℝ) - M') 0 ∂P.law) +
      ((M' : ℝ) - M) * (P.law (Set.Ioi M')).toReal ≤ ∫ x : ℝ≥0, max ((x : ℝ) - M) 0 ∂P.law := by
  have hmeas : MeasurableSet (Set.Ioi M') := measurableSet_Ioi
  have hind : Integrable (Set.indicator (Set.Ioi M') (fun _ => (M' : ℝ) - M)) P.law :=
    (integrable_const _).indicator hmeas
  have key : ∫ x : ℝ≥0, (max ((x : ℝ) - M') 0 +
      Set.indicator (Set.Ioi M') (fun _ => (M' : ℝ) - M) x) ∂P.law ≤
      ∫ x : ℝ≥0, max ((x : ℝ) - M) 0 ∂P.law := by
    apply integral_mono ((int_short P M').add hind) (int_short P M)
    intro x
    show max ((x : ℝ) - M') 0 + Set.indicator (Set.Ioi M') (fun _ => (M' : ℝ) - M) x ≤
      max ((x : ℝ) - M) 0
    by_cases hx : x ∈ Set.Ioi M'
    · rw [Set.indicator_of_mem hx]
      have hx' : (M' : ℝ) < x := hx
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hx' : (x : ℝ) ≤ M' := not_lt.1 hx
      rw [max_eq_right (by linarith : (x : ℝ) - M' ≤ 0)]
      simp
  rw [integral_add (int_short P M') hind, integral_indicator_const _ hmeas] at key
  simpa [smul_eq_mul, mul_comm, measureReal_def] using key

lemma Ioi_eq_iUnion (a : ℝ≥0) :
    Set.Ioi a = ⋃ n : ℕ, Set.Ioi (a + 1 / ((n : ℝ≥0) + 1)) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt h)
    exact ⟨n, lt_tsub_iff_left.1 hn⟩
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt le_self_add hn

lemma leadTimeLaw_prob (P : CappedBaseStock.DemandLaw) (τ : ℕ) :
    IsProbabilityMeasure (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P τ) := by
  unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
  exact Measure.isProbabilityMeasure_map
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)).aemeasurable


lemma floorCost_cont (c : PerishBaseStock.Penalty.Params) (P : CappedBaseStock.DemandLaw) :
    Continuous (floorCost c P) := by
  have hc1 : Continuous (fun s : ℝ => ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun s t => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      exact abs_sub_le_iff.2 ⟨hold_sub_le P.law t s,
        by have := hold_sub_le P.law s t; rwa [abs_sub_comm] at this⟩)).continuous
  have hsg : ∀ s t : ℝ, (∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) -
      ∫ x : ℝ≥0, max ((x : ℝ) - t) 0 ∂P.law ≤ |s - t| := by
    intro s t
    have h : ∫ x : ℝ≥0, (max ((x : ℝ) - s) 0 - max ((x : ℝ) - t) 0) ∂P.law ≤
        ∫ _x : ℝ≥0, |s - t| ∂P.law :=
      integral_mono ((int_short P s).sub (int_short P t)) (integrable_const _) (fun x => by
        have h1 := abs_max_sub_max_le_abs ((x : ℝ) - s) (x - t) 0
        have h2 : ((x : ℝ) - s) - (x - t) = -(s - t) := by ring
        rw [h2, abs_neg] at h1
        exact (le_abs_self _).trans h1)
    rw [integral_sub (int_short P s) (int_short P t)] at h
    simpa using h
  have hc2 : Continuous (fun s : ℝ => ∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun s t => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      exact abs_sub_le_iff.2 ⟨hsg s t, by have := hsg t s; rwa [abs_sub_comm] at this⟩)).continuous
  have : floorCost c P = fun S : ℝ≥0 => c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) + c.θ * S := rfl
  rw [this]
  exact ((continuous_const.mul (hc1.comp NNReal.continuous_coe)).add
    (continuous_const.mul (hc2.comp NNReal.continuous_coe))).add
    (continuous_const.mul NNReal.continuous_coe)

lemma floor_exists (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    ∃ S : ℝ≥0, ∀ S', floorCost c P S ≤ floorCost c P S' := by
  have hcont := floorCost_cont c P
  have hfe : ∀ S : ℝ≥0, floorCost c P S = c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) + c.θ * S := fun _ => rfl
  have hge : ∀ s : ℝ, s - CappedBaseStock.mean P ≤ ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law := by
    intro s
    have hi : Integrable (fun x : ℝ≥0 => s - (x : ℝ)) P.law := (integrable_const s).sub P.finiteMean
    have h1 : ∫ x : ℝ≥0, (s - (x : ℝ)) ∂P.law ≤ ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law :=
      integral_mono hi (int_hold P.law s) (fun x => le_max_left (s - (x : ℝ)) 0)
    rw [integral_sub (integrable_const s) P.finiteMean] at h1
    simpa [CappedBaseStock.mean] using h1
  set R : ℝ≥0 := (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1).toNNReal with hR
  have hbig : ∀ S' : ℝ≥0, R < S' → floorCost c P 0 < floorCost c P S' := by
    intro S' hS'
    have h1 : (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1) < S' := by
      have h0 : ((R : ℝ)) < S' := hS'
      have h00 := Real.le_coe_toNNReal (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1)
      rw [← hR] at h00
      linarith
    have h2 := hge S'
    have h3 : 0 ≤ ∫ x : ℝ≥0, max ((x : ℝ) - (S' : ℝ)) 0 ∂P.law :=
      integral_nonneg (fun _ => le_max_right _ _)
    rw [hfe S']
    have h4 : floorCost c P 0 / c.h * c.h = floorCost c P 0 := div_mul_cancel₀ _ hc.h_pos.ne'
    have h5 := mul_le_mul_of_nonneg_left h2 hc.h_pos.le
    have h6 := mul_nonneg hc.p_pos.le h3
    have h7 : 0 ≤ c.θ * (S' : ℝ) := mul_nonneg hc.θ_nonneg (NNReal.coe_nonneg _)
    have h8 := mul_lt_mul_of_pos_left
      (show floorCost c P 0 / c.h + 1 < (S' : ℝ) - CappedBaseStock.mean P by linarith) hc.h_pos
    have h9 : c.h * (floorCost c P 0 / c.h) = floorCost c P 0 := by rw [mul_comm]; exact h4
    rw [mul_add, h9, mul_one] at h8
    linarith [hc.h_pos]
  obtain ⟨S0, hS0mem, hS0⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.2 (zero_le : (0:ℝ≥0) ≤ R)) hcont.continuousOn
  refine ⟨S0, fun S' => ?_⟩
  by_cases hle : S' ≤ R
  · exact isMinOn_iff.1 hS0 S' ⟨zero_le, hle⟩
  · push Not at hle
    have := isMinOn_iff.1 hS0 0 ⟨le_rfl, zero_le⟩
    linarith [hbig S' hle]

/-- `S̲ ≤ S̃`. -/
lemma floor_le (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0)
    (hS : IsHeuristicLevel c P S) : floorLevel c P ≤ S := by
  have := leadTimeLaw_prob P (c.m - 1)
  obtain ⟨S0, hS0⟩ := floor_exists c hc P
  have hcont := floorCost_cont c P
  have hclosed : IsClosed {S : ℝ≥0 | ∀ S', floorCost c P S ≤ floorCost c P S'} := by
    have : {S : ℝ≥0 | ∀ S', floorCost c P S ≤ floorCost c P S'} =
        ⋂ S', {S | floorCost c P S ≤ floorCost c P S'} := by ext; simp
    rw [this]
    exact isClosed_iInter (fun S' => isClosed_le hcont continuous_const)
  have hmem : floorLevel c P ∈ {S : ℝ≥0 | ∀ S', floorCost c P S ≤ floorCost c P S'} :=
    hclosed.csInf_mem ⟨S0, hS0⟩ (OrderBot.bddBelow _)
  by_contra hlt
  push Not at hlt
  have hnot : S ∉ {S : ℝ≥0 | ∀ S', floorCost c P S ≤ floorCost c P S'} := fun h =>
    absurd (csInf_le (OrderBot.bddBelow _) h) (not_le.2 hlt)
  simp only [Set.mem_ofPred_eq, not_forall, not_le] at hnot
  obtain ⟨S', hS'⟩ := hnot
  have h1 := hmem S'
  have h2 := hS (floorLevel c P)
  set Sl := floorLevel c P
  have hlt' : (S : ℝ) < Sl := hlt
  have hm : (1 : ℝ) ≤ c.m := by exact_mod_cast hc.one_le_m
  have hθm : 0 ≤ c.θ / (c.m : ℝ) := div_nonneg hc.θ_nonneg (by linarith)
  have hθm' : c.θ / (c.m : ℝ) ≤ c.θ := div_le_self hc.θ_nonneg hm
  have hlip := hold_sub_le (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) (S : ℝ) Sl
  rw [abs_of_pos (by linarith)] at hlip
  have e1 := mul_le_mul_of_nonneg_left hlip hθm
  have e2 := mul_le_mul_of_nonneg_right hθm' (by linarith : (0 : ℝ) ≤ Sl - S)
  have hfS : floorCost c P S = c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) + c.θ * S := rfl
  have hfSl : floorCost c P Sl = c.h * (∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (Sl : ℝ)) 0 ∂P.law) + c.θ * Sl := rfl
  have hHS : heuristicCost c P S = c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) + c.θ / (c.m : ℝ) *
      ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) :=
    rfl
  have hHSl : heuristicCost c P Sl = c.h * (∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (Sl : ℝ)) 0 ∂P.law) + c.θ / (c.m : ℝ) *
      ∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) :=
    rfl
  rw [hHS, hHSl] at h2
  have h3 : floorCost c P Sl < floorCost c P S := lt_of_le_of_lt h1 hS'
  rw [hfS, hfSl] at h3
  rw [mul_sub] at e1
  rw [mul_sub, mul_sub] at e2
  nlinarith

/-- Cost decomposition of `π_S`: `C(S) ≤ hE[(S-D)^+] + pE[(D-S)^+] + θ E[O∞(S)]`. -/
lemma cost_decomp (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) :
    baseStockCost c P S ≤
      ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) +
      ENNReal.ofReal c.θ * avgOutdating c P S := by
  have hm := hc.one_le_m
  have hTL : ∀ d t, totalLevel (baseStockPolicy c.m S) d t = S := by
    intro d t
    have h1 : totalLevel (baseStockPolicy c.m S) d t = A c.m S d t c.m := by
      unfold A totalLevel; rw [level_top _ _ hm]; rfl
    rw [h1, A_top S d t hm]
    exact max_eq_left (inv S d hm t).1
  set K := ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) with hK
  set θ' := ENNReal.ofReal c.θ
  have hmp := fun t => measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t
  have hI1 : ∀ t, ∫⁻ d, ENNReal.ofReal c.h * ENNReal.ofReal (max ((S : ℝ) - (d t : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) := by
    intro t
    have hmeas : Measurable (fun x : ℝ≥0 => ENNReal.ofReal (max ((S : ℝ) - (x : ℝ)) 0)) := by
      fun_prop
    rw [lintegral_const_mul _ (by fun_prop)]
    unfold CappedBaseStock.demandPathLaw
    have hcm := (hmp t).lintegral_comp hmeas
    dsimp only [Function.eval] at hcm
    rw [hcm,
      ← ofReal_integral_eq_lintegral_ofReal (int_hold P.law _)
        (Eventually.of_forall (fun _ => le_max_right _ _)),
      ← ENNReal.ofReal_mul hc.h_pos.le]
  have hI2 : ∀ t, ∫⁻ d, ENNReal.ofReal c.p * ENNReal.ofReal (max ((d t : ℝ) - (S : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) := by
    intro t
    have hmeas : Measurable (fun x : ℝ≥0 => ENNReal.ofReal (max ((x : ℝ) - (S : ℝ)) 0)) := by
      fun_prop
    rw [lintegral_const_mul _ (by fun_prop)]
    unfold CappedBaseStock.demandPathLaw
    have hcm := (hmp t).lintegral_comp hmeas
    dsimp only [Function.eval] at hcm
    rw [hcm,
      ← ofReal_integral_eq_lintegral_ofReal (int_short P _)
        (Eventually.of_forall (fun _ => le_max_right _ _)),
      ← ENNReal.ofReal_mul hc.p_pos.le]
  have hI : ∀ t, ∫⁻ d, PerishBaseStock.Penalty.periodCost c (baseStockPolicy c.m S) d t ∂CappedBaseStock.demandPathLaw P =
      K + θ' * ∫⁻ d, ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S) d t)
        ∂CappedBaseStock.demandPathLaw P := by
    intro t
    have hpc : (fun d => PerishBaseStock.Penalty.periodCost c (baseStockPolicy c.m S) d t) = fun d =>
        (ENNReal.ofReal c.h * ENNReal.ofReal (max ((S : ℝ) - (d t : ℝ)) 0) +
          ENNReal.ofReal c.p * ENNReal.ofReal (max ((d t : ℝ) - (S : ℝ)) 0)) +
        θ' * ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S) d t) := by
      funext d; unfold PerishBaseStock.Penalty.periodCost; rw [hTL]
    rw [hpc, lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop), hI1, hI2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold baseStockCost PerishBaseStock.Penalty.policyCost avgOutdating longRunAverage
  simp_rw [hI]
  have hpt : ∀ T : ℕ, (∑ t ∈ Finset.range (T + 1), (K + θ' * ∫⁻ d,
      ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S) d t)
        ∂CappedBaseStock.demandPathLaw P)) / ((T : ℝ≥0∞) + 1) =
      K + θ' * ((∑ t ∈ Finset.range (T + 1), ∫⁻ d,
      ENNReal.ofReal (PerishBaseStock.Penalty.outdated (baseStockPolicy c.m S) d t)
        ∂CappedBaseStock.demandPathLaw P) / ((T : ℝ≥0∞) + 1)) := by
    intro T
    have hT0 : ((T : ℝ≥0∞) + 1) ≠ 0 := by positivity
    have hTt : ((T : ℝ≥0∞) + 1) ≠ ⊤ := by simp
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, ENNReal.add_div]
    congr 1
    · push_cast
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right hT0 hTt
    · exact mul_div_assoc _ _ _
  simp_rw [hpt]
  rw [limsup_const_add atTop _ K (by isBoundedDefault) (by isBoundedDefault),
    ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]

end PerishPenaltyEq26Aux

open PerishBaseStock.Penalty PerishPenaltyEq26Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) (S : ℝ≥0) (hS : IsHeuristicLevel c P S) :
    baseStockCost c P S ≤
      OPT c P + ENNReal.ofReal ((c.h + c.θ) * ((upperSupport P).toReal - floorLevel c P)) := by
  obtain ⟨h13a, h13b⟩ := eq_EC_13 c hc P hP S hS
  have hle := floor_le c hc P S hS
  have h15 := eq_EC_15 c hc P (floorLevel c P) S hle
  have h3 := proposition_3 c hc P hP
  have hdec := cost_decomp c hc P S
  set Sl := floorLevel c P with hSl
  set D := (upperSupport P).toReal with hD
  have hle' : (Sl : ℝ) ≤ S := hle
  have hEH := hold_sub_le P.law (Sl : ℝ) S
  rw [abs_of_nonneg (by linarith)] at hEH
  have hES0 : 0 ≤ ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hEHl0 : 0 ≤ ∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hp13 : c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law ≤ (c.h + c.θ) * (D - S) :=
    h13a.trans h13b
  have hb0 : 0 ≤ (c.h + c.θ) * (D - S) := le_trans (mul_nonneg hc.p_pos.le hES0) hp13
  have ha1 : 0 ≤ c.h * ∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law :=
    mul_nonneg hc.h_pos.le hEHl0
  have ha2 : 0 ≤ c.h * ((S : ℝ) - Sl) := mul_nonneg hc.h_pos.le (by linarith)
  have ha3 : 0 ≤ c.θ * ((S : ℝ) - Sl) := mul_nonneg hc.θ_nonneg (by linarith)
  calc baseStockCost c P S
      ≤ ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal c.θ * avgOutdating c P S := hdec
    _ ≤ ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law + c.h * ((S : ℝ) - Sl)) +
        ENNReal.ofReal ((c.h + c.θ) * (D - S)) +
        ENNReal.ofReal c.θ * (avgOutdating c P Sl + ENNReal.ofReal ((S : ℝ) - Sl)) := by
        gcongr ?_ + ?_ + ?_
        · apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_left hEH hc.h_pos.le
          rw [mul_sub] at this
          linarith
        · exact ENNReal.ofReal_le_ofReal hp13
        · exact mul_le_mul_of_nonneg_left h15 zero_le
    _ = (ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((Sl : ℝ) - (x : ℝ)) 0 ∂P.law) +
          ENNReal.ofReal c.θ * avgOutdating c P Sl) +
        ENNReal.ofReal (c.h * ((S : ℝ) - Sl) + (c.h + c.θ) * (D - S) + c.θ * ((S : ℝ) - Sl)) := by
        rw [ENNReal.ofReal_add ha1 ha2, ENNReal.ofReal_add (add_nonneg ha2 hb0) ha3,
          ENNReal.ofReal_add ha2 hb0, ENNReal.ofReal_mul hc.θ_nonneg, mul_add]
        ring
    _ ≤ OPT c P + ENNReal.ofReal ((c.h + c.θ) * (D - Sl)) := by
        gcongr
        · exact h3
        · apply le_of_eq; ring
