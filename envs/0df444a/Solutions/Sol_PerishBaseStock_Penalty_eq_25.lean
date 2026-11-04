-- Prove2me | solution 1 for PerishBaseStock.Penalty.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:22:39.589211+00:00
-- url     : https://prove2.me/submissions/e3e99af7-6d8d-46b4-a177-5d17565e442f

import Theorems.Thm_PerishBaseStock_Lifetime_lemma_2
import Theorems.Thm_PerishBaseStock_Lifetime_proposition_2
import Definitions.Def_PerishBaseStock_Penalty_Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyEq25Aux
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


lemma run_eq {m : ℕ} (π : Policy m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    PerishBaseStock.Penalty.run π d t = PerishBaseStock.Lifetime.run π d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show step (PerishBaseStock.Penalty.run π d t) (π.φ t (PerishBaseStock.Penalty.run π d t)) (d t) =
      step (runFrom (emptyState m) π d t) (π.φ t (runFrom (emptyState m) π d t)) (d t)
    rw [ih]; rfl

/-- The same parameters, packaged in the record of the `Lifetime` model. -/
def toLife (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) : PerishBaseStock.Lifetime.Params :=
  ⟨c.m, hc.one_le_m, c.h, c.p, c.θ, hc.h_pos, hc.p_pos, hc.θ_nonneg⟩

lemma periodCost_eq (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) (π : Policy c.m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    PerishBaseStock.Penalty.periodCost c π d t =
      PerishBaseStock.Lifetime.periodCost (toLife c hc) π d t := by
  unfold PerishBaseStock.Penalty.periodCost PerishBaseStock.Lifetime.periodCost
    PerishBaseStock.Penalty.totalLevel PerishBaseStock.Penalty.orderQty
    PerishBaseStock.Penalty.outdated PerishBaseStock.Lifetime.upTo
    PerishBaseStock.Lifetime.outdated PerishBaseStock.Lifetime.outdateFrom
  simp only [PerishBaseStock.Penalty.orderQty]
  rw [run_eq]
  show _ = ENNReal.ofReal (c.h * _) + ENNReal.ofReal (c.p * _) + ENNReal.ofReal (c.θ * _)
  rw [ENNReal.ofReal_mul hc.h_pos.le, ENNReal.ofReal_mul hc.p_pos.le,
    ENNReal.ofReal_mul hc.θ_nonneg]
  rfl

lemma OPT_eq (c : PerishBaseStock.Penalty.Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    PerishBaseStock.Penalty.OPT c P = PerishBaseStock.Lifetime.OPT P (toLife c hc) := by
  unfold PerishBaseStock.Penalty.OPT PerishBaseStock.Lifetime.OPT
  congr 1
  funext π
  unfold PerishBaseStock.Penalty.policyCost PerishBaseStock.Lifetime.policyCost
    PerishBaseStock.Penalty.longRunAverage PerishBaseStock.Lifetime.cesaroLimsup
  simp only [periodCost_eq c hc]

lemma avgO_eq (c : PerishBaseStock.Penalty.Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) :
    avgOutdating c P S = PerishBaseStock.Lifetime.avgOutdate P c.m S := by
  unfold avgOutdating PerishBaseStock.Penalty.longRunAverage PerishBaseStock.Lifetime.avgOutdate
    PerishBaseStock.Lifetime.avgOutdateFrom
  simp only [PerishBaseStock.Penalty.outdated, PerishBaseStock.Penalty.orderQty, run_eq]
  rfl

end PerishPenaltyEq25Aux

open PerishBaseStock.Penalty PerishPenaltyEq25Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0)
    (hS : IsHeuristicLevel c P S) :
    baseStockCost c P S ≤ OPT c P + ENNReal.ofReal (c.θ *
      ((∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ) / (c.m : ℝ)) 0 ∂P.law) -
        ∫ d, max ((1 / (c.m : ℝ)) * (∑ i ∈ Finset.range c.m, (d i : ℝ)) - (S : ℝ) / (c.m : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P)) := by
  have hm := hc.one_le_m
  have hmR : (0 : ℝ) < c.m := by exact_mod_cast hm
  have hdec := cost_decomp c hc P S
  have hL2 := (PerishBaseStock.Lifetime.lemma_2 P c.m hm S).2.1
  rw [← avgO_eq c P S] at hL2
  have hP2 := PerishBaseStock.Lifetime.proposition_2 P (toLife c hc) S hS
  rw [← OPT_eq c hc P] at hP2
  set s : ℝ := (S : ℝ) / (c.m : ℝ) with hs
  have hcoe : ((S / (c.m : ℝ≥0) : ℝ≥0) : ℝ) = s := by rw [hs]; push_cast; rfl
  set μ := CappedBaseStock.demandPathLaw P with hμ
  set avg : CappedBaseStock.DemandPath → ℝ :=
    fun d => (1 / (c.m : ℝ)) * ∑ i ∈ Finset.range c.m, (d i : ℝ) with havg
  -- coordinates of the path have law `P.law`
  have hcoordI : ∀ i, Integrable (fun d : CappedBaseStock.DemandPath => (d i : ℝ)) μ := by
    intro i
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i).integrable_comp_of_integrable
      P.finiteMean
    exact h
  have hcoord : ∀ i, ∫ d, (d i : ℝ) ∂μ = CappedBaseStock.mean P := by
    intro i
    have h := integral_map (μ := Measure.infinitePi (fun _ : ℕ => P.law))
      (measurable_pi_apply i).aemeasurable
      (f := fun x : ℝ≥0 => (x : ℝ)) (NNReal.continuous_coe.aestronglyMeasurable)
    rw [Measure.infinitePi_map_eval] at h
    exact h.symm
  have havgI : Integrable avg μ :=
    (integrable_finsetSum _ (fun i _ => hcoordI i)).const_mul _
  have havgE : ∫ d, avg d ∂μ = CappedBaseStock.mean P := by
    simp only [havg]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hcoordI i)]
    simp only [hcoord, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  -- (I1) for `D`
  have hI1 : (∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law) - ∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law =
      s - CappedBaseStock.mean P := by
    rw [← integral_sub (int_hold P.law s) (int_short P s)]
    have : (fun x : ℝ≥0 => max (s - (x : ℝ)) 0 - max ((x : ℝ) - s) 0) =
        fun x : ℝ≥0 => s - (x : ℝ) := by
      funext x
      rcases le_total (x : ℝ) s with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [this, integral_sub (integrable_const s) P.finiteMean]
    simp [CappedBaseStock.mean]
  -- (I3) for the average
  have hI3 : (∫ d, max (s - avg d) 0 ∂μ) - ∫ d, max (avg d - s) 0 ∂μ =
      s - CappedBaseStock.mean P := by
    have i1 : Integrable (fun d => max (s - avg d) 0) μ := ((integrable_const s).sub havgI).pos_part
    have i2 : Integrable (fun d => max (avg d - s) 0) μ := (havgI.sub (integrable_const s)).pos_part
    rw [← integral_sub i1 i2]
    have : (fun d => max (s - avg d) 0 - max (avg d - s) 0) = fun d => s - avg d := by
      funext d
      rcases le_total (avg d) s with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [this, integral_sub (integrable_const s) havgI, havgE]
    simp
  -- (I2) the lead-time holding term
  have hI2 : (1 / (c.m : ℝ)) * ∫ y : ℝ≥0, max ((S : ℝ) - (y : ℝ)) 0
      ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) = ∫ d, max (s - avg d) 0 ∂μ := by
    unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
    have hsm : AEStronglyMeasurable (fun y : ℝ≥0 => max ((S : ℝ) - (y : ℝ)) 0)
        (Measure.map (fun d : CappedBaseStock.DemandPath => ∑ i ∈ Finset.range (c.m - 1 + 1), d i)
          (CappedBaseStock.demandPathLaw P)) :=
      ((continuous_const.sub NNReal.continuous_coe).max continuous_const).aestronglyMeasurable
    rw [integral_map (f := fun y : ℝ≥0 => max ((S : ℝ) - (y : ℝ)) 0)
      (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)).aemeasurable hsm,
      ← integral_const_mul]
    congr 1
    funext d
    rw [show c.m - 1 + 1 = c.m by omega, mul_max_of_nonneg _ _ (by positivity), mul_zero]
    congr 1
    simp only [havg, hs]
    push_cast
    field_simp
  have hEHn : 0 ≤ c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law :=
    mul_nonneg hc.h_pos.le (integral_nonneg (fun _ => le_max_right _ _))
  have hESn : 0 ≤ c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law :=
    mul_nonneg hc.p_pos.le (integral_nonneg (fun _ => le_max_right _ _))
  have han : 0 ≤ c.θ * ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law :=
    mul_nonneg hc.θ_nonneg (integral_nonneg (fun _ => le_max_right _ _))
  have hL2' : avgOutdating c P S ≤ ENNReal.ofReal (∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law) := by
    have h := hL2
    unfold LostSalesOrderUpTo.Asymptotic.expectedHolding at h
    rwa [hcoe] at h
  have hH : PerishBaseStock.Lifetime.heuristicCost P (toLife c hc) S =
      c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) + c.θ / (c.m : ℝ) *
      ∫ y : ℝ≥0, max ((S : ℝ) - (y : ℝ)) 0 ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) :=
    rfl
  calc baseStockCost c P S
      ≤ ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal c.θ * avgOutdating c P S := hdec
    _ ≤ ENNReal.ofReal (c.h * ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal (c.p * ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) +
        ENNReal.ofReal c.θ * ENNReal.ofReal (∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law) := by
        gcongr
    _ = ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P (toLife c hc) S +
          c.θ * ((∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) - ∫ d, max (avg d - s) 0 ∂μ)) := by
        rw [← ENNReal.ofReal_mul hc.θ_nonneg, ← ENNReal.ofReal_add hEHn hESn,
          ← ENNReal.ofReal_add (add_nonneg hEHn hESn) han]
        congr 1
        rw [hH]
        have e : c.θ / (c.m : ℝ) * ∫ y : ℝ≥0, max ((S : ℝ) - (y : ℝ)) 0
            ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) =
            c.θ * ((1 / (c.m : ℝ)) * ∫ y : ℝ≥0, max ((S : ℝ) - (y : ℝ)) 0
            ∂LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) := by ring
        rw [e, hI2]
        linear_combination c.θ * hI1 - c.θ * hI3
    _ ≤ ENNReal.ofReal (PerishBaseStock.Lifetime.heuristicCost P (toLife c hc) S) +
        ENNReal.ofReal (c.θ * ((∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) -
          ∫ d, max (avg d - s) 0 ∂μ)) := ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr
