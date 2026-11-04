-- Prove2me | solution 1 for PerishBaseStock.Penalty.eq_EC_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:06:02.256703+00:00
-- url     : https://prove2.me/submissions/0953ccf4-4972-4163-8f46-356ca2043fad

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyEC13Aux
open PerishBaseStock.Penalty

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

end PerishPenaltyEC13Aux

open PerishBaseStock.Penalty PerishPenaltyEC13Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) (S : ℝ≥0) (hS : IsHeuristicLevel c P S) :
    c.p * LostSalesOrderUpTo.Asymptotic.expectedShortfall P.law S ≤
        c.p * ((upperSupport P).toReal - S) * (P.law (Set.Ioi S)).toReal ∧
      c.p * ((upperSupport P).toReal - S) * (P.law (Set.Ioi S)).toReal ≤
        (c.h + c.θ) * ((upperSupport P).toReal - S) := by
  have := leadTimeLaw_prob P (c.m - 1)
  set μL := LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1) with hμL
  set Dn : ℝ≥0 := (upperSupport P).toNNReal with hDn
  have hDnE : (Dn : ℝ≥0∞) = upperSupport P := ENNReal.coe_toNNReal hP.ne
  have hDnR : (upperSupport P).toReal = (Dn : ℝ) := rfl
  rw [hDnR]
  have hm : (1 : ℝ) ≤ c.m := by exact_mod_cast hc.one_le_m
  have hθm : 0 ≤ c.θ / (c.m : ℝ) := div_nonneg hc.θ_nonneg (by linarith)
  have hθm' : c.θ / (c.m : ℝ) ≤ c.θ := div_le_self hc.θ_nonneg hm
  -- the heuristic cost in terms of the three integrals
  have heq : ∀ S : ℝ≥0, heuristicCost c P S =
      c.h * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) +
      c.p * (∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law) +
      c.θ / (c.m : ℝ) * (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂μL) := fun _ => rfl
  -- demand is a.s. at most `D̄`
  have hnull : P.law (Set.Ioi Dn) = 0 := by
    have hx : ∀ x : ℝ≥0, Dn < x → P.law (Set.Ioi x) = 0 := by
      intro x hx
      have h1 : P.law (Set.Iic x) = 1 := by
        by_contra hne
        have hlt : P.law (Set.Iic x) < 1 := lt_of_le_of_ne prob_le_one hne
        have : (x : ℝ≥0∞) ≤ upperSupport P :=
          le_iSup₂ (f := fun (x : ℝ≥0) (_ : P.law (Set.Iic x) < 1) => (x : ℝ≥0∞)) x hlt
        rw [← hDnE] at this
        exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hx)
      rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h1, tsub_self]
    rw [Ioi_eq_iUnion]
    exact measure_iUnion_null (fun n => hx _ (lt_add_of_pos_right _ (by positivity)))
  have hae : ∀ᵐ x ∂P.law, x ≤ Dn := by
    rw [ae_iff]
    have : {a : ℝ≥0 | ¬ a ≤ Dn} = Set.Ioi Dn := by ext; simp
    rw [this]; exact hnull
  -- `S̃ ≤ D̄`
  have hSle : S ≤ Dn := by
    by_contra hlt
    push Not at hlt
    have h := hS Dn
    rw [heq, heq] at h
    have hlt' : (Dn : ℝ) < S := hlt
    have hh1 : (S : ℝ) - Dn ≤ (∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂P.law) -
        ∫ x : ℝ≥0, max ((Dn : ℝ) - (x : ℝ)) 0 ∂P.law := by
      rw [← integral_sub (int_hold P.law _) (int_hold P.law _)]
      have : ∫ _x : ℝ≥0, ((S : ℝ) - Dn) ∂P.law ≤ ∫ x : ℝ≥0,
          (max ((S : ℝ) - (x : ℝ)) 0 - max ((Dn : ℝ) - (x : ℝ)) 0) ∂P.law := by
        apply integral_mono_ae (integrable_const _) ((int_hold P.law _).sub (int_hold P.law _))
        filter_upwards [hae] with x hx
        have hx' : (x : ℝ) ≤ Dn := hx
        show (S : ℝ) - Dn ≤ max ((S : ℝ) - (x : ℝ)) 0 - max ((Dn : ℝ) - (x : ℝ)) 0
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        linarith
      simpa using this
    have hs1 : ∫ x : ℝ≥0, max ((x : ℝ) - (Dn : ℝ)) 0 ∂P.law = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with x hx
      have hx' : (x : ℝ) ≤ Dn := hx
      simp [max_eq_right (by linarith : (x : ℝ) - Dn ≤ 0)]
    have hs2 : 0 ≤ ∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ)) 0 ∂P.law :=
      integral_nonneg (fun _ => le_max_right _ _)
    have hl := hold_mono μL hlt'.le
    have e1 := mul_le_mul_of_nonneg_left hh1 hc.h_pos.le
    have e2 := mul_le_mul_of_nonneg_left hl hθm
    have e3 := mul_nonneg hc.p_pos.le hs2
    have e4 : 0 < c.h * ((S : ℝ) - Dn) := mul_pos hc.h_pos (by linarith)
    rw [hs1] at h
    nlinarith
  have hSle' : (S : ℝ) ≤ Dn := hSle
  -- inequality (5): `p P(D > S̃) ≤ h + θ/m`
  have hq : c.p * (P.law (Set.Ioi S)).toReal ≤ c.h + c.θ / c.m := by
    have hn : ∀ n : ℕ, c.p * (P.law (Set.Ioi (S + 1 / ((n : ℝ≥0) + 1)))).toReal ≤
        c.h + c.θ / c.m := by
      intro n
      set ε : ℝ≥0 := 1 / ((n : ℝ≥0) + 1) with hε
      have hε0 : (0 : ℝ) < ε := by
        have : (0 : ℝ≥0) < ε := by positivity
        exact_mod_cast this
      have h := hS (S + ε)
      rw [heq, heq] at h
      have hc1 : ((S + ε : ℝ≥0) : ℝ) = S + ε := by push_cast; ring
      rw [hc1] at h
      have a1 := hold_sub_le P.law (S : ℝ) (S + ε)
      have a2 := hold_sub_le μL (S : ℝ) (S + ε)
      have habs : |(S : ℝ) + ε - S| = ε := by rw [add_sub_cancel_left, abs_of_pos hε0]
      rw [habs] at a1 a2
      have a3 := short_gap P (M := (S : ℝ)) (M' := S + ε)
        (by exact_mod_cast (le_add_of_nonneg_right (zero_le : (0:ℝ≥0) ≤ ε)))
      rw [hc1] at a3
      have hεS : (S : ℝ) + ε - S = ε := by ring
      rw [hεS] at a3
      have b1 := mul_le_mul_of_nonneg_left a1 hc.h_pos.le
      have b2 := mul_le_mul_of_nonneg_left a2 hθm
      have b3 := mul_le_mul_of_nonneg_left a3 hc.p_pos.le
      have key : c.p * (ε * (P.law (Set.Ioi (S + ε))).toReal) ≤ (c.h + c.θ / c.m) * ε := by
        nlinarith
      have key2 : (c.p * (P.law (Set.Ioi (S + ε))).toReal) * ε ≤ (c.h + c.θ / c.m) * ε := by
        nlinarith
      exact le_of_mul_le_mul_right key2 hε0
    have hmono : Monotone (fun n : ℕ => Set.Ioi (S + 1 / ((n : ℝ≥0) + 1))) := by
      intro a b hab
      apply Set.Ioi_subset_Ioi
      have hab' : (a : ℝ≥0) ≤ b := by exact_mod_cast hab
      gcongr
    have ht := tendsto_measure_iUnion_atTop (μ := P.law) hmono
    rw [← Ioi_eq_iUnion] at ht
    have ht2 := (ENNReal.tendsto_toReal (measure_ne_top P.law (Set.Ioi S))).comp ht
    exact le_of_tendsto' (ht2.const_mul c.p) (fun n => hn n)
  constructor
  · -- `E[(D - S̃)^+] ≤ (D̄ - S̃) P(D > S̃)`
    have hmeas : MeasurableSet (Set.Ioi S) := measurableSet_Ioi
    have h1 : ∫ x : ℝ≥0, max ((x : ℝ) - S) 0 ∂P.law ≤
        ∫ x : ℝ≥0, Set.indicator (Set.Ioi S) (fun _ => (Dn : ℝ) - S) x ∂P.law := by
      apply integral_mono_ae (int_short P _) ((integrable_const _).indicator hmeas)
      filter_upwards [hae] with x hx
      have hx' : (x : ℝ) ≤ Dn := hx
      by_cases hxS : x ∈ Set.Ioi S
      · rw [Set.indicator_of_mem hxS]
        have : (S : ℝ) < x := hxS
        rw [max_eq_left (by linarith)]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        have : (x : ℝ) ≤ S := not_lt.1 hxS
        rw [max_eq_right (by linarith)]
    rw [integral_indicator_const _ hmeas, smul_eq_mul, measureReal_def] at h1
    have := mul_le_mul_of_nonneg_left h1 hc.p_pos.le
    show c.p * ∫ x : ℝ≥0, max ((x : ℝ) - S) 0 ∂P.law ≤ _
    nlinarith
  · have hq' : c.p * (P.law (Set.Ioi S)).toReal ≤ c.h + c.θ := by linarith
    have hD : 0 ≤ (Dn : ℝ) - S := by linarith
    have := mul_le_mul_of_nonneg_right hq' hD
    nlinarith
