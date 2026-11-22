-- Prove2me | solution 1 for PerishBaseStock.Penalty.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:19:49.150222+00:00
-- url     : https://prove2.me/submissions/3c103f8e-2197-424a-9ece-1e799d631acf

import Definitions.Def_PerishBaseStock_Penalty_Model
import Theorems.Thm_FKZAvg_WStar_theorem_2
import Theorems.Thm_FKZAvg_WStar_theorem_3
import Theorems.Thm_SchalAvg_AvgOpt_lemma_1_2

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace Lemma6Proof

open PerishBaseStock.Penalty
open LostSalesOrderUpTo.Asymptotic
open FeinbergLiang.ACOE SchalAvg.AvgOpt FKZAvg.WStar

abbrev State (m : ℕ) := PerishBaseStock.Lifetime.State m
abbrev emptyState (m : ℕ) := PerishBaseStock.Lifetime.emptyState m
abbrev topLevel {m : ℕ} := @PerishBaseStock.Lifetime.topLevel m
abbrev orderUpTo {m : ℕ} := @PerishBaseStock.Lifetime.orderUpTo m
abbrev firstLevel {m : ℕ} := @PerishBaseStock.Lifetime.firstLevel m
abbrev levelAbove {m : ℕ} := @PerishBaseStock.Lifetime.levelAbove m
abbrev outdate {m : ℕ} := @PerishBaseStock.Lifetime.outdate m
abbrev step {m : ℕ} := @PerishBaseStock.Lifetime.step m
abbrev InvPolicy (m : ℕ) := PerishBaseStock.Lifetime.Policy m

/-! ### Section 1: Newsvendor and floor-level properties -/

section Newsvendor

lemma integrable_max_sub (P : CappedBaseStock.DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max (y - (d : ℝ)) 0) P.law := by
  refine Integrable.mono' (integrable_const (|y|)) (by fun_prop) ?_
  filter_upwards with d
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [d.coe_nonneg, le_abs_self y]) (abs_nonneg y)

lemma integrable_sub_max (P : CappedBaseStock.DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max ((d : ℝ) - y) 0) P.law := by
  refine Integrable.mono' (P.finiteMean.add (integrable_const |y|)) (by fun_prop) ?_
  filter_upwards with d
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  simp only [Pi.add_apply]
  exact max_le (by linarith [neg_abs_le y]) (by linarith [d.coe_nonneg, abs_nonneg y])

def g0 (c : Params) (P : CappedBaseStock.DemandLaw) (y : ℝ) : ℝ :=
  c.h * (∫ d : ℝ≥0, max (y - (d : ℝ)) 0 ∂P.law) +
    c.p * (∫ d : ℝ≥0, max ((d : ℝ) - y) 0 ∂P.law)

lemma g0_coe (c : Params) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) :
    g0 c P (S : ℝ) = backorderCost P.law c.h c.p S := rfl

lemma g0_nonneg (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (y : ℝ) :
    0 ≤ g0 c P y := by
  unfold g0
  have h1 : 0 ≤ ∫ d : ℝ≥0, max (y - (d : ℝ)) 0 ∂P.law :=
    integral_nonneg fun _ => le_max_right _ _
  have h2 : 0 ≤ ∫ d : ℝ≥0, max ((d : ℝ) - y) 0 ∂P.law :=
    integral_nonneg fun _ => le_max_right _ _
  nlinarith [hc.h_pos, hc.p_pos]

lemma g0_sub_eq (c : Params) (P : CappedBaseStock.DemandLaw) (a b : ℝ) :
    g0 c P b - g0 c P a =
      (c.h + c.p) * (∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law) -
        c.p * (b - a) := by
  unfold g0
  have h1 := integrable_max_sub P b
  have h2 := integrable_max_sub P a
  have h3 := integrable_sub_max P b
  have h4 := integrable_sub_max P a
  have hsub1 : (∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) - (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law) =
      ∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law :=
    (integral_sub h1 h2).symm
  have hsub2 : (∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) - (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law) =
      ∫ d : ℝ≥0, (max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0) ∂P.law :=
    (integral_sub h3 h4).symm
  have hpt : ∀ d : ℝ≥0, max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0 =
      (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) - (b - a) := by
    intro d
    rcases le_total b (d : ℝ) with hbd | hdb <;> rcases le_total a (d : ℝ) with had | hda
    · rw [max_eq_left (sub_nonneg.mpr hbd), max_eq_left (sub_nonneg.mpr had),
        max_eq_right (sub_nonpos.mpr hbd), max_eq_right (sub_nonpos.mpr had)]; ring
    · rw [max_eq_left (sub_nonneg.mpr hbd), max_eq_right (sub_nonpos.mpr hda),
        max_eq_right (sub_nonpos.mpr hbd), max_eq_left (sub_nonneg.mpr hda)]; ring
    · rw [max_eq_right (sub_nonpos.mpr hdb), max_eq_left (sub_nonneg.mpr had),
        max_eq_left (sub_nonneg.mpr hdb), max_eq_right (sub_nonpos.mpr had)]; ring
    · rw [max_eq_right (sub_nonpos.mpr hdb), max_eq_right (sub_nonpos.mpr hda),
        max_eq_left (sub_nonneg.mpr hdb), max_eq_left (sub_nonneg.mpr hda)]; ring
  have h12 : Integrable (fun d : ℝ≥0 => max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) P.law :=
    h1.sub h2
  have hint2 : ∫ d : ℝ≥0, (max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0) ∂P.law =
      (∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law) - (b - a) := by
    simp_rw [hpt]
    rw [integral_sub h12 (integrable_const (b - a)), integral_const]
    simp [measureReal_def]
  calc
    c.h * (∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) + c.p * (∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) -
        (c.h * (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law) + c.p * (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law))
      = c.h * ((∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) - (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law)) +
        c.p * ((∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) - (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law)) := by ring
    _ = c.h * (∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law) +
        c.p * ((∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law) - (b - a)) := by
          rw [hsub1, hsub2, hint2]
    _ = _ := by ring

lemma abs_max_sub_max_le (u v : ℝ) : |max u 0 - max v 0| ≤ |u - v| := by
  rw [abs_le]
  have h1 : u - v ≤ |u - v| := le_abs_self _
  have h2 : v - u ≤ |u - v| := by rw [abs_sub_comm]; exact le_abs_self _
  have h3 : 0 ≤ |u - v| := abs_nonneg _
  constructor
  · have : max v 0 ≤ max u 0 + |u - v| :=
      max_le (by linarith [le_max_left u 0]) (by linarith [le_max_right u 0])
    linarith
  · have : max u 0 ≤ max v 0 + |u - v| :=
      max_le (by linarith [le_max_left v 0]) (by linarith [le_max_right v 0])
    linarith

lemma g0_lipschitz (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (a b : ℝ) :
    |g0 c P b - g0 c P a| ≤ (c.h + c.p) * |b - a| := by
  have h1 : ∀ d : ℝ≥0, |max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0| ≤ |b - a| := fun d => by
    have := abs_max_sub_max_le (b - d) (a - d)
    simpa [sub_sub_sub_cancel_right] using this
  have h2 : ∀ d : ℝ≥0, |max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0| ≤ |b - a| := fun d => by
    have := abs_max_sub_max_le ((d : ℝ) - b) ((d : ℝ) - a)
    simpa [sub_sub_sub_cancel_left, abs_sub_comm] using this
  have hi1 : |(∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) - (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law)| ≤ |b - a| := by
    rw [← integral_sub (integrable_max_sub P b) (integrable_max_sub P a)]
    calc |∫ d : ℝ≥0, (max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0) ∂P.law|
        ≤ ∫ d : ℝ≥0, |max (b - (d : ℝ)) 0 - max (a - (d : ℝ)) 0| ∂P.law :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ≥0, |b - a| ∂P.law :=
          integral_mono ((integrable_max_sub P b).sub (integrable_max_sub P a)).abs
            (integrable_const _) h1
      _ = |b - a| := by simp [measureReal_def]
  have hi2 : |(∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) - (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law)| ≤ |b - a| := by
    rw [← integral_sub (integrable_sub_max P b) (integrable_sub_max P a)]
    calc |∫ d : ℝ≥0, (max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0) ∂P.law|
        ≤ ∫ d : ℝ≥0, |max ((d : ℝ) - b) 0 - max ((d : ℝ) - a) 0| ∂P.law :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ≥0, |b - a| ∂P.law :=
          integral_mono ((integrable_sub_max P b).sub (integrable_sub_max P a)).abs
            (integrable_const _) h2
      _ = |b - a| := by simp [measureReal_def]
  unfold g0
  let I1 := (∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) - (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law)
  let I2 := (∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) - (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law)
  have heq : c.h * (∫ d : ℝ≥0, max (b - (d : ℝ)) 0 ∂P.law) + c.p * (∫ d : ℝ≥0, max ((d : ℝ) - b) 0 ∂P.law) -
      (c.h * (∫ d : ℝ≥0, max (a - (d : ℝ)) 0 ∂P.law) + c.p * (∫ d : ℝ≥0, max ((d : ℝ) - a) 0 ∂P.law)) =
      c.h * I1 + c.p * I2 := by dsimp only [I1, I2]; ring
  rw [heq]
  calc |c.h * I1 + c.p * I2|
      ≤ |c.h * I1| + |c.p * I2| := abs_add_le _ _
    _ = c.h * |I1| + c.p * |I2| := by
        rw [abs_mul, abs_mul, abs_of_pos hc.h_pos, abs_of_pos hc.p_pos]
    _ ≤ c.h * |b - a| + c.p * |b - a| := by nlinarith [hc.h_pos, hc.p_pos, hi1, hi2]
    _ = (c.h + c.p) * |b - a| := by ring

lemma continuous_g0 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    Continuous (g0 c P) := by
  refine LipschitzWith.continuous (K := Real.toNNReal (c.h + c.p)) ?_
  intro x y
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  have hhp : 0 ≤ c.h + c.p := by linarith [hc.h_pos, hc.p_pos]
  calc ENNReal.ofReal |g0 c P x - g0 c P y|
      ≤ ENNReal.ofReal ((c.h + c.p) * |x - y|) := ENNReal.ofReal_le_ofReal (g0_lipschitz c hc P y x)
    _ = ENNReal.ofReal (c.h + c.p) * ENNReal.ofReal |x - y| := ENNReal.ofReal_mul hhp
    _ = ↑(Real.toNNReal (c.h + c.p)) * ENNReal.ofReal |x - y| := rfl

lemma g0_diff_bounds (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    {a b : ℝ≥0} (hab : a ≤ b) :
    ((b : ℝ) - a) * ((c.h + c.p) * (P.law (Set.Iic a)).toReal - c.p) ≤ g0 c P b - g0 c P a ∧
    g0 c P b - g0 c P a ≤ ((b : ℝ) - a) * ((c.h + c.p) * (P.law (Set.Iio b)).toReal - c.p) := by
  rw [g0_sub_eq]
  have hhp : 0 < c.h + c.p := by linarith [hc.h_pos, hc.p_pos]
  have hlo : ((b : ℝ) - a) * (P.law (Set.Iic a)).toReal ≤
      ∫ d : ℝ≥0, (max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0) ∂P.law := by
    have hpt : ∀ d : ℝ≥0, Set.indicator (Set.Iic a) (fun _ => (b : ℝ) - a) d ≤
        max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0 := by
      intro d
      by_cases hd : d ≤ a
      · have hda : (d : ℝ) ≤ a := NNReal.coe_le_coe.mpr hd
        have hdb : (d : ℝ) ≤ b := le_trans hda (NNReal.coe_le_coe.mpr hab)
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr hd),
          max_eq_left (sub_nonneg.mpr hda), max_eq_left (sub_nonneg.mpr hdb)]
        linarith
      · rw [Set.indicator_of_notMem (show d ∉ Set.Iic a from hd)]
        have : (a : ℝ) - d ≤ (b : ℝ) - d := by linarith [NNReal.coe_le_coe.mpr hab]
        linarith [max_le_max_right 0 this]
    calc ((b : ℝ) - a) * (P.law (Set.Iic a)).toReal
        = ∫ d : ℝ≥0, Set.indicator (Set.Iic a) (fun _ => (b : ℝ) - a) d ∂P.law := by
          rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_comm, measureReal_def]
      _ ≤ ∫ d : ℝ≥0, (max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0) ∂P.law :=
          integral_mono ((integrable_const _).indicator measurableSet_Iic)
            ((integrable_max_sub P b).sub (integrable_max_sub P a)) hpt
  have hhi : ∫ d : ℝ≥0, (max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0) ∂P.law ≤
      ((b : ℝ) - a) * (P.law (Set.Iio b)).toReal := by
    have hpt : ∀ d : ℝ≥0, max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0 ≤
        Set.indicator (Set.Iio b) (fun _ => (b : ℝ) - a) d := by
      intro d
      by_cases hd : d < b
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hd)]
        have hba : (a : ℝ) ≤ b := NNReal.coe_le_coe.mpr hab
        have h1 : max ((b : ℝ) - d) 0 ≤ max ((a : ℝ) - d) 0 + ((b : ℝ) - a) :=
          max_le (by linarith [le_max_left ((a : ℝ) - d) 0])
            (by linarith [le_max_right ((a : ℝ) - d) 0])
        linarith
      · push Not at hd
        have hbd : (b : ℝ) ≤ d := NNReal.coe_le_coe.mpr hd
        have had : (a : ℝ) ≤ d := le_trans (NNReal.coe_le_coe.mpr hab) hbd
        rw [Set.indicator_of_notMem (Set.notMem_Iio.mpr hd),
          max_eq_right (sub_nonpos.mpr hbd), max_eq_right (sub_nonpos.mpr had)]
        linarith
    calc ∫ d : ℝ≥0, (max ((b : ℝ) - (d : ℝ)) 0 - max ((a : ℝ) - (d : ℝ)) 0) ∂P.law
        ≤ ∫ d : ℝ≥0, Set.indicator (Set.Iio b) (fun _ => (b : ℝ) - a) d ∂P.law :=
          integral_mono ((integrable_max_sub P b).sub (integrable_max_sub P a))
            ((integrable_const _).indicator measurableSet_Iio) hpt
      _ = ((b : ℝ) - a) * (P.law (Set.Iio b)).toReal := by
          rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_comm, measureReal_def]
  constructor <;> nlinarith

lemma quantile_props (P : CappedBaseStock.DemandLaw) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    let S := sInf {x : ℝ≥0 | ENNReal.ofReal q ≤ P.law (Set.Iic x)}
    {x : ℝ≥0 | ENNReal.ofReal q ≤ P.law (Set.Iic x)}.Nonempty ∧
    q ≤ (P.law (Set.Iic S)).toReal ∧
    (P.law (Set.Iio S)).toReal ≤ q := by
  intro S
  set A := {x : ℝ≥0 | ENNReal.ofReal q ≤ P.law (Set.Iic x)}
  have hne : A.Nonempty := by
    have htend : Tendsto (fun n : ℕ => P.law (Set.Iic (n : ℝ≥0))) atTop (𝓝 (P.law Set.univ)) := by
      have hunion : (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = Set.univ := by
        ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
        exact exists_nat_ge x
      rw [← hunion]
      exact tendsto_measure_iUnion_atTop fun m n hmn =>
        Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn)
    rw [measure_univ] at htend
    have hlt : ENNReal.ofReal q < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hq1
    have hev := (tendsto_order.mp htend).1 (ENNReal.ofReal q) hlt
    rcases hev.exists with ⟨n, hn⟩
    exact ⟨(n : ℝ≥0), le_of_lt hn⟩
  have hright : q ≤ (P.law (Set.Iic S)).toReal := by
    have hstep : ∀ n : ℕ, ENNReal.ofReal q ≤ P.law (Set.Iic (S + (1 : ℝ≥0) / ((n : ℝ≥0) + 1))) := by
      intro n
      have hpos : (0 : ℝ≥0) < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) := by positivity
      have hlt : S < S + (1 : ℝ≥0) / ((n : ℝ≥0) + 1) := lt_add_of_pos_right S hpos
      rcases exists_lt_of_csInf_lt hne hlt with ⟨x, hxA, hxl⟩
      exact le_trans hxA (measure_mono (Set.Iic_subset_Iic.mpr (le_of_lt hxl)))
    have hinter : (⋂ n : ℕ, Set.Iic (S + (1 : ℝ≥0) / ((n : ℝ≥0) + 1))) = Set.Iic S := by
      ext y; simp only [Set.mem_iInter, Set.mem_Iic]
      constructor
      · intro hy
        by_contra hgt
        push Not at hgt
        have hdiff : (0 : ℝ) < (y : ℝ) - S := sub_pos.mpr (NNReal.coe_lt_coe.mpr hgt)
        rcases exists_nat_one_div_lt hdiff with ⟨n, hn⟩
        have hyn := hy n
        have hyn' : (y : ℝ) ≤ (S : ℝ) + 1 / ((n : ℝ) + 1) := by exact_mod_cast hyn
        linarith
      · intro hy n
        exact le_trans hy le_self_add
    have htend : Tendsto (fun n : ℕ => P.law (Set.Iic (S + (1 : ℝ≥0) / ((n : ℝ≥0) + 1)))) atTop
        (𝓝 (P.law (Set.Iic S))) := by
      rw [← hinter]
      refine tendsto_measure_iInter_atTop (fun n => measurableSet_Iic.nullMeasurableSet) ?_
        ⟨0, measure_ne_top P.law _⟩
      intro m n hmn
      refine Set.Iic_subset_Iic.mpr (add_le_add_right ?_ S)
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    have hle : ENNReal.ofReal q ≤ P.law (Set.Iic S) :=
      ge_of_tendsto htend (Eventually.of_forall hstep)
    have hfin : P.law (Set.Iic S) ≠ ⊤ := measure_ne_top P.law _
    rwa [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hle
  have hleft : (P.law (Set.Iio S)).toReal ≤ q := by
    by_cases hS0 : S = 0
    · rw [hS0]; simp [hq0]
    · have hSpos : (0 : ℝ≥0) < S := pos_iff_ne_zero.mpr hS0
      let x : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) / ((n : ℝ≥0) + 1)) * S
      have hx_lt : ∀ n : ℕ, x n < S := by
        intro n
        have h1 : (n : ℝ≥0) / ((n : ℝ≥0) + 1) < 1 := by
          rw [div_lt_one (by positivity)]; exact lt_add_one (n : ℝ≥0)
        calc x n = ((n : ℝ≥0) / ((n : ℝ≥0) + 1)) * S := rfl
          _ < 1 * S := mul_lt_mul_of_pos_right h1 hSpos
          _ = S := one_mul S
      have hx_mono : Monotone x := by
        intro m n hmn
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hmn' : (m : ℝ≥0) ≤ n := Nat.cast_le.mpr hmn
        nlinarith
      have hunion : (⋃ n : ℕ, Set.Iic (x n)) = Set.Iio S := by
        ext y; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio]
        constructor
        · rintro ⟨n, hn⟩; exact lt_of_le_of_lt hn (hx_lt n)
        · intro hy
          have hpos : (0 : ℝ) < ((S : ℝ) - y) / S :=
            div_pos (sub_pos.mpr (NNReal.coe_lt_coe.mpr hy)) (NNReal.coe_pos.mpr hSpos)
          rcases exists_nat_one_div_lt hpos with ⟨n, hn⟩
          refine ⟨n, ?_⟩
          rw [← NNReal.coe_le_coe]
          change (y : ℝ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) * (S : ℝ)
          have hS' : (0 : ℝ) < S := NNReal.coe_pos.mpr hSpos
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have : 1 / ((n : ℝ) + 1) * (S : ℝ) < (S : ℝ) - y := by
            rwa [lt_div_iff₀ hS'] at hn
          have heq : ((n : ℝ) / ((n : ℝ) + 1)) * (S : ℝ) = (S : ℝ) - 1 / ((n : ℝ) + 1) * (S : ℝ) := by
            field_simp; ring
          linarith
      have htend : Tendsto (fun n : ℕ => P.law (Set.Iic (x n))) atTop (𝓝 (P.law (Set.Iio S))) := by
        rw [← hunion]
        exact tendsto_measure_iUnion_atTop fun m n hmn => Set.Iic_subset_Iic.mpr (hx_mono hmn)
      have hlt_step : ∀ n : ℕ, P.law (Set.Iic (x n)) ≤ ENNReal.ofReal q := by
        intro n
        by_contra hgt
        push Not at hgt
        have hmem : x n ∈ A := le_of_lt hgt
        exact not_le_of_gt (hx_lt n) (csInf_le (OrderBot.bddBelow A) hmem)
      have hle : P.law (Set.Iio S) ≤ ENNReal.ofReal q :=
        le_of_tendsto htend (Eventually.of_forall hlt_step)
      have hfin : P.law (Set.Iio S) ≠ ⊤ := measure_ne_top P.law _
      rwa [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff hq0] at hle
  exact ⟨hne, hright, hleft⟩

lemma g0_antitone_le_NP (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ newsvendorLevel P.law c.h c.p) :
    g0 c P b ≤ g0 c P a := by
  have hhp : 0 < c.p + c.h := by linarith [hc.h_pos, hc.p_pos]
  have hq0 : 0 ≤ c.p / (c.p + c.h) := div_nonneg (le_of_lt hc.p_pos) (le_of_lt hhp)
  have hq1 : c.p / (c.p + c.h) < 1 := (div_lt_one hhp).mpr (by linarith [hc.h_pos])
  have hqp := quantile_props P hq0 hq1
  have hIio : (P.law (Set.Iio b)).toReal ≤ c.p / (c.p + c.h) := by
    have hm : P.law (Set.Iio b) ≤ P.law (Set.Iio (newsvendorLevel P.law c.h c.p)) :=
      measure_mono (Set.Iio_subset_Iio hb)
    exact le_trans (ENNReal.toReal_mono (measure_ne_top P.law _) hm) hqp.2.2
  have hdiff := (g0_diff_bounds c hc P hab).2
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab)
  have hslope : (c.h + c.p) * (P.law (Set.Iio b)).toReal - c.p ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hIio (le_of_lt hhp)
    rw [mul_div_cancel₀ _ (ne_of_gt hhp)] at this
    linarith
  nlinarith

lemma g0_monotone_ge_NP (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    {a b : ℝ≥0} (ha : newsvendorLevel P.law c.h c.p ≤ a) (hab : a ≤ b) :
    g0 c P a ≤ g0 c P b := by
  have hhp : 0 < c.p + c.h := by linarith [hc.h_pos, hc.p_pos]
  have hq0 : 0 ≤ c.p / (c.p + c.h) := div_nonneg (le_of_lt hc.p_pos) (le_of_lt hhp)
  have hq1 : c.p / (c.p + c.h) < 1 := (div_lt_one hhp).mpr (by linarith [hc.h_pos])
  have hqp := quantile_props P hq0 hq1
  have hIic : c.p / (c.p + c.h) ≤ (P.law (Set.Iic a)).toReal := by
    have hm : P.law (Set.Iic (newsvendorLevel P.law c.h c.p)) ≤ P.law (Set.Iic a) :=
      measure_mono (Set.Iic_subset_Iic.mpr ha)
    exact le_trans hqp.2.1 (ENNReal.toReal_mono (measure_ne_top P.law _) hm)
  have hdiff := (g0_diff_bounds c hc P hab).1
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab)
  have hslope : 0 ≤ (c.h + c.p) * (P.law (Set.Iic a)).toReal - c.p := by
    have := mul_le_mul_of_nonneg_left hIic (le_of_lt hhp)
    rw [mul_div_cancel₀ _ (ne_of_gt hhp)] at this
    linarith
  nlinarith

lemma floorLevel_props (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    (∀ S' : ℝ≥0, floorCost c P (floorLevel c P) ≤ floorCost c P S') ∧
    floorLevel c P ≤ newsvendorLevel P.law c.h c.p := by
  set M := {S : ℝ≥0 | ∀ S' : ℝ≥0, floorCost c P S ≤ floorCost c P S'}
  have hM_closed : IsClosed M := by
    have hcont : Continuous (floorCost c P) := by
      unfold floorCost
      have h1 : Continuous (fun S : ℝ≥0 => g0 c P (S : ℝ)) :=
        (continuous_g0 c hc P).comp NNReal.continuous_coe
      have h2 : Continuous (fun S : ℝ≥0 => c.θ * (S : ℝ)) :=
        continuous_const.mul NNReal.continuous_coe
      exact h1.add h2
    have hM_eq : M = ⋂ S' : ℝ≥0, {S : ℝ≥0 | floorCost c P S ≤ floorCost c P S'} := by
      ext S; simp [M]
    rw [hM_eq]
    exact isClosed_iInter fun S' => isClosed_le hcont continuous_const
  have hex : ∃ S₀ ∈ M, S₀ ≤ newsvendorLevel P.law c.h c.p := by
    by_cases hpθ : c.p ≤ c.θ
    · refine ⟨0, ?_, zero_le⟩
      intro S'
      have hdiff := (g0_diff_bounds c hc P (zero_le : (0 : ℝ≥0) ≤ S')).1
      unfold floorCost
      rw [← g0_coe, ← g0_coe]
      have h0 : 0 ≤ (P.law (Set.Iic 0)).toReal := ENNReal.toReal_nonneg
      have hS' : (0 : ℝ) ≤ (S' : ℝ) := S'.coe_nonneg
      have hhp : 0 < c.h + c.p := by linarith [hc.h_pos, hc.p_pos]
      have h00 : 0 ≤ (c.h + c.p) * (P.law (Set.Iic 0)).toReal := mul_nonneg (le_of_lt hhp) h0
      simp only [NNReal.coe_zero, sub_zero, mul_zero, add_zero] at hdiff ⊢
      nlinarith
    · push Not at hpθ
      have hhp : 0 < c.p + c.h := by linarith [hc.h_pos, hc.p_pos]
      have hq0 : 0 ≤ (c.p - c.θ) / (c.p + c.h) :=
        div_nonneg (sub_nonneg.mpr (le_of_lt hpθ)) (le_of_lt hhp)
      have hq1 : (c.p - c.θ) / (c.p + c.h) < 1 :=
        (div_lt_one hhp).mpr (by linarith [hc.h_pos, hc.θ_nonneg])
      have hqp := quantile_props P hq0 hq1
      set S₀ := sInf {x : ℝ≥0 | ENNReal.ofReal ((c.p - c.θ) / (c.p + c.h)) ≤ P.law (Set.Iic x)}
      have hS₀_mem : S₀ ∈ M := by
        intro S'
        unfold floorCost
        rw [← g0_coe, ← g0_coe]
        rcases le_total S' S₀ with hle | hle
        · have hdiff := (g0_diff_bounds c hc P hle).2
          have hIio : (P.law (Set.Iio S₀)).toReal ≤ (c.p - c.θ) / (c.p + c.h) := hqp.2.2
          have hslope : (c.h + c.p) * (P.law (Set.Iio S₀)).toReal - c.p + c.θ ≤ 0 := by
            have := mul_le_mul_of_nonneg_left hIio (le_of_lt hhp)
            rw [mul_div_cancel₀ _ (ne_of_gt hhp)] at this
            linarith
          have hba : (0 : ℝ) ≤ (S₀ : ℝ) - S' := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)
          nlinarith
        · have hdiff := (g0_diff_bounds c hc P hle).1
          have hIic : (c.p - c.θ) / (c.p + c.h) ≤ (P.law (Set.Iic S₀)).toReal := hqp.2.1
          have hslope : 0 ≤ (c.h + c.p) * (P.law (Set.Iic S₀)).toReal - c.p + c.θ := by
            have := mul_le_mul_of_nonneg_left hIic (le_of_lt hhp)
            rw [mul_div_cancel₀ _ (ne_of_gt hhp)] at this
            linarith
          have hba : (0 : ℝ) ≤ (S' : ℝ) - S₀ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)
          nlinarith
      have hS₀_le : S₀ ≤ newsvendorLevel P.law c.h c.p := by
        have hq_le : (c.p - c.θ) / (c.p + c.h) ≤ c.p / (c.p + c.h) :=
          div_le_div_of_nonneg_right (by linarith [hc.θ_nonneg]) (le_of_lt hhp)
        have hqNP0 : 0 ≤ c.p / (c.p + c.h) := div_nonneg (le_of_lt hc.p_pos) (le_of_lt hhp)
        have hqNP1 : c.p / (c.p + c.h) < 1 := (div_lt_one hhp).mpr (by linarith [hc.h_pos])
        have hqpNP := quantile_props P hqNP0 hqNP1
        refine csInf_le_csInf (OrderBot.bddBelow _) hqpNP.1 ?_
        intro x hx
        exact le_trans (ENNReal.ofReal_le_ofReal hq_le) hx
      exact ⟨S₀, hS₀_mem, hS₀_le⟩
  rcases hex with ⟨S₀, hS₀M, hS₀le⟩
  have hmem : floorLevel c P ∈ M := hM_closed.csInf_mem ⟨S₀, hS₀M⟩ (OrderBot.bddBelow M)
  have hle : floorLevel c P ≤ newsvendorLevel P.law c.h c.p :=
    le_trans (csInf_le (OrderBot.bddBelow M) hS₀M) hS₀le
  exact ⟨hmem, hle⟩

end Newsvendor

/-! ### Section 2: Case `c.m = 1` -/

section CaseM1

lemma lemma_6_m1 (c : Params) (hc : c.Standing) (hm1 : c.m = 1)
    (P : CappedBaseStock.DemandLaw) :
    ∃ π : InvPolicy c.m, policyCost c P π = OPT c P ∧
      ∀ (d : CappedBaseStock.DemandPath) (t : ℕ), (floorLevel c P : ℝ) ≤ totalLevel π d t := by
  let c1 : Params := { m := 1, h := c.h + c.θ, p := c.p, θ := 0 }
  have hc1 : c1.Standing := ⟨le_rfl, by linarith [hc.h_pos, hc.θ_nonneg], hc.p_pos, le_rfl⟩
  let S1 : ℝ≥0 := newsvendorLevel P.law (c.h + c.θ) c.p
  have hS1_min : ∀ S' : ℝ≥0, g0 c1 P S1 ≤ g0 c1 P S' := by
    intro S'
    rcases le_total S' S1 with hle | hle
    · exact g0_antitone_le_NP c1 hc1 P hle le_rfl
    · exact g0_monotone_ge_NP c1 hc1 P le_rfl hle
  have hfl_le_S1 : floorLevel c P ≤ S1 := by
    by_contra hlt
    push Not at hlt
    set M := {S : ℝ≥0 | ∀ S' : ℝ≥0, floorCost c P S ≤ floorCost c P S'}
    have hfl_min := (floorLevel_props c hc P).1
    have hS1_notM : S1 ∉ M := fun hmem => not_le_of_gt hlt (csInf_le (OrderBot.bddBelow M) hmem)
    have hf_lt : floorCost c P (floorLevel c P) < floorCost c P S1 := by
      refine lt_of_le_of_ne (hfl_min S1) ?_
      intro heq
      apply hS1_notM
      intro S'
      rw [← heq]
      exact hfl_min S'
    have hg1_lt : g0 c1 P (floorLevel c P) < g0 c1 P S1 := by
      have hdiff_max : ∫ d : ℝ≥0, (max ((floorLevel c P : ℝ) - (d : ℝ)) 0 -
            max ((S1 : ℝ) - (d : ℝ)) 0) ∂P.law ≤ (floorLevel c P : ℝ) - S1 := by
        calc ∫ d : ℝ≥0, (max ((floorLevel c P : ℝ) - (d : ℝ)) 0 - max ((S1 : ℝ) - (d : ℝ)) 0) ∂P.law
            ≤ ∫ _ : ℝ≥0, ((floorLevel c P : ℝ) - S1) ∂P.law := by
              refine integral_mono ((integrable_max_sub P _).sub (integrable_max_sub P _))
                (integrable_const _) fun d => ?_
              have hlt' : (S1 : ℝ) ≤ (floorLevel c P : ℝ) := le_of_lt (NNReal.coe_lt_coe.mpr hlt)
              have h1 : max ((floorLevel c P : ℝ) - d) 0 ≤
                  max ((S1 : ℝ) - d) 0 + ((floorLevel c P : ℝ) - S1) :=
                max_le (by linarith [le_max_left ((S1 : ℝ) - d) 0])
                  (by linarith [le_max_right ((S1 : ℝ) - d) 0])
              linarith
          _ = (floorLevel c P : ℝ) - S1 := by simp [measureReal_def]
      have hsub := integral_sub (integrable_max_sub P (floorLevel c P)) (integrable_max_sub P S1)
      have h1 : g0 c1 P (floorLevel c P) - g0 c1 P S1 =
          (g0 c P (floorLevel c P) - g0 c P S1) +
            c.θ * ∫ d : ℝ≥0, (max ((floorLevel c P : ℝ) - (d : ℝ)) 0 -
              max ((S1 : ℝ) - (d : ℝ)) 0) ∂P.law := by
        unfold g0 c1; rw [hsub]; ring
      have hf_eq : floorCost c P (floorLevel c P) - floorCost c P S1 =
          (g0 c P (floorLevel c P) - g0 c P S1) + c.θ * ((floorLevel c P : ℝ) - S1) := by
        unfold floorCost; rw [← g0_coe, ← g0_coe]; ring
      nlinarith [hc.θ_nonneg]
    exact not_le_of_gt hg1_lt (hS1_min (floorLevel c P))
  have hm0 : ¬ (0 < c.m - 1) := by omega
  have htop_zero : ∀ x : State c.m, topLevel x = 0 := fun x => by
    simp [topLevel, PerishBaseStock.Lifetime.topLevel, hm0]
  have hfirst : ∀ (x : State c.m) (q : ℝ≥0), firstLevel x q = (q : ℝ) := fun x q => by
    simp [firstLevel, PerishBaseStock.Lifetime.firstLevel,
      PerishBaseStock.Lifetime.orderUpTo, PerishBaseStock.Lifetime.topLevel, hm0]
  have hstate_eq : ∀ x : State c.m, x = emptyState c.m := fun x => by
    ext j; exact absurd j.isLt (by omega)
  have hperiod_int : ∀ (π : InvPolicy c.m) (t : ℕ),
      ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P =
        ENNReal.ofReal (g0 c1 P (π.φ t (emptyState c.m))) := by
    intro π t
    let q := π.φ t (emptyState c.m)
    have hpt : ∀ d : CappedBaseStock.DemandPath,
        periodCost c π d t =
          ENNReal.ofReal (c.h * max ((q : ℝ) - d t) 0 + c.p * max ((d t : ℝ) - q) 0 +
            c.θ * max ((q : ℝ) - d t) 0) := by
      intro d
      unfold periodCost totalLevel outdated orderQty
      change ENNReal.ofReal c.h * ENNReal.ofReal (max (orderUpTo (run π d t) (π.φ t (run π d t)) - ↑(d t)) 0) +
          ENNReal.ofReal c.p * ENNReal.ofReal (max (↑(d t) - orderUpTo (run π d t) (π.φ t (run π d t))) 0) +
          ENNReal.ofReal c.θ * ENNReal.ofReal (outdate (run π d t) (π.φ t (run π d t)) (d t)) = _
      rw [hstate_eq (run π d t)]
      change ENNReal.ofReal c.h * ENNReal.ofReal (max (topLevel (emptyState c.m) + (q : ℝ) - ↑(d t)) 0) +
          ENNReal.ofReal c.p * ENNReal.ofReal (max (↑(d t) - (topLevel (emptyState c.m) + (q : ℝ))) 0) +
          ENNReal.ofReal c.θ * ENNReal.ofReal (max (firstLevel (emptyState c.m) q - ↑(d t)) 0) = _
      rw [htop_zero, hfirst]
      simp only [zero_add]
      rw [← ENNReal.ofReal_mul (le_of_lt hc.h_pos), ← ENNReal.ofReal_mul (le_of_lt hc.p_pos),
        ← ENNReal.ofReal_mul hc.θ_nonneg,
        ← ENNReal.ofReal_add (mul_nonneg (le_of_lt hc.h_pos) (le_max_right _ _))
          (mul_nonneg (le_of_lt hc.p_pos) (le_max_right _ _)),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (le_of_lt hc.h_pos) (le_max_right _ _))
          (mul_nonneg (le_of_lt hc.p_pos) (le_max_right _ _)))
          (mul_nonneg hc.θ_nonneg (le_max_right _ _))]
    simp_rw [hpt]
    have hmap : (CappedBaseStock.demandPathLaw P).map (fun d : CappedBaseStock.DemandPath => d t) =
        P.law := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) t
    have hmeas : Measurable (fun x : ℝ≥0 =>
        ENNReal.ofReal (c.h * max ((q : ℝ) - x) 0 + c.p * max ((x : ℝ) - q) 0 +
          c.θ * max ((q : ℝ) - x) 0)) := by fun_prop
    rw [← lintegral_map hmeas (measurable_pi_apply t), hmap]
    have hint : Integrable (fun x : ℝ≥0 =>
        c.h * max ((q : ℝ) - x) 0 + c.p * max ((x : ℝ) - q) 0 + c.θ * max ((q : ℝ) - x) 0) P.law :=
      (((integrable_max_sub P q).const_mul c.h).add
        ((integrable_sub_max P q).const_mul c.p)).add
        ((integrable_max_sub P q).const_mul c.θ)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by
      dsimp only [Pi.zero_apply]
      have h1 := le_max_right ((q : ℝ) - x) 0
      have h2 := le_max_right ((x : ℝ) - q) 0
      nlinarith [hc.h_pos, hc.p_pos, hc.θ_nonneg])]
    congr 1
    have h1 := integrable_max_sub P q
    have h2 := integrable_sub_max P q
    have h12 : Integrable (fun x : ℝ≥0 => c.h * max ((q : ℝ) - x) 0 + c.p * max ((x : ℝ) - q) 0) P.law :=
      (h1.const_mul c.h).add (h2.const_mul c.p)
    rw [integral_add h12 (h1.const_mul c.θ),
      integral_add (h1.const_mul c.h) (h2.const_mul c.p),
      integral_const_mul, integral_const_mul, integral_const_mul]
    unfold g0 c1; ring
  refine ⟨baseStockPolicy c.m S1, ?_, ?_⟩
  · apply le_antisymm
    · refine le_iInf fun π => ?_
      unfold policyCost longRunAverage
      refine limsup_le_limsup (Eventually.of_forall fun T => ?_)
      refine ENNReal.div_le_div_right (Finset.sum_le_sum fun t _ => ?_) _
      rw [hperiod_int, hperiod_int]
      have hφ : (baseStockPolicy c.m S1).φ t (emptyState c.m) = S1 := by
        simp [baseStockPolicy, htop_zero]
      rw [hφ]
      exact ENNReal.ofReal_le_ofReal (hS1_min _)
    · exact iInf_le _ (baseStockPolicy c.m S1)
  · intro d t
    unfold totalLevel orderQty baseStockPolicy
    change (floorLevel c P : ℝ) ≤ topLevel (run (baseStockPolicy c.m S1) d t) +
      (Real.toNNReal ((S1 : ℝ) - topLevel (run (baseStockPolicy c.m S1) d t)) : ℝ)
    rw [htop_zero]
    simp [NNReal.coe_le_coe.mpr hfl_le_S1]

end CaseM1

/-! ### Section 3: State spaces, dynamics, and MDPs `modelFull`, `modelBox` for `2 ≤ c.m` -/

section MDPSetup

def XFullSet (m : ℕ) : Set (State m) :=
  {x | (∀ j, 0 ≤ x j) ∧ Monotone x}

def XBoxSet (m : ℕ) (S : ℝ≥0) : Set (State m) :=
  {x | (∀ j, 0 ≤ x j) ∧ Monotone x ∧ ∀ j, x j ≤ (S : ℝ)}

abbrev XFull (m : ℕ) := {x : State m // x ∈ XFullSet m}
abbrev XBox (m : ℕ) (S : ℝ≥0) := {x : State m // x ∈ XBoxSet m S}

lemma isClosed_XFullSet (m : ℕ) : IsClosed (XFullSet m) := by
  have h1 : IsClosed {x : State m | ∀ j, 0 ≤ x j} := by
    have : {x : State m | ∀ j, 0 ≤ x j} = ⋂ j, {x : State m | 0 ≤ x j} := by ext x; simp
    rw [this]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {x : State m | Monotone x} := by
    have : {x : State m | Monotone x} = ⋂ (i : Fin (m - 1)), ⋂ (j : Fin (m - 1)),
        ⋂ (_ : i ≤ j), {x : State m | x i ≤ x j} := by
      ext x; simp [Monotone]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply j)
  exact h1.inter h2

lemma isClosed_XBoxSet (m : ℕ) (S : ℝ≥0) : IsClosed (XBoxSet m S) := by
  have h3 : IsClosed {x : State m | ∀ j, x j ≤ (S : ℝ)} := by
    have : {x : State m | ∀ j, x j ≤ (S : ℝ)} = ⋂ j, {x : State m | x j ≤ (S : ℝ)} := by
      ext x; simp
    rw [this]; exact isClosed_iInter fun j => isClosed_le (continuous_apply j) continuous_const
  have heq : XBoxSet m S = XFullSet m ∩ {x : State m | ∀ j, x j ≤ (S : ℝ)} := by
    ext x; simp [XBoxSet, XFullSet, and_assoc]
  rw [heq]
  exact (isClosed_XFullSet m).inter h3

instance standardBorel_XFull (m : ℕ) : StandardBorelSpace (XFull m) := by
  have : PolishSpace (XFull m) := (isClosed_XFullSet m).polishSpace
  infer_instance

instance standardBorel_XBox (m : ℕ) (S : ℝ≥0) : StandardBorelSpace (XBox m S) := by
  have : PolishSpace (XBox m S) := (isClosed_XBoxSet m S).polishSpace
  infer_instance

def x0Full (m : ℕ) : XFull m :=
  ⟨emptyState m, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

def x0Box (m : ℕ) (S : ℝ≥0) : XBox m S :=
  ⟨emptyState m, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => S.coe_nonneg⟩

lemma max_sub_sub_max_eq (a b d : ℝ) (hab : a ≤ b) :
    max (b - d - max (a - d) 0) 0 = max (b - d) 0 - max (a - d) 0 := by
  rcases le_total d a with hda | had
  · have hdb : d ≤ b := le_trans hda hab
    rw [max_eq_left (sub_nonneg.mpr hda), max_eq_left (sub_nonneg.mpr hdb)]
    have : b - d - (a - d) = b - a := by ring
    rw [this, max_eq_left (sub_nonneg.mpr hab)]
  · rw [max_eq_right (sub_nonpos.mpr had), sub_zero, sub_zero]

lemma topLevel_eq_last {m : ℕ} (hm2 : 2 ≤ m) (x : State m) :
    topLevel x = x ⟨m - 2, by omega⟩ := by
  unfold topLevel PerishBaseStock.Lifetime.topLevel
  have h : 0 < m - 1 := by omega
  simp [h]

lemma firstLevel_eq_zero {m : ℕ} (hm2 : 2 ≤ m) (x : State m) (q : ℝ≥0) :
    firstLevel x q = x ⟨0, by omega⟩ := by
  unfold firstLevel PerishBaseStock.Lifetime.firstLevel
  have h : 0 < m - 1 := by omega
  simp [h]

lemma levelAbove_mono {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q : ℝ≥0) :
    Monotone (levelAbove x.val q) := by
  intro i j hij
  unfold levelAbove PerishBaseStock.Lifetime.levelAbove
  split_ifs with hi hj hj
  · exact x.prop.2 (Fin.mk_le_mk.mpr (Nat.add_le_add_right hij 1))
  · have hi_lt := i.isLt
    exact le_trans (x.prop.2 (show (⟨i.val + 1, hi⟩ : Fin (m - 1)) ≤ ⟨m - 2, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega)))
      (by unfold PerishBaseStock.Lifetime.orderUpTo
          rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
            topLevel_eq_last hm2 x.val]
          exact le_add_of_nonneg_right q.coe_nonneg)
  · omega
  · exact le_rfl

lemma firstLevel_le_levelAbove {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q : ℝ≥0) (j : Fin (m - 1)) :
    x.val ⟨0, by omega⟩ ≤ levelAbove x.val q j := by
  unfold levelAbove PerishBaseStock.Lifetime.levelAbove
  split_ifs with hj
  · exact x.prop.2 (Fin.mk_le_mk.mpr (Nat.zero_le _))
  · unfold PerishBaseStock.Lifetime.orderUpTo
    rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
      topLevel_eq_last hm2 x.val]
    exact le_trans (x.prop.2 (Fin.mk_le_mk.mpr (Nat.zero_le _))) (le_add_of_nonneg_right q.coe_nonneg)

lemma step_eq_diff {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q d : ℝ≥0) (j : Fin (m - 1)) :
    step x.val q d j =
      max (levelAbove x.val q j - (d : ℝ)) 0 - max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 := by
  unfold step PerishBaseStock.Lifetime.step PerishBaseStock.Lifetime.outdate
  rw [show PerishBaseStock.Lifetime.firstLevel x.val q = x.val ⟨0, by omega⟩ from
    firstLevel_eq_zero hm2 x.val q]
  exact max_sub_sub_max_eq _ _ _ (firstLevel_le_levelAbove hm2 x q j)

lemma step_mem_XFullSet {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q d : ℝ≥0) :
    step x.val q d ∈ XFullSet m := by
  refine ⟨fun j => le_max_right _ _, fun i j hij => ?_⟩
  unfold step PerishBaseStock.Lifetime.step
  exact max_le_max_right 0 (sub_le_sub_right (sub_le_sub_right (levelAbove_mono hm2 x q hij) _) _)

def stepFull {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q d : ℝ≥0) : XFull m :=
  ⟨step x.val q d, step_mem_XFullSet hm2 x q d⟩

lemma continuous_levelAbove {m : ℕ} (j : Fin (m - 1)) :
    Continuous (fun p : State m × ℝ≥0 => levelAbove p.1 p.2 j) := by
  unfold levelAbove PerishBaseStock.Lifetime.levelAbove
  split_ifs with hj
  · exact (continuous_apply _).comp continuous_fst
  · unfold PerishBaseStock.Lifetime.orderUpTo PerishBaseStock.Lifetime.topLevel
    split_ifs with h0
    · exact ((continuous_apply _).comp continuous_fst).add
        (NNReal.continuous_coe.comp continuous_snd)
    · exact continuous_const.add (NNReal.continuous_coe.comp continuous_snd)

lemma continuous_outdate {m : ℕ} (d : ℝ≥0) :
    Continuous (fun p : State m × ℝ≥0 => outdate p.1 p.2 d) := by
  unfold outdate PerishBaseStock.Lifetime.outdate PerishBaseStock.Lifetime.firstLevel
  split_ifs with h0
  · exact (((continuous_apply _).comp continuous_fst).sub continuous_const).max continuous_const
  · unfold PerishBaseStock.Lifetime.orderUpTo PerishBaseStock.Lifetime.topLevel
    simp only [h0, ↓reduceDIte]
    exact ((continuous_const.add (NNReal.continuous_coe.comp continuous_snd)).sub
      continuous_const).max continuous_const

lemma continuous_step_pair {m : ℕ} (d : ℝ≥0) :
    Continuous (fun p : State m × ℝ≥0 => step p.1 p.2 d) := by
  refine continuous_pi fun j => ?_
  unfold step PerishBaseStock.Lifetime.step
  exact (((continuous_levelAbove j).sub continuous_const).sub
    (continuous_outdate d)).max continuous_const

lemma continuous_step_triple {m : ℕ} :
    Continuous (fun p : (State m × ℝ≥0) × ℝ≥0 => step p.1.1 p.1.2 p.2) := by
  refine continuous_pi fun j => ?_
  unfold step PerishBaseStock.Lifetime.step
  have hlev : Continuous (fun p : (State m × ℝ≥0) × ℝ≥0 => levelAbove p.1.1 p.1.2 j) :=
    (continuous_levelAbove j).comp continuous_fst
  have hout : Continuous (fun p : (State m × ℝ≥0) × ℝ≥0 => outdate p.1.1 p.1.2 p.2) := by
    unfold outdate PerishBaseStock.Lifetime.outdate PerishBaseStock.Lifetime.firstLevel
    split_ifs with h0
    · exact (((continuous_apply _).comp (continuous_fst.comp continuous_fst)).sub
        (NNReal.continuous_coe.comp continuous_snd)).max continuous_const
    · unfold PerishBaseStock.Lifetime.orderUpTo PerishBaseStock.Lifetime.topLevel
      simp only [h0, ↓reduceDIte]
      exact ((continuous_const.add
          (NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst))).sub
          (NNReal.continuous_coe.comp continuous_snd)).max continuous_const
  exact ((hlev.sub (NNReal.continuous_coe.comp continuous_snd)).sub hout).max continuous_const

lemma step_le_orderUpTo {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q d : ℝ≥0) (j : Fin (m - 1)) :
    step x.val q d j ≤ orderUpTo x.val q := by
  rw [step_eq_diff hm2]
  have h1 : levelAbove x.val q j ≤ orderUpTo x.val q := by
    unfold levelAbove PerishBaseStock.Lifetime.levelAbove
    split_ifs with hj
    · unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
        topLevel_eq_last hm2 x.val]
      have hj_lt := j.isLt
      exact le_trans (x.prop.2 (Fin.mk_le_mk.mpr (by omega))) (le_add_of_nonneg_right q.coe_nonneg)
    · exact le_rfl
  have h2 : 0 ≤ orderUpTo x.val q := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
      topLevel_eq_last hm2 x.val]
    exact add_nonneg (x.prop.1 _) q.coe_nonneg
  have h3 : max (levelAbove x.val q j - (d : ℝ)) 0 ≤ orderUpTo x.val q :=
    max_le (by linarith [d.coe_nonneg]) h2
  linarith [le_max_right (x.val ⟨0, by omega⟩ - (d : ℝ)) 0]

def stepBox {m : ℕ} (hm2 : 2 ≤ m) (S : ℝ≥0) (x : XBox m S) (q d : ℝ≥0) : XBox m S :=
  ⟨fun j => min (step x.val q d j) (S : ℝ), by
    have hxFull : x.val ∈ XFullSet m := ⟨x.prop.1, x.prop.2.1⟩
    have hs := step_mem_XFullSet hm2 ⟨x.val, hxFull⟩ q d
    refine ⟨fun j => le_min (hs.1 j) S.coe_nonneg, fun i j hij => min_le_min_right _ (hs.2 hij),
      fun j => min_le_right _ _⟩⟩

lemma stepBox_eq_step {m : ℕ} (hm2 : 2 ≤ m) (S : ℝ≥0) (x : XBox m S) (q d : ℝ≥0)
    (hq : orderUpTo x.val q ≤ (S : ℝ)) :
    (stepBox hm2 S x q d).val = step x.val q d := by
  ext j
  simp only [stepBox]
  exact min_eq_left (le_trans (step_le_orderUpTo hm2 ⟨x.val, x.prop.1, x.prop.2.1⟩ q d j) hq)

def stageCost (c : Params) (P : CappedBaseStock.DemandLaw) (x : State c.m) (q : ℝ≥0) : ℝ :=
  g0 c P (orderUpTo x q) + c.θ * (∫ d : ℝ≥0, max (firstLevel x q - (d : ℝ)) 0 ∂P.law)

lemma stageCost_nonneg (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (x : State c.m) (q : ℝ≥0) : 0 ≤ stageCost c P x q := by
  unfold stageCost
  have h1 := g0_nonneg c hc P (orderUpTo x q)
  have h2 : 0 ≤ ∫ d : ℝ≥0, max (firstLevel x q - (d : ℝ)) 0 ∂P.law :=
    integral_nonneg fun _ => le_max_right _ _
  nlinarith [hc.θ_nonneg]

lemma continuous_stageCost (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    Continuous (fun p : State c.m × ℝ≥0 => stageCost c P p.1 p.2) := by
  unfold stageCost
  have hord : Continuous (fun p : State c.m × ℝ≥0 => orderUpTo p.1 p.2) := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo PerishBaseStock.Lifetime.topLevel
    split_ifs with h0
    · exact ((continuous_apply _).comp continuous_fst).add (NNReal.continuous_coe.comp continuous_snd)
    · exact continuous_const.add (NNReal.continuous_coe.comp continuous_snd)
  have hfirst : Continuous (fun p : State c.m × ℝ≥0 => firstLevel p.1 p.2) := by
    unfold firstLevel PerishBaseStock.Lifetime.firstLevel
    split_ifs with h0
    · exact (continuous_apply _).comp continuous_fst
    · exact hord
  have hout_int : Continuous (fun y : ℝ => ∫ d : ℝ≥0, max (y - (d : ℝ)) 0 ∂P.law) := by
    refine LipschitzWith.continuous (K := 1) fun a b => ?_
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ENNReal.coe_one, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_sub (integrable_max_sub P a) (integrable_max_sub P b)]
    calc |∫ d : ℝ≥0, (max (a - (d : ℝ)) 0 - max (b - (d : ℝ)) 0) ∂P.law|
        ≤ ∫ d : ℝ≥0, |max (a - (d : ℝ)) 0 - max (b - (d : ℝ)) 0| ∂P.law :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ≥0, |a - b| ∂P.law :=
          integral_mono ((integrable_max_sub P a).sub (integrable_max_sub P b)).abs
            (integrable_const _) fun d => by
              have := abs_max_sub_max_le (a - d) (b - d)
              simpa [sub_sub_sub_cancel_right] using this
      _ = |a - b| := by simp [measureReal_def]
  exact ((continuous_g0 c hc P).comp hord).add (continuous_const.mul (hout_int.comp hfirst))

lemma measurable_stageCost (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) :
    Measurable (fun p : State c.m × ℝ≥0 => stageCost c P p.1 p.2) := by
  unfold stageCost
  have hord : Measurable (fun p : State c.m × ℝ≥0 => orderUpTo p.1 p.2) := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    exact ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp measurable_fst).add
      (measurable_coe_nnreal_real.comp measurable_snd)
  have hfirst : Measurable (fun p : State c.m × ℝ≥0 => firstLevel p.1 p.2) := by
    unfold firstLevel PerishBaseStock.Lifetime.firstLevel
    split_ifs with h0
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact hord
  have hout_cont : Continuous (fun y : ℝ => ∫ d : ℝ≥0, max (y - (d : ℝ)) 0 ∂P.law) := by
    refine LipschitzWith.continuous (K := 1) fun a b => ?_
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ENNReal.coe_one, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_sub (integrable_max_sub P a) (integrable_max_sub P b)]
    calc |∫ d : ℝ≥0, (max (a - (d : ℝ)) 0 - max (b - (d : ℝ)) 0) ∂P.law|
        ≤ ∫ d : ℝ≥0, |max (a - (d : ℝ)) 0 - max (b - (d : ℝ)) 0| ∂P.law :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ : ℝ≥0, |a - b| ∂P.law :=
          integral_mono ((integrable_max_sub P a).sub (integrable_max_sub P b)).abs
            (integrable_const _) fun d => by
              have := abs_max_sub_max_le (a - d) (b - d)
              simpa [sub_sub_sub_cancel_right] using this
      _ = |a - b| := by simp [measureReal_def]
  exact ((continuous_g0 c hc P).measurable.comp hord).add
    (measurable_const.mul (hout_cont.measurable.comp hfirst))

lemma ofReal_stageCost_eq_lintegral (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (x : State c.m) (q : ℝ≥0) :
    ENNReal.ofReal (stageCost c P x q) =
      ∫⁻ d : ℝ≥0, (ENNReal.ofReal c.h * ENNReal.ofReal (max (orderUpTo x q - (d : ℝ)) 0) +
        ENNReal.ofReal c.p * ENNReal.ofReal (max ((d : ℝ) - orderUpTo x q) 0) +
        ENNReal.ofReal c.θ * ENNReal.ofReal (outdate x q d)) ∂P.law := by
  have h1 := integrable_max_sub P (orderUpTo x q)
  have h2 := integrable_sub_max P (orderUpTo x q)
  have h3 := integrable_max_sub P (firstLevel x q)
  have hpt : ∀ d : ℝ≥0,
      ENNReal.ofReal c.h * ENNReal.ofReal (max (orderUpTo x q - (d : ℝ)) 0) +
        ENNReal.ofReal c.p * ENNReal.ofReal (max ((d : ℝ) - orderUpTo x q) 0) +
        ENNReal.ofReal c.θ * ENNReal.ofReal (outdate x q d) =
      ENNReal.ofReal (c.h * max (orderUpTo x q - (d : ℝ)) 0 +
        c.p * max ((d : ℝ) - orderUpTo x q) 0 +
        c.θ * max (firstLevel x q - (d : ℝ)) 0) := by
    intro d
    unfold outdate PerishBaseStock.Lifetime.outdate
    rw [← ENNReal.ofReal_mul (le_of_lt hc.h_pos), ← ENNReal.ofReal_mul (le_of_lt hc.p_pos),
      ← ENNReal.ofReal_mul hc.θ_nonneg,
      ← ENNReal.ofReal_add (mul_nonneg (le_of_lt hc.h_pos) (le_max_right _ _))
        (mul_nonneg (le_of_lt hc.p_pos) (le_max_right _ _)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (le_of_lt hc.h_pos) (le_max_right _ _))
        (mul_nonneg (le_of_lt hc.p_pos) (le_max_right _ _)))
        (mul_nonneg hc.θ_nonneg (le_max_right _ _))]
  simp_rw [hpt]
  have hint : Integrable (fun d : ℝ≥0 =>
      c.h * max (orderUpTo x q - (d : ℝ)) 0 +
      c.p * max ((d : ℝ) - orderUpTo x q) 0 +
      c.θ * max (firstLevel x q - (d : ℝ)) 0) P.law :=
    ((h1.const_mul c.h).add (h2.const_mul c.p)).add (h3.const_mul c.θ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun d => by
    dsimp only [Pi.zero_apply]
    have a := le_max_right (orderUpTo x q - (d : ℝ)) 0
    have b := le_max_right ((d : ℝ) - orderUpTo x q) 0
    have e := le_max_right (firstLevel x q - (d : ℝ)) 0
    nlinarith [hc.h_pos, hc.p_pos, hc.θ_nonneg])]
  congr 1
  have h12 : Integrable (fun d : ℝ≥0 =>
      c.h * max (orderUpTo x q - (d : ℝ)) 0 + c.p * max ((d : ℝ) - orderUpTo x q) 0) P.law :=
    (h1.const_mul c.h).add (h2.const_mul c.p)
  rw [integral_add h12 (h3.const_mul c.θ),
    integral_add (h1.const_mul c.h) (h2.const_mul c.p),
    integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

lemma measurable_stepFull_triple {m : ℕ} (hm2 : 2 ≤ m) :
    Measurable (fun z : (XFull m × ℝ≥0) × ℝ≥0 => stepFull hm2 z.1.1 z.1.2 z.2) :=
  Measurable.subtype_mk (continuous_step_triple.comp
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd)).measurable

lemma measurable_stepBox_triple {m : ℕ} (hm2 : 2 ≤ m) (S : ℝ≥0) :
    Measurable (fun z : (XBox m S × ℝ≥0) × ℝ≥0 => stepBox hm2 S z.1.1 z.1.2 z.2) := by
  refine Measurable.subtype_mk (measurable_pi_lambda _ fun j => ?_)
  have hstep : Continuous (fun z : (XBox m S × ℝ≥0) × ℝ≥0 => step z.1.1.val z.1.2 z.2) :=
    continuous_step_triple.comp
      (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  exact (((continuous_apply j).comp hstep).min continuous_const).measurable

def kernelFull (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw) :
    Kernel (XFull c.m × ℝ≥0) (XFull c.m) :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const (XFull c.m × ℝ≥0) P.law)
    (fun z : (XFull c.m × ℝ≥0) × ℝ≥0 => stepFull hm2 z.1.1 z.1.2 z.2)

instance isMarkov_kernelFull (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw) :
    IsMarkovKernel (kernelFull c hm2 P) :=
  Kernel.IsMarkovKernel.map _ (measurable_stepFull_triple hm2)

def kernelBox (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) :
    Kernel (XBox c.m S × ℝ≥0) (XBox c.m S) :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const (XBox c.m S × ℝ≥0) P.law)
    (fun z : (XBox c.m S × ℝ≥0) × ℝ≥0 => stepBox hm2 S z.1.1 z.1.2 z.2)

instance isMarkov_kernelBox (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0) :
    IsMarkovKernel (kernelBox c hm2 P S) :=
  Kernel.IsMarkovKernel.map _ (measurable_stepBox_triple hm2 S)

lemma kernelFull_apply (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw)
    (p : XFull c.m × ℝ≥0) :
    kernelFull c hm2 P p = P.law.map (fun d : ℝ≥0 => stepFull hm2 p.1 p.2 d) := by
  unfold kernelFull
  have hmeas := measurable_stepFull_triple hm2
  have hmk : Measurable (fun d : ℝ≥0 => (p, d)) := measurable_const.prodMk measurable_id
  rw [Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply]
  dsimp only [id_eq]
  have hdp : (Measure.dirac p).prod P.law = P.law.map (fun d : ℝ≥0 => (p, d)) := by
    ext s hs
    rw [Measure.prod_apply hs, Measure.map_apply hmk hs,
      lintegral_dirac' _ (measurable_measure_prodMk_left hs)]
  rw [hdp, Measure.map_map hmeas hmk]
  rfl

lemma kernelBox_apply (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0)
    (p : XBox c.m S × ℝ≥0) :
    kernelBox c hm2 P S p = P.law.map (fun d : ℝ≥0 => stepBox hm2 S p.1 p.2 d) := by
  unfold kernelBox
  have hmeas := measurable_stepBox_triple hm2 S
  have hmk : Measurable (fun d : ℝ≥0 => (p, d)) := measurable_const.prodMk measurable_id
  rw [Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply]
  dsimp only [id_eq]
  have hdp : (Measure.dirac p).prod P.law = P.law.map (fun d : ℝ≥0 => (p, d)) := by
    ext s hs
    rw [Measure.prod_apply hs, Measure.map_apply hmk hs,
      lintegral_dirac' _ (measurable_measure_prodMk_left hs)]
  rw [hdp, Measure.map_map hmeas hmk]
  rfl

lemma continuous_stepFull_d {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) (q : ℝ≥0) :
    Continuous (fun d : ℝ≥0 => stepFull hm2 x q d) := by
  let g : ℝ≥0 → (State m × ℝ≥0) × ℝ≥0 := fun d => ((x.val, q), d)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  exact Continuous.subtype_mk (continuous_step_triple.comp hg) _

lemma continuous_stepFull_pair {m : ℕ} (hm2 : 2 ≤ m) (d : ℝ≥0) :
    Continuous (fun p : XFull m × ℝ≥0 => stepFull hm2 p.1 p.2 d) := by
  let g : XFull m × ℝ≥0 → State m × ℝ≥0 := fun p => (p.1.val, p.2)
  have hg : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact Continuous.subtype_mk ((continuous_step_pair d).comp hg) _

lemma continuous_stepBox_d {m : ℕ} (hm2 : 2 ≤ m) (S : ℝ≥0) (x : XBox m S) (q : ℝ≥0) :
    Continuous (fun d : ℝ≥0 => stepBox hm2 S x q d) := by
  let g : ℝ≥0 → (State m × ℝ≥0) × ℝ≥0 := fun d => ((x.val, q), d)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  have hs : Continuous (fun d : ℝ≥0 => step x.val q d) := continuous_step_triple.comp hg
  exact Continuous.subtype_mk (continuous_pi fun j => ((continuous_apply j).comp hs).min continuous_const) _

lemma continuous_stepBox_pair {m : ℕ} (hm2 : 2 ≤ m) (S : ℝ≥0) (d : ℝ≥0) :
    Continuous (fun p : XBox m S × ℝ≥0 => stepBox hm2 S p.1 p.2 d) := by
  let g : XBox m S × ℝ≥0 → State m × ℝ≥0 := fun p => (p.1.val, p.2)
  have hg : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hs : Continuous (fun p : XBox m S × ℝ≥0 => step p.1.val p.2 d) :=
    (continuous_step_pair d).comp hg
  exact Continuous.subtype_mk (continuous_pi fun j => ((continuous_apply j).comp hs).min continuous_const) _

lemma continuous_stageCost_subtype (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (S_set : Set (State c.m)) :
    Continuous (fun p : {x : State c.m // x ∈ S_set} × ℝ≥0 => stageCost c P p.1.val p.2) := by
  let g : {x : State c.m // x ∈ S_set} × ℝ≥0 → State c.m × ℝ≥0 := fun p => (p.1.val, p.2)
  have hg : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact (continuous_stageCost c hc P).comp hg

lemma measurable_cost_subtype (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (S_set : Set (State c.m)) :
    Measurable (fun p : {x : State c.m // x ∈ S_set} × ℝ≥0 =>
      ENNReal.ofReal (stageCost c P p.1.val p.2)) :=
  (ENNReal.continuous_ofReal.comp (continuous_stageCost_subtype c hc P S_set)).measurable

def modelFull (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : Model (XFull c.m) ℝ≥0 where
  toMDP := {
    lower := 0
    cost := fun x q => ENNReal.ofReal (stageCost c P x.val q)
    q := kernelFull c hm2 P
  }
  lower_eq := rfl
  Aset := fun _ => Set.univ
  Aset_nonempty := fun _ => Set.univ_nonempty
  graph_meas := by simp
  cost_meas := measurable_cost_subtype c hc P (XFullSet c.m)

def modelBox (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : Model (XBox c.m (newsvendorLevel P.law c.h c.p)) ℝ≥0 where
  toMDP := {
    lower := 0
    cost := fun x q => ENNReal.ofReal (stageCost c P x.val q)
    q := kernelBox c hm2 P (newsvendorLevel P.law c.h c.p)
  }
  lower_eq := rfl
  Aset := fun x => {q : ℝ≥0 | (floorLevel c P : ℝ) ≤ orderUpTo x.val q ∧
    orderUpTo x.val q ≤ (newsvendorLevel P.law c.h c.p : ℝ)}
  Aset_nonempty := fun x => by
    let S_NP := newsvendorLevel P.law c.h c.p
    refine ⟨Real.toNNReal ((S_NP : ℝ) - topLevel x.val), ?_⟩
    have htop : topLevel x.val ≤ (S_NP : ℝ) := by
      rw [topLevel_eq_last hm2]; exact x.prop.2.2 _
    have hord : orderUpTo x.val (Real.toNNReal ((S_NP : ℝ) - topLevel x.val)) = (S_NP : ℝ) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel x.val + (Real.toNNReal ((S_NP : ℝ) - topLevel x.val) : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]
      ring
    change (floorLevel c P : ℝ) ≤ orderUpTo x.val _ ∧ orderUpTo x.val _ ≤ (S_NP : ℝ)
    rw [hord]
    exact ⟨NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_rfl⟩
  graph_meas := by
    have hord : Measurable (fun p : XBox c.m (newsvendorLevel P.law c.h c.p) × ℝ≥0 =>
        orderUpTo p.1.val p.2) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      exact ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp
        (measurable_subtype_coe.comp measurable_fst)).add
        (measurable_coe_nnreal_real.comp measurable_snd)
    exact (measurableSet_le measurable_const hord).inter (measurableSet_le hord measurable_const)
  cost_meas := measurable_cost_subtype c hc P (XBoxSet c.m (newsvendorLevel P.law c.h c.p))

lemma hasSelector_full (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : HasSelector (modelFull c hc hm2 P) :=
  ⟨fun _ => 0, measurable_const, fun _ => trivial⟩

lemma hasSelector_box (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : HasSelector (modelBox c hc hm2 P) := by
  let S_NP := newsvendorLevel P.law c.h c.p
  refine ⟨fun x => Real.toNNReal ((S_NP : ℝ) - topLevel x.val), ?_, ?_⟩
  · exact measurable_real_toNNReal.comp
      (measurable_const.sub ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp
        measurable_subtype_coe))
  · intro x
    have htop : topLevel x.val ≤ (S_NP : ℝ) := by
      rw [topLevel_eq_last hm2]; exact x.prop.2.2 _
    have hord : orderUpTo x.val (Real.toNNReal ((S_NP : ℝ) - topLevel x.val)) = (S_NP : ℝ) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel x.val + (Real.toNNReal ((S_NP : ℝ) - topLevel x.val) : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]
      ring
    show (floorLevel c P : ℝ) ≤ orderUpTo x.val _ ∧ orderUpTo x.val _ ≤ (S_NP : ℝ)
    rw [hord]
    exact ⟨NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_rfl⟩

lemma condWStar_full (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : CondWStar (modelFull c hc hm2 P) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun p : XFull c.m × ℝ≥0 => (modelFull c hc hm2 P).toMDP.cost p.1 p.2) :=
      ENNReal.continuous_ofReal.comp (continuous_stageCost_subtype c hc P (XFullSet c.m))
    exact hcont.lowerSemicontinuous.lowerSemicontinuousOn _
  · intro xs x as _ _ ⟨C, hC⟩
    let R : ℝ≥0 := Real.toNNReal ((C : ℝ) / c.h + CappedBaseStock.mean P)
    have hbdd : ∀ n, as n ∈ Set.Icc (0 : ℝ≥0) R := by
      intro n
      refine ⟨zero_le, ?_⟩
      have hcost := hC n
      change ENNReal.ofReal (stageCost c P (xs n).val (as n)) ≤ (C : ℝ≥0∞) at hcost
      rw [← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg C)] at hcost
      have h1 : c.h * (∫ d : ℝ≥0, max (orderUpTo (xs n).val (as n) - (d : ℝ)) 0 ∂P.law) ≤ (C : ℝ) := by
        unfold stageCost g0 at hcost
        have hp : 0 ≤ c.p * ∫ d : ℝ≥0, max ((d : ℝ) - orderUpTo (xs n).val (as n)) 0 ∂P.law :=
          mul_nonneg (le_of_lt hc.p_pos) (integral_nonneg fun _ => le_max_right _ _)
        have hθ : 0 ≤ c.θ * ∫ d : ℝ≥0, max (firstLevel (xs n).val (as n) - (d : ℝ)) 0 ∂P.law :=
          mul_nonneg hc.θ_nonneg (integral_nonneg fun _ => le_max_right _ _)
        linarith
      have h2 : orderUpTo (xs n).val (as n) - CappedBaseStock.mean P ≤
          ∫ d : ℝ≥0, max (orderUpTo (xs n).val (as n) - (d : ℝ)) 0 ∂P.law := by
        calc orderUpTo (xs n).val (as n) - CappedBaseStock.mean P
            = ∫ d : ℝ≥0, (orderUpTo (xs n).val (as n) - (d : ℝ)) ∂P.law := by
              rw [integral_sub (integrable_const _) P.finiteMean, integral_const]
              simp [measureReal_def, CappedBaseStock.mean]
          _ ≤ ∫ d : ℝ≥0, max (orderUpTo (xs n).val (as n) - (d : ℝ)) 0 ∂P.law :=
              integral_mono ((integrable_const _).sub P.finiteMean) (integrable_max_sub P _)
                fun _ => le_max_left _ _
      have h3 : (as n : ℝ) ≤ orderUpTo (xs n).val (as n) := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
        rw [show PerishBaseStock.Lifetime.topLevel (xs n).val = (xs n).val ⟨c.m - 2, by omega⟩ from
          topLevel_eq_last hm2 (xs n).val]
        exact le_add_of_nonneg_left ((xs n).prop.1 _)
      have h4 : (as n : ℝ) ≤ (C : ℝ) / c.h + CappedBaseStock.mean P := by
        have h5 : (as n : ℝ) - CappedBaseStock.mean P ≤ (C : ℝ) / c.h := by
          rw [le_div_iff₀ hc.h_pos]; nlinarith [hc.h_pos]
        linarith
      rw [← NNReal.coe_le_coe]
      exact le_trans h4 (Real.le_coe_toNNReal _)
    rcases isCompact_Icc.tendsto_subseq hbdd with ⟨a, _, φ, hφ_mono, hφ_tend⟩
    exact ⟨a, trivial, MapClusterPt.of_comp hφ_mono.tendsto_atTop hφ_tend.mapClusterPt⟩
  · intro f
    have hcont : Continuous (fun p : XFull c.m × ℝ≥0 =>
        ∫ y, f y ∂((modelFull c hc hm2 P).toMDP.q p)) := by
      have heq : ∀ p : XFull c.m × ℝ≥0,
          ∫ y, f y ∂((modelFull c hc hm2 P).toMDP.q p) =
            ∫ d : ℝ≥0, f (stepFull hm2 p.1 p.2 d) ∂P.law := by
        intro p
        change ∫ y, f y ∂(kernelFull c hm2 P p) = _
        rw [kernelFull_apply]
        have hms : Measurable (fun d : ℝ≥0 => stepFull hm2 p.1 p.2 d) :=
          (continuous_stepFull_d hm2 p.1 p.2).measurable
        exact integral_map hms.aemeasurable f.continuous.aestronglyMeasurable
      simp_rw [heq]
      refine continuous_of_dominated (bound := fun _ => ‖f‖) ?_ ?_ (integrable_const _) ?_
      · intro p
        exact (f.continuous.comp (continuous_stepFull_d hm2 p.1 p.2)).aestronglyMeasurable
      · intro p; exact Eventually.of_forall fun d => f.norm_coe_le_norm _
      · exact Eventually.of_forall fun d =>
          f.continuous.comp (continuous_stepFull_pair hm2 d)
    exact hcont.continuousOn

lemma condWStar_box (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) : CondWStar (modelBox c hc hm2 P) := by
  let S_NP := newsvendorLevel P.law c.h c.p
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun p : XBox c.m S_NP × ℝ≥0 => (modelBox c hc hm2 P).toMDP.cost p.1 p.2) :=
      ENNReal.continuous_ofReal.comp (continuous_stageCost_subtype c hc P (XBoxSet c.m S_NP))
    exact hcont.lowerSemicontinuous.lowerSemicontinuousOn _
  · intro xs x as hxs has _
    have hbdd : ∀ n, as n ∈ Set.Icc (0 : ℝ≥0) S_NP := by
      intro n
      refine ⟨zero_le, ?_⟩
      have hle := (has n).2
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo at hle
      rw [show PerishBaseStock.Lifetime.topLevel (xs n).val = (xs n).val ⟨c.m - 2, by omega⟩ from
        topLevel_eq_last hm2 (xs n).val] at hle
      rw [← NNReal.coe_le_coe]
      linarith [(xs n).prop.1 ⟨c.m - 2, by omega⟩]
    rcases isCompact_Icc.tendsto_subseq hbdd with ⟨a, _, φ, hφ_mono, hφ_tend⟩
    have hcl : MapClusterPt a atTop as :=
      MapClusterPt.of_comp hφ_mono.tendsto_atTop hφ_tend.mapClusterPt
    have hord_tend : Tendsto (fun k => orderUpTo (xs (φ k)).val (as (φ k))) atTop
        (𝓝 (orderUpTo x.val a)) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      have : ∀ y : State c.m, PerishBaseStock.Lifetime.topLevel y = y ⟨c.m - 2, by omega⟩ :=
        topLevel_eq_last hm2
      simp_rw [this]
      have hxs' : Tendsto (fun k => (xs (φ k)).val ⟨c.m - 2, by omega⟩) atTop
          (𝓝 (x.val ⟨c.m - 2, by omega⟩)) :=
        ((continuous_apply _).comp continuous_subtype_val).continuousAt.tendsto.comp
          (hxs.comp hφ_mono.tendsto_atTop)
      exact hxs'.add (NNReal.continuous_coe.continuousAt.tendsto.comp hφ_tend)
    refine ⟨a, ?_, hcl⟩
    exact ⟨ge_of_tendsto hord_tend (Eventually.of_forall fun k => (has (φ k)).1),
      le_of_tendsto hord_tend (Eventually.of_forall fun k => (has (φ k)).2)⟩
  · intro f
    have hcont : Continuous (fun p : XBox c.m S_NP × ℝ≥0 =>
        ∫ y, f y ∂((modelBox c hc hm2 P).toMDP.q p)) := by
      have heq : ∀ p : XBox c.m S_NP × ℝ≥0,
          ∫ y, f y ∂((modelBox c hc hm2 P).toMDP.q p) =
            ∫ d : ℝ≥0, f (stepBox hm2 S_NP p.1 p.2 d) ∂P.law := by
        intro p
        change ∫ y, f y ∂(kernelBox c hm2 P S_NP p) = _
        rw [kernelBox_apply]
        have hms : Measurable (fun d : ℝ≥0 => stepBox hm2 S_NP p.1 p.2 d) :=
          (continuous_stepBox_d hm2 S_NP p.1 p.2).measurable
        exact integral_map hms.aemeasurable f.continuous.aestronglyMeasurable
      simp_rw [heq]
      refine continuous_of_dominated (bound := fun _ => ‖f‖) ?_ ?_ (integrable_const _) ?_
      · intro p
        exact (f.continuous.comp (continuous_stepBox_d hm2 S_NP p.1 p.2)).aestronglyMeasurable
      · intro p; exact Eventually.of_forall fun d => f.norm_coe_le_norm _
      · exact Eventually.of_forall fun d =>
          f.continuous.comp (continuous_stepBox_pair hm2 S_NP d)
    exact hcont.continuousOn

end MDPSetup

/-! ### Section 4: Bellman iteration, invariants P and Q, and `vβ M_box α ≤ vβ M_full α` -/

section BellmanIteration

/-- Age-cohort dominance `z(x) ≤ z(x')`: `x 0 ≤ x' 0` and `x (j+1) - x j ≤ x' (j+1) - x' j`. -/
def zLe (m : ℕ) (x x' : State m) : Prop :=
  (∀ h : 0 < m - 1, x ⟨0, h⟩ ≤ x' ⟨0, h⟩) ∧
  (∀ (j : Fin (m - 1)) (hj : j.val + 1 < m - 1), x ⟨j.val + 1, hj⟩ - x j ≤ x' ⟨j.val + 1, hj⟩ - x' j)

lemma zLe_le {m : ℕ} {x x' : State m} (hz : zLe m x x') (j : Fin (m - 1)) : x j ≤ x' j := by
  rcases j with ⟨k, hk⟩
  induction k with
  | zero => exact hz.1 hk
  | succ k ih =>
    have hk' : k < m - 1 := by omega
    have h1 := ih hk'
    have h2 := hz.2 ⟨k, hk'⟩ hk
    linarith

lemma max_sub_max_eq_min (a b d : ℝ) (hab : a ≤ b) :
    max (b - d) 0 - max (a - d) 0 = min (b - a) (max (b - d) 0) := by
  rcases le_total d a with hda | had
  · have hdb : d ≤ b := le_trans hda hab
    rw [max_eq_left (sub_nonneg.mpr hdb), max_eq_left (sub_nonneg.mpr hda),
      min_eq_left (by linarith)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr had), sub_zero]
    rcases le_total d b with hdb | hbd
    · rw [max_eq_left (sub_nonneg.mpr hdb), min_eq_right (by linarith)]
    · rw [max_eq_right (sub_nonpos.mpr hbd), min_eq_right (by linarith)]

lemma max_sub_max_mono {a b a' b' d : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a ≤ a') (hdiff : b - a ≤ b' - a') :
    max (b - d) 0 - max (a - d) 0 ≤ max (b' - d) 0 - max (a' - d) 0 := by
  rw [max_sub_max_eq_min a b d hab, max_sub_max_eq_min a' b' d hab']
  exact min_le_min hdiff (max_le_max_right 0 (by linarith))

lemma zLe_step_zero {m : ℕ} (hm2 : 2 ≤ m) {x x' : XFull m} (hz : zLe m x.val x'.val) (d : ℝ≥0) :
    zLe m (step x.val 0 d) (step x'.val 0 d) := by
  constructor
  · intro h0
    rw [step_eq_diff hm2, step_eq_diff hm2]
    unfold levelAbove PerishBaseStock.Lifetime.levelAbove
    split_ifs with h1
    · exact max_sub_max_mono (x.prop.2 (Fin.mk_le_mk.mpr (Nat.zero_le _)))
        (x'.prop.2 (Fin.mk_le_mk.mpr (Nat.zero_le _)))
        (hz.1 h0) (hz.2 ⟨0, h0⟩ h1)
    · dsimp only at h1
      have hidx : (⟨0, h0⟩ : Fin (m - 1)) = ⟨m - 2, by omega⟩ := Fin.ext (by dsimp; omega)
      unfold PerishBaseStock.Lifetime.orderUpTo
      rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
          topLevel_eq_last hm2 x.val,
        show PerishBaseStock.Lifetime.topLevel x'.val = x'.val ⟨m - 2, by omega⟩ from
          topLevel_eq_last hm2 x'.val, ← hidx]
      simp
  · intro j hj
    rw [step_eq_diff hm2, step_eq_diff hm2, step_eq_diff hm2, step_eq_diff hm2]
    have hcancel : ∀ a b c : ℝ, (a - c) - (b - c) = a - b := fun _ _ _ => by ring
    rw [hcancel, hcancel]
    unfold levelAbove PerishBaseStock.Lifetime.levelAbove
    simp only [hj, ↓reduceDIte]
    split_ifs with h2
    · exact max_sub_max_mono
        (x.prop.2 (Fin.mk_le_mk.mpr (Nat.le_succ _)))
        (x'.prop.2 (Fin.mk_le_mk.mpr (Nat.le_succ _)))
        (zLe_le hz ⟨j.val + 1, hj⟩)
        (hz.2 ⟨j.val + 1, hj⟩ h2)
    · change ¬ (j.val + 1 + 1 < m - 1) at h2
      have hlast : (⟨j.val + 1, hj⟩ : Fin (m - 1)) = ⟨m - 2, by omega⟩ :=
        Fin.ext (by change j.val + 1 = m - 2; omega)
      unfold PerishBaseStock.Lifetime.orderUpTo
      rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨m - 2, by omega⟩ from
          topLevel_eq_last hm2 x.val,
        show PerishBaseStock.Lifetime.topLevel x'.val = x'.val ⟨m - 2, by omega⟩ from
          topLevel_eq_last hm2 x'.val, ← hlast]
      simp

lemma zLe_step_mono_q {m : ℕ} (hm2 : 2 ≤ m) (x : XFull m) {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (d : ℝ≥0) :
    zLe m (step x.val q₁ d) (step x.val q₂ d) := by
  have hord : orderUpTo x.val q₁ ≤ orderUpTo x.val q₂ := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    linarith [NNReal.coe_le_coe.mpr hq]
  have hlev_le : ∀ j : Fin (m - 1), levelAbove x.val q₁ j ≤ levelAbove x.val q₂ j := by
    intro j; unfold levelAbove PerishBaseStock.Lifetime.levelAbove
    split_ifs
    · exact le_rfl
    · exact hord
  have hlev_eq : ∀ (j : Fin (m - 1)), j.val + 1 < m - 1 →
      levelAbove x.val q₁ j = levelAbove x.val q₂ j := by
    intro j hj; unfold levelAbove PerishBaseStock.Lifetime.levelAbove; simp [hj]
  constructor
  · intro h0
    rw [step_eq_diff hm2, step_eq_diff hm2]
    linarith [max_le_max_right 0 (sub_le_sub_right (hlev_le ⟨0, h0⟩) (d : ℝ))]
  · intro j hj
    rw [step_eq_diff hm2, step_eq_diff hm2, step_eq_diff hm2, step_eq_diff hm2]
    have hcancel : ∀ a b c : ℝ, (a - c) - (b - c) = a - b := fun _ _ _ => by ring
    rw [hcancel, hcancel, hlev_eq j hj]
    linarith [max_le_max_right 0 (sub_le_sub_right (hlev_le ⟨j.val + 1, hj⟩) (d : ℝ))]

structure VInv (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw)
    (v : XFull c.m → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ v x
  linear : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, v x ≤ C * (1 + topLevel x.val)
  cont : Continuous v
  propP : ∀ x x' : XFull c.m,
    topLevel x.val ≤ (newsvendorLevel P.law c.h c.p : ℝ) →
    topLevel x'.val ≤ (newsvendorLevel P.law c.h c.p : ℝ) →
    ∀ δ : ℝ, 0 ≤ δ → (∀ j, x'.val j ≤ x.val j + δ) → v x' ≤ v x + c.θ * δ
  propQ : ∀ x x' : XFull c.m, zLe c.m x.val x'.val → v x ≤ v x'

def bellmanQ (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw)
    (α : ℝ) (v : XFull c.m → ℝ) (x : XFull c.m) (q : ℝ≥0) : ℝ :=
  stageCost c P x.val q + α * ∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law

def bellmanT (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw)
    (α : ℝ) (v : XFull c.m → ℝ) (x : XFull c.m) : ℝ :=
  sInf (Set.range fun q : ℝ≥0 => bellmanQ c hm2 P α v x q)

def bellmanV (c : Params) (hm2 : 2 ≤ c.m) (P : CappedBaseStock.DemandLaw)
    (α : ℝ) : ℕ → XFull c.m → ℝ
  | 0 => fun _ => 0
  | n + 1 => bellmanT c hm2 P α (bellmanV c hm2 P α n)

lemma integrable_v_stepFull {c : Params} {hm2 : 2 ≤ c.m} {P : CappedBaseStock.DemandLaw}
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) (x : XFull c.m) (q : ℝ≥0) :
    Integrable (fun d : ℝ≥0 => v (stepFull hm2 x q d)) P.law := by
  rcases hv.linear with ⟨C, hC0, hC⟩
  have hcont : Continuous (fun d : ℝ≥0 => v (stepFull hm2 x q d)) :=
    hv.cont.comp (continuous_stepFull_d hm2 x q)
  refine Integrable.mono' (integrable_const (C * (1 + orderUpTo x.val q)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun d => ?_)
  rw [Real.norm_of_nonneg (hv.nonneg _)]
  have htop : topLevel (stepFull hm2 x q d).val ≤ orderUpTo x.val q := by
    rw [topLevel_eq_last hm2]; exact step_le_orderUpTo hm2 x q d _
  calc v (stepFull hm2 x q d)
      ≤ C * (1 + topLevel (stepFull hm2 x q d).val) := hC _
    _ ≤ C * (1 + orderUpTo x.val q) := by nlinarith

lemma bellmanQ_nonneg {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) (x : XFull c.m) (q : ℝ≥0) :
    0 ≤ bellmanQ c hm2 P α v x q := by
  unfold bellmanQ
  have h1 := stageCost_nonneg c hc P x.val q
  have h2 : 0 ≤ ∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law :=
    integral_nonneg fun d => hv.nonneg _
  nlinarith

lemma continuous_bellmanQ {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ}
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) :
    Continuous (fun p : XFull c.m × ℝ≥0 => bellmanQ c hm2 P α v p.1 p.2) := by
  unfold bellmanQ
  have hc1 : Continuous (fun p : XFull c.m × ℝ≥0 => stageCost c P p.1.val p.2) :=
    continuous_stageCost_subtype c hc P (XFullSet c.m)
  have hc2 : Continuous (fun p : XFull c.m × ℝ≥0 => ∫ d : ℝ≥0, v (stepFull hm2 p.1 p.2 d) ∂P.law) := by
    rw [continuous_iff_continuousAt]
    intro p₀
    rcases hv.linear with ⟨C, hC0, hC⟩
    have hord_cont : Continuous (fun p : XFull c.m × ℝ≥0 => orderUpTo p.1.val p.2) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      have : ∀ y : State c.m, PerishBaseStock.Lifetime.topLevel y = y ⟨c.m - 2, by omega⟩ :=
        topLevel_eq_last hm2
      simp_rw [this]
      exact ((continuous_apply _).comp (continuous_subtype_val.comp continuous_fst)).add
        (NNReal.continuous_coe.comp continuous_snd)
    have hnhds : ∀ᶠ p in 𝓝 p₀, orderUpTo p.1.val p.2 ≤ orderUpTo p₀.1.val p₀.2 + 1 :=
      hord_cont.continuousAt.eventually (ge_mem_nhds (lt_add_one _))
    refine continuousAt_of_dominated
      (bound := fun _ => C * (1 + (orderUpTo p₀.1.val p₀.2 + 1))) ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun p =>
        (hv.cont.comp (continuous_stepFull_d hm2 p.1 p.2)).aestronglyMeasurable
    · refine hnhds.mono fun p hp => Eventually.of_forall fun d => ?_
      rw [Real.norm_of_nonneg (hv.nonneg _)]
      have htop : topLevel (stepFull hm2 p.1 p.2 d).val ≤ orderUpTo p.1.val p.2 := by
        rw [topLevel_eq_last hm2]; exact step_le_orderUpTo hm2 p.1 p.2 d _
      calc v (stepFull hm2 p.1 p.2 d)
          ≤ C * (1 + topLevel (stepFull hm2 p.1 p.2 d).val) := hC _
        _ ≤ C * (1 + (orderUpTo p₀.1.val p₀.2 + 1)) := by nlinarith
    · exact Eventually.of_forall fun d =>
        (hv.cont.comp (continuous_stepFull_pair hm2 d)).continuousAt
  exact hc1.add (continuous_const.mul hc2)

lemma bellmanQ_ge_NP {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) (x : XFull c.m) (q : ℝ≥0) :
    let q0 : ℝ≥0 := Real.toNNReal ((newsvendorLevel P.law c.h c.p : ℝ) - topLevel x.val)
    q0 ≤ q → bellmanQ c hm2 P α v x q0 ≤ bellmanQ c hm2 P α v x q := by
  intro q0 hq
  unfold bellmanQ stageCost
  rw [firstLevel_eq_zero hm2, firstLevel_eq_zero hm2]
  have htop_nn : 0 ≤ topLevel x.val := by rw [topLevel_eq_last hm2]; exact x.prop.1 _
  let y0 : ℝ≥0 := Real.toNNReal (orderUpTo x.val q0)
  let y : ℝ≥0 := Real.toNNReal (orderUpTo x.val q)
  have hy0_coe : (y0 : ℝ) = orderUpTo x.val q0 :=
    Real.coe_toNNReal _ (add_nonneg htop_nn q0.coe_nonneg)
  have hy_coe : (y : ℝ) = orderUpTo x.val q :=
    Real.coe_toNNReal _ (add_nonneg htop_nn q.coe_nonneg)
  have hNP_le_y0 : newsvendorLevel P.law c.h c.p ≤ y0 := by
    rw [← NNReal.coe_le_coe, hy0_coe]
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    change (newsvendorLevel P.law c.h c.p : ℝ) ≤ topLevel x.val + (q0 : ℝ)
    have := Real.le_coe_toNNReal ((newsvendorLevel P.law c.h c.p : ℝ) - topLevel x.val)
    linarith
  have hy0_le_y : y0 ≤ y := by
    rw [← NNReal.coe_le_coe, hy0_coe, hy_coe]
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    linarith [NNReal.coe_le_coe.mpr hq]
  have hg : g0 c P (orderUpTo x.val q0) ≤ g0 c P (orderUpTo x.val q) := by
    rw [← hy0_coe, ← hy_coe]
    exact g0_monotone_ge_NP c hc P hNP_le_y0 hy0_le_y
  have hint : ∫ d : ℝ≥0, v (stepFull hm2 x q0 d) ∂P.law ≤
      ∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law :=
    integral_mono (integrable_v_stepFull hv x q0) (integrable_v_stepFull hv x q) fun d =>
      hv.propQ _ _ (zLe_step_mono_q hm2 x hq d)
  nlinarith

lemma bellmanT_eq_zero_of_ge_NP {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) {x : XFull c.m}
    (hx : (newsvendorLevel P.law c.h c.p : ℝ) ≤ topLevel x.val) :
    bellmanT c hm2 P α v x = bellmanQ c hm2 P α v x 0 := by
  unfold bellmanT
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact bellmanQ_nonneg hc hα0 hv x q⟩ ⟨0, rfl⟩
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨q, rfl⟩
    have hq0 : Real.toNNReal ((newsvendorLevel P.law c.h c.p : ℝ) - topLevel x.val) = 0 :=
      Real.toNNReal_of_nonpos (sub_nonpos.mpr hx)
    have := bellmanQ_ge_NP hc hα0 hv x q
    rw [hq0] at this
    exact this zero_le

lemma bellmanQ_le_fl {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) {x : XFull c.m}
    (_hx : topLevel x.val ≤ (newsvendorLevel P.law c.h c.p : ℝ))
    {q : ℝ≥0} (hq : orderUpTo x.val q ≤ (floorLevel c P : ℝ)) :
    bellmanQ c hm2 P α v x (Real.toNNReal ((floorLevel c P : ℝ) - topLevel x.val)) ≤
      bellmanQ c hm2 P α v x q := by
  let q_fl : ℝ≥0 := Real.toNNReal ((floorLevel c P : ℝ) - topLevel x.val)
  have htop_nn : 0 ≤ topLevel x.val := by rw [topLevel_eq_last hm2]; exact x.prop.1 _
  have htop_fl : topLevel x.val ≤ (floorLevel c P : ℝ) := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo at hq
    linarith [q.coe_nonneg]
  have hord_fl : orderUpTo x.val q_fl = (floorLevel c P : ℝ) := by
    unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
    change topLevel x.val + (q_fl : ℝ) = (floorLevel c P : ℝ)
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop_fl)]
    ring
  let y : ℝ≥0 := Real.toNNReal (orderUpTo x.val q)
  have hy_coe : (y : ℝ) = orderUpTo x.val q :=
    Real.coe_toNNReal _ (add_nonneg htop_nn q.coe_nonneg)
  let Δ : ℝ := (floorLevel c P : ℝ) - orderUpTo x.val q
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hq
  have hg_fl : g0 c P (floorLevel c P) - g0 c P (orderUpTo x.val q) ≤ -(c.θ * Δ) := by
    have hmin := (floorLevel_props c hc P).1 y
    unfold floorCost at hmin
    rw [← g0_coe, ← g0_coe, hy_coe] at hmin
    linarith
  have hpt : ∀ d : ℝ≥0, v (stepFull hm2 x q_fl d) ≤ v (stepFull hm2 x q d) + c.θ * Δ := by
    intro d
    have hfl_le_NP : (floorLevel c P : ℝ) ≤ (newsvendorLevel P.law c.h c.p : ℝ) :=
      NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2
    have ht1 : topLevel (stepFull hm2 x q d).val ≤ (newsvendorLevel P.law c.h c.p : ℝ) := by
      rw [topLevel_eq_last hm2]; exact le_trans (step_le_orderUpTo hm2 x q d _) (le_trans hq hfl_le_NP)
    have ht2 : topLevel (stepFull hm2 x q_fl d).val ≤ (newsvendorLevel P.law c.h c.p : ℝ) := by
      rw [topLevel_eq_last hm2]; exact le_trans (step_le_orderUpTo hm2 x q_fl d _) (by rw [hord_fl]; exact hfl_le_NP)
    refine hv.propP _ _ ht1 ht2 Δ hΔ fun j => ?_
    change step x.val q_fl d j ≤ step x.val q d j + Δ
    rw [step_eq_diff hm2, step_eq_diff hm2]
    have hlev : levelAbove x.val q_fl j ≤ levelAbove x.val q j + Δ := by
      unfold levelAbove PerishBaseStock.Lifetime.levelAbove
      split_ifs
      · linarith
      · change orderUpTo x.val q_fl ≤ orderUpTo x.val q + Δ
        rw [hord_fl]; linarith
    have hmax : max (levelAbove x.val q_fl j - (d : ℝ)) 0 ≤
        max (levelAbove x.val q j - (d : ℝ)) 0 + Δ :=
      max_le (by linarith [le_max_left (levelAbove x.val q j - (d : ℝ)) 0])
        (by linarith [le_max_right (levelAbove x.val q j - (d : ℝ)) 0])
    linarith
  have hint : ∫ d : ℝ≥0, v (stepFull hm2 x q_fl d) ∂P.law ≤
      (∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law) + c.θ * Δ := by
    calc ∫ d : ℝ≥0, v (stepFull hm2 x q_fl d) ∂P.law
        ≤ ∫ d : ℝ≥0, (v (stepFull hm2 x q d) + c.θ * Δ) ∂P.law :=
          integral_mono (integrable_v_stepFull hv x q_fl)
            ((integrable_v_stepFull hv x q).add (integrable_const _)) hpt
      _ = (∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law) + c.θ * Δ := by
          rw [integral_add (integrable_v_stepFull hv x q) (integrable_const _), integral_const]
          simp [measureReal_def]
  show bellmanQ c hm2 P α v x q_fl ≤ bellmanQ c hm2 P α v x q
  unfold bellmanQ stageCost
  rw [firstLevel_eq_zero hm2, firstLevel_eq_zero hm2, hord_fl]
  have hθΔ : 0 ≤ c.θ * Δ := mul_nonneg hc.θ_nonneg hΔ
  have hint' : α * ∫ d : ℝ≥0, v (stepFull hm2 x q_fl d) ∂P.law ≤
      α * ∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law + c.θ * Δ := by
    nlinarith
  linarith

lemma bellmanT_eq_sInf_box {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) {x : XFull c.m}
    (hx : topLevel x.val ≤ (newsvendorLevel P.law c.h c.p : ℝ)) :
    bellmanT c hm2 P α v x =
      sInf ((fun q : ℝ≥0 => bellmanQ c hm2 P α v x q) ''
        {q : ℝ≥0 | (floorLevel c P : ℝ) ≤ orderUpTo x.val q ∧
          orderUpTo x.val q ≤ (newsvendorLevel P.law c.h c.p : ℝ)}) := by
  set S_NP := newsvendorLevel P.law c.h c.p
  set S_fl := floorLevel c P
  set A := {q : ℝ≥0 | (S_fl : ℝ) ≤ orderUpTo x.val q ∧ orderUpTo x.val q ≤ (S_NP : ℝ)}
  have hqNP_mem : Real.toNNReal ((S_NP : ℝ) - topLevel x.val) ∈ A := by
    have hord : orderUpTo x.val (Real.toNNReal ((S_NP : ℝ) - topLevel x.val)) = (S_NP : ℝ) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel x.val + (Real.toNNReal ((S_NP : ℝ) - topLevel x.val) : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr hx)]; ring
    exact ⟨by rw [hord]; exact NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_of_eq hord⟩
  have hne : ((fun q => bellmanQ c hm2 P α v x q) '' A).Nonempty := ⟨_, ⟨_, hqNP_mem, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun q : ℝ≥0 => bellmanQ c hm2 P α v x q) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact bellmanQ_nonneg hc hα0 hv x q⟩
  unfold bellmanT
  apply le_antisymm
  · refine le_csInf hne ?_
    rintro _ ⟨q, _, rfl⟩
    exact csInf_le hbdd ⟨q, rfl⟩
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨q, rfl⟩
    by_cases hhi : (S_NP : ℝ) ≤ orderUpTo x.val q
    · have hq0_le : Real.toNNReal ((S_NP : ℝ) - topLevel x.val) ≤ q := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (sub_nonneg.mpr hx)]
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo at hhi
        linarith
      exact le_trans (csInf_le (hbdd.mono (Set.image_subset_range _ _)) ⟨_, hqNP_mem, rfl⟩)
        (bellmanQ_ge_NP hc hα0 hv x q hq0_le)
    · push Not at hhi
      by_cases hlo : orderUpTo x.val q ≤ (S_fl : ℝ)
      · let q_fl := Real.toNNReal ((S_fl : ℝ) - topLevel x.val)
        have htop_fl : topLevel x.val ≤ (S_fl : ℝ) := by
          unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo at hlo; linarith [q.coe_nonneg]
        have hord_fl : orderUpTo x.val q_fl = (S_fl : ℝ) := by
          unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
          change topLevel x.val + (q_fl : ℝ) = (S_fl : ℝ)
          rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop_fl)]; ring
        have hqfl_mem : q_fl ∈ A :=
          ⟨le_of_eq hord_fl.symm, by rw [hord_fl]; exact NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2⟩
        exact le_trans (csInf_le (hbdd.mono (Set.image_subset_range _ _)) ⟨q_fl, hqfl_mem, rfl⟩)
          (bellmanQ_le_fl hc hα0 hα1 hv hx hlo)
      · push Not at hlo
        exact csInf_le (hbdd.mono (Set.image_subset_range _ _)) ⟨q, ⟨le_of_lt hlo, le_of_lt hhi⟩, rfl⟩

lemma bellmanT_preserves_VInv {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {v : XFull c.m → ℝ} (hv : VInv c hm2 P v) :
    VInv c hm2 P (bellmanT c hm2 P α v) := by
  have hbdd : ∀ x, BddBelow (Set.range fun q : ℝ≥0 => bellmanQ c hm2 P α v x q) := fun x =>
    ⟨0, by rintro _ ⟨q, rfl⟩; exact bellmanQ_nonneg hc hα0 hv x q⟩
  have hnonneg : ∀ x, 0 ≤ bellmanT c hm2 P α v x := fun x =>
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact bellmanQ_nonneg hc hα0 hv x q)
  have hlinear : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, bellmanT c hm2 P α v x ≤ C * (1 + topLevel x.val) := by
    rcases hv.linear with ⟨C₀, hC₀0, hC₀⟩
    let C := max (c.h + c.θ + α * C₀) (c.p * CappedBaseStock.mean P + α * C₀)
    have hC0 : 0 ≤ C := le_trans (by nlinarith [hc.h_pos, hc.θ_nonneg]) (le_max_left _ _)
    refine ⟨C, hC0, fun x => ?_⟩
    have hle0 : bellmanT c hm2 P α v x ≤ bellmanQ c hm2 P α v x 0 :=
      csInf_le (hbdd x) ⟨0, rfl⟩
    have htop_nn : 0 ≤ topLevel x.val := by rw [topLevel_eq_last hm2]; exact x.prop.1 _
    have hord0 : orderUpTo x.val 0 = topLevel x.val := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo; simp
    have h1 : ∫ d : ℝ≥0, max (topLevel x.val - (d : ℝ)) 0 ∂P.law ≤ topLevel x.val := by
      calc ∫ d : ℝ≥0, max (topLevel x.val - (d : ℝ)) 0 ∂P.law
          ≤ ∫ _ : ℝ≥0, topLevel x.val ∂P.law :=
            integral_mono (integrable_max_sub P _) (integrable_const _) fun d =>
              max_le (by linarith [d.coe_nonneg]) htop_nn
        _ = topLevel x.val := by simp [measureReal_def]
    have h2 : ∫ d : ℝ≥0, max ((d : ℝ) - topLevel x.val) 0 ∂P.law ≤ CappedBaseStock.mean P := by
      calc ∫ d : ℝ≥0, max ((d : ℝ) - topLevel x.val) 0 ∂P.law
          ≤ ∫ d : ℝ≥0, (d : ℝ) ∂P.law :=
            integral_mono (integrable_sub_max P _) P.finiteMean fun d =>
              max_le (by linarith) d.coe_nonneg
        _ = CappedBaseStock.mean P := rfl
    have h3 : ∫ d : ℝ≥0, max (firstLevel x.val 0 - (d : ℝ)) 0 ∂P.law ≤ topLevel x.val := by
      rw [firstLevel_eq_zero hm2]
      have hx0 : x.val ⟨0, by omega⟩ ≤ topLevel x.val := by
        rw [topLevel_eq_last hm2]; exact x.prop.2 (Fin.mk_le_mk.mpr (Nat.zero_le _))
      calc ∫ d : ℝ≥0, max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law
          ≤ ∫ _ : ℝ≥0, topLevel x.val ∂P.law :=
            integral_mono (integrable_max_sub P _) (integrable_const _) fun d =>
              max_le (by linarith [d.coe_nonneg]) htop_nn
        _ = topLevel x.val := by simp [measureReal_def]
    have h4 : ∫ d : ℝ≥0, v (stepFull hm2 x 0 d) ∂P.law ≤ C₀ * (1 + topLevel x.val) := by
      calc ∫ d : ℝ≥0, v (stepFull hm2 x 0 d) ∂P.law
          ≤ ∫ _ : ℝ≥0, C₀ * (1 + topLevel x.val) ∂P.law :=
            integral_mono (integrable_v_stepFull hv x 0) (integrable_const _) fun d => by
              have hst : topLevel (stepFull hm2 x 0 d).val ≤ topLevel x.val := by
                rw [topLevel_eq_last hm2, ← hord0]; exact step_le_orderUpTo hm2 x 0 d _
              calc v (stepFull hm2 x 0 d)
                  ≤ C₀ * (1 + topLevel (stepFull hm2 x 0 d).val) := hC₀ _
                _ ≤ C₀ * (1 + topLevel x.val) := by nlinarith
        _ = C₀ * (1 + topLevel x.val) := by simp [measureReal_def]
    have hC1 : c.h + c.θ + α * C₀ ≤ C := le_max_left _ _
    have hC2 : c.p * CappedBaseStock.mean P + α * C₀ ≤ C := le_max_right _ _
    unfold bellmanQ stageCost g0 at hle0
    rw [hord0] at hle0
    nlinarith [hc.h_pos, hc.p_pos, hc.θ_nonneg]
  have hpropP : ∀ x x' : XFull c.m,
      topLevel x.val ≤ (newsvendorLevel P.law c.h c.p : ℝ) →
      topLevel x'.val ≤ (newsvendorLevel P.law c.h c.p : ℝ) →
      ∀ δ : ℝ, 0 ≤ δ → (∀ j, x'.val j ≤ x.val j + δ) →
      bellmanT c hm2 P α v x' ≤ bellmanT c hm2 P α v x + c.θ * δ := by
    intro x x' hx hx' δ hδ hxx'
    set S_NP := newsvendorLevel P.law c.h c.p
    rw [bellmanT_eq_sInf_box hc hα0 hα1 hv hx]
    have hqNP_mem : Real.toNNReal ((S_NP : ℝ) - topLevel x.val) ∈
        {q : ℝ≥0 | (floorLevel c P : ℝ) ≤ orderUpTo x.val q ∧ orderUpTo x.val q ≤ (S_NP : ℝ)} := by
      have hord : orderUpTo x.val (Real.toNNReal ((S_NP : ℝ) - topLevel x.val)) = (S_NP : ℝ) := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
        change topLevel x.val + (Real.toNNReal ((S_NP : ℝ) - topLevel x.val) : ℝ) = (S_NP : ℝ)
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr hx)]; ring
      exact ⟨by rw [hord]; exact NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_of_eq hord⟩
    have hne : ((fun q => bellmanQ c hm2 P α v x q) ''
        {q : ℝ≥0 | (floorLevel c P : ℝ) ≤ orderUpTo x.val q ∧ orderUpTo x.val q ≤ (S_NP : ℝ)}).Nonempty :=
      ⟨_, ⟨_, hqNP_mem, rfl⟩⟩
    have hgoal : bellmanT c hm2 P α v x' - c.θ * δ ≤
        sInf ((fun q => bellmanQ c hm2 P α v x q) ''
          {q : ℝ≥0 | (floorLevel c P : ℝ) ≤ orderUpTo x.val q ∧ orderUpTo x.val q ≤ (S_NP : ℝ)}) := by
      refine le_csInf hne ?_
      rintro _ ⟨q, ⟨_, hq_le⟩, rfl⟩
      let y := orderUpTo x.val q
      let y' := max y (topLevel x'.val)
      let q' : ℝ≥0 := Real.toNNReal (y' - topLevel x'.val)
      have hy'_ord : orderUpTo x'.val q' = y' := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
        change topLevel x'.val + (q' : ℝ) = y'
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr (le_max_right _ _))]; ring
      have htop_x_nn : 0 ≤ topLevel x.val := by rw [topLevel_eq_last hm2]; exact x.prop.1 _
      have hy_nn : 0 ≤ y := add_nonneg htop_x_nn q.coe_nonneg
      have hy_le_y' : y ≤ y' := le_max_left _ _
      have hy'_le_NP : y' ≤ (S_NP : ℝ) := max_le hq_le hx'
      have hy'_le_add : y' ≤ y + δ := by
        refine max_le (by linarith) ?_
        rw [topLevel_eq_last hm2]
        have h1 := hxx' ⟨c.m - 2, by omega⟩
        unfold y orderUpTo PerishBaseStock.Lifetime.orderUpTo
        rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨c.m - 2, by omega⟩ from
          topLevel_eq_last hm2 x.val]
        linarith [q.coe_nonneg]
      have hg : g0 c P y' ≤ g0 c P y := by
        let yn : ℝ≥0 := Real.toNNReal y
        let yn' : ℝ≥0 := Real.toNNReal y'
        have h1 : (yn : ℝ) = y := Real.coe_toNNReal y hy_nn
        have h2 : (yn' : ℝ) = y' := Real.coe_toNNReal y' (le_trans hy_nn hy_le_y')
        rw [← h1, ← h2]
        exact g0_antitone_le_NP c hc P
          (by rw [← NNReal.coe_le_coe, h1, h2]; exact hy_le_y')
          (by rw [← NNReal.coe_le_coe, h2]; exact hy'_le_NP)
      have hpt : ∀ d : ℝ≥0,
          c.θ * (max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 - max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0) +
            α * (v (stepFull hm2 x' q' d) - v (stepFull hm2 x q d)) ≤ c.θ * δ := by
        intro d
        let diff0 := max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 - max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0
        have hdiff0_le : diff0 ≤ δ := by
          have h0 := hxx' ⟨0, by omega⟩
          have hm : max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 ≤
              max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 + δ :=
            max_le (by linarith [le_max_left (x.val ⟨0, by omega⟩ - (d : ℝ)) 0])
              (by linarith [le_max_right (x.val ⟨0, by omega⟩ - (d : ℝ)) 0])
          linarith
        let η := δ - diff0
        have hη : 0 ≤ η := sub_nonneg.mpr hdiff0_le
        have hst1 : topLevel (stepFull hm2 x q d).val ≤ (S_NP : ℝ) := by
          rw [topLevel_eq_last hm2]; exact le_trans (step_le_orderUpTo hm2 x q d _) hq_le
        have hst2 : topLevel (stepFull hm2 x' q' d).val ≤ (S_NP : ℝ) := by
          rw [topLevel_eq_last hm2]
          exact le_trans (step_le_orderUpTo hm2 x' q' d _) (by rw [hy'_ord]; exact hy'_le_NP)
        have hv_le : v (stepFull hm2 x' q' d) ≤ v (stepFull hm2 x q d) + c.θ * η := by
          refine hv.propP _ _ hst1 hst2 η hη fun j => ?_
          change step x'.val q' d j ≤ step x.val q d j + η
          rw [step_eq_diff hm2, step_eq_diff hm2]
          have hlev : levelAbove x'.val q' j ≤ levelAbove x.val q j + δ := by
            unfold levelAbove PerishBaseStock.Lifetime.levelAbove
            split_ifs with hj
            · exact hxx' ⟨j.val + 1, hj⟩
            · change orderUpTo x'.val q' ≤ orderUpTo x.val q + δ
              rw [hy'_ord]; exact hy'_le_add
          have hm : max (levelAbove x'.val q' j - (d : ℝ)) 0 ≤
              max (levelAbove x.val q j - (d : ℝ)) 0 + δ :=
            max_le (by linarith [le_max_left (levelAbove x.val q j - (d : ℝ)) 0])
              (by linarith [le_max_right (levelAbove x.val q j - (d : ℝ)) 0])
          linarith
        have h1 : α * (v (stepFull hm2 x' q' d) - v (stepFull hm2 x q d)) ≤ α * (c.θ * η) :=
          mul_le_mul_of_nonneg_left (by linarith) hα0
        have h2 : α * (c.θ * η) ≤ c.θ * η := by
          nlinarith [mul_nonneg hc.θ_nonneg hη]
        dsimp only [η, diff0] at h1 h2
        linarith
      have hint : c.θ * (∫ d : ℝ≥0, max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law -
            ∫ d : ℝ≥0, max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law) +
          α * (∫ d : ℝ≥0, v (stepFull hm2 x' q' d) ∂P.law -
            ∫ d : ℝ≥0, v (stepFull hm2 x q d) ∂P.law) ≤ c.θ * δ := by
        have hsub1 : Integrable (fun d : ℝ≥0 =>
            c.θ * (max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 - max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0)) P.law :=
          ((integrable_max_sub P _).sub (integrable_max_sub P _)).const_mul c.θ
        have hsub2 : Integrable (fun d : ℝ≥0 =>
            α * (v (stepFull hm2 x' q' d) - v (stepFull hm2 x q d))) P.law :=
          ((integrable_v_stepFull hv x' q').sub (integrable_v_stepFull hv x q)).const_mul α
        rw [← integral_sub (integrable_max_sub P _) (integrable_max_sub P _),
          ← integral_sub (integrable_v_stepFull hv x' q') (integrable_v_stepFull hv x q),
          ← integral_const_mul, ← integral_const_mul, ← integral_add hsub1 hsub2]
        calc ∫ d : ℝ≥0, (c.θ * (max (x'.val ⟨0, by omega⟩ - (d : ℝ)) 0 - max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0) +
              α * (v (stepFull hm2 x' q' d) - v (stepFull hm2 x q d))) ∂P.law
            ≤ ∫ _ : ℝ≥0, c.θ * δ ∂P.law :=
              integral_mono (hsub1.add hsub2) (integrable_const _) hpt
          _ = c.θ * δ := by simp [measureReal_def]
      have hQ_le : bellmanQ c hm2 P α v x' q' ≤ bellmanQ c hm2 P α v x q + c.θ * δ := by
        unfold bellmanQ stageCost
        rw [firstLevel_eq_zero hm2, firstLevel_eq_zero hm2, hy'_ord]
        linarith
      have hT_le : bellmanT c hm2 P α v x' ≤ bellmanQ c hm2 P α v x' q' :=
        csInf_le (hbdd x') ⟨q', rfl⟩
      linarith
    linarith
  have hcont : Continuous (bellmanT c hm2 P α v) := by
    set S_NP := newsvendorLevel P.law c.h c.p
    set U1 : Set (XFull c.m) := {x | topLevel x.val ≤ (S_NP : ℝ)}
    set U2 : Set (XFull c.m) := {x | (S_NP : ℝ) ≤ topLevel x.val}
    have htop_cont : Continuous (fun x : XFull c.m => topLevel x.val) := by
      have : ∀ y : State c.m, topLevel y = y ⟨c.m - 2, by omega⟩ := topLevel_eq_last hm2
      simp_rw [this]
      exact (continuous_apply _).comp continuous_subtype_val
    have hU1_cl : IsClosed U1 := isClosed_le htop_cont continuous_const
    have hU2_cl : IsClosed U2 := isClosed_le continuous_const htop_cont
    have hU1_cont : ContinuousOn (bellmanT c hm2 P α v) U1 := by
      rw [Metric.continuousOn_iff]
      intro x hx ε hε
      refine ⟨ε / (c.θ + 1), div_pos hε (by linarith [hc.θ_nonneg]), fun y hy hdist => ?_⟩
      rw [Real.dist_eq, abs_lt]
      have hle_j : ∀ j, |y.val j - x.val j| ≤ dist y x := fun j => by
        rw [Subtype.dist_eq]
        simpa [Real.dist_eq] using dist_le_pi_dist y.val x.val j
      have h1 : bellmanT c hm2 P α v y ≤ bellmanT c hm2 P α v x + c.θ * dist y x :=
        hpropP x y hx hy (dist y x) dist_nonneg fun j => by linarith [(abs_le.mp (hle_j j)).2]
      have h2 : bellmanT c hm2 P α v x ≤ bellmanT c hm2 P α v y + c.θ * dist y x :=
        hpropP y x hy hx (dist y x) dist_nonneg fun j => by linarith [(abs_le.mp (hle_j j)).1]
      have hθd : c.θ * dist y x < ε := by
        have hpos : 0 < c.θ + 1 := by linarith [hc.θ_nonneg]
        have : (c.θ + 1) * dist y x < ε := by
          have := mul_lt_mul_of_pos_left hdist hpos
          rwa [mul_div_cancel₀ _ (ne_of_gt hpos)] at this
        nlinarith [dist_nonneg (x := y) (y := x)]
      constructor <;> linarith
    have hU2_cont : ContinuousOn (bellmanT c hm2 P α v) U2 := by
      let g : XFull c.m → XFull c.m × ℝ≥0 := fun x => (x, 0)
      have hg : Continuous g := continuous_id.prodMk continuous_const
      have hcont0 : Continuous (fun x : XFull c.m => bellmanQ c hm2 P α v x 0) :=
        (continuous_bellmanQ hc hv).comp hg
      refine hcont0.continuousOn.congr fun x hx => ?_
      exact bellmanT_eq_zero_of_ge_NP hc hα0 hv hx
    have hunion : U1 ∪ U2 = Set.univ := by
      ext x
      change topLevel x.val ≤ (S_NP : ℝ) ∨ (S_NP : ℝ) ≤ topLevel x.val ↔ True
      exact iff_true_intro (le_total _ _)
    rw [← continuousOn_univ, ← hunion, continuousOn_union_iff_of_isClosed hU1_cl hU2_cl]
    exact ⟨hU1_cont, hU2_cont⟩
  have hpropQ : ∀ x x' : XFull c.m, zLe c.m x.val x'.val →
      bellmanT c hm2 P α v x ≤ bellmanT c hm2 P α v x' := by
    intro x x' hz
    set S_NP := newsvendorLevel P.law c.h c.p
    have hcase1 : ∀ a b : XFull c.m, zLe c.m a.val b.val → topLevel b.val ≤ (S_NP : ℝ) →
        bellmanT c hm2 P α v a ≤ bellmanT c hm2 P α v b := by
      intro a b hab hb
      have ha : topLevel a.val ≤ (S_NP : ℝ) := by
        rw [topLevel_eq_last hm2] at hb ⊢; exact le_trans (zLe_le hab _) hb
      have h := hpropP b a hb ha 0 le_rfl (fun j => by simpa using zLe_le hab j)
      linarith
    have hcase2 : ∀ a b : XFull c.m, zLe c.m a.val b.val → (S_NP : ℝ) ≤ topLevel a.val →
        bellmanT c hm2 P α v a ≤ bellmanT c hm2 P α v b := by
      intro a b hab ha
      have hb : (S_NP : ℝ) ≤ topLevel b.val := by
        rw [topLevel_eq_last hm2] at ha ⊢; exact le_trans ha (zLe_le hab _)
      rw [bellmanT_eq_zero_of_ge_NP hc hα0 hv ha, bellmanT_eq_zero_of_ge_NP hc hα0 hv hb]
      unfold bellmanQ stageCost
      rw [firstLevel_eq_zero hm2, firstLevel_eq_zero hm2]
      have hord_a : orderUpTo a.val 0 = topLevel a.val := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo; simp
      have hord_b : orderUpTo b.val 0 = topLevel b.val := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo; simp
      rw [hord_a, hord_b]
      have htop_a_nn : 0 ≤ topLevel a.val := by rw [topLevel_eq_last hm2]; exact a.prop.1 _
      have htop_b_nn : 0 ≤ topLevel b.val := by rw [topLevel_eq_last hm2]; exact b.prop.1 _
      let an : ℝ≥0 := Real.toNNReal (topLevel a.val)
      let bn : ℝ≥0 := Real.toNNReal (topLevel b.val)
      have han : (an : ℝ) = topLevel a.val := Real.coe_toNNReal _ htop_a_nn
      have hbn : (bn : ℝ) = topLevel b.val := Real.coe_toNNReal _ htop_b_nn
      have hg : g0 c P (topLevel a.val) ≤ g0 c P (topLevel b.val) := by
        rw [← han, ← hbn]
        exact g0_monotone_ge_NP c hc P
          (by rw [← NNReal.coe_le_coe, han]; exact ha)
          (by rw [← NNReal.coe_le_coe, han, hbn, topLevel_eq_last hm2, topLevel_eq_last hm2]
              exact zLe_le hab _)
      have hout : ∫ d : ℝ≥0, max (a.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law ≤
          ∫ d : ℝ≥0, max (b.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law :=
        integral_mono (integrable_max_sub P _) (integrable_max_sub P _) fun d =>
          max_le_max_right 0 (sub_le_sub_right (hab.1 (by omega)) (d : ℝ))
      have hint : ∫ d : ℝ≥0, v (stepFull hm2 a 0 d) ∂P.law ≤
          ∫ d : ℝ≥0, v (stepFull hm2 b 0 d) ∂P.law :=
        integral_mono (integrable_v_stepFull hv a 0) (integrable_v_stepFull hv b 0) fun d =>
          hv.propQ _ _ (zLe_step_zero hm2 hab d)
      nlinarith [hc.θ_nonneg]
    rcases le_total (topLevel x'.val) (S_NP : ℝ) with hx' | hx'
    · exact hcase1 x x' hz hx'
    · rcases le_total (S_NP : ℝ) (topLevel x.val) with hx | hx
      · exact hcase2 x x' hz hx
      · by_cases heq : topLevel x.val = topLevel x'.val
        · exact hcase1 x x' hz (by linarith)
        · have hlt : topLevel x.val < topLevel x'.val :=
            lt_of_le_of_ne (by rw [topLevel_eq_last hm2, topLevel_eq_last hm2]; exact zLe_le hz _) heq
          let lam : ℝ := ((S_NP : ℝ) - topLevel x.val) / (topLevel x'.val - topLevel x.val)
          have hden : 0 < topLevel x'.val - topLevel x.val := sub_pos.mpr hlt
          have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hx) (le_of_lt hden)
          have hlam1 : lam ≤ 1 := (div_le_one hden).mpr (by linarith)
          let xm : XFull c.m := ⟨fun j => (1 - lam) * x.val j + lam * x'.val j,
            ⟨fun j => add_nonneg (mul_nonneg (by linarith) (x.prop.1 j))
              (mul_nonneg hlam0 (x'.prop.1 j)),
            fun i j hij => add_le_add
              (mul_le_mul_of_nonneg_left (x.prop.2 hij) (by linarith))
              (mul_le_mul_of_nonneg_left (x'.prop.2 hij) hlam0)⟩⟩
          have htop_m : topLevel xm.val = (S_NP : ℝ) := by
            rw [topLevel_eq_last hm2]
            change (1 - lam) * x.val ⟨c.m - 2, by omega⟩ + lam * x'.val ⟨c.m - 2, by omega⟩ = (S_NP : ℝ)
            rw [← topLevel_eq_last hm2 x.val, ← topLevel_eq_last hm2 x'.val]
            dsimp only [lam]
            field_simp [ne_of_gt hden]; ring
          have hz1 : zLe c.m x.val xm.val := by
            constructor
            · intro h0; change x.val _ ≤ (1 - lam) * x.val _ + lam * x'.val _
              nlinarith [hz.1 h0]
            · intro j hj
              change x.val _ - x.val _ ≤
                ((1 - lam) * x.val _ + lam * x'.val _) - ((1 - lam) * x.val _ + lam * x'.val _)
              nlinarith [hz.2 j hj]
          have hz2 : zLe c.m xm.val x'.val := by
            constructor
            · intro h0; change (1 - lam) * x.val _ + lam * x'.val _ ≤ x'.val _
              nlinarith [hz.1 h0]
            · intro j hj
              change ((1 - lam) * x.val _ + lam * x'.val _) - ((1 - lam) * x.val _ + lam * x'.val _) ≤
                x'.val _ - x'.val _
              nlinarith [hz.2 j hj]
          exact le_trans (hcase1 x xm hz1 (le_of_eq htop_m)) (hcase2 xm x' hz2 (le_of_eq htop_m.symm))
  exact ⟨hnonneg, hlinear, hcont, hpropP, hpropQ⟩

lemma bellmanV_VInv {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℕ) :
    VInv c hm2 P (bellmanV c hm2 P α n) := by
  induction n with
  | zero =>
    refine ⟨fun _ => le_rfl, ⟨0, le_rfl, fun _ => by simp [bellmanV]⟩, continuous_const,
      fun _ _ _ _ δ hδ _ => by simp only [bellmanV, zero_add]; exact mul_nonneg hc.θ_nonneg hδ,
      fun _ _ _ => le_rfl⟩
  | succ n ih => exact bellmanT_preserves_VInv hc hα0 hα1 ih

lemma bellmanV_mono {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℕ) (x : XFull c.m) :
    bellmanV c hm2 P α n x ≤ bellmanV c hm2 P α (n + 1) x := by
  induction n generalizing x with
  | zero => exact (bellmanV_VInv hc hα0 hα1 1).nonneg x
  | succ n ih =>
    unfold bellmanV bellmanT
    have hbdd : BddBelow (Set.range fun q : ℝ≥0 => bellmanQ c hm2 P α (bellmanV c hm2 P α n) x q) :=
      ⟨0, by rintro _ ⟨q, rfl⟩; exact bellmanQ_nonneg hc hα0 (bellmanV_VInv hc hα0 hα1 n) x q⟩
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨q, rfl⟩
    refine le_trans (csInf_le hbdd ⟨q, rfl⟩) ?_
    unfold bellmanQ
    have hint : ∫ d : ℝ≥0, bellmanV c hm2 P α n (stepFull hm2 x q d) ∂P.law ≤
        ∫ d : ℝ≥0, bellmanV c hm2 P α (n + 1) (stepFull hm2 x q d) ∂P.law :=
      integral_mono (integrable_v_stepFull (bellmanV_VInv hc hα0 hα1 n) x q)
        (integrable_v_stepFull (bellmanV_VInv hc hα0 hα1 (n + 1)) x q) (fun d => ih _)
    nlinarith

lemma ofReal_bellmanV_le_vFull {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (n : ℕ) (x : XFull c.m) :
    ENNReal.ofReal (bellmanV c hm2 P α n x) ≤ vβ (modelFull c hc hm2 P) α x := by
  have hthm2 := FKZAvg.WStar.theorem_2 (modelFull c hc hm2 P) (hasSelector_full c hc hm2 P)
    (condWStar_full c hc hm2 P) α hα0 hα1
  have hbell := hthm2.2.1.1
  induction n generalizing x with
  | zero => simp [bellmanV]
  | succ n ih =>
    rw [hbell x]
    refine le_iInf fun q => le_iInf fun _ => ?_
    have hv := bellmanV_VInv (hm2 := hm2) (P := P) hc hα0 hα1 n
    have hle : bellmanV c hm2 P α (n + 1) x ≤ bellmanQ c hm2 P α (bellmanV c hm2 P α n) x q :=
      csInf_le ⟨0, by rintro _ ⟨q', rfl⟩; exact bellmanQ_nonneg hc hα0 hv x q'⟩ ⟨q, rfl⟩
    calc ENNReal.ofReal (bellmanV c hm2 P α (n + 1) x)
        ≤ ENNReal.ofReal (bellmanQ c hm2 P α (bellmanV c hm2 P α n) x q) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (stageCost c P x.val q) +
            ENNReal.ofReal α * ENNReal.ofReal (∫ d : ℝ≥0, bellmanV c hm2 P α n (stepFull hm2 x q d) ∂P.law) := by
          unfold bellmanQ
          rw [ENNReal.ofReal_add (stageCost_nonneg c hc P x.val q)
            (mul_nonneg hα0 (integral_nonneg fun d => hv.nonneg _)),
            ENNReal.ofReal_mul hα0]
      _ = (modelFull c hc hm2 P).toMDP.cost x q +
            ENNReal.ofReal α * ∫⁻ y, ENNReal.ofReal (bellmanV c hm2 P α n y) ∂((modelFull c hc hm2 P).toMDP.q (x, q)) := by
          congr 2
          rw [ofReal_integral_eq_lintegral_ofReal (integrable_v_stepFull hv x q)
            (Eventually.of_forall fun d => hv.nonneg _)]
          change ∫⁻ d, ENNReal.ofReal (bellmanV c hm2 P α n (stepFull hm2 x q d)) ∂P.law =
            ∫⁻ y, ENNReal.ofReal (bellmanV c hm2 P α n y) ∂(kernelFull c hm2 P (x, q))
          rw [kernelFull_apply]
          dsimp only
          have hmeas_v : Measurable (fun y : XFull c.m => ENNReal.ofReal (bellmanV c hm2 P α n y)) :=
            ENNReal.continuous_ofReal.measurable.comp hv.cont.measurable
          rw [lintegral_map hmeas_v (continuous_stepFull_d hm2 x q).measurable]
      _ ≤ eta (modelFull c hc hm2 P) (vβ (modelFull c hc hm2 P) α) α x q := by
          unfold eta
          gcongr with y
          exact ih y

def boxToFull {m : ℕ} {S : ℝ≥0} (x : XBox m S) : XFull m :=
  ⟨x.val, x.prop.1, x.prop.2.1⟩

lemma bellmanV_box_bdd {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    let S_NP := newsvendorLevel P.law c.h c.p
    let K := g0 c P S_NP + c.θ * (S_NP : ℝ)
    0 ≤ K ∧ ∀ (n : ℕ) (x : XBox c.m S_NP), bellmanV c hm2 P α n (boxToFull x) ≤ K / (1 - α) := by
  intro S_NP K
  have hK0 : 0 ≤ K := add_nonneg (g0_nonneg c hc P S_NP) (mul_nonneg hc.θ_nonneg S_NP.coe_nonneg)
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  refine ⟨hK0, fun n => ?_⟩
  induction n with
  | zero => intro x; simp only [bellmanV]; exact div_nonneg hK0 (le_of_lt h1α)
  | succ n ih =>
    intro x
    have hv := bellmanV_VInv (hm2 := hm2) (P := P) hc hα0 hα1 n
    have htop : topLevel x.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact x.prop.2.2 _
    let q : ℝ≥0 := Real.toNNReal ((S_NP : ℝ) - topLevel x.val)
    have hord : orderUpTo x.val q = (S_NP : ℝ) := by
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel x.val + (q : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]; ring
    have hle : bellmanV c hm2 P α (n + 1) (boxToFull x) ≤
        bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) q :=
      csInf_le ⟨0, by rintro _ ⟨q', rfl⟩; exact bellmanQ_nonneg hc hα0 hv _ q'⟩ ⟨q, rfl⟩
    have hsc : stageCost c P x.val q ≤ K := by
      unfold stageCost
      rw [hord, firstLevel_eq_zero hm2]
      have hx0 : x.val ⟨0, by omega⟩ ≤ (S_NP : ℝ) := x.prop.2.2 _
      have hout : ∫ d : ℝ≥0, max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law ≤ (S_NP : ℝ) := by
        calc ∫ d : ℝ≥0, max (x.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law
            ≤ ∫ _ : ℝ≥0, (S_NP : ℝ) ∂P.law :=
              integral_mono (integrable_max_sub P _) (integrable_const _) fun d =>
                max_le (by linarith [d.coe_nonneg]) S_NP.coe_nonneg
          _ = (S_NP : ℝ) := by simp [measureReal_def]
      nlinarith [hc.θ_nonneg]
    have hint : ∫ d : ℝ≥0, bellmanV c hm2 P α n (stepFull hm2 (boxToFull x) q d) ∂P.law ≤
        K / (1 - α) := by
      calc ∫ d : ℝ≥0, bellmanV c hm2 P α n (stepFull hm2 (boxToFull x) q d) ∂P.law
          ≤ ∫ _ : ℝ≥0, K / (1 - α) ∂P.law :=
            integral_mono (integrable_v_stepFull hv _ q) (integrable_const _) fun d => by
              have hst : stepFull hm2 (boxToFull x) q d = boxToFull (stepBox hm2 S_NP x q d) := by
                ext j; exact (congrFun (stepBox_eq_step hm2 S_NP x q d (le_of_eq hord)) j).symm
              rw [hst]; exact ih _
        _ = K / (1 - α) := by simp [measureReal_def]
    have heq : K + α * (K / (1 - α)) = K / (1 - α) := by field_simp [ne_of_gt h1α]; ring
    unfold bellmanQ at hle
    change stageCost c P (boxToFull x).val q ≤ K at hsc
    nlinarith

lemma ae_action_eq_statPolicy {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableEq A]
    (M : Model X A) {φ : X → A} (hφ : IsStationary M φ) (x : X) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M.toMDP (statPolicy hφ) x), (ω t).2 = φ (ω t).1 := by
  have hm_eq : MeasurableSet {p : X × A | p.2 = φ p.1} :=
    measurableSet_eq_fun measurable_snd (hφ.1.comp measurable_fst)
  cases t with
  | zero =>
    have hmap0 : (pathMeasure M.toMDP (statPolicy hφ) x).map (fun ω => ω 0) =
        initMeasure (statPolicy hφ) x := by
      unfold pathMeasure Kernel.trajMeasure
      have h1 : (fun ω : ℕ → X × A => ω 0) =
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × A)) ∘
            (Preorder.frestrictLe 0) := rfl
      rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_comp _ _ (by fun_prop),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
        Measure.map_map (by fun_prop) (by fun_prop)]
      have hid : (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × A)) ∘
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × A)).symm = id :=
        MeasurableEquiv.self_comp_symm _
      rw [hid, Measure.map_id]
    rw [ae_iff]
    have hpre : {ω : ℕ → X × A | ¬ (ω 0).2 = φ (ω 0).1} =
        (fun ω => ω 0) ⁻¹' {p : X × A | p.2 = φ p.1}ᶜ := rfl
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hm_eq.compl, hmap0]
    unfold initMeasure statPolicy Policy.ofStationary
    have hmk : Measurable (fun a : A => (x, a)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmk hm_eq.compl, Kernel.deterministic_apply]
    simp
  | succ t =>
    have hprob_init : IsProbabilityMeasure (initMeasure (statPolicy hφ) x) := by
      unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hpair := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => X × A)
      (μ₀ := initMeasure (statPolicy hφ) x)
      (κ := stepKernel M.toMDP (statPolicy hφ)) (a := t)
    rw [ae_iff]
    have hpre : {ω : ℕ → X × A | ¬ (ω (t + 1)).2 = φ (ω (t + 1)).1} =
        (fun ω => (Preorder.frestrictLe t ω, ω (t + 1))) ⁻¹' (Prod.snd ⁻¹' {p | p.2 = φ p.1}ᶜ) := rfl
    change pathMeasure M.toMDP (statPolicy hφ) x _ = 0
    unfold pathMeasure
    rw [hpre, ← Measure.map_apply ((Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t + 1)))
        (measurable_snd hm_eq.compl), ← hpair,
      ← Measure.snd_apply hm_eq.compl, Measure.snd_compProd,
      Measure.bind_apply hm_eq.compl (Kernel.aemeasurable _)]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ hm_eq.compl)).mpr
      (Eventually.of_forall fun h => ?_)
    have hlast_meas : Measurable (lastPair (X := X) (A := A) t) := measurable_pi_apply _
    have h1 : IsMarkovKernel (M.toMDP.q.comap (lastPair (X := X) (A := A) t) hlast_meas) :=
      Kernel.IsMarkovKernel.comap _ _
    have h2 : IsMarkovKernel (((statPolicy hφ).rule (t + 1)).comap
        (fun p : (Π _ : Finset.Iic t, X × A) × X => (histFin t p.1, p.2))
        (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
      Kernel.IsMarkovKernel.comap _ _
    change ((M.toMDP.q.comap (lastPair (X := X) (A := A) t) hlast_meas) ⊗ₖ
      (((statPolicy hφ).rule (t + 1)).comap
        (fun p : (Π _ : Finset.Iic t, X × A) × X => (histFin t p.1, p.2))
        (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))) h {p | p.2 = φ p.1}ᶜ = 0
    rw [Kernel.compProd_apply hm_eq.compl]
    have hzero : (fun y : X =>
        (((statPolicy hφ).rule (t + 1)).comap
          (fun p : (Π _ : Finset.Iic t, X × A) × X => (histFin t p.1, p.2))
          (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))
          (h, y) (Prod.mk y ⁻¹' {p | p.2 = φ p.1}ᶜ)) = fun _ => 0 := by
      ext y
      rw [Kernel.comap_apply]
      unfold statPolicy Policy.ofStationary
      have hs' : MeasurableSet (Prod.mk y ⁻¹' {p : X × A | p.2 = φ p.1}ᶜ) :=
        measurable_prodMk_left hm_eq.compl
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hs']
      simp
    rw [hzero, lintegral_zero]

lemma vBox_le_const {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (x : XBox c.m (newsvendorLevel P.law c.h c.p)) :
    let S_NP := newsvendorLevel P.law c.h c.p
    let K := g0 c P S_NP + c.θ * (S_NP : ℝ)
    vβ (modelBox c hc hm2 P) α x ≤ ENNReal.ofReal (K / (1 - α)) := by
  intro S_NP K
  let φ : XBox c.m S_NP → ℝ≥0 := fun y => Real.toNNReal ((S_NP : ℝ) - topLevel y.val)
  have hφ : IsStationary (modelBox c hc hm2 P) φ := by
    refine ⟨measurable_real_toNNReal.comp
      (measurable_const.sub ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp
        measurable_subtype_coe)), fun y => ?_⟩
    have htop : topLevel y.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact y.prop.2.2 _
    have hord : orderUpTo y.val (φ y) = (S_NP : ℝ) := by
      unfold φ orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel y.val + (Real.toNNReal ((S_NP : ℝ) - topLevel y.val) : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]; ring
    show (floorLevel c P : ℝ) ≤ orderUpTo y.val (φ y) ∧ orderUpTo y.val (φ y) ≤ (S_NP : ℝ)
    rw [hord]
    exact ⟨NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_rfl⟩
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  have hK0 : 0 ≤ K := add_nonneg (g0_nonneg c hc P S_NP) (mul_nonneg hc.θ_nonneg S_NP.coe_nonneg)
  have hφ_cost : ∀ y : XBox c.m S_NP, (modelBox c hc hm2 P).toMDP.cost y (φ y) ≤ ENNReal.ofReal K := by
    intro y
    refine ENNReal.ofReal_le_ofReal ?_
    have htop : topLevel y.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact y.prop.2.2 _
    have hord : orderUpTo y.val (φ y) = (S_NP : ℝ) := by
      unfold φ orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change topLevel y.val + (Real.toNNReal ((S_NP : ℝ) - topLevel y.val) : ℝ) = (S_NP : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]; ring
    unfold stageCost
    rw [hord, firstLevel_eq_zero hm2]
    have hout : ∫ d : ℝ≥0, max (y.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law ≤ (S_NP : ℝ) := by
      calc ∫ d : ℝ≥0, max (y.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law
          ≤ ∫ _ : ℝ≥0, (S_NP : ℝ) ∂P.law :=
            integral_mono (integrable_max_sub P _) (integrable_const _) fun d =>
              max_le (by linarith [d.coe_nonneg, y.prop.2.2 ⟨0, by omega⟩]) S_NP.coe_nonneg
        _ = (S_NP : ℝ) := by simp [measureReal_def]
    nlinarith [hc.θ_nonneg]
  have hstat_adm : Admissible (modelBox c hc hm2 P) (statPolicy hφ) := by
    intro t h
    simp [statPolicy, Policy.ofStationary, Kernel.deterministic_apply, hφ.2]
  refine le_trans (iInf_le (fun π : {π : FeinbergLiang.ACOE.Policy _ _ // Admissible (modelBox c hc hm2 P) π} =>
    Jbeta (modelBox c hc hm2 P) π.1 α x) ⟨statPolicy hφ, hstat_adm⟩) ?_
  unfold Jbeta vDisc
  have hprob : IsProbabilityMeasure (pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) x) := by
    unfold pathMeasure
    have : IsProbabilityMeasure (initMeasure (statPolicy hφ) x) := by
      unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)
    infer_instance
  have hae_all : ∀ᵐ ω ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) x),
      ∀ t : ℕ, (ω t).2 = φ (ω t).1 :=
    ae_all_iff.mpr fun t => ae_action_eq_statPolicy (modelBox c hc hm2 P) hφ x t
  calc ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t) * (modelBox c hc hm2 P).toMDP.cost (ω t).1 (ω t).2
        ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) x)
      ≤ ∫⁻ _, ∑' t : ℕ, ENNReal.ofReal (α ^ t) * ENNReal.ofReal K
        ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) x) := by
        refine lintegral_mono_ae (hae_all.mono fun ω hω => ?_)
        refine ENNReal.tsum_le_tsum fun t => ?_
        rw [hω t]
        gcongr
        exact hφ_cost _
    _ = ∑' t : ℕ, ENNReal.ofReal (α ^ t) * ENNReal.ofReal K := by simp
    _ = ENNReal.ofReal K * ∑' t : ℕ, ENNReal.ofReal (α ^ t) := by
        simp_rw [mul_comm (ENNReal.ofReal (α ^ _))]; rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (K / (1 - α)) := by
        have hgeom : (∑' t : ℕ, ENNReal.ofReal (α ^ t)) = ENNReal.ofReal (1 / (1 - α)) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg hα0 t)
            (summable_geometric_of_lt_one hα0 hα1), tsum_geometric_of_lt_one hα0 hα1, one_div]
        rw [hgeom, ← ENNReal.ofReal_mul hK0, mul_one_div]

/-- Key theorem of Section 4: on `XBox`, `vβ M_box α` coincides with `ENNReal.ofReal ∘ V_lim`,
which is ≤ `vβ M_full α` and satisfies the `c.θ`-Lipschitz bound `P`. -/
lemma vBox_eq_Vlim_and_le_vFull {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    {P : CappedBaseStock.DemandLaw} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    let S_NP := newsvendorLevel P.law c.h c.p
    (∀ x : XBox c.m S_NP, vβ (modelBox c hc hm2 P) α x ≤ vβ (modelFull c hc hm2 P) α (boxToFull x)) ∧
    (∀ x : XBox c.m S_NP, vβ (modelBox c hc hm2 P) α (x0Box c.m S_NP) ≤ vβ (modelBox c hc hm2 P) α x) ∧
    (∀ x : XBox c.m S_NP, vβ (modelBox c hc hm2 P) α x ≤
      vβ (modelBox c hc hm2 P) α (x0Box c.m S_NP) + ENNReal.ofReal (c.θ * (S_NP : ℝ))) := by
  intro S_NP
  let K := g0 c P S_NP + c.θ * (S_NP : ℝ)
  have hbdd_V := bellmanV_box_bdd hc hα0 hα1 (c := c) (hm2 := hm2) (P := P) (α := α)
  let Vlim : XBox c.m S_NP → ℝ := fun x => ⨆ n : ℕ, bellmanV c hm2 P α n (boxToFull x)
  have hBddAbove : ∀ x : XBox c.m S_NP, BddAbove (Set.range fun n => bellmanV c hm2 P α n (boxToFull x)) :=
    fun x => ⟨K / (1 - α), by rintro _ ⟨n, rfl⟩; exact hbdd_V.2 n x⟩
  have hVlim_nonneg : ∀ x, 0 ≤ Vlim x := fun x =>
    le_trans ((bellmanV_VInv hc hα0 hα1 0).nonneg (boxToFull x)) (le_ciSup (hBddAbove x) 0)
  have hVlim_le_K : ∀ x, Vlim x ≤ K / (1 - α) := fun x =>
    ciSup_le fun n => hbdd_V.2 n x
  have hVlim_tend : ∀ x, Tendsto (fun n => bellmanV c hm2 P α n (boxToFull x)) atTop (𝓝 (Vlim x)) :=
    fun x => tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => bellmanV_mono hc hα0 hα1 n _) (hBddAbove x)
  have hVlim_ofReal_tend : ∀ x, Tendsto (fun n => ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull x)))
      atTop (𝓝 (ENNReal.ofReal (Vlim x))) :=
    fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hVlim_tend x)
  have hVlim_le_vFull : ∀ x, ENNReal.ofReal (Vlim x) ≤ vβ (modelFull c hc hm2 P) α (boxToFull x) :=
    fun x => le_of_tendsto (hVlim_ofReal_tend x) (Eventually.of_forall fun n => ofReal_bellmanV_le_vFull hc hα0 hα1 n _)
  have hVlim_P : ∀ x x' : XBox c.m S_NP, ∀ δ : ℝ, 0 ≤ δ → (∀ j, x'.val j ≤ x.val j + δ) →
      Vlim x' ≤ Vlim x + c.θ * δ := by
    intro x x' δ hδ hxx'
    refine le_of_tendsto_of_tendsto (hVlim_tend x') ((hVlim_tend x).add tendsto_const_nhds)
      (Eventually.of_forall fun n => ?_)
    have htx : topLevel (boxToFull x).val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact x.prop.2.2 _
    have htx' : topLevel (boxToFull x').val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact x'.prop.2.2 _
    exact (bellmanV_VInv hc hα0 hα1 n).propP _ _ htx htx' δ hδ hxx'
  have hVlim_cont : Continuous Vlim := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε / (c.θ + 1), div_pos hε (by linarith [hc.θ_nonneg]), fun y hdist => ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hle_j : ∀ j, |y.val j - x.val j| ≤ dist y x := fun j => by
      rw [Subtype.dist_eq]
      simpa [Real.dist_eq] using dist_le_pi_dist y.val x.val j
    have h1 := hVlim_P x y (dist y x) dist_nonneg fun j => by linarith [(abs_le.mp (hle_j j)).2]
    have h2 := hVlim_P y x (dist y x) dist_nonneg fun j => by linarith [(abs_le.mp (hle_j j)).1]
    have hθd : c.θ * dist y x < ε := by
      have hpos : 0 < c.θ + 1 := by linarith [hc.θ_nonneg]
      have : (c.θ + 1) * dist y x < ε := by
        have := mul_lt_mul_of_pos_left hdist hpos
        rwa [mul_div_cancel₀ _ (ne_of_gt hpos)] at this
      nlinarith [dist_nonneg (x := y) (y := x)]
    constructor <;> linarith
  -- Show ENNReal.ofReal ∘ Vlim is a fixed point of the modelBox Bellman operator!
  have hVlim_bell : ∀ x : XBox c.m S_NP,
      ENNReal.ofReal (Vlim x) =
        ⨅ a ∈ (modelBox c hc hm2 P).Aset x,
          eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (Vlim y)) α x a := by
    intro x
    have htop_x : topLevel x.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact x.prop.2.2 _
    have heta_eq : ∀ (n : ℕ) (a : ℝ≥0), a ∈ (modelBox c hc hm2 P).Aset x →
        ENNReal.ofReal (bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) a) =
          eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull y))) α x a := by
      intro n a ha
      have hv := bellmanV_VInv (hm2 := hm2) (P := P) hc hα0 hα1 n
      unfold bellmanQ eta
      rw [ENNReal.ofReal_add (stageCost_nonneg c hc P (boxToFull x).val a)
        (mul_nonneg hα0 (integral_nonneg fun d => hv.nonneg _)),
        ENNReal.ofReal_mul hα0,
        ofReal_integral_eq_lintegral_ofReal (integrable_v_stepFull hv (boxToFull x) a)
          (Eventually.of_forall fun d => hv.nonneg _)]
      congr 2
      change ∫⁻ d, ENNReal.ofReal (bellmanV c hm2 P α n (stepFull hm2 (boxToFull x) a d)) ∂P.law =
        ∫⁻ y, ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull y)) ∂(kernelBox c hm2 P S_NP (x, a))
      have hbf : Measurable (boxToFull (m := c.m) (S := S_NP)) := measurable_subtype_coe.subtype_mk
      have hmeas_vb : Measurable (fun y : XBox c.m S_NP =>
          ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull y))) :=
        ENNReal.measurable_ofReal.comp (hv.cont.measurable.comp hbf)
      rw [kernelBox_apply]
      dsimp only
      rw [lintegral_map hmeas_vb (continuous_stepBox_d hm2 S_NP x a).measurable]
      refine lintegral_congr fun d => ?_
      have hst : stepFull hm2 (boxToFull x) a d = boxToFull (stepBox hm2 S_NP x a d) := by
        ext j; exact (congrFun (stepBox_eq_step hm2 S_NP x a d ha.2) j).symm
      rw [hst]
    apply le_antisymm
    · refine le_iInf fun a => le_iInf fun ha => ?_
      refine le_of_tendsto (hVlim_ofReal_tend x) (Eventually.of_forall fun n => ?_)
      have hle1 : bellmanV c hm2 P α n (boxToFull x) ≤ bellmanV c hm2 P α (n + 1) (boxToFull x) :=
        bellmanV_mono hc hα0 hα1 n _
      have hle2 : bellmanV c hm2 P α (n + 1) (boxToFull x) ≤
          bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) a :=
        csInf_le ⟨0, by rintro _ ⟨q', rfl⟩; exact bellmanQ_nonneg hc hα0 (bellmanV_VInv hc hα0 hα1 n) _ q'⟩ ⟨a, rfl⟩
      calc ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull x))
          ≤ ENNReal.ofReal (bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) a) :=
            ENNReal.ofReal_le_ofReal (le_trans hle1 hle2)
        _ = eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (bellmanV c hm2 P α n (boxToFull y))) α x a :=
            heta_eq n a ha
        _ ≤ eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (Vlim y)) α x a := by
            unfold eta; gcongr with y
            exact ENNReal.ofReal_le_ofReal (le_ciSup (hBddAbove y) n)
    · -- Reverse direction via compactness of Aset x + Monotone Convergence
      have hA_comp : IsCompact ((modelBox c hc hm2 P).Aset x) := by
        have hsub : (modelBox c hc hm2 P).Aset x ⊆ Set.Icc (0 : ℝ≥0) S_NP := fun q hq => by
          refine ⟨zero_le, ?_⟩
          have hle := hq.2
          unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo at hle
          rw [show PerishBaseStock.Lifetime.topLevel x.val = x.val ⟨c.m - 2, by omega⟩ from
            topLevel_eq_last hm2 x.val] at hle
          rw [← NNReal.coe_le_coe]; linarith [x.prop.1 ⟨c.m - 2, by omega⟩]
        have hcl : IsClosed ((modelBox c hc hm2 P).Aset x) := by
          have hord : Continuous (fun q : ℝ≥0 => orderUpTo x.val q) :=
            continuous_const.add NNReal.continuous_coe
          exact (isClosed_le continuous_const hord).inter (isClosed_le hord continuous_const)
        exact isCompact_Icc.of_isClosed_subset hcl hsub
      have hex_a : ∀ n : ℕ, ∃ a ∈ (modelBox c hc hm2 P).Aset x,
          bellmanV c hm2 P α (n + 1) (boxToFull x) =
            bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) a := by
        intro n
        have hv := bellmanV_VInv (hm2 := hm2) (P := P) hc hα0 hα1 n
        have hne_A := (modelBox c hc hm2 P).Aset_nonempty x
        let gq : ℝ≥0 → XFull c.m × ℝ≥0 := fun a => (boxToFull x, a)
        have hgq : Continuous gq := continuous_const.prodMk continuous_id
        have hcont_q : ContinuousOn (fun a : ℝ≥0 => bellmanQ c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) a)
            ((modelBox c hc hm2 P).Aset x) :=
          ((continuous_bellmanQ hc hv).comp hgq).continuousOn
        rcases hA_comp.exists_isMinOn hne_A hcont_q with ⟨a, ha, hmin⟩
        refine ⟨a, ha, ?_⟩
        change bellmanT c hm2 P α (bellmanV c hm2 P α n) (boxToFull x) = _
        rw [bellmanT_eq_sInf_box hc hα0 hα1 hv htop_x]
        apply le_antisymm
        · exact csInf_le ⟨0, by rintro _ ⟨q, _, rfl⟩; exact bellmanQ_nonneg hc hα0 hv _ q⟩ ⟨a, ha, rfl⟩
        · exact le_csInf ⟨_, ⟨a, ha, rfl⟩⟩ (by rintro _ ⟨q, hq, rfl⟩; exact hmin hq)
      choose as has_mem has_eq using hex_a
      rcases hA_comp.tendsto_subseq has_mem with ⟨astar, hastar, φ, hφ_mono, hφ_tend⟩
      have hge_m : ∀ m : ℕ,
          eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (bellmanV c hm2 P α m (boxToFull y))) α x astar ≤
            ENNReal.ofReal (Vlim x) := by
        intro m
        rw [← heta_eq m astar hastar]
        refine ENNReal.ofReal_le_ofReal ?_
        let gq : ℝ≥0 → XFull c.m × ℝ≥0 := fun a => (boxToFull x, a)
        have hgq : Continuous gq := continuous_const.prodMk continuous_id
        have hcont_m : Continuous (fun a : ℝ≥0 => bellmanQ c hm2 P α (bellmanV c hm2 P α m) (boxToFull x) a) :=
          (continuous_bellmanQ hc (bellmanV_VInv hc hα0 hα1 m)).comp hgq
        have htend_m : Tendsto (fun k => bellmanQ c hm2 P α (bellmanV c hm2 P α m) (boxToFull x) (as (φ k)))
            atTop (𝓝 (bellmanQ c hm2 P α (bellmanV c hm2 P α m) (boxToFull x) astar)) :=
          hcont_m.continuousAt.tendsto.comp hφ_tend
        refine le_of_tendsto htend_m ?_
        filter_upwards [Filter.eventually_ge_atTop m] with k hk
        have hm_le : m ≤ φ k := le_trans hk (hφ_mono.id_le k)
        have hmono_k : bellmanQ c hm2 P α (bellmanV c hm2 P α m) (boxToFull x) (as (φ k)) ≤
            bellmanQ c hm2 P α (bellmanV c hm2 P α (φ k)) (boxToFull x) (as (φ k)) := by
          unfold bellmanQ
          have hint : ∫ d : ℝ≥0, bellmanV c hm2 P α m (stepFull hm2 (boxToFull x) (as (φ k)) d) ∂P.law ≤
              ∫ d : ℝ≥0, bellmanV c hm2 P α (φ k) (stepFull hm2 (boxToFull x) (as (φ k)) d) ∂P.law :=
            integral_mono (integrable_v_stepFull (bellmanV_VInv hc hα0 hα1 m) _ _)
              (integrable_v_stepFull (bellmanV_VInv hc hα0 hα1 (φ k)) _ _) fun d =>
                (monotone_nat_of_le_succ fun r => bellmanV_mono hc hα0 hα1 r _) hm_le
          nlinarith
        rw [← has_eq (φ k)] at hmono_k
        exact le_trans hmono_k (le_ciSup (hBddAbove x) (φ k + 1))
      have hsup : eta (modelBox c hc hm2 P) (fun y => ENNReal.ofReal (Vlim y)) α x astar ≤
          ENNReal.ofReal (Vlim x) := by
        have hmct : ∫⁻ y, ENNReal.ofReal (Vlim y) ∂((modelBox c hc hm2 P).toMDP.q (x, astar)) =
            ⨆ m : ℕ, ∫⁻ y, ENNReal.ofReal (bellmanV c hm2 P α m (boxToFull y))
              ∂((modelBox c hc hm2 P).toMDP.q (x, astar)) := by
          have hpt : (fun y => ENNReal.ofReal (Vlim y)) =
              fun y => ⨆ m : ℕ, ENNReal.ofReal (bellmanV c hm2 P α m (boxToFull y)) := by
            ext y
            exact tendsto_nhds_unique (hVlim_ofReal_tend y)
              (tendsto_atTop_iSup (monotone_nat_of_le_succ fun r =>
                ENNReal.ofReal_le_ofReal (bellmanV_mono hc hα0 hα1 r _)))
          rw [hpt, lintegral_iSup]
          · intro m
            exact ENNReal.measurable_ofReal.comp
              ((bellmanV_VInv (hm2 := hm2) (P := P) hc hα0 hα1 m).cont.measurable.comp
                measurable_subtype_coe.subtype_mk)
          · exact monotone_nat_of_le_succ fun r y =>
              ENNReal.ofReal_le_ofReal (bellmanV_mono hc hα0 hα1 r _)
        unfold eta
        rw [hmct, ENNReal.mul_iSup, ENNReal.add_iSup]
        exact iSup_le fun m => hge_m m
      exact le_trans (iInf_le_of_le astar (iInf_le _ hastar)) hsup
  -- Contraction uniqueness in ℝ≥0∞: vβ (modelBox) α = ENNReal.ofReal ∘ Vlim!
  have hthm2_box := FKZAvg.WStar.theorem_2 (modelBox c hc hm2 P) (hasSelector_box c hc hm2 P)
    (condWStar_box c hc hm2 P) α hα0 hα1
  have hbox_bell := hthm2_box.2.1.1
  let u : XBox c.m S_NP → ℝ≥0∞ := vβ (modelBox c hc hm2 P) α
  let w : XBox c.m S_NP → ℝ≥0∞ := fun x => ENNReal.ofReal (Vlim x)
  let D : ℝ≥0∞ := ⨆ x : XBox c.m S_NP, max (u x - w x) (w x - u x)
  have hD_ne_top : D ≠ ⊤ := by
    have hD_le : D ≤ ENNReal.ofReal (K / (1 - α)) := by
      refine iSup_le fun x => max_le ?_ ?_
      · exact le_trans tsub_le_self (vBox_le_const hc hα0 hα1 x)
      · exact le_trans tsub_le_self (ENNReal.ofReal_le_ofReal (hVlim_le_K x))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD_le
  have hstep_contr : ∀ (f₁ f₂ : XBox c.m S_NP → ℝ≥0∞),
      (∀ x, f₁ x = ⨅ a ∈ (modelBox c hc hm2 P).Aset x, eta (modelBox c hc hm2 P) f₁ α x a) →
      (∀ x, f₂ x = ⨅ a ∈ (modelBox c hc hm2 P).Aset x, eta (modelBox c hc hm2 P) f₂ α x a) →
      (∀ y, f₁ y ≤ f₂ y + D) → ∀ x, f₁ x - f₂ x ≤ ENNReal.ofReal α * D := by
    intro f₁ f₂ hf₁ hf₂ hle x
    refine tsub_le_iff_left.mpr ?_
    rw [hf₁ x, hf₂ x]
    have hadd : (⨅ a ∈ (modelBox c hc hm2 P).Aset x, eta (modelBox c hc hm2 P) f₂ α x a) +
        ENNReal.ofReal α * D =
        ⨅ a ∈ (modelBox c hc hm2 P).Aset x, (eta (modelBox c hc hm2 P) f₂ α x a + ENNReal.ofReal α * D) := by
      rw [ENNReal.iInf_add]
      exact iInf_congr fun a => ENNReal.iInf_add
    rw [hadd]
    refine le_iInf fun a => le_iInf fun ha => ?_
    refine le_trans (iInf_le_of_le a (iInf_le _ ha)) ?_
    unfold eta
    have hprob_q : IsProbabilityMeasure ((modelBox c hc hm2 P).toMDP.q (x, a)) := inferInstance
    have hint_le : ∫⁻ y, f₁ y ∂((modelBox c hc hm2 P).toMDP.q (x, a)) ≤
        (∫⁻ y, f₂ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))) + D := by
      calc ∫⁻ y, f₁ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))
          ≤ ∫⁻ y, (f₂ y + D) ∂((modelBox c hc hm2 P).toMDP.q (x, a)) := lintegral_mono hle
        _ = (∫⁻ y, f₂ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))) + ∫⁻ _, D ∂((modelBox c hc hm2 P).toMDP.q (x, a)) :=
            lintegral_add_right _ measurable_const
        _ = (∫⁻ y, f₂ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))) + D := by simp
    calc (modelBox c hc hm2 P).toMDP.cost x a + ENNReal.ofReal α * ∫⁻ y, f₁ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))
        ≤ (modelBox c hc hm2 P).toMDP.cost x a + ENNReal.ofReal α * ((∫⁻ y, f₂ y ∂((modelBox c hc hm2 P).toMDP.q (x, a))) + D) := by
          gcongr
      _ = (modelBox c hc hm2 P).toMDP.cost x a + ENNReal.ofReal α * ∫⁻ y, f₂ y ∂((modelBox c hc hm2 P).toMDP.q (x, a)) +
            ENNReal.ofReal α * D := by rw [mul_add, add_assoc]
  have hu_le_wD : ∀ y, u y ≤ w y + D := fun y => by
    have : u y - w y ≤ D := le_trans (le_max_left _ _) (le_iSup (fun z => max (u z - w z) (w z - u z)) y)
    exact tsub_le_iff_left.mp this
  have hw_le_uD : ∀ y, w y ≤ u y + D := fun y => by
    have : w y - u y ≤ D := le_trans (le_max_right _ _) (le_iSup (fun z => max (u z - w z) (w z - u z)) y)
    exact tsub_le_iff_left.mp this
  have hD_le : D ≤ ENNReal.ofReal α * D :=
    iSup_le fun x => max_le (hstep_contr u w hbox_bell hVlim_bell hu_le_wD x)
      (hstep_contr w u hVlim_bell hbox_bell hw_le_uD x)
  have hD_zero : D = 0 := by
    by_contra hne0
    have hD_pos : 0 < D := pos_iff_ne_zero.mpr hne0
    have hα_lt1 : ENNReal.ofReal α < 1 := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hα1
    have hlt : D * ENNReal.ofReal α < D * 1 := ENNReal.mul_lt_mul_right hne0 hD_ne_top hα_lt1
    rw [mul_comm, mul_one] at hlt
    exact not_lt_of_ge hD_le hlt
  have hu_eq_w : ∀ x : XBox c.m S_NP, vβ (modelBox c hc hm2 P) α x = ENNReal.ofReal (Vlim x) := by
    intro x
    have h1 : u x - w x = 0 := le_antisymm (by
      rw [← hD_zero]; exact le_trans (le_max_left _ _) (le_iSup (fun z => max (u z - w z) (w z - u z)) x)) zero_le
    have h2 : w x - u x = 0 := le_antisymm (by
      rw [← hD_zero]; exact le_trans (le_max_right _ _) (le_iSup (fun z => max (u z - w z) (w z - u z)) x)) zero_le
    exact le_antisymm (tsub_eq_zero_iff_le.mp h1) (tsub_eq_zero_iff_le.mp h2)
  refine ⟨fun x => by rw [hu_eq_w]; exact hVlim_le_vFull x, fun x => ?_, fun x => ?_⟩
  · rw [hu_eq_w, hu_eq_w]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hVlim_P x (x0Box c.m S_NP) 0 le_rfl (fun j => by simpa [x0Box, emptyState, PerishBaseStock.Lifetime.emptyState] using x.prop.1 j)
    linarith
  · rw [hu_eq_w, hu_eq_w, ← ENNReal.ofReal_add (hVlim_nonneg _) (mul_nonneg hc.θ_nonneg S_NP.coe_nonneg)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact hVlim_P (x0Box c.m S_NP) x (S_NP : ℝ) S_NP.coe_nonneg fun j => by
      simpa [x0Box, emptyState, PerishBaseStock.Lifetime.emptyState] using x.prop.2.2 j

lemma condBLow_box {c : Params} (hc : c.Standing) {hm2 : 2 ≤ c.m}
    (P : CappedBaseStock.DemandLaw) : CondBLow (modelBox c hc hm2 P) := by
  let S_NP := newsvendorLevel P.law c.h c.p
  let K := g0 c P S_NP + c.θ * (S_NP : ℝ)
  have hK0 : 0 ≤ K := add_nonneg (g0_nonneg c hc P S_NP) (mul_nonneg hc.θ_nonneg S_NP.coe_nonneg)
  constructor
  · -- GeneralAssumption: gStar (modelBox) < ⊤
    unfold GeneralAssumption gStar
    let φ : XBox c.m S_NP → ℝ≥0 := fun y => Real.toNNReal ((S_NP : ℝ) - topLevel y.val)
    have hφ : IsStationary (modelBox c hc hm2 P) φ := by
      refine ⟨measurable_real_toNNReal.comp
        (measurable_const.sub ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp
          measurable_subtype_coe)), fun y => ?_⟩
      have htop : topLevel y.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact y.prop.2.2 _
      have hord : orderUpTo y.val (φ y) = (S_NP : ℝ) := by
        unfold φ orderUpTo PerishBaseStock.Lifetime.orderUpTo
        change topLevel y.val + (Real.toNNReal ((S_NP : ℝ) - topLevel y.val) : ℝ) = (S_NP : ℝ)
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]; ring
      show (floorLevel c P : ℝ) ≤ orderUpTo y.val (φ y) ∧ orderUpTo y.val (φ y) ≤ (S_NP : ℝ)
      rw [hord]
      exact ⟨NNReal.coe_le_coe.mpr (floorLevel_props c hc P).2, le_rfl⟩
    have hstat_adm : Admissible (modelBox c hc hm2 P) (statPolicy hφ) := by
      intro t h; simp [statPolicy, Policy.ofStationary, Kernel.deterministic_apply, hφ.2]
    refine lt_of_le_of_lt (iInf_le_of_le (x0Box c.m S_NP) (iInf_le _ ⟨statPolicy hφ, hstat_adm⟩)) ?_
    have hφ_cost : ∀ y : XBox c.m S_NP, (modelBox c hc hm2 P).toMDP.cost y (φ y) ≤ ENNReal.ofReal K := by
      intro y
      refine ENNReal.ofReal_le_ofReal ?_
      have htop : topLevel y.val ≤ (S_NP : ℝ) := by rw [topLevel_eq_last hm2]; exact y.prop.2.2 _
      have hord : orderUpTo y.val (φ y) = (S_NP : ℝ) := by
        unfold φ orderUpTo PerishBaseStock.Lifetime.orderUpTo
        change topLevel y.val + (Real.toNNReal ((S_NP : ℝ) - topLevel y.val) : ℝ) = (S_NP : ℝ)
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr htop)]; ring
      unfold stageCost; rw [hord, firstLevel_eq_zero hm2]
      have hout : ∫ d : ℝ≥0, max (y.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law ≤ (S_NP : ℝ) := by
        calc ∫ d : ℝ≥0, max (y.val ⟨0, by omega⟩ - (d : ℝ)) 0 ∂P.law
            ≤ ∫ _ : ℝ≥0, (S_NP : ℝ) ∂P.law :=
              integral_mono (integrable_max_sub P _) (integrable_const _) fun d =>
                max_le (by linarith [d.coe_nonneg, y.prop.2.2 ⟨0, by omega⟩]) S_NP.coe_nonneg
          _ = (S_NP : ℝ) := by simp [measureReal_def]
      nlinarith [hc.θ_nonneg]
    have hprob : IsProbabilityMeasure (pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) (x0Box c.m S_NP)) := by
      unfold pathMeasure
      have : IsProbabilityMeasure (initMeasure (statPolicy hφ) (x0Box c.m S_NP)) := by
        unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)
      infer_instance
    have hae_all : ∀ᵐ ω ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) (x0Box c.m S_NP)),
        ∀ t : ℕ, (ω t).2 = φ (ω t).1 :=
      ae_all_iff.mpr fun t => ae_action_eq_statPolicy (modelBox c hc hm2 P) hφ (x0Box c.m S_NP) t
    have hPhi_le : Phi (modelBox c hc hm2 P) (statPolicy hφ) (x0Box c.m S_NP) ≤ ENNReal.ofReal K := by
      unfold Phi avgCost
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      unfold vN
      have hvN : ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal ((1 : ℝ) ^ t) *
            (modelBox c hc hm2 P).toMDP.cost (ω t).1 (ω t).2
          ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) (x0Box c.m S_NP)) ≤
          (N : ℝ≥0∞) * ENNReal.ofReal K := by
        calc _ ≤ ∫⁻ _, ∑ _t ∈ Finset.range N, ENNReal.ofReal K
              ∂(pathMeasure (modelBox c hc hm2 P).toMDP (statPolicy hφ) (x0Box c.m S_NP)) := by
                refine lintegral_mono_ae (hae_all.mono fun ω hω => Finset.sum_le_sum fun t _ => ?_)
                rw [hω t, one_pow, ENNReal.ofReal_one, one_mul]
                exact hφ_cost _
          _ = (N : ℝ≥0∞) * ENNReal.ofReal K := by simp
      calc (N : ℝ≥0∞)⁻¹ * _
          ≤ (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * ENNReal.ofReal K) := by gcongr
        _ = ENNReal.ofReal K := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top N), one_mul]
    exact lt_of_le_of_lt hPhi_le ENNReal.ofReal_lt_top
  · -- ∀ x, liminf_{α ↑ 1} wβ (modelBox) α x < ⊤
    intro x
    have hw_le : ∀ᶠ α : ℝ in 𝓝[<] 1, wβ (modelBox c hc hm2 P) α x ≤ ENNReal.ofReal (c.θ * (S_NP : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
      have hprops := vBox_eq_Vlim_and_le_vFull (c := c) hc (hm2 := hm2) (P := P) (le_of_lt hα.1) hα.2
      have hm_eq : mβ (modelBox c hc hm2 P) α = vβ (modelBox c hc hm2 P) α (x0Box c.m S_NP) := by
        unfold mβ
        exact le_antisymm (iInf_le _ _) (le_iInf fun y => hprops.2.1 y)
      unfold wβ
      rw [hm_eq]
      exact tsub_le_iff_left.mpr (hprops.2.2 x)
    have hlim_le : liminf (fun α : ℝ => wβ (modelBox c hc hm2 P) α x) (𝓝[<] 1) ≤
        ENNReal.ofReal (c.θ * (S_NP : ℝ)) :=
      liminf_le_of_frequently_le' hw_le.frequently
    exact lt_of_le_of_lt hlim_le ENNReal.ofReal_lt_top

end BellmanIteration

/-! ### Section 5: Bridge between `policyCost` (on `DemandPath`) and `Phi` (on `pathMeasure`) -/

section Bridge

lemma demandPath_split_indep (P : CappedBaseStock.DemandLaw) (t : ℕ) :
    IndepFun (fun d : CappedBaseStock.DemandPath => (Finset.range t).restrict d)
      (fun d : CappedBaseStock.DemandPath => d t) (CappedBaseStock.demandPathLaw P) := by
  have hind : iIndepFun (fun i (d : CappedBaseStock.DemandPath) => d i)
      (CappedBaseStock.demandPathLaw P) := by
    unfold CappedBaseStock.demandPathLaw
    exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => x) (fun _ => measurable_id)
  have hdisj : Disjoint (Finset.range t) {t} := by simp
  have hfin := hind.indepFun_finset (Finset.range t) {t} hdisj (fun i => measurable_pi_apply i)
  have hcomp : IndepFun (id ∘ fun d : CappedBaseStock.DemandPath => (Finset.range t).restrict d)
      ((fun f : ({t} : Finset ℕ) → ℝ≥0 => f ⟨t, Finset.mem_singleton_self t⟩) ∘
        fun d : CappedBaseStock.DemandPath => ({t} : Finset ℕ).restrict d)
      (CappedBaseStock.demandPathLaw P) :=
    hfin.comp measurable_id (measurable_pi_apply _)
  exact hcomp

/-- Generic bridge: for any state-space subtype `X` with transition `stepX`, Markov kernel
`q (x, a) = P.law.map (stepX x a)`, expected one-step cost `ENNReal.ofReal (stageCost c P x.val a)`,
and a target policy `π` whose trajectory stays in `X` (matching `stepX`), `policyCost c P π = Phi M π_MDP x₀`. -/
lemma policyCost_eq_Phi_of_markov
    {c : Params} (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    {X : Type*} [MeasurableSpace X]
    (toState : X → State c.m) (htoState : Measurable toState)
    (stepX : X → ℝ≥0 → ℝ≥0 → X) (hstepX_meas : Measurable (fun z : (X × ℝ≥0) × ℝ≥0 => stepX z.1.1 z.1.2 z.2))
    (M : Model X ℝ≥0)
    (hq_eq : ∀ p : X × ℝ≥0, M.toMDP.q p = P.law.map (fun d : ℝ≥0 => stepX p.1 p.2 d))
    (hcost_eq : ∀ x a, M.toMDP.cost x a = ENNReal.ofReal (stageCost c P (toState x) a))
    (x₀ : X) (hx₀ : toState x₀ = emptyState c.m)
    (π : InvPolicy c.m)
    (f : ℕ → X → ℝ≥0) (hf_meas : ∀ t, Measurable (f t))
    (hf_eq : ∀ t x, f t x = π.φ t (toState x))
    (hstep_compat : ∀ t (x : X) (d : ℝ≥0),
      toState (stepX x (f t x) d) = step (toState x) (π.φ t (toState x)) d) :
    let πMDP : FeinbergLiang.ACOE.Policy X ℝ≥0 :=
      { rule := fun t => Kernel.deterministic (fun h => f t h.2) ((hf_meas t).comp measurable_snd) }
    policyCost c P π = Phi M πMDP x₀ := by
  intro πMDP
  -- Define trajectory in X from x₀
  let runX : CappedBaseStock.DemandPath → ℕ → X := fun d t =>
    Nat.rec x₀ (fun k x => stepX x (f k x) (d k)) t
  have hrunX_compat : ∀ d t, toState (runX d t) = run π d t := by
    intro d t
    induction t with
    | zero => exact hx₀
    | succ t ih =>
      show toState (stepX (runX d t) (f t (runX d t)) (d t)) =
        step (run π d t) (π.φ t (run π d t)) (d t)
      rw [hstep_compat, ih]
  -- runX d t is a measurable function of (Finset.range t).restrict d
  have hrunX_factor : ∀ t : ℕ, ∃ g : ((Finset.range t) → ℝ≥0) → X, Measurable g ∧
      ∀ d : CappedBaseStock.DemandPath, runX d t = g ((Finset.range t).restrict d) := by
    intro t
    induction t with
    | zero => exact ⟨fun _ => x₀, measurable_const, fun _ => rfl⟩
    | succ t ih =>
      rcases ih with ⟨g, hg_meas, hg_eq⟩
      let restrictPrev : ((Finset.range (t + 1)) → ℝ≥0) → ((Finset.range t) → ℝ≥0) :=
        fun u i => u ⟨i.val, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp i.prop))⟩
      have hprev_meas : Measurable restrictPrev :=
        measurable_pi_lambda _ fun i => measurable_pi_apply _
      refine ⟨fun u => stepX (g (restrictPrev u)) (f t (g (restrictPrev u)))
        (u ⟨t, Finset.mem_range.mpr (Nat.lt_succ_self t)⟩), ?_, ?_⟩
      · exact hstepX_meas.comp
          ((((hg_meas.comp hprev_meas).prodMk ((hf_meas t).comp (hg_meas.comp hprev_meas))).prodMk
            (measurable_pi_apply _)))
      · intro d
        show stepX (runX d t) (f t (runX d t)) (d t) = _
        rw [hg_eq d]; rfl
  have hrunX_meas : ∀ t, Measurable (fun d : CappedBaseStock.DemandPath => runX d t) := by
    intro t
    rcases hrunX_factor t with ⟨g, hg_meas, hg_eq⟩
    have : (fun d => runX d t) = g ∘ (Finset.range t).restrict := funext hg_eq
    rw [this]
    exact hg_meas.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
  -- Marginal law equality by induction on t
  have hmarg : ∀ t : ℕ,
      (CappedBaseStock.demandPathLaw P).map (fun d => (runX d t, f t (runX d t))) =
        (pathMeasure M.toMDP πMDP x₀).map (fun ω => ω t) := by
    intro t
    induction t with
    | zero =>
      have hmap0 : (pathMeasure M.toMDP πMDP x₀).map (fun ω => ω 0) = initMeasure πMDP x₀ := by
        unfold pathMeasure Kernel.trajMeasure
        have h1 : (fun ω : ℕ → X × ℝ≥0 => ω 0) =
            (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × ℝ≥0)) ∘
              (Preorder.frestrictLe 0) := rfl
        rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_comp _ _ (by fun_prop),
          Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
          Measure.map_map (by fun_prop) (by fun_prop)]
        have hid : (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × ℝ≥0)) ∘
            (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X × ℝ≥0)).symm = id :=
          MeasurableEquiv.self_comp_symm _
        rw [hid, Measure.map_id]
      rw [hmap0]
      unfold initMeasure
      change (CappedBaseStock.demandPathLaw P).map (fun _ => (x₀, f 0 x₀)) =
        (Kernel.deterministic (fun h : (Fin 0 → X × ℝ≥0) × X => f 0 h.2)
          ((hf_meas 0).comp measurable_snd) (fun j => j.elim0, x₀)).map (fun a => (x₀, a))
      rw [Kernel.deterministic_apply]
      dsimp only
      have hmk : Measurable (fun a : ℝ≥0 => (x₀, a)) := measurable_const.prodMk measurable_id
      rw [Measure.map_dirac' hmk, Measure.map_const, measure_univ, one_smul]
    | succ t ih =>
      have hprob_init : IsProbabilityMeasure (initMeasure πMDP x₀) := by
        unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)
      have hpair := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ => X × ℝ≥0)
        (μ₀ := initMeasure πMDP x₀) (κ := stepKernel M.toMDP πMDP) (a := t)
      have hrhs_eq : (pathMeasure M.toMDP πMDP x₀).map (fun ω => ω (t + 1)) =
          (stepKernel M.toMDP πMDP t) ∘ₘ ((pathMeasure M.toMDP πMDP x₀).map (Preorder.frestrictLe t)) := by
        unfold pathMeasure
        rw [← Measure.snd_compProd, hpair, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
        rfl
      rw [hrhs_eq]
      -- Show independence of (runX d t, f t (runX d t)) and d t
      rcases hrunX_factor t with ⟨g, hg_meas, hg_eq⟩
      have hind_t : IndepFun (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t)))
          (fun d : CappedBaseStock.DemandPath => d t) (CappedBaseStock.demandPathLaw P) := by
        have hcomp : (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t))) =
            (fun u => (g u, f t (g u))) ∘ (Finset.range t).restrict := by
          ext d <;> simp [hg_eq d]
        rw [hcomp]
        exact (demandPath_split_indep P t).comp (hg_meas.prodMk ((hf_meas t).comp hg_meas)) measurable_id
      have hpair_meas_t : Measurable (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t))) :=
        (hrunX_meas t).prodMk ((hf_meas t).comp (hrunX_meas t))
      have hprod_t : (CappedBaseStock.demandPathLaw P).map
          (fun d => ((runX d t, f t (runX d t)), d t)) =
          ((CappedBaseStock.demandPathLaw P).map (fun d => (runX d t, f t (runX d t)))).prod P.law := by
        rw [hind_t.map_prod_eq_prod_map_map hpair_meas_t.aemeasurable
          (measurable_pi_apply t).aemeasurable]
        congr 1
        exact Measure.infinitePi_map_eval (fun _ : ℕ => P.law) t
      ext s hs
      let stepPair : (X × ℝ≥0) × ℝ≥0 → X × ℝ≥0 := fun z =>
        (stepX z.1.1 z.1.2 z.2, f (t + 1) (stepX z.1.1 z.1.2 z.2))
      have hstep_meas_pair : Measurable stepPair :=
        hstepX_meas.prodMk ((hf_meas (t + 1)).comp hstepX_meas)
      have hlhs : ((CappedBaseStock.demandPathLaw P).map
            (fun d => (runX d (t + 1), f (t + 1) (runX d (t + 1))))) s =
          ∫⁻ p, ∫⁻ d, s.indicator 1 (stepX p.1 p.2 d, f (t + 1) (stepX p.1 p.2 d)) ∂P.law
            ∂((CappedBaseStock.demandPathLaw P).map (fun d => (runX d t, f t (runX d t)))) := by
        have hcomp_run : (fun d : CappedBaseStock.DemandPath => (runX d (t + 1), f (t + 1) (runX d (t + 1)))) =
            stepPair ∘ (fun d => ((runX d t, f t (runX d t)), d t)) := rfl
        have hpd_meas : Measurable (fun d : CappedBaseStock.DemandPath => ((runX d t, f t (runX d t)), d t)) :=
          hpair_meas_t.prodMk (measurable_pi_apply t)
        rw [hcomp_run, ← Measure.map_map hstep_meas_pair hpd_meas,
          hprod_t, Measure.map_apply hstep_meas_pair hs]
        have hind_meas : Measurable (fun z : (X × ℝ≥0) × ℝ≥0 =>
            s.indicator (1 : X × ℝ≥0 → ℝ≥0∞) (stepPair z)) :=
          (measurable_const.indicator hs).comp hstep_meas_pair
        rw [← lintegral_indicator_one (hstep_meas_pair hs),
          show (fun z => (stepPair ⁻¹' s).indicator (1 : ((X × ℝ≥0) × ℝ≥0) → ℝ≥0∞) z) =
            fun z => s.indicator 1 (stepPair z) by
            ext z; by_cases hz : stepPair z ∈ s <;> simp [hz],
          lintegral_prod _ hind_meas.aemeasurable]
      rw [hlhs, ih, Measure.bind_apply hs (Kernel.aemeasurable _)]
      have hker_eval : ∀ h : Π _ : Finset.Iic t, X × ℝ≥0,
          stepKernel M.toMDP πMDP t h s =
            ∫⁻ d, s.indicator 1 (stepX (lastPair t h).1 (lastPair t h).2 d,
              f (t + 1) (stepX (lastPair t h).1 (lastPair t h).2 d)) ∂P.law := by
        intro h
        have hlast_meas : Measurable (lastPair (X := X) (A := ℝ≥0) t) := measurable_pi_apply _
        have h1 : IsMarkovKernel (M.toMDP.q.comap (lastPair (X := X) (A := ℝ≥0) t) hlast_meas) :=
          Kernel.IsMarkovKernel.comap _ _
        have h2 : IsMarkovKernel ((πMDP.rule (t + 1)).comap
            (fun p : (Π _ : Finset.Iic t, X × ℝ≥0) × X => (histFin t p.1, p.2))
            (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
          Kernel.IsMarkovKernel.comap _ _
        change ((M.toMDP.q.comap (lastPair (X := X) (A := ℝ≥0) t) hlast_meas) ⊗ₖ
          ((πMDP.rule (t + 1)).comap
            (fun p : (Π _ : Finset.Iic t, X × ℝ≥0) × X => (histFin t p.1, p.2))
            (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))) h s = _
        rw [Kernel.compProd_apply hs]
        have hq_comap : (M.toMDP.q.comap (lastPair (X := X) (A := ℝ≥0) t) hlast_meas) h =
            P.law.map (fun d : ℝ≥0 => stepX (lastPair t h).1 (lastPair t h).2 d) := by
          rw [Kernel.comap_apply, hq_eq]
        rw [hq_comap]
        have hms1 : Measurable (fun x' : X =>
            (πMDP.rule (t + 1)).comap
              (fun p : (Π _ : Finset.Iic t, X × ℝ≥0) × X => (histFin t p.1, p.2))
              (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)
              (h, x') (Prod.mk x' ⁻¹' s)) := by
          have : (fun x' : X => (πMDP.rule (t + 1)) (histFin t h, x') (Prod.mk x' ⁻¹' s)) =
              fun x' : X => s.indicator 1 (x', f (t + 1) x') := by
            ext x'
            change (Kernel.deterministic (fun q : (Fin (t + 1) → X × ℝ≥0) × X => f (t + 1) q.2)
              ((hf_meas (t + 1)).comp measurable_snd) (histFin t h, x')) (Prod.mk x' ⁻¹' s) = _
            have hs' : MeasurableSet (Prod.mk x' ⁻¹' s) := measurable_prodMk_left hs
            rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hs']
            by_cases hx' : (x', f (t + 1) x') ∈ s <;> simp [hx']
          exact this ▸ (measurable_const.indicator hs).comp (measurable_id.prodMk (hf_meas (t + 1)))
        let gd : ℝ≥0 → (X × ℝ≥0) × ℝ≥0 := fun d => (lastPair t h, d)
        have hgd : Measurable gd := measurable_const.prodMk measurable_id
        have hstep_d : Measurable (fun d : ℝ≥0 => stepX (lastPair t h).1 (lastPair t h).2 d) :=
          hstepX_meas.comp hgd
        rw [lintegral_map hms1 hstep_d]
        refine lintegral_congr fun d => ?_
        rw [Kernel.comap_apply]
        change (Kernel.deterministic (fun q : (Fin (t + 1) → X × ℝ≥0) × X => f (t + 1) q.2)
          ((hf_meas (t + 1)).comp measurable_snd)
          (histFin t h, stepX (lastPair t h).1 (lastPair t h).2 d))
          (Prod.mk (stepX (lastPair t h).1 (lastPair t h).2 d) ⁻¹' s) = _
        have hs' : MeasurableSet (Prod.mk (stepX (lastPair t h).1 (lastPair t h).2 d) ⁻¹' s) :=
          measurable_prodMk_left hs
        rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hs']
        by_cases hx' : (stepX (lastPair t h).1 (lastPair t h).2 d,
            f (t + 1) (stepX (lastPair t h).1 (lastPair t h).2 d)) ∈ s <;> simp [hx']
      simp_rw [hker_eval]
      have hlast_meas : Measurable (lastPair (X := X) (A := ℝ≥0) t) := measurable_pi_apply _
      have hlast_map : ((pathMeasure M.toMDP πMDP x₀).map (Preorder.frestrictLe t)).map (lastPair t) =
          (pathMeasure M.toMDP πMDP x₀).map (fun ω => ω t) := by
        rw [Measure.map_map hlast_meas (Preorder.measurable_frestrictLe t)]
        rfl
      have hmeas_inner : Measurable (fun p : X × ℝ≥0 =>
          ∫⁻ d, s.indicator 1 (stepX p.1 p.2 d, f (t + 1) (stepX p.1 p.2 d)) ∂P.law) :=
        Measurable.lintegral_prod_right' ((measurable_const.indicator hs).comp hstep_meas_pair)
      rw [← hlast_map, lintegral_map hmeas_inner hlast_meas]
  -- Per-period expected cost equality
  have hcost_t : ∀ t : ℕ,
      ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P =
        ∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2 ∂(pathMeasure M.toMDP πMDP x₀) := by
    intro t
    rcases hrunX_factor t with ⟨g, hg_meas, hg_eq⟩
    have hind_t : IndepFun (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t)))
        (fun d : CappedBaseStock.DemandPath => d t) (CappedBaseStock.demandPathLaw P) := by
      have hcomp : (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t))) =
          (fun u => (g u, f t (g u))) ∘ (Finset.range t).restrict := by
        ext d <;> simp [hg_eq d]
      rw [hcomp]
      exact (demandPath_split_indep P t).comp (hg_meas.prodMk ((hf_meas t).comp hg_meas)) measurable_id
    have hpair_meas_t : Measurable (fun d : CappedBaseStock.DemandPath => (runX d t, f t (runX d t))) :=
      (hrunX_meas t).prodMk ((hf_meas t).comp (hrunX_meas t))
    have hpd_meas : Measurable (fun d : CappedBaseStock.DemandPath => ((runX d t, f t (runX d t)), d t)) :=
      hpair_meas_t.prodMk (measurable_pi_apply t)
    have hprod_t : (CappedBaseStock.demandPathLaw P).map
        (fun d => ((runX d t, f t (runX d t)), d t)) =
        ((CappedBaseStock.demandPathLaw P).map (fun d => (runX d t, f t (runX d t)))).prod P.law := by
      rw [hind_t.map_prod_eq_prod_map_map hpair_meas_t.aemeasurable
        (measurable_pi_apply t).aemeasurable]
      congr 1
      exact Measure.infinitePi_map_eval (fun _ : ℕ => P.law) t
    let pc : (X × ℝ≥0) × ℝ≥0 → ℝ≥0∞ := fun z =>
      ENNReal.ofReal c.h * ENNReal.ofReal (max (orderUpTo (toState z.1.1) z.1.2 - (z.2 : ℝ)) 0) +
      ENNReal.ofReal c.p * ENNReal.ofReal (max ((z.2 : ℝ) - orderUpTo (toState z.1.1) z.1.2) 0) +
      ENNReal.ofReal c.θ * ENNReal.ofReal (outdate (toState z.1.1) z.1.2 z.2)
    have hpc_meas : Measurable pc := by
      have hord : Measurable (fun z : (X × ℝ≥0) × ℝ≥0 => orderUpTo (toState z.1.1) z.1.2) := by
        unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
        exact ((PerishBaseStock.Lifetime.measurable_topLevel c.m).comp
          (htoState.comp (measurable_fst.comp measurable_fst))).add
          (measurable_coe_nnreal_real.comp (measurable_snd.comp measurable_fst))
      have hout : Measurable (fun z : (X × ℝ≥0) × ℝ≥0 => outdate (toState z.1.1) z.1.2 z.2) := by
        unfold outdate PerishBaseStock.Lifetime.outdate PerishBaseStock.Lifetime.firstLevel
        split_ifs with h0
        · exact (((measurable_pi_apply _).comp (htoState.comp (measurable_fst.comp measurable_fst))).sub
            (measurable_coe_nnreal_real.comp measurable_snd)).max measurable_const
        · exact (hord.sub (measurable_coe_nnreal_real.comp measurable_snd)).max measurable_const
      exact ((measurable_const.mul (ENNReal.measurable_ofReal.comp
          ((hord.sub (measurable_coe_nnreal_real.comp measurable_snd)).max measurable_const))).add
        (measurable_const.mul (ENNReal.measurable_ofReal.comp
          (((measurable_coe_nnreal_real.comp measurable_snd).sub hord).max measurable_const)))).add
        (measurable_const.mul (ENNReal.measurable_ofReal.comp hout))
    have hpt : ∀ d : CappedBaseStock.DemandPath,
        periodCost c π d t = pc ((runX d t, f t (runX d t)), d t) := by
      intro d
      unfold periodCost totalLevel outdated orderQty
      simp only [pc]
      rw [← hrunX_compat d t, ← hf_eq t (runX d t)]
    simp_rw [hpt]
    rw [← lintegral_map hpc_meas hpd_meas, hprod_t, lintegral_prod _ hpc_meas.aemeasurable]
    have hinner : ∀ p : X × ℝ≥0, ∫⁻ d : ℝ≥0, pc (p, d) ∂P.law = M.toMDP.cost p.1 p.2 := fun p => by
      rw [hcost_eq p.1 p.2, ofReal_stageCost_eq_lintegral c hc P (toState p.1) p.2]
    simp_rw [hinner]
    rw [hmarg t, lintegral_map M.cost_meas (measurable_pi_apply t)]
  -- Conclude policyCost = Phi
  unfold policyCost longRunAverage Phi avgCost vN
  have hsum : ∀ N : ℕ,
      (∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal ((1 : ℝ) ^ t) * M.toMDP.cost (ω t).1 (ω t).2
        ∂(pathMeasure M.toMDP πMDP x₀)) =
      ∑ t ∈ Finset.range N, ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P := by
    intro N
    simp_rw [one_pow, ENNReal.ofReal_one, one_mul]
    have hcm : ∀ t : ℕ, Measurable (fun ω : ℕ → X × ℝ≥0 => M.toMDP.cost (ω t).1 (ω t).2) :=
      fun t => M.cost_meas.comp (measurable_pi_apply t)
    rw [lintegral_finsetSum _ fun t _ => hcm t]
    exact Finset.sum_congr rfl fun t _ => (hcost_t t).symm
  simp_rw [hsum]
  have hshift : (fun T : ℕ =>
      (∑ t ∈ Finset.range (T + 1), ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P) /
        ((T : ℝ≥0∞) + 1)) =
      fun T : ℕ => ((T + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ t ∈ Finset.range (T + 1), ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P := by
    ext T
    rw [div_eq_mul_inv, mul_comm, Nat.cast_add, Nat.cast_one]
  rw [hshift]
  exact limsup_nat_add (fun N : ℕ => (N : ℝ≥0∞)⁻¹ *
    ∑ t ∈ Finset.range N, ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P) 1

end Bridge

/-! ### Section 6: Final assembly for `2 ≤ c.m` -/

section Assembly

lemma lemma_6_m2 (c : Params) (hc : c.Standing) (hm2 : 2 ≤ c.m)
    (P : CappedBaseStock.DemandLaw) :
    ∃ π : InvPolicy c.m, policyCost c P π = OPT c P ∧
      ∀ (d : CappedBaseStock.DemandPath) (t : ℕ), (floorLevel c P : ℝ) ≤ totalLevel π d t := by
  classical
  let S_NP := newsvendorLevel P.law c.h c.p
  let Mbox := modelBox c hc hm2 P
  let Mfull := modelFull c hc hm2 P
  have hthm3 := FKZAvg.WStar.theorem_3 Mbox (hasSelector_box c hc hm2 P)
    (condWStar_box c hc hm2 P) (condBLow_box hc P)
  rcases hthm3.1 with ⟨φ, hφ, _, hEq10⟩
  -- Extend φ from XBox to all of State c.m
  let πStar : InvPolicy c.m := {
    φ := fun _ x =>
      if hx : x ∈ XBoxSet c.m S_NP then φ ⟨x, hx⟩
      else Real.toNNReal ((floorLevel c P : ℝ) - topLevel x)
    measurable_φ := fun _ => by
      have hmeas_set : MeasurableSet (XBoxSet c.m S_NP) := (isClosed_XBoxSet c.m S_NP).measurableSet
      have hmeas_else : Measurable (fun x : State c.m => Real.toNNReal ((floorLevel c P : ℝ) - topLevel x)) :=
        measurable_real_toNNReal.comp (measurable_const.sub (PerishBaseStock.Lifetime.measurable_topLevel c.m))
      -- Extend φ by 0 outside XBoxSet using measurable_of_restrict or dite
      let φext : State c.m → ℝ≥0 := fun x =>
        if hx : x ∈ XBoxSet c.m S_NP then φ ⟨x, hx⟩ else 0
      have hφext_meas : Measurable φext := by
        intro s hs
        have hpre : φext ⁻¹' s = (Subtype.val '' (φ ⁻¹' s)) ∪ ((XBoxSet c.m S_NP)ᶜ ∩ (fun _ => (0 : ℝ≥0)) ⁻¹' s) := by
          ext x
          by_cases hx : x ∈ XBoxSet c.m S_NP
          · simp only [Set.mem_preimage, φext, dif_pos hx, Set.mem_union, Set.mem_image,
              Set.mem_inter_iff, Set.mem_compl_iff]
            exact ⟨fun h => Or.inl ⟨⟨x, hx⟩, h, rfl⟩,
              fun h => h.elim (fun ⟨y, hy, hyx⟩ => by subst hyx; exact hy) (fun ⟨hnx, _⟩ => absurd hx hnx)⟩
          · simp only [Set.mem_preimage, φext, dif_neg hx, Set.mem_union, Set.mem_image,
              Set.mem_inter_iff, Set.mem_compl_iff]
            exact ⟨fun h => Or.inr ⟨hx, h⟩,
              fun h => h.elim (fun ⟨y, _, hyx⟩ => absurd (hyx ▸ y.prop) hx) And.right⟩
        rw [hpre]
        refine MeasurableSet.union ?_ (hmeas_set.compl.inter (measurable_const hs))
        exact (IsClosed.isClosedEmbedding_subtypeVal (isClosed_XBoxSet c.m S_NP)).measurableEmbedding.measurableSet_image.mpr
          (hφ.1 hs)
      have heq : (fun x => if hx : x ∈ XBoxSet c.m S_NP then φ ⟨x, hx⟩
          else Real.toNNReal ((floorLevel c P : ℝ) - topLevel x)) =
          fun x => if x ∈ XBoxSet c.m S_NP then φext x
            else Real.toNNReal ((floorLevel c P : ℝ) - topLevel x) := by
        ext x; by_cases hx : x ∈ XBoxSet c.m S_NP <;> simp [φext, hx]
      rw [heq]
      exact Measurable.ite hmeas_set hφext_meas hmeas_else
  }
  -- Floor property on every demand path d and every t
  have hfloor : ∀ (d : CappedBaseStock.DemandPath) (t : ℕ), (floorLevel c P : ℝ) ≤ totalLevel πStar d t := by
    intro d t
    unfold totalLevel orderQty
    change (floorLevel c P : ℝ) ≤ orderUpTo (run πStar d t) (πStar.φ t (run πStar d t))
    by_cases hx : run πStar d t ∈ XBoxSet c.m S_NP
    · have hφeq : πStar.φ t (run πStar d t) = φ ⟨run πStar d t, hx⟩ := by simp [πStar, hx]
      rw [hφeq]
      exact (hφ.2 ⟨run πStar d t, hx⟩).1
    · have hφeq : πStar.φ t (run πStar d t) = Real.toNNReal ((floorLevel c P : ℝ) - topLevel (run πStar d t)) := by
        simp [πStar, hx]
      rw [hφeq]
      unfold orderUpTo PerishBaseStock.Lifetime.orderUpTo
      change (floorLevel c P : ℝ) ≤ topLevel (run πStar d t) +
        (Real.toNNReal ((floorLevel c P : ℝ) - topLevel (run πStar d t)) : ℝ)
      linarith [Real.le_coe_toNNReal ((floorLevel c P : ℝ) - topLevel (run πStar d t))]
  -- Bridge for πStar on Mbox
  have hcost_star : policyCost c P πStar = Phi Mbox (statPolicy hφ) (x0Box c.m S_NP) := by
    have hbr := policyCost_eq_Phi_of_markov hc P
      (X := XBox c.m S_NP) Subtype.val measurable_subtype_coe
      (stepBox hm2 S_NP) (measurable_stepBox_triple hm2 S_NP)
      Mbox (kernelBox_apply c hm2 P S_NP) (fun _ _ => rfl)
      (x0Box c.m S_NP) rfl πStar
      (fun _ => φ) (fun _ => hφ.1)
      (fun _ x => by simp [πStar, x.prop])
      (fun _ x d => by
        have hord : orderUpTo x.val (φ x) ≤ (S_NP : ℝ) := (hφ.2 x).2
        have hstep := stepBox_eq_step hm2 S_NP x (φ x) d hord
        simp [πStar, x.prop, hstep])
    exact hbr
  refine ⟨πStar, ?_, hfloor⟩
  apply le_antisymm
  · refine le_iInf fun π => ?_
    -- Bridge for arbitrary π on Mfull
    let fFull : ℕ → XFull c.m → ℝ≥0 := fun t x => π.φ t x.val
    have hfFull_meas : ∀ t, Measurable (fFull t) := fun t =>
      (π.measurable_φ t).comp measurable_subtype_coe
    let πMDP : FeinbergLiang.ACOE.Policy (XFull c.m) ℝ≥0 :=
      { rule := fun t => Kernel.deterministic (fun h => fFull t h.2) ((hfFull_meas t).comp measurable_snd) }
    have hcost_π : policyCost c P π = Phi Mfull πMDP (x0Full c.m) :=
      policyCost_eq_Phi_of_markov hc P
        (X := XFull c.m) Subtype.val measurable_subtype_coe
        (stepFull hm2) (measurable_stepFull_triple hm2)
        Mfull (kernelFull_apply c hm2 P) (fun _ _ => rfl)
        (x0Full c.m) rfl π
        fFull hfFull_meas (fun _ _ => rfl) (fun _ _ _ => rfl)
    have hπ_adm : Admissible Mfull πMDP := fun _ _ => by simp [Mfull, modelFull]
    have htaub := (SchalAvg.AvgOpt.lemma_1_2 Mfull).1 πMDP hπ_adm (x0Full c.m)
    have hEq_x0 := (hEq10 (x0Box c.m S_NP)).2.1
    rw [hcost_star, hEq_x0, hcost_π]
    refine le_trans ?_ htaub
    refine limsup_le_limsup ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
    gcongr
    have hle_full := (vBox_eq_Vlim_and_le_vFull (c := c) hc (hm2 := hm2) (P := P)
      (le_of_lt hα.1) hα.2).1 (x0Box c.m S_NP)
    have hle_π : vβ Mfull α (x0Full c.m) ≤ Jbeta Mfull πMDP α (x0Full c.m) :=
      iInf_le (fun σ : {σ : FeinbergLiang.ACOE.Policy _ _ // Admissible Mfull σ} =>
        Jbeta Mfull σ.1 α (x0Full c.m)) ⟨πMDP, hπ_adm⟩
    exact le_trans hle_full hle_π
  · exact iInf_le _ πStar

end Assembly

end Lemma6Proof

/-- Lemma 6: with bounded demand there is an optimal admissible policy whose
order-up-to level is at least `S̲` in every period and on every demand path. -/
theorem solution (c : PerishBaseStock.Penalty.Params) (hc : c.Standing)
    (P : CappedBaseStock.DemandLaw)
    (hP : PerishBaseStock.Penalty.DemandBounded P) :
    ∃ π : PerishBaseStock.Lifetime.Policy c.m,
      PerishBaseStock.Penalty.policyCost c P π = PerishBaseStock.Penalty.OPT c P ∧
      ∀ (d : CappedBaseStock.DemandPath) (t : ℕ),
        (PerishBaseStock.Penalty.floorLevel c P : ℝ) ≤
          PerishBaseStock.Penalty.totalLevel π d t := by
  let _ := hP
  by_cases hm1 : c.m = 1
  · exact Lemma6Proof.lemma_6_m1 c hc hm1 P
  · have hm2 : 2 ≤ c.m := by have := hc.one_le_m; omega
    exact Lemma6Proof.lemma_6_m2 c hc hm2 P
