-- Prove2me | solution 1 for PerishBaseStock.Penalty.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:59:46.215576+00:00
-- url     : https://prove2.me/submissions/b3f99cd6-bbe7-4bc1-800d-35e29049af88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PerishBaseStock_Penalty_eq_25
import Theorems.Thm_PerishBaseStock_Penalty_eq_26
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyThm3Aux
open PerishBaseStock.Penalty

variable (P : CappedBaseStock.DemandLaw)

/-- `s ↦ E[(D - s)^+]`. -/
def sf (s : ℝ) : ℝ := ∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law

/-- `s ↦ E[(s - D)^+]`. -/
def hf (s : ℝ) : ℝ := ∫ x : ℝ≥0, max (s - (x : ℝ)) 0 ∂P.law

lemma int_sf (s : ℝ) : Integrable (fun x : ℝ≥0 => max ((x : ℝ) - s) 0) P.law :=
  (P.finiteMean.sub (integrable_const s)).pos_part

lemma int_hf (s : ℝ) : Integrable (fun x : ℝ≥0 => max (s - (x : ℝ)) 0) P.law :=
  ((integrable_const s).sub P.finiteMean).pos_part

lemma sf_nonneg (s : ℝ) : 0 ≤ sf P s := integral_nonneg (fun _ => le_max_right _ _)

lemma hf_nonneg (s : ℝ) : 0 ≤ hf P s := integral_nonneg (fun _ => le_max_right _ _)

lemma sf_anti {s t : ℝ} (h : s ≤ t) : sf P t ≤ sf P s :=
  integral_mono (int_sf P t) (int_sf P s) (fun x => max_le_max (by linarith) le_rfl)

lemma holding_le (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (S : ℝ≥0) :
    ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂μ ≤ S := by
  have : ∫ x : ℝ≥0, max ((S : ℝ) - (x : ℝ)) 0 ∂μ ≤ ∫ _x : ℝ≥0, (S : ℝ) ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall (fun _ => le_max_right _ _))
      (integrable_const _) (Eventually.of_forall (fun x =>
        max_le (by have := NNReal.coe_nonneg x; linarith) (NNReal.coe_nonneg S)))
  simpa using this

lemma hf_ge (s : ℝ) : s - CappedBaseStock.mean P ≤ hf P s := by
  have hi : Integrable (fun x : ℝ≥0 => s - (x : ℝ)) P.law := (integrable_const s).sub P.finiteMean
  have h1 : ∫ x : ℝ≥0, (s - (x : ℝ)) ∂P.law ≤ hf P s :=
    integral_mono hi (int_hf P s) (fun x => le_max_left (s - (x : ℝ)) 0)
  rw [integral_sub (integrable_const s) P.finiteMean] at h1
  simpa [CappedBaseStock.mean] using h1

lemma hf_sub_le (s t : ℝ) : hf P s - hf P t ≤ |s - t| := by
  have h : ∫ x : ℝ≥0, (max (s - (x : ℝ)) 0 - max (t - (x : ℝ)) 0) ∂P.law ≤
      ∫ _x : ℝ≥0, |s - t| ∂P.law :=
    integral_mono ((int_hf P s).sub (int_hf P t)) (integrable_const _) (fun x => by
      have h1 := abs_max_sub_max_le_abs (s - (x : ℝ)) (t - x) 0
      have h2 : (s - (x : ℝ)) - (t - x) = s - t := by ring
      rw [h2] at h1
      exact (le_abs_self _).trans h1)
  rw [integral_sub (int_hf P s) (int_hf P t)] at h
  simpa [hf] using h

lemma sf_sub_le (s t : ℝ) : sf P s - sf P t ≤ |s - t| := by
  have h : ∫ x : ℝ≥0, (max ((x : ℝ) - s) 0 - max ((x : ℝ) - t) 0) ∂P.law ≤
      ∫ _x : ℝ≥0, |s - t| ∂P.law :=
    integral_mono ((int_sf P s).sub (int_sf P t)) (integrable_const _) (fun x => by
      have h1 := abs_max_sub_max_le_abs ((x : ℝ) - s) (x - t) 0
      have h2 : ((x : ℝ) - s) - (x - t) = -(s - t) := by ring
      rw [h2, abs_neg] at h1
      exact (le_abs_self _).trans h1)
  rw [integral_sub (int_sf P s) (int_sf P t)] at h
  simpa [sf] using h

lemma hf_cont : Continuous (hf P) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun s t => by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_sub_le_iff.2 ⟨hf_sub_le P s t, by
      have := hf_sub_le P t s; rwa [abs_sub_comm] at this⟩)).continuous

lemma sf_cont : Continuous (sf P) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun s t => by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_sub_le_iff.2 ⟨sf_sub_le P s t, by
      have := sf_sub_le P t s; rwa [abs_sub_comm] at this⟩)).continuous

/-- `E[(D - M)^+] ≥ E[(D - M')^+] + (M' - M) P(D > M')` for `M ≤ M'`. -/
lemma sf_gap {M : ℝ} {M' : ℝ≥0} (h : M ≤ M') :
    sf P M' + ((M' : ℝ) - M) * (P.law (Set.Ioi M')).toReal ≤ sf P M := by
  have hmeas : MeasurableSet (Set.Ioi M') := measurableSet_Ioi
  have hind : Integrable (Set.indicator (Set.Ioi M') (fun _ => (M' : ℝ) - M)) P.law :=
    (integrable_const _).indicator hmeas
  have key : ∫ x : ℝ≥0, (max ((x : ℝ) - M') 0 +
      Set.indicator (Set.Ioi M') (fun _ => (M' : ℝ) - M) x) ∂P.law ≤ sf P M := by
    apply integral_mono ((int_sf P M').add hind) (int_sf P M)
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
  rw [integral_add (int_sf P M') hind, integral_indicator_const _ hmeas] at key
  simpa [sf, smul_eq_mul, mul_comm, measureReal_def] using key

/-- Abstract minimizer bound: a minimizer of a function squeezed between
`p E[(D-S)^+]` and `K S + p E[(D-S)^+]` lies above `M`, once `p` is large. -/
lemma minimizer_gt (f : ℝ≥0 → ℝ) (p K : ℝ) (hp : 0 < p)
    (hlo : ∀ S : ℝ≥0, p * sf P S ≤ f S) (hhi : ∀ S : ℝ≥0, f S ≤ K * S + p * sf P S)
    {M : ℝ} {M' : ℝ≥0} (hMM : M < M')
    (hbig : K * M' < p * (((M' : ℝ) - M) * (P.law (Set.Ioi M')).toReal))
    (S : ℝ≥0) (hS : ∀ S', f S ≤ f S') : M < S := by
  by_contra hle
  push Not at hle
  have h1 := hlo S
  have h2 := mul_le_mul_of_nonneg_left (sf_anti P hle) hp.le
  have h3 := mul_le_mul_of_nonneg_left (sf_gap P hMM.le) hp.le
  have h4 := hhi M'
  have h5 := hS M'
  rw [mul_add] at h3
  linarith

lemma prob_Ioi_pos {a : ℝ≥0} (ha : (a : ℝ≥0∞) < upperSupport P) :
    0 < (P.law (Set.Ioi a)).toReal := by
  unfold upperSupport at ha
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 ha
  obtain ⟨hx1, hx2⟩ := lt_iSup_iff.1 hx
  have hax : a ≤ x := le_of_lt (by exact_mod_cast hx2)
  have hlt : P.law (Set.Iic a) < 1 :=
    lt_of_le_of_lt (measure_mono (Set.Iic_subset_Iic.2 hax)) hx1
  have hc : P.law (Set.Ioi a) = 1 - P.law (Set.Iic a) := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  apply ENNReal.toReal_pos
  · rw [hc]; exact (tsub_pos_iff_lt.2 hlt).ne'
  · exact measure_ne_top _ _

lemma floorCost_eq (c : Params) (S : ℝ≥0) :
    floorCost c P S = c.h * hf P S + c.p * sf P S + c.θ * S := rfl

lemma floor_exists (c : Params) (hh : 0 < c.h) (hθ : 0 ≤ c.θ) (hp : 0 < c.p) :
    ∃ S : ℝ≥0, ∀ S', floorCost c P S ≤ floorCost c P S' := by
  have hcont : Continuous (floorCost c P) := by
    have : floorCost c P = fun S : ℝ≥0 => c.h * hf P S + c.p * sf P S + c.θ * S := rfl
    rw [this]
    exact ((continuous_const.mul ((hf_cont P).comp NNReal.continuous_coe)).add
      (continuous_const.mul ((sf_cont P).comp NNReal.continuous_coe))).add
      (continuous_const.mul NNReal.continuous_coe)
  set R : ℝ≥0 := (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1).toNNReal with hR
  have hbig : ∀ S' : ℝ≥0, R < S' → floorCost c P 0 < floorCost c P S' := by
    intro S' hS'
    have h1 : (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1) < S' := by
      have h0 : ((R : ℝ)) < S' := hS'
      have h00 := Real.le_coe_toNNReal (CappedBaseStock.mean P + floorCost c P 0 / c.h + 1)
      rw [← hR] at h00
      linarith
    have h2 := hf_ge P S'
    have h3 := sf_nonneg P S'
    rw [floorCost_eq P c S']
    have h4 : floorCost c P 0 / c.h * c.h = floorCost c P 0 := div_mul_cancel₀ _ hh.ne'
    have h5 : c.h * ((S' : ℝ) - CappedBaseStock.mean P) ≤ c.h * hf P S' :=
      mul_le_mul_of_nonneg_left h2 hh.le
    have h6 : 0 ≤ c.p * sf P S' := mul_nonneg hp.le h3
    have h7 : 0 ≤ c.θ * (S' : ℝ) := mul_nonneg hθ (NNReal.coe_nonneg _)
    nlinarith
  obtain ⟨S0, hS0mem, hS0⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.2 (zero_le : (0:ℝ≥0) ≤ R)) hcont.continuousOn
  refine ⟨S0, fun S' => ?_⟩
  by_cases hle : S' ≤ R
  · exact isMinOn_iff.1 hS0 S' ⟨zero_le, hle⟩
  · push Not at hle
    have := isMinOn_iff.1 hS0 0 ⟨le_rfl, zero_le⟩
    linarith [hbig S' hle]

lemma floorLevel_ge (c : Params) (hc : c.Standing) {M : ℝ} {M' : ℝ≥0} (hMM : M < M')
    (hbig : (c.h + c.θ) * M' < c.p * (((M' : ℝ) - M) * (P.law (Set.Ioi M')).toReal)) :
    M ≤ floorLevel c P := by
  obtain ⟨S0, hS0⟩ := floor_exists P c hc.h_pos hc.θ_nonneg hc.p_pos
  have hlo : ∀ S : ℝ≥0, c.p * sf P S ≤ floorCost c P S := by
    intro S
    rw [floorCost_eq]
    have := mul_nonneg hc.h_pos.le (hf_nonneg P S)
    have := mul_nonneg hc.θ_nonneg (NNReal.coe_nonneg S)
    linarith
  have hhi : ∀ S : ℝ≥0, floorCost c P S ≤ (c.h + c.θ) * S + c.p * sf P S := by
    intro S
    rw [floorCost_eq]
    have := mul_le_mul_of_nonneg_left (holding_le P.law S) hc.h_pos.le
    have : c.h * hf P S ≤ c.h * S := this
    nlinarith
  have hall : ∀ S ∈ {S : ℝ≥0 | ∀ S', floorCost c P S ≤ floorCost c P S'}, M < S :=
    fun S hS => minimizer_gt P (floorCost c P) c.p (c.h + c.θ) hc.p_pos hlo hhi hMM hbig S hS
  by_cases hM : M ≤ 0
  · exact hM.trans (NNReal.coe_nonneg _)
  · push Not at hM
    have h1 : M.toNNReal ≤ floorLevel c P :=
      le_csInf ⟨S0, hS0⟩ (fun S hS => Real.toNNReal_le_iff_le_coe.2 (hall S hS).le)
    have h2 := NNReal.coe_le_coe.2 h1
    rwa [Real.coe_toNNReal _ hM.le] at h2

lemma leadTimeLaw_prob (τ : ℕ) :
    IsProbabilityMeasure (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P τ) := by
  unfold LostSalesOrderUpTo.Asymptotic.leadTimeLaw
  exact Measure.isProbabilityMeasure_map
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)).aemeasurable

lemma heuristic_gt (c : Params) (hc : c.Standing) {M : ℝ} {M' : ℝ≥0} (hMM : M < M')
    (hbig : (c.h + c.θ / c.m) * M' < c.p * (((M' : ℝ) - M) * (P.law (Set.Ioi M')).toReal))
    (S : ℝ≥0) (hS : IsHeuristicLevel c P S) : M < S := by
  have := leadTimeLaw_prob P (c.m - 1)
  have hθm : 0 ≤ c.θ / (c.m : ℝ) := div_nonneg hc.θ_nonneg (Nat.cast_nonneg _)
  have heq : ∀ S : ℝ≥0, heuristicCost c P S = c.h * hf P S + c.p * sf P S + c.θ / (c.m : ℝ) *
      LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S := fun _ => rfl
  have hlo : ∀ S : ℝ≥0, c.p * sf P S ≤ heuristicCost c P S := by
    intro S
    rw [heq]
    have := mul_nonneg hc.h_pos.le (hf_nonneg P S)
    have : 0 ≤ c.θ / (c.m : ℝ) * LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S :=
      mul_nonneg hθm (integral_nonneg (fun x : ℝ≥0 => le_max_right ((S : ℝ) - x) 0))
    linarith
  have hhi : ∀ S : ℝ≥0, heuristicCost c P S ≤ (c.h + c.θ / c.m) * S + c.p * sf P S := by
    intro S
    rw [heq]
    have h1 : c.h * hf P S ≤ c.h * S := mul_le_mul_of_nonneg_left (holding_le P.law S) hc.h_pos.le
    have h2 : c.θ / (c.m : ℝ) * LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S ≤ c.θ / (c.m : ℝ) * S :=
      mul_le_mul_of_nonneg_left (holding_le _ S) hθm
    nlinarith
  exact minimizer_gt P (heuristicCost c P) c.p (c.h + c.θ / c.m) hc.p_pos hlo hhi hMM hbig S hS

lemma sf_tendsto : Tendsto (sf P) atTop (𝓝 0) := by
  have : Tendsto (fun s : ℝ => ∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) atTop
      (𝓝 (∫ _x : ℝ≥0, (0 : ℝ) ∂P.law)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x : ℝ≥0 => (x : ℝ)) ?_ ?_
      P.finiteMean ?_
    · exact Eventually.of_forall (fun s => (int_sf P s).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop 0] with s hs
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (NNReal.coe_nonneg x))
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (x : ℝ)] with s hs
      rw [max_eq_right (by linarith)]
  show Tendsto (fun s : ℝ => ∫ x : ℝ≥0, max ((x : ℝ) - s) 0 ∂P.law) atTop (𝓝 0)
  simpa using this

lemma gap_bound {C O : ℝ≥0∞} {B : ℝ} (h1 : C ≤ O + ENNReal.ofReal B) (h2 : O ≤ C) :
    0 ≤ C.toReal - O.toReal ∧ C.toReal - O.toReal ≤ max B 0 := by
  rcases eq_or_ne O ⊤ with hO | hO
  · have hC : C = ⊤ := top_le_iff.1 (hO ▸ h2)
    simp [hO, hC]
  · have hne : O + ENNReal.ofReal B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hO, ENNReal.ofReal_ne_top⟩
    have hC : C ≠ ⊤ := ne_top_of_le_ne_top hne h1
    have h3 := ENNReal.toReal_mono hne h1
    rw [ENNReal.toReal_add hO ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal'] at h3
    have h4 := ENNReal.toReal_mono hC h2
    constructor <;> linarith

lemma max_sub_le (θ a e : ℝ) (hθ : 0 ≤ θ) (he : 0 ≤ e) (ha : 0 ≤ a) :
    max (θ * (a - e)) 0 ≤ θ * a :=
  max_le (by nlinarith) (mul_nonneg hθ ha)

end PerishPenaltyThm3Aux

open PerishBaseStock.Penalty PerishPenaltyThm3Aux in
theorem solution (c : Params) (hm : 1 ≤ c.m) (hh : 0 < c.h) (hθ : 0 ≤ c.θ)
    (P : CappedBaseStock.DemandLaw) (S : ℝ → ℝ≥0)
    (hS : ∀ p : ℝ, 0 < p → IsHeuristicLevel { c with p := p } P (S p)) :
    Tendsto (fun p : ℝ => (baseStockCost { c with p := p } P (S p)).toReal -
      (OPT { c with p := p } P).toReal) atTop (𝓝 0) := by
  have hst : ∀ p : ℝ, 0 < p → ({ c with p := p } : Params).Standing :=
    fun p hp => ⟨hm, hh, hp, hθ⟩
  have hOPT : ∀ p : ℝ, OPT { c with p := p } P ≤ baseStockCost { c with p := p } P (S p) :=
    fun p => iInf_le _ _
  have hK : 0 < c.h + c.θ := by linarith
  by_cases hP : DemandBounded P
  · -- bounded demand: inequality (26)
    set Db := (upperSupport P).toReal with hDb
    have hUS : upperSupport P = ENNReal.ofReal Db := (ENNReal.ofReal_toReal hP.ne).symm
    have hfl : ∀ δ > 0, ∀ᶠ p in atTop, Db - floorLevel { c with p := p } P ≤ δ := by
      intro δ hδ
      by_cases hsmall : Db ≤ δ
      · exact Eventually.of_forall (fun p => by
          have := NNReal.coe_nonneg (floorLevel { c with p := p } P); linarith)
      · push Not at hsmall
        set M' : ℝ≥0 := (Db - δ / 2).toNNReal with hM'
        have hM'v : (M' : ℝ) = Db - δ / 2 := Real.coe_toNNReal _ (by linarith)
        have hq : 0 < (P.law (Set.Ioi M')).toReal := by
          apply prob_Ioi_pos
          rw [hUS]
          show ENNReal.ofReal (Db - δ / 2) < ENNReal.ofReal Db
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        have hN0 : 0 ≤ (c.h + c.θ) * M' / (δ / 2 * (P.law (Set.Ioi M')).toReal) := by positivity
        filter_upwards [eventually_ge_atTop
          ((c.h + c.θ) * M' / (δ / 2 * (P.law (Set.Ioi M')).toReal) + 1)] with p hp
        have hp0 : 0 < p := by linarith
        have hbig : (({ c with p := p } : Params).h + ({ c with p := p } : Params).θ) * M' <
            ({ c with p := p } : Params).p *
              (((M' : ℝ) - (Db - δ)) * (P.law (Set.Ioi M')).toReal) := by
          show (c.h + c.θ) * M' < p * (((M' : ℝ) - (Db - δ)) * (P.law (Set.Ioi M')).toReal)
          have h1 : (c.h + c.θ) * M' / (δ / 2 * (P.law (Set.Ioi M')).toReal) < p := by linarith
          rw [div_lt_iff₀ (by positivity)] at h1
          have h2 : (M' : ℝ) - (Db - δ) = δ / 2 := by rw [hM'v]; ring
          rw [h2]
          linarith
        have := floorLevel_ge P { c with p := p } (hst p hp0) (M := Db - δ) (M' := M')
          (by rw [hM'v]; linarith) hbig
        linarith
    have hup : Tendsto (fun p : ℝ =>
        max ((c.h + c.θ) * (Db - floorLevel { c with p := p } P)) 0) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hfl (ε / (2 * (c.h + c.θ))) (by positivity)] with p hp
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
      have h1 : (c.h + c.θ) * (Db - floorLevel { c with p := p } P) ≤
          (c.h + c.θ) * (ε / (2 * (c.h + c.θ))) := mul_le_mul_of_nonneg_left hp hK.le
      have h2 : (c.h + c.θ) * (ε / (2 * (c.h + c.θ))) = ε / 2 := by
        field_simp
      exact max_lt (by linarith) hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [eventually_gt_atTop 0] with p hp
      exact (gap_bound (eq_26 _ (hst p hp) P hP (S p) (hS p hp)) (hOPT p)).1
    · filter_upwards [eventually_gt_atTop 0] with p hp
      exact (gap_bound (eq_26 _ (hst p hp) P hP (S p) (hS p hp)) (hOPT p)).2
  · -- unbounded demand: inequality (25)
    have hUS : upperSupport P = ⊤ := by
      simpa [DemandBounded, lt_top_iff_ne_top] using hP
    have hm' : (0 : ℝ) < c.m := by exact_mod_cast hm
    have hθm : 0 ≤ c.θ / (c.m : ℝ) := div_nonneg hθ hm'.le
    have hSt : Tendsto (fun p => (S p : ℝ)) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      have hb0 : 0 ≤ max b 0 := le_max_right b 0
      have hM'v : (((max b 0 + 1).toNNReal : ℝ≥0) : ℝ) = max b 0 + 1 :=
        Real.coe_toNNReal _ (by linarith)
      have hq : 0 < (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal :=
        prob_Ioi_pos P (by rw [hUS]; exact ENNReal.coe_lt_top)
      have hN0 : 0 ≤ (c.h + c.θ / c.m) * ((max b 0 + 1).toNNReal : ℝ) /
          (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal := by positivity
      filter_upwards [eventually_ge_atTop ((c.h + c.θ / c.m) * ((max b 0 + 1).toNNReal : ℝ) /
          (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal + 1)] with p hp
      have hp0 : 0 < p := by linarith
      have hbig : (({ c with p := p } : Params).h +
            ({ c with p := p } : Params).θ / (({ c with p := p } : Params).m : ℝ)) *
            ((max b 0 + 1).toNNReal : ℝ) <
          ({ c with p := p } : Params).p * ((((max b 0 + 1).toNNReal : ℝ) - max b 0) *
            (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal) := by
        show (c.h + c.θ / c.m) * ((max b 0 + 1).toNNReal : ℝ) <
          p * ((((max b 0 + 1).toNNReal : ℝ) - max b 0) *
            (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal)
        have h1 : (c.h + c.θ / c.m) * ((max b 0 + 1).toNNReal : ℝ) /
            (P.law (Set.Ioi (max b 0 + 1).toNNReal)).toReal < p := by linarith
        rw [div_lt_iff₀ hq] at h1
        have h2 : (((max b 0 + 1).toNNReal : ℝ) - max b 0) = 1 := by rw [hM'v]; ring
        rw [h2, one_mul]
        exact h1
      have := heuristic_gt P { c with p := p } (hst p hp0) (M := max b 0)
        (M' := (max b 0 + 1).toNNReal) (by rw [hM'v]; linarith) hbig (S p) (hS p hp0)
      exact (le_max_left b 0).trans this.le
    have hT : Tendsto (fun p => c.θ * sf P ((S p : ℝ) / c.m)) atTop (𝓝 0) := by
      have := ((sf_tendsto P).comp (hSt.atTop_div_const hm')).const_mul c.θ
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    · filter_upwards [eventually_gt_atTop 0] with p hp
      exact (gap_bound (eq_25 _ (hst p hp) P (S p) (hS p hp)) (hOPT p)).1
    · filter_upwards [eventually_gt_atTop 0] with p hp
      refine (gap_bound (eq_25 _ (hst p hp) P (S p) (hS p hp)) (hOPT p)).2.trans ?_
      exact max_sub_le _ _ _ hθ (integral_nonneg fun _ => le_max_right _ _) (sf_nonneg P _)

end
