-- Prove2me | solution 1 for ServiceParts.Shortfall.shortfall_exponential_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T02:42:01.262095+00:00
-- url     : https://prove2.me/submissions/84d8cc9f-fb29-46e2-b1b0-4d605245d20d

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Theorems.Thm_ServiceParts_Shortfall_stationary_shortfall_exists
import Theorems.Thm_ServiceParts_Shortfall_adjustment_coefficient_unique
import Theorems.Thm_GoldieRenewal_Implicit_theorem_2_3

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall.ExpTail

/-! Reduction of the Cramér–Lundberg tail to Goldie's implicit renewal theorem (Case 1),
applied on the product space `law(V) ⊗ law(D)` with `R = e^{V}` and `M = e^{D - c}`. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma walk_meas (M : ShortfallModel Ω P) (n : ℕ) : Measurable (M.walk n) := by
  have hD := M.demand_measurable
  show Measurable (fun ω => ∑ k ∈ Finset.Icc 1 n, (M.demand k ω - M.capacity))
  exact Finset.measurable_sum _ (fun k _ => (hD k).sub measurable_const)

lemma V_meas (M : ShortfallModel Ω P) : Measurable M.stationaryShortfall := by
  show Measurable (fun ω => (⨆ n : ℕ, ENNReal.ofReal (M.walk n ω)).toReal)
  exact (Measurable.iSup fun n => (walk_meas M n).ennreal_ofReal).ennreal_toReal

lemma V_nonneg (M : ShortfallModel Ω P) (ω : Ω) : 0 ≤ M.stationaryShortfall ω :=
  ENNReal.toReal_nonneg

noncomputable def lawV (M : ShortfallModel Ω P) : Measure ℝ := P.map M.stationaryShortfall

noncomputable def lawD (M : ShortfallModel Ω P) : Measure ℝ := P.map (M.demand 1)

noncomputable def QQ (M : ShortfallModel Ω P) : Measure (ℝ × ℝ) := (lawV M).prod (lawD M)

noncomputable def Rv (q : ℝ × ℝ) : ℝ := Real.exp q.1

noncomputable def Mv (c : ℝ) (q : ℝ × ℝ) : ℝ := Real.exp (q.2 - c)

instance lawV_prob (M : ShortfallModel Ω P) : IsProbabilityMeasure (lawV M) :=
  Measure.isProbabilityMeasure_map (V_meas M).aemeasurable

instance lawD_prob (M : ShortfallModel Ω P) : IsProbabilityMeasure (lawD M) :=
  Measure.isProbabilityMeasure_map (M.demand_measurable 1).aemeasurable

instance QQ_prob (M : ShortfallModel Ω P) : IsProbabilityMeasure (QQ M) := by
  unfold QQ; infer_instance

lemma QQ_fst (M : ShortfallModel Ω P) (s : Set ℝ) : QQ M (Prod.fst ⁻¹' s) = lawV M s := by
  rw [QQ, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

lemma MR_eq (c : ℝ) (q : ℝ × ℝ) : Mv c q * Rv q = Real.exp (q.1 + q.2 - c) := by
  unfold Mv Rv; rw [← Real.exp_add]; congr 1; ring

/-- Stationarity on the product space (from `stationary_shortfall_exists`, part 3). -/
lemma stat_prod (M : ShortfallModel Ω P) (v : ℝ) (hv : 0 ≤ v) :
    P {ω | v < M.stationaryShortfall ω} = QQ M {q | v < q.1 + q.2 - M.capacity} := by
  have hS : MeasurableSet {q : ℝ × ℝ | v < q.1 + q.2 - M.capacity} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [(stationary_shortfall_exists M).2.2 v, QQ, Measure.prod_apply hS, lawV,
    lintegral_map (measurable_measure_prodMk_left hS) (V_meas M)]
  congr 1; funext ω; unfold lawD; congr 1; ext d
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, lt_max_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_lt.2 hv)
  · exact Or.inl

lemma tailR (M : ShortfallModel Ω P) (v : ℝ) :
    (QQ M).real {q | Real.exp v < Rv q} = (P {ω | v < M.stationaryShortfall ω}).toReal := by
  have : {q : ℝ × ℝ | Real.exp v < Rv q} = Prod.fst ⁻¹' Set.Ioi v := by
    ext q; simp [Rv, Real.exp_lt_exp]
  rw [measureReal_def, this, QQ_fst, lawV, Measure.map_apply (V_meas M) measurableSet_Ioi]
  rfl

lemma tailMR (M : ShortfallModel Ω P) (v : ℝ) :
    (QQ M).real {q | Real.exp v < Mv M.capacity q * Rv q} =
      ((QQ M) {q | v < q.1 + q.2 - M.capacity}).toReal := by
  have : {q : ℝ × ℝ | Real.exp v < Mv M.capacity q * Rv q} =
      {q | v < q.1 + q.2 - M.capacity} := by
    ext q; simp only [Set.mem_ofPred_eq, MR_eq, Real.exp_lt_exp]
  rw [measureReal_def, this]

lemma tailDiff_zero (M : ShortfallModel Ω P) (α t : ℝ) (ht : 1 ≤ t) :
    GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α t = 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hv : 0 ≤ Real.log t := Real.log_nonneg ht
  unfold GoldieRenewal.Implicit.tailDiffPlus
  rw [← Real.exp_log ht0, tailR, tailMR, stat_prod M _ hv, sub_self, zero_mul]

lemma real_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : μ.real s ≤ 1 := measureReal_le_one

lemma antiR (M : ShortfallModel Ω P) : Antitone (fun t : ℝ => (QQ M).real {q | t < Rv q}) :=
  fun _ _ hab => measureReal_mono (fun _ hq => lt_of_le_of_lt hab hq)

lemma antiMR (M : ShortfallModel Ω P) :
    Antitone (fun t : ℝ => (QQ M).real {q | t < Mv M.capacity q * Rv q}) :=
  fun _ _ hab => measureReal_mono (fun _ hq => lt_of_le_of_lt hab hq)

lemma tailDiff_meas (M : ShortfallModel Ω P) (α : ℝ) :
    Measurable (GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α) := by
  unfold GoldieRenewal.Implicit.tailDiffPlus
  exact ((antiR M).measurable.sub (antiMR M).measurable).mul (measurable_id.pow_const _)

lemma tailCond (M : ShortfallModel Ω P) (α : ℝ) (hα : 0 < α) :
    GoldieRenewal.Implicit.TailCondPlus (QQ M) (Mv M.capacity) Rv α := by
  unfold GoldieRenewal.Implicit.TailCondPlus
  have hg0 : IntegrableOn (fun t : ℝ => t ^ (α - 1)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hg : IntegrableOn ((Set.Ioc (0:ℝ) 1).indicator (fun t : ℝ => t ^ (α - 1))) (Set.Ioi 0) :=
    (hg0.integrable_indicator measurableSet_Ioc).integrableOn
  refine hg.mono' (tailDiff_meas M α).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht
  rcases le_or_gt t 1 with h1 | h1
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) 1 from ⟨ht0, h1⟩)]
    unfold GoldieRenewal.Implicit.tailDiffPlus
    have hp : 0 ≤ t ^ (α - 1) := Real.rpow_nonneg ht0.le _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]
    have ha := real_le_one (QQ M) {q | t < Rv q}
    have hb := real_le_one (QQ M) {q | t < Mv M.capacity q * Rv q}
    have ha0 : 0 ≤ (QQ M).real {q | t < Rv q} := measureReal_nonneg
    have hb0 : 0 ≤ (QQ M).real {q | t < Mv M.capacity q * Rv q} := measureReal_nonneg
    have habs : |(QQ M).real {q | t < Rv q} - (QQ M).real {q | t < Mv M.capacity q * Rv q}| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    calc _ ≤ 1 * t ^ (α - 1) := mul_le_mul_of_nonneg_right habs hp
      _ = _ := one_mul _
  · rw [tailDiff_zero M α t h1.le, norm_zero]
    exact Set.indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) t

/-! Real inequalities. -/

lemma y_le_exp (y ε : ℝ) (hε : 0 < ε) : y ≤ Real.exp (ε * y) / ε := by
  rw [le_div_iff₀ hε]
  have := Real.add_one_le_exp (ε * y)
  nlinarith

lemma exp_max_le (y α ε : ℝ) (hε : 0 < ε) :
    Real.exp (α * y) * max y 0 ≤ Real.exp ((α + ε) * y) / ε := by
  have hE := Real.exp_pos (α * y)
  have hsplit : Real.exp ((α + ε) * y) = Real.exp (α * y) * Real.exp (ε * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rcases le_or_gt y 0 with hy | hy
  · rw [max_eq_right hy, mul_zero]; positivity
  · rw [max_eq_left hy.le, hsplit, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (y_le_exp y ε hε) hE.le

lemma abs_bound (y α ε c : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hc : 0 ≤ c) (hy : -c ≤ y) :
    |y * Real.exp (α * y)| ≤ c + Real.exp ((α + ε) * y) / ε := by
  have hE := Real.exp_pos (α * y)
  have hpos : 0 < Real.exp ((α + ε) * y) / ε := by positivity
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg (mul_nonneg hy0 hE.le)]
    have := exp_max_le y α ε hε
    rw [max_eq_left hy0, mul_comm] at this
    linarith
  · have hle : Real.exp (α * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [abs_of_neg (mul_neg_of_neg_of_pos hy0 hE)]
    nlinarith

lemma key_ineq (x α : ℝ) (hα : 0 < α) : (Real.exp (α * x) - 1) / α ≤ x * Real.exp (α * x) := by
  have h1 := Real.add_one_le_exp (-(α * x))
  have h2 : Real.exp (α * x) * Real.exp (-(α * x)) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (α * x)
  rw [div_le_iff₀ hα]
  nlinarith [mul_le_mul_of_nonneg_left h1 hE.le]

lemma key_ineq_strict (x α : ℝ) (hα : 0 < α) (hx : x ≠ 0) :
    (Real.exp (α * x) - 1) / α < x * Real.exp (α * x) := by
  have h1 := Real.add_one_lt_exp (show -(α * x) ≠ 0 by
    intro h; apply hx; nlinarith [mul_self_nonneg x, sq_nonneg α, h])
  have h2 : Real.exp (α * x) * Real.exp (-(α * x)) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (α * x)
  rw [div_lt_iff₀ hα]
  nlinarith [mul_lt_mul_of_pos_left h1 hE]

/-! Integrability on `P`. -/

lemma int_exp_shift (M : ShortfallModel Ω P) (δ : ℝ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (a : ℝ) (ha : a < δ) :
    Integrable (fun ω => Real.exp (a * (M.demand 1 ω - M.capacity))) P := by
  have := (hmgf a ha).const_mul (Real.exp (-(a * M.capacity)))
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only
  rw [← Real.exp_add]; congr 1; ring

lemma cap_pos (M : ShortfallModel Ω P) : 0 < M.capacity := by
  have h0 : 0 ≤ ∫ ω, M.demand 1 ω ∂P := integral_nonneg (fun ω => M.demand_nonneg 1 ω)
  linarith [M.mean_lt_capacity]

lemma int_xexp (M : ShortfallModel Ω P) (δ : ℝ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (α : ℝ) (hα : 0 < α) (hαδ : α < δ) :
    Integrable (fun ω => (M.demand 1 ω - M.capacity) *
      Real.exp (α * (M.demand 1 ω - M.capacity))) P := by
  set ε := (δ - α) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hb : Integrable (fun ω => M.capacity +
      Real.exp ((α + ε) * (M.demand 1 ω - M.capacity)) / ε) P :=
    (integrable_const _).add ((int_exp_shift M δ hmgf (α + ε) (by rw [hεdef]; linarith)).div_const ε)
  have hD := M.demand_measurable 1
  refine hb.mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bound _ α ε _ hα.le hε (cap_pos M).le (by linarith [M.demand_nonneg 1 ω])

/-! The law of `M = e^{D - c}`. -/

lemma map_Mv (M : ShortfallModel Ω P) :
    (QQ M).map (Mv M.capacity) = P.map (fun ω => Real.exp (M.demand 1 ω - M.capacity)) := by
  have hD := M.demand_measurable 1
  have hf : Measurable (fun y : ℝ => Real.exp (y - M.capacity)) := by fun_prop
  have : Mv M.capacity = (fun y : ℝ => Real.exp (y - M.capacity)) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map hf measurable_snd, QQ, Measure.map_snd_prod, measure_univ, one_smul,
    lawD, Measure.map_map hf hD]
  rfl

lemma cramer (M : ShortfallModel Ω P) (δ : ℝ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (hnonlattice : ¬ IsLattice (P.map (M.demand 1)))
    (α : ℝ) (hα : 0 < α) (hαδ : α < δ)
    (hroot : ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    GoldieRenewal.Implicit.CramerConditions α ((QQ M).map (Mv M.capacity)) := by
  have hD := M.demand_measurable 1
  have hh : Measurable (fun ω => Real.exp (M.demand 1 ω - M.capacity)) := by fun_prop
  have : IsProbabilityMeasure (P.map (fun ω => Real.exp (M.demand 1 ω - M.capacity))) :=
    Measure.isProbabilityMeasure_map hh.aemeasurable
  rw [map_Mv]
  refine ⟨measure_univ, hα, ?_, ?_, ?_⟩
  · have hm : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ α)) :=
      (measurable_abs.pow_const α).ennreal_ofReal
    rw [lintegral_map hm hh]
    have hfun : (fun ω => ENNReal.ofReal (|Real.exp (M.demand 1 ω - M.capacity)| ^ α)) =
        fun ω => ENNReal.ofReal (Real.exp (-α * (M.capacity - M.demand 1 ω))) := by
      funext ω
      rw [abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2; ring
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal, hroot, ENNReal.ofReal_one]
    · have := int_exp_shift M δ hmgf α hαδ
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only; congr 1; ring
    · exact Eventually.of_forall fun ω => (Real.exp_pos _).le
  · have hm : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ α * max (Real.log |x|) 0)) :=
      ((measurable_abs.pow_const α).mul
        ((Real.measurable_log.comp measurable_abs).max measurable_const)).ennreal_ofReal
    rw [lintegral_map hm hh]
    set ε := (δ - α) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hb := (int_exp_shift M δ hmgf (α + ε) (by rw [hεdef]; linarith)).div_const ε
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hb.lintegral_lt_top
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_mul, mul_comm _ α]
    exact exp_max_le _ α ε hε
  · intro hAr
    apply hnonlattice
    have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton (0:ℝ)).compl
    have h0 : (P.map (fun ω => Real.exp (M.demand 1 ω - M.capacity))) {x : ℝ | x ≠ 0}ᶜ = 0 := by
      rw [Measure.map_apply hh hs.compl]
      convert measure_empty (μ := P)
      ext ω
      simp [Real.exp_ne_zero]
    have h1 := (prob_compl_eq_zero_iff hs).1 h0
    have hrestr := Measure.restrict_eq_self_of_ae_mem
      (μ := P.map (fun ω => Real.exp (M.demand 1 ω - M.capacity))) (s := {x : ℝ | x ≠ 0})
      (mem_ae_iff.2 h0)
    rw [ProbabilityTheory.cond, h1, inv_one, one_smul, hrestr,
      Measure.map_map (by fun_prop : Measurable (fun x : ℝ => Real.log |x|)) hh] at hAr
    have hcomp : ((fun x : ℝ => Real.log |x|) ∘ fun ω => Real.exp (M.demand 1 ω - M.capacity)) =
        fun ω => M.demand 1 ω - M.capacity := by
      funext ω; simp [Real.log_exp]
    rw [hcomp] at hAr
    obtain ⟨l, hl, hnull⟩ := hAr
    refine ⟨M.capacity, l, hl, ?_⟩
    have hset : {x : ℝ | ∃ k : ℤ, x = M.capacity + k * l} =
        Set.range (fun k : ℤ => M.capacity + k * l) := by
      ext x; simp [eq_comm]
    rw [hset, Measure.map_apply hD (Set.countable_range _).measurableSet.compl]
    rw [Measure.map_apply (by fun_prop) (Set.countable_range _).measurableSet.compl] at hnull
    convert hnull using 2
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
    constructor
    · intro h ⟨k, hk⟩; exact h ⟨k, by linarith⟩
    · intro h ⟨k, hk⟩; exact h ⟨k, by linarith⟩

lemma indep (M : ShortfallModel Ω P) : IndepFun Rv (Mv M.capacity) (QQ M) := by
  have := indepFun_prod (μ := lawV M) (ν := lawD M) (X := Real.exp)
    (Y := fun y : ℝ => Real.exp (y - M.capacity)) Real.measurable_exp (by fun_prop)
  exact this

/-! Positivity of Goldie's constant `C₊`. -/

lemma cramerMean_pos (M : ShortfallModel Ω P) (δ : ℝ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (hexceed : 0 < P {ω | M.capacity < M.demand 1 ω})
    (α : ℝ) (hα : 0 < α) (hαδ : α < δ)
    (hroot : ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    0 < GoldieRenewal.Implicit.cramerMean α ((QQ M).map (Mv M.capacity)) := by
  have hD := M.demand_measurable 1
  have hh : Measurable (fun ω => Real.exp (M.demand 1 ω - M.capacity)) := by fun_prop
  rw [map_Mv]
  unfold GoldieRenewal.Implicit.cramerMean
  have hmf : Measurable (fun x : ℝ => |x| ^ α * Real.log |x|) :=
    (measurable_abs.pow_const α).mul (Real.measurable_log.comp measurable_abs)
  rw [integral_map hh.aemeasurable hmf.aestronglyMeasurable]
  have hfun : (fun ω => |Real.exp (M.demand 1 ω - M.capacity)| ^ α *
      Real.log |Real.exp (M.demand 1 ω - M.capacity)|) =
      fun ω => (M.demand 1 ω - M.capacity) * Real.exp (α * (M.demand 1 ω - M.capacity)) := by
    funext ω
    rw [abs_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_mul,
      mul_comm (M.demand 1 ω - M.capacity) α, mul_comm]
  rw [hfun]
  have i1 := int_exp_shift M δ hmgf α hαδ
  have i2 := int_xexp M δ hmgf α hα hαδ
  have e1 : ∫ ω, Real.exp (α * (M.demand 1 ω - M.capacity)) ∂P = 1 := by
    rw [← hroot]; congr 1; funext ω; congr 1; ring
  have i3 : Integrable (fun ω => (Real.exp (α * (M.demand 1 ω - M.capacity)) - 1) / α) P :=
    (i1.sub (integrable_const 1)).div_const α
  have hint : Integrable (fun ω => (M.demand 1 ω - M.capacity) *
      Real.exp (α * (M.demand 1 ω - M.capacity)) -
      (Real.exp (α * (M.demand 1 ω - M.capacity)) - 1) / α) P := i2.sub i3
  have hsplit : ∫ ω, (M.demand 1 ω - M.capacity) * Real.exp (α * (M.demand 1 ω - M.capacity)) ∂P =
      ∫ ω, ((M.demand 1 ω - M.capacity) * Real.exp (α * (M.demand 1 ω - M.capacity)) -
        (Real.exp (α * (M.demand 1 ω - M.capacity)) - 1) / α) ∂P := by
    rw [integral_sub i2 i3, integral_div, integral_sub i1 (integrable_const 1), e1]
    simp
  rw [hsplit, integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun ω => sub_nonneg.2 (key_ineq _ α hα)) hint]
  refine lt_of_lt_of_le hexceed (measure_mono fun ω hω => ?_)
  have hω' : M.capacity < M.demand 1 ω := hω
  rw [Function.mem_support]
  exact (sub_pos.2 (key_ineq_strict _ α hα (by linarith))).ne'

lemma neg_part_pos (M : ShortfallModel Ω P) :
    0 < QQ M {q : ℝ × ℝ | q.1 + q.2 - M.capacity < 0} := by
  by_contra hcon
  have h0 : QQ M {q : ℝ × ℝ | q.1 + q.2 - M.capacity < 0} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
  have hs : Measurable (fun q : ℝ × ℝ => q.1 + q.2 - M.capacity) := by fun_prop
  have hprob : IsProbabilityMeasure ((QQ M).map (fun q : ℝ × ℝ => q.1 + q.2 - M.capacity)) :=
    Measure.isProbabilityMeasure_map hs.aemeasurable
  have hlaw : lawV M = (QQ M).map (fun q : ℝ × ℝ => q.1 + q.2 - M.capacity) := by
    refine Measure.ext_of_Iic _ _ (fun a => ?_)
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
      prob_compl_eq_one_sub measurableSet_Ioi]
    congr 1
    rw [lawV, Measure.map_apply (V_meas M) measurableSet_Ioi, Measure.map_apply hs measurableSet_Ioi]
    rcases le_or_gt 0 a with ha | ha
    · exact stat_prod M a ha
    · have e1 : M.stationaryShortfall ⁻¹' Set.Ioi a = Set.univ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
        linarith [V_nonneg M ω]
      have e2 : QQ M ((fun q : ℝ × ℝ => q.1 + q.2 - M.capacity) ⁻¹' Set.Ioi a) = 1 := by
        have hm : MeasurableSet ((fun q : ℝ × ℝ => q.1 + q.2 - M.capacity) ⁻¹' Set.Ioi a) :=
          hs measurableSet_Ioi
        rw [← prob_compl_eq_zero_iff hm]
        refine measure_mono_null (fun q hq => ?_) h0
        have hq' : ¬ a < q.1 + q.2 - M.capacity := hq
        show q.1 + q.2 - M.capacity < 0
        linarith [not_lt.1 hq']
      rw [e1, measure_univ, e2]
  have hV := V_meas M
  have hD := M.demand_measurable 1
  have iL : Integrable (fun ω => Real.exp (-M.stationaryShortfall ω)) P :=
    Integrable.of_bound (Real.measurable_exp.comp hV.neg).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by linarith [V_nonneg M ω]))
  have iK : Integrable (fun ω => Real.exp (M.capacity - M.demand 1 ω)) P :=
    Integrable.of_bound (Real.measurable_exp.comp (measurable_const.sub hD)).aestronglyMeasurable
      (Real.exp M.capacity)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (by linarith [M.demand_nonneg 1 ω]))
  have L_eq : ∫ x, Real.exp (-x) ∂(lawV M) = ∫ ω, Real.exp (-M.stationaryShortfall ω) ∂P :=
    integral_map hV.aemeasurable (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).aestronglyMeasurable
  have K_eq : ∫ y, Real.exp (M.capacity - y) ∂(lawD M) =
      ∫ ω, Real.exp (M.capacity - M.demand 1 ω) ∂P :=
    integral_map hD.aemeasurable
      (by fun_prop : Continuous fun y : ℝ => Real.exp (M.capacity - y)).aestronglyMeasurable
  have Lpos : 0 < ∫ ω, Real.exp (-M.stationaryShortfall ω) ∂P := integral_exp_pos iL
  have Kgt : 1 < ∫ ω, Real.exp (M.capacity - M.demand 1 ω) ∂P := by
    have hlin : Integrable (fun ω => 1 + (M.capacity - M.demand 1 ω)) P :=
      (integrable_const 1).add ((integrable_const M.capacity).sub M.demand_integrable)
    have hle : ∫ ω, (1 + (M.capacity - M.demand 1 ω)) ∂P ≤
        ∫ ω, Real.exp (M.capacity - M.demand 1 ω) ∂P :=
      integral_mono hlin iK (fun ω => by
        have := Real.add_one_le_exp (M.capacity - M.demand 1 ω)
        simp only; linarith)
    have hone : Integrable (fun _ : Ω => (1:ℝ)) P := integrable_const _
    have hcst : Integrable (fun _ : Ω => M.capacity) P := integrable_const _
    have hsub' : Integrable (fun ω => M.capacity - M.demand 1 ω) P := hcst.sub M.demand_integrable
    rw [integral_add hone hsub', integral_sub hcst M.demand_integrable] at hle
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    linarith [M.mean_lt_capacity]
  have prod_eq : ∫ x, Real.exp (-x) ∂(lawV M) =
      (∫ x, Real.exp (-x) ∂(lawV M)) * ∫ y, Real.exp (M.capacity - y) ∂(lawD M) := by
    conv_lhs => rw [hlaw]
    rw [integral_map hs.aemeasurable
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).aestronglyMeasurable,
      ← integral_prod_mul (μ := lawV M) (ν := lawD M) (fun x => Real.exp (-x))
        (fun y => Real.exp (M.capacity - y))]
    unfold QQ
    congr 1; funext q
    rw [← Real.exp_add]; congr 1; ring
  rw [L_eq, K_eq] at prod_eq
  nlinarith [mul_lt_mul_of_pos_left Kgt Lpos]

lemma tail_val (M : ShortfallModel Ω P) (α t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α t =
      (QQ M).real {q | Mv M.capacity q * Rv q ≤ t} * t ^ (α - 1) := by
  unfold GoldieRenewal.Implicit.tailDiffPlus
  congr 1
  have hmeas : MeasurableSet {q : ℝ × ℝ | t < Mv M.capacity q * Rv q} :=
    measurableSet_lt measurable_const (by unfold Mv Rv; fun_prop)
  have h1 : (QQ M).real {q | t < Rv q} = 1 := by
    apply le_antisymm (real_le_one _ _)
    have e : M.stationaryShortfall ⁻¹' Set.Ici 0 = Set.univ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]; exact V_nonneg M ω
    calc (1:ℝ) = (QQ M).real (Prod.fst ⁻¹' Set.Ici 0) := by
          rw [measureReal_def, QQ_fst, lawV, Measure.map_apply (V_meas M) measurableSet_Ici, e,
            measure_univ, ENNReal.toReal_one]
      _ ≤ _ := measureReal_mono (fun q hq => by
          have hq' : (0:ℝ) ≤ q.1 := hq
          show t < Real.exp q.1
          exact lt_of_lt_of_le ht1 (Real.one_le_exp hq'))
  have h2 : (QQ M).real {q | Mv M.capacity q * Rv q ≤ t} =
      1 - (QQ M).real {q | t < Mv M.capacity q * Rv q} := by
    have : {q : ℝ × ℝ | Mv M.capacity q * Rv q ≤ t} = {q | t < Mv M.capacity q * Rv q}ᶜ := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [this, measureReal_compl hmeas, probReal_univ]
  rw [h1, h2]

lemma integral_tail_pos (M : ShortfallModel Ω P) (α : ℝ) (hα : 0 < α) :
    0 < ∫ t in Set.Ioi 0, GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α t := by
  have hneg := neg_part_pos M
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      0 < QQ M {q : ℝ × ℝ | q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1))} := by
    by_contra hall
    simp only [not_exists, not_lt] at hall
    have hU : QQ M (⋃ n : ℕ, {q : ℝ × ℝ | q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1))}) = 0 :=
      measure_iUnion_null (fun n => nonpos_iff_eq_zero.1 (hall n))
    have hsub : {q : ℝ × ℝ | q.1 + q.2 - M.capacity < 0} ⊆
        ⋃ n : ℕ, {q : ℝ × ℝ | q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1))} := by
      intro q hq
      have hq' : q.1 + q.2 - M.capacity < 0 := hq
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hq')
      exact Set.mem_iUnion.2 ⟨n, by
        show q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1)); linarith⟩
    exact absurd (measure_mono_null hsub hU) hneg.ne'
  set t0 := Real.exp (-(1 / ((n:ℝ) + 1))) with ht0def
  have ht0 : 0 < t0 := Real.exp_pos _
  have ht01 : t0 < 1 := Real.exp_lt_one_iff.2 (by
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith)
  have hEpos : 0 < (QQ M).real {q : ℝ × ℝ | q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1))} :=
    ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  have hnn : ∀ t ∈ Set.Ioi (0:ℝ),
      0 ≤ GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α t := by
    intro t ht
    have ht' : 0 < t := ht
    rcases le_or_gt 1 t with h1 | h1
    · rw [tailDiff_zero M α t h1]
    · rw [tail_val M α t ht' h1]
      exact mul_nonneg measureReal_nonneg (Real.rpow_nonneg ht'.le _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)) (tailCond M α hα)]
  have hsub : Set.Ioo t0 1 ⊆ Function.support
      (GoldieRenewal.Implicit.tailDiffPlus (QQ M) (Mv M.capacity) Rv α) ∩ Set.Ioi 0 := by
    intro t ht
    obtain ⟨hta, htb⟩ := ht
    have ht' : 0 < t := lt_trans ht0 hta
    refine ⟨?_, ht'⟩
    rw [Function.mem_support, tail_val M α t ht' htb]
    refine (mul_pos (lt_of_lt_of_le hEpos (measureReal_mono (fun q hq => ?_)))
      (Real.rpow_pos_of_pos ht' _)).ne'
    have hq' : q.1 + q.2 - M.capacity ≤ -(1 / ((n:ℝ) + 1)) := hq
    show Mv M.capacity q * Rv q ≤ t
    rw [MR_eq]
    exact le_trans (Real.exp_le_exp.2 hq') hta.le
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

end ServiceParts.Shortfall.ExpTail

open MeasureTheory ProbabilityTheory Filter Topology in
open scoped ENNReal in
open ServiceParts.Shortfall in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (δ : ℝ) (hδ : 0 < δ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (hexceed : 0 < P {ω | M.capacity < M.demand 1 ω})
    (hnonlattice : ¬ IsLattice (P.map (M.demand 1)))
    (hroot : ∃ α ∈ Set.Ioo 0 δ,
      ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    ∃ β α : ℝ, 0 < β ∧ 0 < α ∧
      Tendsto (fun v : ℝ =>
          (P {ω | v < M.stationaryShortfall ω}).toReal / (β * Real.exp (-α * v)))
        atTop (𝓝 1) ∧
      ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1 ∧
      ∀ α' : ℝ, 0 < α' →
        ∫ ω, Real.exp (-α' * (M.capacity - M.demand 1 ω)) ∂P = 1 → α' = α := by
  obtain ⟨α, ⟨hα, hαδ⟩, hroot1⟩ := hroot
  have hC := ExpTail.cramer M δ hmgf hnonlattice α hα hαδ hroot1
  have hMm : Measurable (ExpTail.Mv M.capacity) := by unfold ExpTail.Mv; fun_prop
  have hR : Measurable ExpTail.Rv := by unfold ExpTail.Rv; fun_prop
  have hG := ((GoldieRenewal.Implicit.theorem_2_3 (ExpTail.QQ M) (ExpTail.Mv M.capacity)
    ExpTail.Rv hMm hR α hC (ExpTail.indep M)).1
    (Eventually.of_forall fun q => (Real.exp_pos _).le)).1 (ExpTail.tailCond M α hα)
  set β := GoldieRenewal.Implicit.Cplus (ExpTail.QQ M) (ExpTail.Mv M.capacity) ExpTail.Rv α
    with hβdef
  have hβ : 0 < β := mul_pos
    (inv_pos.2 (ExpTail.cramerMean_pos M δ hmgf hexceed α hα hαδ hroot1))
    (ExpTail.integral_tail_pos M α hα)
  have hlim : Tendsto (fun v : ℝ => Real.exp (α * v) *
      (P {ω | v < M.stationaryShortfall ω}).toReal) atTop (𝓝 β) := by
    refine (hG.comp Real.tendsto_exp_atTop).congr (fun v => ?_)
    show Real.exp v ^ α * (ExpTail.QQ M).real {q | Real.exp v < ExpTail.Rv q} = _
    rw [ExpTail.tailR, ← Real.exp_mul, mul_comm v α]
  refine ⟨β, α, hβ, hα, ?_, hroot1,
    fun α' hα' h' => adjustment_coefficient_unique M α' α hα' hα h' hroot1⟩
  have h2 := hlim.div_const β
  rw [div_self hβ.ne'] at h2
  refine h2.congr (fun v => ?_)
  rw [show -α * v = -(α * v) by ring, Real.exp_neg]
  field_simp
