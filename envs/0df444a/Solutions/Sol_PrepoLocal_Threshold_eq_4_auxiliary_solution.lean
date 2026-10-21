-- Prove2me | solution 1 for PrepoLocal.Threshold.eq_4_auxiliary_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:45:48.574457+00:00
-- url     : https://prove2.me/submissions/1d4269ad-8616-4784-824c-185568de1e65

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

variable {Ω : Type*} [MeasurableSpace Ω]

lemma min_eq_sub_pos (a b : ℝ) : min a b = a - max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

/-- Pointwise form of the cost identity. -/
lemma cycleCost_eq (P : Params) (E : Env Ω) (x : ℝ) (ω : Ω) :
    cycleCost P E x ω = P.hold * E.T ω * x + P.al * E.D ω + (1 - P.al) * S P E x ω
      + (P.v - 1) * max (S P E x ω - x) 0 := by
  unfold cycleCost
  have h1 := min_eq_sub_pos (E.D ω) (min (E.Q ω) (bhat P E x ω / P.al))
  have h2 : min x (S P E x ω) = S P E x ω - max (S P E x ω - x) 0 := by
    rw [min_comm, min_eq_sub_pos]
  have h3 : S P E x ω = max (E.D ω - min (E.Q ω) (bhat P E x ω / P.al)) 0 := rfl
  rw [h1, h2, ← h3]; ring

/-- The auxiliary integrand. -/
noncomputable def gA (P : Params) (E : Env Ω) (x : ℝ) (ω : Ω) : ℝ :=
  P.hold * E.T ω * x + P.al * E.D ω + (1 - P.al) * max (E.D ω - E.Q ω) 0
    + (P.v - 1) * max (E.D ω - E.Q ω - x) 0

lemma integrable_posPart {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => max (f ω) 0) μ :=
  hf.sup (integrable_zero _ _ μ)

lemma Ca_eq_integral (μ : Measure Ω) (P : Params) (E : Env Ω) (hE : E.Standing μ) (x : ℝ) :
    Ca P μ E x = ∫ ω, gA P E x ω ∂μ := by
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have i1 : Integrable (fun ω => P.hold * E.T ω * x) μ := (hTi.const_mul P.hold).mul_const x
  have i2 : Integrable (fun ω => P.al * E.D ω) μ := hDi.const_mul _
  have i3 : Integrable (fun ω => (1 - P.al) * max (E.D ω - E.Q ω) 0) μ :=
    (integrable_posPart (hDi.sub hQi)).const_mul _
  have i4 : Integrable (fun ω => (P.v - 1) * max (E.D ω - E.Q ω - x) 0) μ :=
    (integrable_posPart ((hDi.sub hQi).sub (integrable_const x))).const_mul _
  unfold gA Ca
  have i12 : Integrable (fun ω => P.hold * E.T ω * x + P.al * E.D ω) μ := i1.add i2
  have i123 : Integrable (fun ω => P.hold * E.T ω * x + P.al * E.D ω
      + (1 - P.al) * max (E.D ω - E.Q ω) 0) μ := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_mul_const, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

lemma integrable_S (μ : Measure Ω) (P : Params) (E : Env Ω) (hE : E.Standing μ) (x : ℝ) :
    Integrable (S P E x) μ := by
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have hb : Integrable (bhat P E x) μ :=
    (((integrable_const P.b).add (hTi.const_mul P.gam)).add hRi).sub (integrable_const x)
  have hq : Integrable (fun ω => min (E.Q ω) (bhat P E x ω / P.al)) μ :=
    hQi.inf (hb.div_const P.al)
  exact integrable_posPart (hDi.sub hq)

lemma integrable_cycleCost (μ : Measure Ω) (P : Params) (E : Env Ω) (hE : E.Standing μ)
    (x : ℝ) : Integrable (cycleCost P E x) μ := by
  have hS := integrable_S μ P E hE x
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have : cycleCost P E x = fun ω => P.hold * E.T ω * x + P.al * E.D ω + (1 - P.al) * S P E x ω
      + (P.v - 1) * max (S P E x ω - x) 0 := funext (cycleCost_eq P E x)
  rw [this]
  exact ((((hTi.const_mul P.hold).mul_const x).add (hDi.const_mul _)).add (hS.const_mul _)).add
    ((integrable_posPart (hS.sub (integrable_const x))).const_mul _)

/-- Milestone: Ca ≤ C. -/
theorem Ca_le_C' (μ : Measure Ω) (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (x : ℝ) : Ca P μ E x ≤ C P μ E x := by
  rw [Ca_eq_integral μ P E hE x]
  have hCi := integrable_cycleCost μ P E hE x
  have hgi : Integrable (gA P E x) μ := by
    obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
    exact (((hTi.const_mul P.hold).mul_const x).add (hDi.const_mul _)).add
      ((integrable_posPart (hDi.sub hQi)).const_mul _) |>.add
      ((integrable_posPart ((hDi.sub hQi).sub (integrable_const x))).const_mul _)
  unfold C
  refine integral_mono hgi hCi (fun ω => ?_)
  obtain ⟨h0, h1, _, hv, _, _⟩ := hP
  rw [cycleCost_eq]
  unfold gA
  set q := min (E.Q ω) (bhat P E x ω / P.al)
  have hq : q ≤ E.Q ω := min_le_left _ _
  have hS : S P E x ω = max (E.D ω - q) 0 := rfl
  rw [hS]
  have e1 : max (E.D ω - E.Q ω) 0 ≤ max (E.D ω - q) 0 := max_le_max (by linarith) le_rfl
  have e2 : max (E.D ω - E.Q ω - x) 0 ≤ max (max (E.D ω - q) 0 - x) 0 :=
    max_le_max (by linarith [le_max_left (E.D ω - q) 0]) le_rfl
  nlinarith

theorem cost_identity' (μ : Measure Ω) (P : Params) (hP : P.Standing) (E : Env Ω)
    (hE : E.Standing μ) (x : ℝ) :
    C P μ E x = P.al * (∫ ω, E.D ω ∂μ) + P.hold * (∫ ω, E.T ω ∂μ) * x
      + (1 - P.al) * (∫ ω, S P E x ω ∂μ)
      + (P.v - 1) * (∫ ω, max (S P E x ω - x) 0 ∂μ) := by
  have hS := integrable_S μ P E hE x
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have i1 : Integrable (fun ω => P.hold * E.T ω * x) μ := (hTi.const_mul P.hold).mul_const x
  have i2 : Integrable (fun ω => P.al * E.D ω) μ := hDi.const_mul _
  have i3 : Integrable (fun ω => (1 - P.al) * S P E x ω) μ := hS.const_mul _
  have i4 : Integrable (fun ω => (P.v - 1) * max (S P E x ω - x) 0) μ :=
    (integrable_posPart (hS.sub (integrable_const x))).const_mul _
  have i12 : Integrable (fun ω => P.hold * E.T ω * x + P.al * E.D ω) μ := i1.add i2
  have i123 : Integrable (fun ω => P.hold * E.T ω * x + P.al * E.D ω
      + (1 - P.al) * S P E x ω) μ := i12.add i3
  unfold C
  simp_rw [cycleCost_eq]
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_mul_const, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

theorem eq_5' (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b)
    (x : ℝ) (hx0 : 0 ≤ x) (hxp : x ≤ max xplus 0) :
    (∀ᵐ ω ∂μ, min (E.D ω) (E.Q ω) ≤ bhat P E x ω / P.al) ∧
      (∀ᵐ ω ∂μ, S P E x ω = max (E.D ω - E.Q ω) 0) := by
  obtain ⟨ha0, ha1, _, hv, _, hg⟩ := hP
  have key : ∀ᵐ ω ∂μ, min (E.D ω) (E.Q ω) ≤ bhat P E x ω / P.al := by
    filter_upwards [hM, hT] with ω h1 h2
    rw [le_div_iff₀ ha0]
    unfold bhat
    have : P.gam * Tlo ≤ P.gam * E.T ω := mul_le_mul_of_nonneg_left h2 hg
    nlinarith
  refine ⟨key, ?_⟩
  filter_upwards [key] with ω h
  unfold S
  rcases le_total (E.Q ω) (bhat P E x ω / P.al) with h' | h'
  · rw [min_eq_left h']
  · rw [min_eq_right h']
    have hDQ : E.D ω ≤ E.Q ω ∨ E.Q ω ≤ E.D ω := le_total _ _
    rcases hDQ with h3 | h3
    · rw [min_eq_left h3] at h
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    · rw [min_eq_right h3] at h
      have : bhat P E x ω / P.al = E.Q ω := le_antisymm h' h
      rw [this]

theorem reduction' (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b) :
    ∀ x ∈ Set.Icc 0 (min (max xplus 0) P.b), C P μ E x = Ca P μ E x := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hxp : x ≤ max xplus 0 := hx.2.trans (min_le_left _ _)
  have h5 := (eq_5' μ P hP E hE xplus M Tlo hM hT hb x hx0 hxp).2
  rw [Ca_eq_integral μ P E hE x]
  unfold C
  refine integral_congr_ae ?_
  filter_upwards [h5] with ω h
  rw [cycleCost_eq, h]
  unfold gA
  congr 2
  rcases le_total (E.D ω - E.Q ω) 0 with h' | h'
  · rw [max_eq_right h', max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h']

/-- `h(x) = E[(D - Q - x)⁺]`. -/
lemma newsvendor_upper (μ : Measure Ω) (E : Env Ω) (hE : E.Standing μ) (a y : ℝ) (hay : a ≤ y) :
    (∫ ω, max (E.D ω - E.Q ω - a) 0 ∂μ) - (∫ ω, max (E.D ω - E.Q ω - y) 0 ∂μ)
      ≤ (y - a) * (μ {ω | a < E.D ω - E.Q ω}).toReal := by
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have ia : Integrable (fun ω => max (E.D ω - E.Q ω - a) 0) μ :=
    integrable_posPart ((hDi.sub hQi).sub (integrable_const a))
  have iy : Integrable (fun ω => max (E.D ω - E.Q ω - y) 0) μ :=
    integrable_posPart ((hDi.sub hQi).sub (integrable_const y))
  have hs : MeasurableSet {ω | a < E.D ω - E.Q ω} :=
    measurableSet_lt measurable_const (hDm.sub hQm)
  rw [← integral_sub ia iy]
  have hind : Integrable ({ω | a < E.D ω - E.Q ω}.indicator (fun _ => y - a)) μ :=
    (integrable_const (y - a)).indicator hs
  calc (∫ ω, (max (E.D ω - E.Q ω - a) 0 - max (E.D ω - E.Q ω - y) 0) ∂μ)
      ≤ ∫ ω, {ω | a < E.D ω - E.Q ω}.indicator (fun _ => y - a) ω ∂μ := by
        refine integral_mono (ia.sub iy) hind (fun ω => ?_)
        by_cases h : a < E.D ω - E.Q ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | a < E.D ω - E.Q ω} from h)]
          rw [max_eq_left (by linarith : (0:ℝ) ≤ E.D ω - E.Q ω - a)]
          have := le_max_left (E.D ω - E.Q ω - y) 0
          linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | a < E.D ω - E.Q ω} from h)]
          push Not at h
          rw [max_eq_right (by linarith : E.D ω - E.Q ω - a ≤ 0)]
          have := le_max_right (E.D ω - E.Q ω - y) 0
          linarith
    _ = (y - a) * (μ {ω | a < E.D ω - E.Q ω}).toReal := by
        rw [integral_indicator_const _ hs, smul_eq_mul, measureReal_def, mul_comm]

lemma newsvendor_lower (μ : Measure Ω) (E : Env Ω) (hE : E.Standing μ) (y z a : ℝ)
    (hyz : y < z) (hza : z < a) :
    (z - y) * (μ {ω | z < E.D ω - E.Q ω}).toReal ≤
    (∫ ω, max (E.D ω - E.Q ω - y) 0 ∂μ) - (∫ ω, max (E.D ω - E.Q ω - a) 0 ∂μ) := by
  obtain ⟨hprob, hDm, hQm, hRm, hTm, hDi, hQi, hRi, hTi, _, _⟩ := hE
  have ia : Integrable (fun ω => max (E.D ω - E.Q ω - a) 0) μ :=
    integrable_posPart ((hDi.sub hQi).sub (integrable_const a))
  have iy : Integrable (fun ω => max (E.D ω - E.Q ω - y) 0) μ :=
    integrable_posPart ((hDi.sub hQi).sub (integrable_const y))
  have hs : MeasurableSet {ω | z < E.D ω - E.Q ω} :=
    measurableSet_lt measurable_const (hDm.sub hQm)
  rw [← integral_sub iy ia]
  have hind : Integrable ({ω | z < E.D ω - E.Q ω}.indicator (fun _ => z - y)) μ :=
    (integrable_const (z - y)).indicator hs
  calc (z - y) * (μ {ω | z < E.D ω - E.Q ω}).toReal
      = ∫ ω, {ω | z < E.D ω - E.Q ω}.indicator (fun _ => z - y) ω ∂μ := by
        rw [integral_indicator_const _ hs, smul_eq_mul, measureReal_def, mul_comm]
    _ ≤ (∫ ω, (max (E.D ω - E.Q ω - y) 0 - max (E.D ω - E.Q ω - a) 0) ∂μ) := by
        refine integral_mono hind (iy.sub ia) (fun ω => ?_)
        by_cases h : z < E.D ω - E.Q ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | z < E.D ω - E.Q ω} from h)]
          rw [max_eq_left (by linarith : (0:ℝ) ≤ E.D ω - E.Q ω - y)]
          rcases le_total (E.D ω - E.Q ω - a) 0 with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | z < E.D ω - E.Q ω} from h)]
          push Not at h
          have h1 := le_max_right (E.D ω - E.Q ω - y) 0
          have h2 : max (E.D ω - E.Q ω - a) 0 = 0 := max_eq_right (by linarith)
          linarith

theorem eq_4' (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus) :
    IsMinOn (Ca P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) := by
  obtain ⟨ha0, ha1, hi, hv, hb0, hg⟩ := hP
  have hprob : IsProbabilityMeasure μ := hE.1
  set a := min (max xplus 0) P.b with ha_def
  set β := betaStar P μ E with hβ
  have hv1 : 0 < P.v - 1 := by linarith
  have hβeq : P.hold * (∫ ω, E.T ω ∂μ) = (P.v - 1) * β := by
    rw [hβ, betaStar]; field_simp
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hCa : ∀ t, Ca P μ E t = P.al * (∫ ω, E.D ω ∂μ)
      + (1 - P.al) * (∫ ω, max (E.D ω - E.Q ω) 0 ∂μ)
      + (P.v - 1) * (β * t + ∫ ω, max (E.D ω - E.Q ω - t) 0 ∂μ) := by
    intro t; unfold Ca; rw [hβeq]; ring
  rw [hCa, hCa]
  rcases le_or_gt a y with hay | hya
  · -- y ≥ a
    have h1 := newsvendor_upper μ E hE a y hay
    rcases eq_or_lt_of_le hay with heq | hlt
    · rw [heq]
    have haeq : a = max xplus 0 := by
      rw [ha_def]; apply min_eq_left
      by_contra hc; push Not at hc
      have : a = P.b := min_eq_right hc.le
      linarith [hy.2]
    have hP : (μ {ω | a < E.D ω - E.Q ω}).toReal ≤ β := by
      rcases hx with ⟨hx1, _⟩ | ⟨hx1, _⟩
      · refine le_trans ?_ hx1
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have : xplus ≤ a := haeq ▸ le_max_left _ _
        linarith
      · refine le_trans ?_ hx1
        have := ENNReal.toReal_mono ENNReal.one_ne_top
          (prob_le_one (μ := μ) (s := {ω | a < E.D ω - E.Q ω}))
        simpa using this
    have : (∫ ω, max (E.D ω - E.Q ω - a) 0 ∂μ) - (∫ ω, max (E.D ω - E.Q ω - y) 0 ∂μ)
        ≤ (y - a) * β := h1.trans (mul_le_mul_of_nonneg_left hP (by linarith))
    nlinarith
  · -- y < a
    have ha_pos : 0 < a := lt_of_le_of_lt hy.1 hya
    have hax : a ≤ xplus := by
      have h1 : a ≤ max xplus 0 := min_le_left _ _
      rcases le_total xplus 0 with h | h
      · rw [max_eq_right h] at h1; linarith
      · rwa [max_eq_left h] at h1
    have hfr : ∀ z < xplus, β < (μ {ω | z < E.D ω - E.Q ω}).toReal := by
      rcases hx with ⟨_, hx2⟩ | ⟨_, hx2⟩
      · exact hx2
      · linarith
    have key : (a - y) * β ≤
        (∫ ω, max (E.D ω - E.Q ω - y) 0 ∂μ) - (∫ ω, max (E.D ω - E.Q ω - a) 0 ∂μ) := by
      have hlim : Filter.Tendsto (fun z : ℝ => (z - y) * β) (nhdsWithin a (Set.Iio a))
          (nhds ((a - y) * β)) := by
        have : Continuous (fun z : ℝ => (z - y) * β) := by fun_prop
        exact (this.tendsto a).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hya] with z hz
      have h1 := newsvendor_lower μ E hE y z a hz.1 hz.2
      have h2 := hfr z (lt_of_lt_of_le hz.2 hax)
      have h3 : (z - y) * β ≤ (z - y) * (μ {ω | z < E.D ω - E.Q ω}).toReal :=
        mul_le_mul_of_nonneg_left h2.le (by linarith [hz.1])
      linarith
    nlinarith

end PrepoLocal.Threshold

open PrepoLocal.Threshold

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus) :
    IsMinOn (Ca P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) :=
  eq_4' μ P hP E hE xplus hx
