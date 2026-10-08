-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.eoq_relative_cost_increase_le
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T03:40:07.340991+00:00
-- url     : https://prove2.me/submissions/0a5591f0-cdc9-4c7c-b998-6158dacfec2c

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

set_option autoImplicit false


/- Inlined checked module: CostProfile -/
section
namespace ZhengQR.EOQProof

/-- Analytic properties derived from the exact newsvendor probability model. No
density or differentiability of the cost function is assumed. -/
structure CostProfile (G : ℝ → ℝ) (h p m : ℝ) : Prop where
  continuous : Continuous G
  convex : ConvexOn ℝ Set.univ G
  nonneg : ∀ y : ℝ, 0 ≤ G y
  slopes : ∀ x y : ℝ, x ≤ y →
    -p * (y - x) ≤ G y - G x ∧ G y - G x ≤ h * (y - x)
  lower_h : ∀ y : ℝ, h * (y - m) ≤ G y
  lower_p : ∀ y : ℝ, p * (m - y) ≤ G y

end ZhengQR.EOQProof
end


/- Inlined checked module: CoerciveMinimum -/
section
namespace ZhengQR.EOQProof
open Set

/-- Two coercive affine lower bounds give an attained global minimum. -/
theorem exists_min_of_affine_bounds (F : ℝ → ℝ) (hF : Continuous F)
    (A B C D : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hup : ∀ x, A * x + B ≤ F x) (hlo : ∀ x, C - D * x ≤ F x) :
    ∃ r : ℝ, ∀ x : ℝ, F r ≤ F x := by
  let l := (C - F 0) / D
  let u := (F 0 - B) / A
  have hl : l ≤ 0 := (div_le_iff₀ hD).mpr (by have := hlo 0; linarith)
  have hu : 0 ≤ u := (le_div_iff₀ hA).mpr (by have := hup 0; linarith)
  have h0 : (0 : ℝ) ∈ Icc l u := ⟨hl, hu⟩
  obtain ⟨r, hr, hm⟩ := isCompact_Icc.exists_isMinOn ⟨0, h0⟩ hF.continuousOn
  have hr0 : F r ≤ F 0 := hm h0
  refine ⟨r, fun x => ?_⟩
  by_cases hxl : x < l
  · have hx := (lt_div_iff₀ hD).mp hxl
    have hh := hlo x
    linarith
  by_cases hux : u < x
  · have hx := (div_lt_iff₀ hA).mp hux
    have hh := hup x
    linarith
  · exact hm ⟨le_of_not_gt hxl, le_of_not_gt hux⟩

end ZhengQR.EOQProof
end


/- Inlined checked module: WindowAverage -/
section
noncomputable section
namespace ZhengQR.EOQProof
open MeasureTheory Set

def centerAverage (G : ℝ → ℝ) (c Q : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, G (c - Q / 2 + Q * t)

lemma centerAverage_eq (G : ℝ → ℝ) (c Q : ℝ) (hQ : Q ≠ 0) :
    centerAverage G c Q = (∫ y in (c - Q / 2)..(c + Q / 2), G y) / Q := by
  unfold centerAverage
  rw [intervalIntegral.integral_comp_add_mul G hQ]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  rw [show c - Q / 2 + Q = c + Q / 2 by ring]
  ring

/-- A convex cost's average over centered uniform intervals is nondecreasing with
the positive interval length. The reflected-pair argument permits nonsmooth costs. -/
theorem centerAverage_mono (G : ℝ → ℝ) (hG : Continuous G)
    (hc : ConvexOn ℝ univ G) (c q Q : ℝ) (hq : 0 ≤ q) (hQ : 0 < Q) (hle : q ≤ Q) :
    centerAverage G c q ≤ centerAverage G c Q := by
  let θ := (1 + q / Q) / 2
  have hratio : 0 ≤ q / Q := div_nonneg hq hQ.le
  have hratio1 : q / Q ≤ 1 := (div_le_one₀ hQ).mpr hle
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hpoint (t : ℝ) :
      G (c - q / 2 + q * t) ≤
        θ * G (c - Q / 2 + Q * t) + (1 - θ) * G (c - Q / 2 + Q * (1 - t)) := by
    have h := hc.2 (mem_univ (c - Q / 2 + Q * t))
      (mem_univ (c - Q / 2 + Q * (1 - t))) hθ (sub_nonneg.mpr hθ1) (by ring)
    have heq : θ * (c - Q / 2 + Q * t) +
        (1 - θ) * (c - Q / 2 + Q * (1 - t)) = c - q / 2 + q * t := by
      dsimp [θ]
      field_simp
      ring
    simpa only [smul_eq_mul, heq] using h
  have hsmall : Continuous (fun t : ℝ => G (c - q / 2 + q * t)) := by fun_prop
  have hbig : Continuous (fun t : ℝ => G (c - Q / 2 + Q * t)) := by fun_prop
  have hreflect : Continuous (fun t : ℝ => G (c - Q / 2 + Q * (1 - t))) := by fun_prop
  have hI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hsmall.intervalIntegrable 0 1)
    (((hbig.const_mul θ).add (hreflect.const_mul (1 - θ))).intervalIntegrable 0 1)
    (fun t _ => hpoint t)
  have hr : (∫ t in (0 : ℝ)..1, G (c - Q / 2 + Q * (1 - t))) = centerAverage G c Q := by
    simpa only [sub_self, sub_zero, centerAverage] using
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => G (c - Q / 2 + Q * t))
        (a := 0) (b := 1) 1
  simp only [Pi.add_apply] at hI
  rw [intervalIntegral.integral_add (μ := volume)
      ((hbig.const_mul θ).intervalIntegrable 0 1)
      ((hreflect.const_mul (1 - θ)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hr] at hI
  change centerAverage G c q ≤ θ * centerAverage G c Q +
    (1 - θ) * centerAverage G c Q at hI
  nlinarith

end ZhengQR.EOQProof
end
end


/- Inlined checked module: WindowCalculus -/
section
noncomputable section
namespace ZhengQR.EOQProof
open MeasureTheory Set ZhengQR.EOQHeuristic

def primitive (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, G y

lemma primitive_hasDerivAt (G : ℝ → ℝ) (hG : Continuous G) (x : ℝ) :
    HasDerivAt (primitive G) (G x) x :=
  intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 x)
    hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt

lemma windowIntegral_eq (G : ℝ → ℝ) (hG : Continuous G) (r Q : ℝ) :
    (∫ y in r..r + Q, G y) = primitive G (r + Q) - primitive G r :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt G hG x) (hG.intervalIntegrable r (r + Q))

lemma qrCost_reorder_hasDerivAt (G : ℝ → ℝ) (hG : Continuous G) (lam K Q r : ℝ) :
    HasDerivAt (qrCost G lam K Q) ((G (r + Q) - G r) / Q) r := by
  have heq : (fun s : ℝ => qrCost G lam K Q s) =
      fun s => (lam * K + (primitive G (s + Q) - primitive G s)) / Q := by
    funext s
    rw [qrCost, windowIntegral_eq G hG]
  change HasDerivAt (fun s : ℝ => qrCost G lam K Q s) _ r
  rw [heq]
  have hshift := (primitive_hasDerivAt G hG (r + Q)).comp r ((hasDerivAt_id r).add_const Q)
  convert! ((hshift.sub (primitive_hasDerivAt G hG r)).const_add (lam * K)).div_const Q using 1
  all_goals first | rfl | ring

lemma qrCost_reorder_continuous (G : ℝ → ℝ) (hG : Continuous G) (lam K Q : ℝ) :
    Continuous (qrCost G lam K Q) :=
  continuous_iff_continuousAt.mpr fun r => (qrCost_reorder_hasDerivAt G hG lam K Q r).continuousAt

lemma qrCost_quantity_hasDerivAt (G : ℝ → ℝ) (hG : Continuous G) (lam K Q r : ℝ)
    (hQ : Q ≠ 0) :
    HasDerivAt (fun q => qrCost G lam K q r)
      ((G (r + Q) * Q - (lam * K + ∫ y in r..r + Q, G y)) / Q ^ 2) Q := by
  have heq : (fun q : ℝ => qrCost G lam K q r) =
      fun q => (lam * K + (primitive G (r + q) - primitive G r)) / q := by
    funext q
    rw [qrCost, windowIntegral_eq G hG]
  rw [heq, windowIntegral_eq G hG]
  have hshift := (primitive_hasDerivAt G hG (r + Q)).comp Q ((hasDerivAt_id Q).const_add r)
  convert! (((hshift.sub_const (primitive G r)).const_add (lam * K)).div (hasDerivAt_id Q) hQ) using 1
  all_goals first | rfl | (dsimp; ring)

lemma integral_affine_window (A B r Q : ℝ) :
    (∫ y in r..r + Q, A * y + B) = Q * (A * (r + Q / 2) + B) := by
  have ha : Continuous (fun y : ℝ => A * y) := by fun_prop
  have hb : Continuous (fun _ : ℝ => B) := continuous_const
  rw [intervalIntegral.integral_add (μ := volume)
    (ha.intervalIntegrable r (r + Q)) (hb.intervalIntegrable r (r + Q)),
    intervalIntegral.integral_const_mul A (fun y : ℝ => y),
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end ZhengQR.EOQProof
end
end


/- Inlined checked module: ReorderExistence -/
section
namespace ZhengQR.EOQProof
open MeasureTheory Set ZhengQR.EOQHeuristic

lemma qrCost_ge_of_affine_lower (G : ℝ → ℝ) (hG : Continuous G)
    (lam K Q A B r : ℝ) (hQ : 0 < Q) (hlo : ∀ y, A * y + B ≤ G y) :
    A * r + (lam * K / Q + A * Q / 2 + B) ≤ qrCost G lam K Q r := by
  have hAffine : Continuous (fun y : ℝ => A * y + B) := by fun_prop
  have hint : (∫ y in r..r + Q, A * y + B) ≤ ∫ y in r..r + Q, G y :=
    intervalIntegral.integral_mono_on (μ := volume)
    (show r ≤ r + Q by linarith)
    (hAffine.intervalIntegrable r (r + Q))
    (hG.intervalIntegrable r (r + Q)) (fun y _ => hlo y)
  rw [integral_affine_window] at hint
  unfold qrCost
  apply (le_div_iff₀ hQ).mpr
  have hcancel : (lam * K / Q) * Q = lam * K := div_mul_cancel₀ _ (ne_of_gt hQ)
  nlinarith only [hint, hcancel]

theorem reorder_exists (G : ℝ → ℝ) (h p m : ℝ) (prof : CostProfile G h p m)
    (hh : 0 < h) (hp : 0 < p) (lam K Q : ℝ) (hQ : 0 < Q) :
    ∃ r : ℝ, IsOptReorder G lam K Q r := by
  have hup (r : ℝ) : h * r + (lam * K / Q + h * Q / 2 - h * m) ≤ qrCost G lam K Q r := by
    have hlow (y : ℝ) : h * y + (-h * m) ≤ G y := by
      have hh := prof.lower_h y
      nlinarith
    have hz := qrCost_ge_of_affine_lower G prof.continuous lam K Q h (-h * m) r hQ hlow
    nlinarith
  have hlo (r : ℝ) : (lam * K / Q - p * Q / 2 + p * m) - p * r ≤ qrCost G lam K Q r := by
    have hlow (y : ℝ) : (-p) * y + p * m ≤ G y := by
      have hh := prof.lower_p y
      nlinarith
    have hz := qrCost_ge_of_affine_lower G prof.continuous lam K Q (-p) (p * m) r hQ hlow
    nlinarith
  obtain ⟨r, hr⟩ := exists_min_of_affine_bounds (qrCost G lam K Q)
    (qrCost_reorder_continuous G prof.continuous lam K Q) h
    (lam * K / Q + h * Q / 2 - h * m) (lam * K / Q - p * Q / 2 + p * m) p hh hp hup hlo
  exact ⟨r, hr⟩

theorem selected_reorder_valid (G : ℝ → ℝ) (h p m : ℝ) (prof : CostProfile G h p m)
    (hh : 0 < h) (hp : 0 < p) (lam K Q : ℝ) (hQ : 0 < Q) :
    IsOptReorder G lam K Q (reorderPt G lam K Q) := by
  have hex := reorder_exists G h p m prof hh hp lam K Q hQ
  unfold reorderPt
  rw [dif_pos hex]
  exact hex.choose_spec

theorem selected_cost_le (G : ℝ → ℝ) (h p m : ℝ) (prof : CostProfile G h p m)
    (hh : 0 < h) (hp : 0 < p) (lam K Q r : ℝ) (hQ : 0 < Q) :
    optCost G lam K Q ≤ qrCost G lam K Q r :=
  selected_reorder_valid G h p m prof hh hp lam K Q hQ r

end ZhengQR.EOQProof
end


/- Inlined checked module: JointOptimality -/
section
namespace ZhengQR.EOQProof
open Set Filter
open scoped Topology
open ZhengQR.EOQHeuristic

/-- Joint optimality is derived from the supplied positive quantity optimum and the
proved validity of every reorder choice. Only moving integrals are differentiated. -/
theorem optimal_cost_endpoints (G : ℝ → ℝ) (h p m : ℝ) (prof : CostProfile G h p m)
    (hh : 0 < h) (hp : 0 < p) (lam K Qs : ℝ) (hQs : IsOptQty G lam K Qs) :
    let r := reorderPt G lam K Qs
    optCost G lam K Qs = G r ∧ optCost G lam K Qs = G (r + Qs) ∧
      lam * K = Qs * optCost G lam K Qs - ∫ y in r..r + Qs, G y := by
  let r := reorderPt G lam K Qs
  have hQ : 0 < Qs := hQs.1
  have hminR : ∀ s, qrCost G lam K Qs r ≤ qrCost G lam K Qs s :=
    selected_reorder_valid G h p m prof hh hp lam K Qs hQ
  have hlocalR : IsLocalMin (qrCost G lam K Qs) r :=
    (show IsMinOn (qrCost G lam K Qs) univ r from fun s _ => hminR s).isLocalMin Filter.univ_mem
  have hzeroR := hlocalR.hasDerivAt_eq_zero
    (qrCost_reorder_hasDerivAt G prof.continuous lam K Qs r)
  have hend : G (r + Qs) = G r :=
    sub_eq_zero.mp (((div_eq_zero_iff).mp hzeroR).resolve_right (ne_of_gt hQ))
  have hminQ : ∀ q, 0 < q → qrCost G lam K Qs r ≤ qrCost G lam K q r := by
    intro q hq
    exact (hQs.2 q hq).trans (selected_cost_le G h p m prof hh hp lam K q r hq)
  have hlocalQ : IsLocalMin (fun q => qrCost G lam K q r) Qs :=
    (show IsMinOn (fun q => qrCost G lam K q r) (Ioi 0) Qs from hminQ).isLocalMin (Ioi_mem_nhds hQ)
  have hzeroQ := hlocalQ.hasDerivAt_eq_zero
    (qrCost_quantity_hasDerivAt G prof.continuous lam K Qs r (ne_of_gt hQ))
  have hnum : G (r + Qs) * Qs = lam * K + ∫ y in r..r + Qs, G y :=
    sub_eq_zero.mp (((div_eq_zero_iff).mp hzeroQ).resolve_right (pow_ne_zero _ (ne_of_gt hQ)))
  have hcost : optCost G lam K Qs = G (r + Qs) := by
    change (lam * K + ∫ y in r..r + Qs, G y) / Qs = G (r + Qs)
    rw [← hnum]
    exact mul_div_cancel_right₀ _ (ne_of_gt hQ)
  refine ⟨hcost.trans hend, hcost, ?_⟩
  rw [hcost]
  nlinarith only [hnum]

end ZhengQR.EOQProof
end


/- Inlined checked module: HoldingComparison -/
section
namespace ZhengQR.EOQProof
open ZhengQR.EOQHeuristic

lemma qrCost_at_center (G : ℝ → ℝ) (lam K c Q : ℝ) (hQ : Q ≠ 0) :
    qrCost G lam K Q (c - Q / 2) = lam * K / Q + centerAverage G c Q := by
  rw [qrCost, centerAverage_eq G c Q hQ,
    show c - Q / 2 + Q = c + Q / 2 by ring, add_div]

/-- Optimized holding-cost averages are monotone in quantity. Reorder choices are
proved valid first, so their fallback values never enter this comparison. -/
theorem optimal_cost_gap (G : ℝ → ℝ) (h p m : ℝ) (prof : CostProfile G h p m)
    (hh : 0 < h) (hp : 0 < p) (lam K q Q : ℝ)
    (hq : 0 < q) (hQ : 0 < Q) (hqQ : q ≤ Q) :
    optCost G lam K q - optCost G lam K Q ≤ lam * K * (1 / q - 1 / Q) := by
  let c := reorderPt G lam K Q + Q / 2
  have hc : c - Q / 2 = reorderPt G lam K Q := by dsimp [c]; ring
  have hbig : optCost G lam K Q = lam * K / Q + centerAverage G c Q := by
    have hz := qrCost_at_center G lam K c Q (ne_of_gt hQ)
    rw [hc] at hz
    exact hz
  have hsmall := selected_cost_le G h p m prof hh hp lam K q (c - q / 2) hq
  rw [qrCost_at_center G lam K c q (ne_of_gt hq)] at hsmall
  have havg := centerAverage_mono G prof.continuous prof.convex c q Q hq.le hQ hqQ
  calc
    _ ≤ lam * K / q - lam * K / Q := by linarith
    _ = _ := by ring

end ZhengQR.EOQProof
end


/- Inlined checked module: NewsvendorProfile -/
section
open MeasureTheory

namespace ZhengQR.EOQProof
open ZhengQR.EOQHeuristic

noncomputable def inventoryLoss (h p y x : ℝ) : ℝ :=
  h * max (y - x) 0 + p * max (x - y) 0

theorem inventoryLoss_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h p y : ℝ) (hint : Integrable (fun x : ℝ => x) μ) :
    Integrable (inventoryLoss h p y) μ := by
  exact ((((integrable_const y).sub hint).sup (integrable_const 0)).const_mul h).add
    (((hint.sub (integrable_const y)).sup (integrable_const 0)).const_mul p)

theorem inventoryLoss_convex (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (fun y => inventoryLoss h p y x) := by
  have hleft : ConvexOn ℝ Set.univ (fun y : ℝ => y - x) :=
    (convexOn_id convex_univ).sub (concaveOn_const x convex_univ)
  have hright : ConvexOn ℝ Set.univ (fun y : ℝ => x - y) :=
    (convexOn_const x convex_univ).sub (concaveOn_id convex_univ)
  refine ⟨convex_univ, ?_⟩
  intro y hy z hz a b ha hb hab
  have hl := (hleft.sup (convexOn_const 0 convex_univ)).2 hy hz ha hb hab
  have hr := (hright.sup (convexOn_const 0 convex_univ)).2 hy hz ha hb hab
  change max (a * y + b * z - x) 0 ≤ a * max (y - x) 0 + b * max (z - x) 0 at hl
  change max (x - (a * y + b * z)) 0 ≤ a * max (x - y) 0 + b * max (x - z) 0 at hr
  change h * max (a * y + b * z - x) 0 + p * max (x - (a * y + b * z)) 0 ≤
    a * (h * max (y - x) 0 + p * max (x - y) 0) +
    b * (h * max (z - x) 0 + p * max (x - z) 0)
  nlinarith [mul_le_mul_of_nonneg_left hl hh, mul_le_mul_of_nonneg_left hr hp]

theorem inventoryLoss_nonneg (h p y x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    0 ≤ inventoryLoss h p y x :=
  add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

theorem inventoryLoss_slopes (h p a b x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hab : a ≤ b) :
    -p * (b - a) ≤ inventoryLoss h p b x - inventoryLoss h p a x ∧
      inventoryLoss h p b x - inventoryLoss h p a x ≤ h * (b - a) := by
  by_cases hxa : x ≤ a
  · simp only [inventoryLoss, max_eq_left (sub_nonneg.mpr hxa),
      max_eq_right (sub_nonpos.mpr hxa),
      max_eq_left (sub_nonneg.mpr (hxa.trans hab)),
      max_eq_right (sub_nonpos.mpr (hxa.trans hab)), mul_zero, add_zero]
    constructor <;> nlinarith [mul_nonneg (add_nonneg hh hp) (sub_nonneg.mpr hab)]
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
    by_cases hxb : x ≤ b
    · simp only [inventoryLoss, max_eq_right (sub_nonpos.mpr hax),
        max_eq_left (sub_nonneg.mpr hax), max_eq_left (sub_nonneg.mpr hxb),
        max_eq_right (sub_nonpos.mpr hxb), mul_zero, zero_add, add_zero]
      constructor <;> nlinarith [mul_nonneg (add_nonneg hh hp) (sub_nonneg.mpr hax),
        mul_nonneg (add_nonneg hh hp) (sub_nonneg.mpr hxb)]
    · have hbx : b ≤ x := le_of_lt (lt_of_not_ge hxb)
      simp only [inventoryLoss, max_eq_right (sub_nonpos.mpr hax),
        max_eq_left (sub_nonneg.mpr hax), max_eq_right (sub_nonpos.mpr hbx),
        max_eq_left (sub_nonneg.mpr hbx), mul_zero, zero_add]
      constructor <;> nlinarith [mul_nonneg (add_nonneg hh hp) (sub_nonneg.mpr hab)]

theorem inventoryLoss_lower_h (h p y x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    h * (y - x) ≤ inventoryLoss h p y x := by
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hh).trans
    (le_add_of_nonneg_right (mul_nonneg hp (le_max_right _ _)))

theorem inventoryLoss_lower_p (h p y x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    p * (x - y) ≤ inventoryLoss h p y x := by
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hp).trans
    (le_add_of_nonneg_left (mul_nonneg hh (le_max_right _ _)))

theorem newsvendor_profile {lam L h p : ℝ} {μ : Measure ℝ}
    (hM : IsQRModel lam L h p μ) :
    CostProfile (newsvendorCost μ h p) h p (lam * L) := by
  let : IsProbabilityMeasure μ := hM.isProb
  have hint (y : ℝ) := inventoryLoss_integrable h p y hM.integrable
  have hconv : ConvexOn ℝ Set.univ (newsvendorCost μ h p) :=
    integral_convexOn_of_integrand_ae convex_univ
      (ae_of_all μ (fun x => inventoryLoss_convex h p x hM.h_pos.le hM.p_pos.le))
      (fun y _ => hint y)
  refine ⟨continuousOn_univ.mp (hconv.continuousOn isOpen_univ), hconv, ?_, ?_, ?_, ?_⟩
  · intro y
    exact integral_nonneg (fun x => inventoryLoss_nonneg h p y x hM.h_pos.le hM.p_pos.le)
  · intro a b hab
    have hlo := integral_mono (integrable_const (-p * (b - a))) ((hint b).sub (hint a))
      (fun x => (inventoryLoss_slopes h p a b x hM.h_pos.le hM.p_pos.le hab).1)
    have hhi := integral_mono ((hint b).sub (hint a)) (integrable_const (h * (b - a)))
      (fun x => (inventoryLoss_slopes h p a b x hM.h_pos.le hM.p_pos.le hab).2)
    have he : (∫ x, (inventoryLoss h p b - inventoryLoss h p a) x ∂μ) =
        newsvendorCost μ h p b - newsvendorCost μ h p a := by
      change (∫ x, inventoryLoss h p b x - inventoryLoss h p a x ∂μ) = _
      rw [integral_sub (hint b) (hint a)]
      rfl
    rw [he] at hlo hhi
    simpa only [integral_const, probReal_univ, one_smul] using And.intro hlo hhi
  · intro y
    have hlow := integral_mono (((integrable_const y).sub hM.integrable).const_mul h)
      (hint y) (fun x => inventoryLoss_lower_h h p y x hM.h_pos.le hM.p_pos.le)
    change (∫ x, h * (y - x) ∂μ) ≤ newsvendorCost μ h p y at hlow
    rw [integral_const_mul, integral_sub (integrable_const y) hM.integrable,
      integral_const, probReal_univ, one_smul, hM.mean] at hlow
    exact hlow
  · intro y
    have hlow := integral_mono ((hM.integrable.sub (integrable_const y)).const_mul p)
      (hint y) (fun x => inventoryLoss_lower_p h p y x hM.h_pos.le hM.p_pos.le)
    change (∫ x, p * (x - y) ∂μ) ≤ newsvendorCost μ h p y at hlow
    rw [integral_const_mul, integral_sub hM.integrable (integrable_const y),
      integral_const, probReal_univ, one_smul, hM.mean] at hlow
    exact hlow

end ZhengQR.EOQProof
end


/- Inlined checked module: TriangleDeficit -/
section
open MeasureTheory

namespace ZhengQR.EOQProof

theorem endpoint_level_lower {G : ℝ → ℝ} {h p m r Q C : ℝ}
    (hG : CostProfile G h p m) (hh : 0 < h) (hp : 0 < p)
    (hl : G r = C) (hr : G (r + Q) = C) :
    h * p / (h + p) * Q ≤ C := by
  have h0 := hG.lower_p r
  have h1 := hG.lower_h (r + Q)
  rw [hl] at h0
  rw [hr] at h1
  have hsum : h * p * Q ≤ C * (h + p) := by
    nlinarith [mul_le_mul_of_nonneg_left h0 hh.le,
      mul_le_mul_of_nonneg_left h1 hp.le]
  simpa only [div_mul_eq_mul_div] using (div_le_iff₀ (add_pos hh hp)).mpr hsum

theorem deficit_integral_bound {G : ℝ → ℝ} {h p m r Q C : ℝ}
    (hG : CostProfile G h p m) (hh : 0 < h) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hl : G r = C) (hr : G (r + Q) = C) :
    (∫ y in r..r + Q, C - G y) ≤ h * p / (h + p) * Q ^ 2 / 2 := by
  let d : ℝ := h * Q / (h + p)
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hh.le hQ) (add_pos hh hp).le
  have hdQ : d ≤ Q := by
    dsimp [d]
    apply (div_le_iff₀ (add_pos hh hp)).mpr
    nlinarith [mul_nonneg hp.le hQ]
  have hf : Continuous (fun y => C - G y) := continuous_const.sub hG.continuous
  have hpl : Continuous (fun y : ℝ => p * (y - r)) := by fun_prop
  have hpr : Continuous (fun y : ℝ => h * (r + Q - y)) := by fun_prop
  have hlower (y : ℝ) (hy : r ≤ y) : C - G y ≤ p * (y - r) := by
    have hs := (hG.slopes r y hy).1
    rw [hl] at hs
    linarith
  have hupper (y : ℝ) (hy : y ≤ r + Q) : C - G y ≤ h * (r + Q - y) := by
    have hs := (hG.slopes y (r + Q) hy).2
    rw [hr] at hs
    exact hs
  calc
    (∫ y in r..r + Q, C - G y) =
        (∫ y in r..r + d, C - G y) + (∫ y in r + d..r + Q, C - G y) :=
      (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    _ ≤ (∫ y in r..r + d, p * (y - r)) +
        (∫ y in r + d..r + Q, h * (r + Q - y)) := by
      apply add_le_add
      · exact intervalIntegral.integral_mono_on (μ := volume) (by linarith)
          (hf.intervalIntegrable _ _) (hpl.intervalIntegrable _ _) (fun y hy => hlower y hy.1)
      · exact intervalIntegral.integral_mono_on (μ := volume) (by linarith)
          (hf.intervalIntegrable _ _) (hpr.intervalIntegrable _ _) (fun y hy => hupper y hy.2)
    _ = h * p / (h + p) * Q ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun y : ℝ => y) (g := fun _ => r)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_sub (f := fun _ : ℝ => r + Q) (g := fun y => y)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
      simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
      dsimp [d]
      field_simp [ne_of_gt (add_pos hh hp)]
      ring

theorem setup_le_triangle {G : ℝ → ℝ} {h p m r Q C a : ℝ}
    (hG : CostProfile G h p m) (hh : 0 < h) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hl : G r = C) (hr : G (r + Q) = C)
    (hcost : C * Q = a + ∫ y in r..r + Q, G y) :
    a ≤ h * p / (h + p) * Q ^ 2 / 2 := by
  have hd := deficit_integral_bound hG hh hp hQ hl hr
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => C) (g := G)
    (continuous_const.intervalIntegrable _ _) (hG.continuous.intervalIntegrable _ _),
    intervalIntegral.integral_const] at hd
  simp only [smul_eq_mul] at hd
  nlinarith

end ZhengQR.EOQProof
end


/- Inlined checked module: EOQRatio -/
section
namespace ZhengQR.EOQProof
open ZhengQR.EOQHeuristic

theorem eoqQty_pos {lam K h p : ℝ} (hlam : 0 < lam) (hK : 0 < K)
    (hh : 0 < h) (hp : 0 < p) : 0 < eoqQty lam K h p := by
  unfold eoqQty
  positivity

theorem eoqQty_square {lam K h p : ℝ} (hlam : 0 < lam) (hK : 0 < K)
    (hh : 0 < h) (hp : 0 < p) :
    h * p / (h + p) * (eoqQty lam K h p) ^ 2 = 2 * (lam * K) := by
  unfold eoqQty
  rw [Real.sq_sqrt (by positivity)]
  field_simp [ne_of_gt hh, ne_of_gt hp, ne_of_gt (add_pos hh hp)]

theorem eoqQty_le_of_setup_bound {lam K h p Q : ℝ} (hlam : 0 < lam) (hK : 0 < K)
    (hh : 0 < h) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hsetup : lam * K ≤ h * p / (h + p) * Q ^ 2 / 2) :
    eoqQty lam K h p ≤ Q := by
  have hc : 0 < h * p / (h + p) := div_pos (mul_pos hh hp) (add_pos hh hp)
  have hs := eoqQty_square hlam hK hh hp
  have hq := (eoqQty_pos hlam hK hh hp).le
  apply (sq_le_sq₀ hq hQ).mp
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hs, hsetup]

theorem relative_gap_bound {c q Q C D : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hC : c * Q ≤ C)
    (hgap : D - C ≤ (c * q ^ 2 / 2) * (1 / q - 1 / Q)) :
    (D - C) / C ≤ 1 / 8 - 1 / 2 * (1 / 2 - q / Q) ^ 2 ∧
      1 / 8 - 1 / 2 * (1 / 2 - q / Q) ^ 2 ≤ (1 / 8 : ℝ) := by
  have hCpos : 0 < C := (mul_pos hc hQ).trans_le hC
  have ht0 : 0 ≤ q / Q := (div_pos hq hQ).le
  have ht1 : q / Q ≤ 1 := (div_le_one₀ hQ).mpr hqQ
  have hR : 0 ≤ q / Q * (1 - q / Q) / 2 :=
    div_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (by norm_num)
  have hid : (c * q ^ 2 / 2) * (1 / q - 1 / Q) =
      (q / Q * (1 - q / Q) / 2) * (c * Q) := by
    field_simp [ne_of_gt hq, ne_of_gt hQ]
  constructor
  · rw [show (1 / 8 - 1 / 2 * (1 / 2 - q / Q) ^ 2 : ℝ) =
        q / Q * (1 - q / Q) / 2 by ring]
    apply (div_le_iff₀ hCpos).mpr
    calc
      D - C ≤ (q / Q * (1 - q / Q) / 2) * (c * Q) := hid ▸ hgap
      _ ≤ (q / Q * (1 - q / Q) / 2) * C := mul_le_mul_of_nonneg_left hC hR
  · nlinarith [sq_nonneg (1 / 2 - q / Q)]

end ZhengQR.EOQProof
end


/- Inlined checked module: EOQRoot -/
section
open MeasureTheory

namespace ZhengQR.EOQHeuristic
open ZhengQR.EOQProof

theorem eoq_relative_cost_increase_le {lam L K h p : ℝ} {μ : Measure ℝ}
    (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    (optCost (newsvendorCost μ h p) lam K (eoqQty lam K h p) -
      optCost (newsvendorCost μ h p) lam K Qs) / optCost (newsvendorCost μ h p) lam K Qs
        ≤ 1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ∧
      1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ≤ (1 / 8 : ℝ) := by
  let G := newsvendorCost μ h p
  let r := reorderPt G lam K Qs
  let C := optCost G lam K Qs
  have prof : CostProfile G h p (lam * L) := newsvendor_profile hM
  have hQ : 0 < Qs := hQs.1
  obtain ⟨hl, hr, hid⟩ := optimal_cost_endpoints G h p (lam * L) prof hM.h_pos hM.p_pos lam K Qs hQs
  have hlevel : h * p / (h + p) * Qs ≤ C :=
    endpoint_level_lower prof hM.h_pos hM.p_pos hl.symm hr.symm
  have hcost : C * Qs = lam * K + ∫ y in r..r + Qs, G y := by
    nlinarith only [hid]
  have hsetup := setup_le_triangle prof hM.h_pos hM.p_pos hQ.le hl.symm hr.symm hcost
  have hq := eoqQty_pos hM.lam_pos hK hM.h_pos hM.p_pos
  have hqQ := eoqQty_le_of_setup_bound hM.lam_pos hK hM.h_pos hM.p_pos hQ.le hsetup
  have hgap := optimal_cost_gap G h p (lam * L) prof hM.h_pos hM.p_pos lam K
    (eoqQty lam K h p) Qs hq hQ hqQ
  have hsquare := eoqQty_square hM.lam_pos hK hM.h_pos hM.p_pos
  have hcoefficient : (h * p / (h + p)) * (eoqQty lam K h p) ^ 2 / 2 = lam * K := by
    nlinarith only [hsquare]
  rw [← hcoefficient] at hgap
  exact relative_gap_bound (div_pos (mul_pos hM.h_pos hM.p_pos) (add_pos hM.h_pos hM.p_pos))
    hq hQ hqQ hlevel hgap

end ZhengQR.EOQHeuristic
end


open MeasureTheory Filter Topology ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    (optCost (newsvendorCost μ h p) lam K (eoqQty lam K h p) - optCost (newsvendorCost μ h p) lam K Qs) / optCost (newsvendorCost μ h p) lam K Qs
        ≤ 1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ∧
      1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ≤ (1 / 8 : ℝ) := ZhengQR.EOQHeuristic.eoq_relative_cost_increase_le hM hK Qs hQs
