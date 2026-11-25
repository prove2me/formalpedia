-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:26.68355+00:00
-- url     : https://prove2.me/submissions/821d84c3-5d48-424c-9c1e-0dfc94e8fa4a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_lint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_contOn_ph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_nsq_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_G_ne_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffG
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by
  classical
  obtain ⟨U, hU, hfin⟩ := hloc ((A.chart i).symm v)
  have hc1 : ContinuousAt (A.ph A.kap i ∘ (A.chart i).symm) v :=
    (A.smooth_ph A.kap i).continuousOn.continuousAt ((A.chart i).open_target.mem_nhds hv)
  have hc2 : ContinuousAt (A.ph la i ∘ (A.chart i).symm) v :=
    (A.smooth_ph la i).continuousOn.continuousAt ((A.chart i).open_target.mem_nhds hv)
  have he1 : ∀ᶠ u in 𝓝 v, u ∈ (A.chart i).target := (A.chart i).open_target.mem_nhds hv
  have he2 : ∀ᶠ u in 𝓝 v, (A.chart i).symm u ∈ U := ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hU
  have hev := he1.and (he2.and
      ((hc1.eventually (Metric.ball_mem_nhds _ one_pos)).and
        (hc2.eventually (Metric.ball_mem_nhds _ one_pos))))
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hball : Metric.ball v r ⊆ (A.chart i).target := fun u hu => (hrP u hu).1
  refine ⟨r, hr, hball, ?_⟩
  have hGc : ContinuousOn (fnG A w0 s De i) (Metric.ball v r) :=
    ((fn_diffG A hD i).mono hball).continuousOn
  have hSo : IsOpen (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) :=
    hGc.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hSM : ∀ u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0},
      u ∈ (A.chart i).target ∧ (A.chart i).symm u ∈ A.Mset w0 s De := fun u hu =>
    ⟨hball hu.1, (fn_G_ne_iff A hD (hball hu.1)).1 hu.2⟩
  have hFS : ContinuousOn (F i ∘ (A.chart i).symm) (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) :=
    (hFs.1 i).continuousOn.mono fun u hu => hSM u hu
  set W := (A.chart i).source ∩ (A.chart i) ⁻¹' (Metric.ball v r \ {u | fnG A w0 s De i u = 0}) with hWdef
  have hWo : IsOpen W := (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source hSo
  have hWM : ∀ y ∈ W, y ∈ A.Mset w0 s De ∧ y ∈ U := by
    intro y hy
    have h := (hSM _ hy.2)
    rw [(A.chart i).left_inv hy.1] at h
    have h2 := (hrP _ hy.2.1).2.1
    rw [(A.chart i).left_inv hy.1] at h2
    exact ⟨h.2, h2⟩
  have hFW : ContinuousOn (F i) W := by
    refine (hFS.comp ((A.chart i).continuousOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)).congr ?_
    intro y hy
    simp [Function.comp, (A.chart i).left_inv hy.1]
  have hphW : ContinuousOn (A.ph la i) W := (fn_contOn_ph A la i).mono fun y hy => hy.1
  have hgc : ContinuousOn (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((continuous_norm.comp_continuousOn hFW).pow 2).mul (Real.continuous_exp.comp_continuousOn hphW.neg))
  have hφm : Measurable (W.indicator fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) := by
    rw [← Set.piecewise_eq_indicator]
    exact hgc.measurable_piecewise continuousOn_const hWo.measurableSet
  have hlint := fn_lint A i hφm
  have hY : ∫⁻ x in (A.chart i).source,
      W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    calc ∫⁻ x in (A.chart i).source,
          W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu
        ≤ ∫⁻ x, W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y))) x ∂A.mu :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ x in W, ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)) ∂A.mu :=
          lintegral_indicator hWo.measurableSet _
      _ ≤ ∫⁻ x in W, ENNReal.ofReal (A.nsq la F x) ∂A.mu := by
          refine setLIntegral_mono' hWo.measurableSet fun x hx => le_of_eq ?_
          rw [fn_nsq_eq A hFs hx.1 (hWM x hx).1]
      _ ≤ ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu :=
          lintegral_mono_set fun x hx => ⟨(hWM x hx).2, (hWM x hx).1⟩
  rw [hlint] at hY
  set a := Real.exp (-(A.ph la i ((A.chart i).symm v)) - 1) with ha
  set b := Real.exp (A.ph A.kap i ((A.chart i).symm v) - 1) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hpt : ∀ u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0},
      ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) ≤ ENNReal.ofReal (1 / (a * b)) *
        (fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u)) := by
    intro u hu
    have huW : (A.chart i).symm u ∈ W :=
      ⟨(A.chart i).map_target (hball hu.1), by rw [Set.mem_preimage, (A.chart i).right_inv (hball hu.1)]; exact hu⟩
    rw [Set.indicator_of_mem huW]
    have h3 := (hrP u hu.1).2.2.1
    have h4 := (hrP u hu.1).2.2.2
    rw [Real.dist_eq] at h3 h4
    have h3' := abs_lt.1 h3
    have h4' := abs_lt.1 h4
    simp only [Function.comp] at h3' h4'
    have hA : a ≤ Real.exp (-A.ph la i ((A.chart i).symm u)) := Real.exp_le_exp.2 (by linarith)
    have hB : b ≤ Real.exp (A.ph A.kap i ((A.chart i).symm u)) := Real.exp_le_exp.2 (by linarith)
    have hX : 0 ≤ ‖F i ((A.chart i).symm u)‖ ^ 2 := by positivity
    show ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) ≤ ENNReal.ofReal (1 / (a * b)) *
      (ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm u))) *
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u))))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hab : a * b ≤ Real.exp (-A.ph la i ((A.chart i).symm u)) * Real.exp (A.ph A.kap i ((A.chart i).symm u)) :=
      mul_le_mul hA hB hb0.le (Real.exp_pos _).le
    have key : ‖F i ((A.chart i).symm u)‖ ^ 2 * (a * b) ≤
        ‖F i ((A.chart i).symm u)‖ ^ 2 * (Real.exp (-A.ph la i ((A.chart i).symm u)) *
          Real.exp (A.ph A.kap i ((A.chart i).symm u))) := mul_le_mul_of_nonneg_left hab hX
    calc ‖F i ((A.chart i).symm u)‖ ^ 2
        = 1 / (a * b) * (‖F i ((A.chart i).symm u)‖ ^ 2 * (a * b)) := by field_simp
      _ ≤ 1 / (a * b) * (‖F i ((A.chart i).symm u)‖ ^ 2 * (Real.exp (-A.ph la i ((A.chart i).symm u)) *
          Real.exp (A.ph A.kap i ((A.chart i).symm u)))) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = 1 / (a * b) * (Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
          (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u)))) := by ring
  calc ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0}, ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2)
      ≤ ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0}, ENNReal.ofReal (1 / (a * b)) *
        (fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u)) := setLIntegral_mono' hSo.measurableSet hpt
    _ = ENNReal.ofReal (1 / (a * b)) * ∫⁻ u in Metric.ball v r \ {u | fnG A w0 s De i u = 0},
        fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / (a * b)) * ∫⁻ u in (A.chart i).target,
        fnRho A i u * W.indicator (fun y => ENNReal.ofReal (‖F i y‖ ^ 2 * Real.exp (-A.ph la i y)))
          ((A.chart i).symm u) := by
          gcongr
          first
            | exact fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1
            | exact Measure.restrict_mono (fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1) le_rfl
            | exact lintegral_mono_set fun u (hu : u ∈ Metric.ball v r \ {u | fnG A w0 s De i u = 0}) => hball hu.1
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hY
end ReciprocityTheory.L2DbarEstimates.Y
