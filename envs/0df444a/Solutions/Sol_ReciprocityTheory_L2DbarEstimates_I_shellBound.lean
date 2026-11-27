-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.shellBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:50.790374+00:00
-- url     : https://prove2.me/submissions/0d42b9fa-27a0-44f0-b501-c55a3420b8dc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_norm_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_jac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_num
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_val
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hP : PolarStatement n) (hCov : CovStatement n) : ShellStatement n M := by
  intro z g ph ph2 r j p hn hz hg hph hph2 hr hp hJ
  obtain ⟨e, he, hpe⟩ := exists_chart n z hz p
  obtain ⟨ρ, hρ, hbt, hinj, hsmall⟩ := sh_local n z g hg p hp hJ e he hpe
  have hcph : Continuous ph :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph)).congr (fun x => by simp)
  have hcph2 : Continuous ph2 :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph2)).congr (fun x => by simp)
  have hcg : ∀ i, Continuous (g i) := fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))
  have hevc : Continuous (ev n g ph r) := by
    unfold ev
    exact ((continuous_finsetSum _ fun i _ => (hcg i).norm.pow 2).mul
      (Real.continuous_exp.comp hcph.neg)).div_const _
  have hy0 : e p ∈ e.target := e.map_source hpe
  have hsp : e.symm (e p) = p := e.left_inv hpe
  have hca : ContinuousAt (fun y => ph (e.symm y)) (e p) :=
    hcph.continuousAt.comp (e.continuousAt_symm hy0)
  have hcb : ContinuousAt (fun y => ph2 (e.symm y) + (j : ℝ) * ph (e.symm y)) (e p) :=
    (hcph2.continuousAt.comp (e.continuousAt_symm hy0)).add
      (continuousAt_const.mul (hcph.continuousAt.comp (e.continuousAt_symm hy0)))
  obtain ⟨δ0, hδ0, h0⟩ := Metric.continuousAt_iff.1 hca 1 one_pos
  set ρ1 := min ρ δ0 with hρ1
  have hρ1p : 0 < ρ1 := lt_min hρ hδ0
  refine ⟨e.source ∩ e ⁻¹' ball (e p) ρ1, e.isOpen_inter_preimage isOpen_ball,
    ⟨hpe, mem_ball_self hρ1p⟩, ?_⟩
  intro τ hτ
  set θ := min (τ / 10) (1 / 4) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hca θ hθ
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 hcb θ hθ
  set ρ' := min (min δ1 δ2) ρ1 with hρ'
  have hρ'p : 0 < ρ' := lt_min (lt_min hδ1 hδ2) hρ1p
  obtain ⟨κ, hκ, hκs⟩ := hsmall ρ' hρ'p
  set C0 := r ^ 2 * Real.exp (ph p + 1) with hC0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ^ 2 * C0 < κ ^ 2 := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin ?_
    apply nhdsWithin_le_nhds
    have ht : Tendsto (fun ε : ℝ => ε ^ 2 * C0) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 * C0)) :=
      ((continuous_pow 2).mul continuous_const).tendsto 0
    rw [zero_pow two_ne_zero, zero_mul] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with ε ⟨hε, hεκ⟩
  set G := shG n g e.symm with hGdef
  set A := (e.source ∩ e ⁻¹' ball (e p) ρ1) ∩ shell n g ph r ε with hAdef
  have hAm : MeasurableSet A := by
    refine (e.isOpen_inter_preimage isOpen_ball).measurableSet.inter ?_
    exact ((isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)).measurableSet
  set Fh : M → ℝ≥0∞ := fun x => ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G (z x) : V n →ₗ[ℂ] V n)‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) with hFh
  have hFm : Measurable Fh := by
    have hd : Measurable fun x => (fderiv ℂ G (z x)).det :=
      ContinuousLinearMap.continuous_det.measurable.comp
        ((measurable_fderiv ℂ G).comp hz.continuous.measurable)
    refine Measurable.ennreal_ofReal ?_
    refine ((hd.norm.pow_const 2).mul ?_).mul (hevc.measurable.pow_const _)
    exact (Real.continuous_exp.comp ((hcph2.neg).sub (continuous_const.mul hcph))).measurable
  set a := ε ^ 2 * r ^ 2 * Real.exp (ph p - θ) / 2 with hadef
  set b := ε ^ 2 * r ^ 2 * Real.exp (ph p + θ) with hbdef
  have ha : 0 < a := by positivity
  have hba : b / a = 2 * Real.exp (2 * θ) := by
    rw [div_eq_iff ha.ne', hadef, hbdef]
    have : Real.exp (ph p + θ) = Real.exp (2 * θ) * Real.exp (ph p - θ) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hab : a ≤ b := by
    have : 1 ≤ b / a := by rw [hba]; nlinarith [Real.add_one_le_exp (2 * θ)]
    rwa [le_div_iff₀ ha, one_mul] at this
  set Ann := {w : V n | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ b} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ with hK
  have hK0 : 0 ≤ K := by positivity
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set U' := ball (e p) ρ' with hU'
  have hU'1 : U' ⊆ ball (e p) ρ1 := ball_subset_ball (min_le_right _ _)
  have hU'ρ : U' ⊆ ball (e p) ρ := hU'1.trans (ball_subset_ball (min_le_left _ _))
  set h2f : V n → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G y : V n →ₗ[ℂ] V n)‖ ^ 2) * f (G y) with hh2

  have step1 : ∫⁻ x in (e.source ∩ e ⁻¹' ball (e p) ρ1) ∩ shell n g ph r ε,
      ENNReal.ofReal (‖jac n z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
        ev n g ph r x ^ (-(n : ℝ))) ∂vol n z = ∫⁻ x in A, Fh x ∂vol n z := by
    refine setLIntegral_congr_fun hAm (fun x hx => ?_)
    have hxs : x ∈ e.source := hx.1.1
    have hj := sh_jac n z g hg e he (e x) (e.map_source hxs)
    rw [e.left_inv hxs] at hj
    simp only [hFh, hj, he hxs, hGdef]

  have step2 : ∫⁻ x in A, Fh x ∂vol n z = ∫⁻ y in e.target, A.indicator Fh (e.symm y) := by
    rw [← lintegral_indicator hAm]
    exact lintegral_vol_chart n z hz e he _ (hFm.indicator hAm)
      (fun x hx => indicator_of_notMem (fun h => hx h.1.1) _)

  have step3 : ∫⁻ y in e.target, A.indicator Fh (e.symm y) ≤ ∫⁻ y in e.target, U'.indicator h2f y := by
    refine setLIntegral_mono' e.open_target.measurableSet (fun y hy => ?_)
    by_cases hA : e.symm y ∈ A
    swap
    · rw [indicator_of_notMem hA]; exact zero_le
    have hey : e (e.symm y) = y := e.right_inv hy
    have hzy : z (e.symm y) = y := chart_z_symm n z e he y hy
    have hyb : y ∈ ball (e p) ρ1 := by
      have h := hA.1.2
      simp only [mem_preimage, hey] at h
      exact h
    have hsh : ε ^ 2 / 2 ≤ ev n g ph r (e.symm y) ∧ ev n g ph r (e.symm y) ≤ ε ^ 2 := hA.2
    have hGS : ‖G y‖ ^ 2 = ∑ i, ‖g i (e.symm y)‖ ^ 2 := shG_norm_sq n g e.symm y
    set x := e.symm y with hxdef
    set S := ∑ i, ‖g i x‖ ^ 2 with hS
    have hevx : ev n g ph r x = S * Real.exp (-ph x) / r ^ 2 := rfl
    have hSev : S = ev n g ph r x * r ^ 2 * Real.exp (ph x) := by
      rw [hevx, Real.exp_neg]; field_simp
    have hevpos : 0 < ev n g ph r x := lt_of_lt_of_le (by positivity) hsh.1
    have hSpos : 0 < S := by
      rw [hSev]; exact mul_pos (mul_pos hevpos (by positivity)) (Real.exp_pos _)
    have hd0 : dist y (e p) < δ0 := lt_of_lt_of_le (mem_ball.1 hyb) (min_le_right _ _)
    have hph0 := h0 hd0
    rw [hsp, Real.dist_eq, abs_lt] at hph0
    have hSle : S ≤ ε ^ 2 * C0 := by
      rw [hSev, hC0]
      have h3 : Real.exp (ph x) ≤ Real.exp (ph p + 1) := Real.exp_le_exp.2 (by linarith)
      calc ev n g ph r x * r ^ 2 * Real.exp (ph x) ≤ ε ^ 2 * r ^ 2 * Real.exp (ph p + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hsh.2 (by positivity)) h3 (by positivity)
              (by positivity)
        _ = ε ^ 2 * (r ^ 2 * Real.exp (ph p + 1)) := by ring
    have hGk : ‖G y‖ < κ := by
      have h3 : ‖G y‖ ^ 2 < κ ^ 2 := by rw [hGS]; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hκ.le h3
    have hyU : y ∈ U' := hκs y (ball_subset_ball (min_le_left _ _) hyb) hGk
    have hd1 : dist y (e p) < δ1 :=
      lt_of_lt_of_le (mem_ball.1 hyU) ((min_le_left _ _).trans (min_le_left _ _))
    have hd2 : dist y (e p) < δ2 :=
      lt_of_lt_of_le (mem_ball.1 hyU) ((min_le_left _ _).trans (min_le_right _ _))
    have hph1 := h1 hd1
    have hph2' := h2 hd2
    rw [hsp, Real.dist_eq, abs_lt] at hph1 hph2'
    have hGA : G y ∈ Ann := by
      refine ⟨?_, ?_⟩ <;> rw [hGS, hSev]
      · calc a = ε ^ 2 / 2 * r ^ 2 * Real.exp (ph p - θ) := by rw [hadef]; ring
          _ ≤ ev n g ph r x * r ^ 2 * Real.exp (ph x) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hsh.1 (by positivity))
              (Real.exp_le_exp.2 (by linarith)) (by positivity) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hsh.2 (by positivity))
          (Real.exp_le_exp.2 (by linarith)) (by positivity) (by positivity)
    rw [indicator_of_mem hA, indicator_of_mem hyU]
    simp only [hFh, hh2, hfdef, indicator_of_mem hGA, hzy]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hGS, hevx, mul_assoc, sh_val n j S r (ph x) (ph2 x) hSpos hr]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hK]
    have hexp : Real.exp (-ph2 x - (j : ℝ) * ph x) ≤
        Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hSn : 0 ≤ S ^ (-(n : ℝ)) := Real.rpow_nonneg hSpos.le _
    calc r ^ (2 * n) * Real.exp (-ph2 x - (j : ℝ) * ph x) * S ^ (-(n : ℝ)) ≤
          r ^ (2 * n) * (Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ) * S ^ (-(n : ℝ)) := by
          gcongr
      _ = _ := by ring
  have step4 : ∫⁻ y in e.target, U'.indicator h2f y ≤ ∫⁻ w in G '' U', f w := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [lintegral_indicator measurableSet_ball]
    rw [hCov U' G f isOpen_ball
      (((shG_contDiffOn n z g hg e he).differentiableOn (by simp)).mono (hU'ρ.trans hbt))
      (hinj.mono hU'ρ) hfm]
  have step5 : ∫⁻ w in G '' U', f w ≤ ENNReal.ofReal K *
      ENNReal.ofReal (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * Real.log (b / a)) := by
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    rw [lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hP hn a b ha hab]
  rw [step1, step2]
  refine step3.trans (step4.trans (step5.trans ?_))
  rw [← ENNReal.ofReal_mul hK0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hba, Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp, hK]
  have hnum := sh_num τ hτ
  rw [← hθdef] at hnum
  have hX : 0 ≤ r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
      (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ)) := by positivity
  calc r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * (Real.log 2 + 2 * θ))
      = (r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ))) * (Real.exp θ * (Real.log 2 + 2 * θ)) := by ring
    _ ≤ (r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ))) * ((1 + τ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hnum hX
    _ = _ := by ring
end ReciprocityTheory.L2DbarEstimates.I
