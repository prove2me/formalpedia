-- Prove2me | solution 1 for RoughSurfaceScattering.vCorr_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T01:21:02.984575+00:00
-- url     : https://prove2.me/submissions/372c66a8-fb39-4375-aefb-f49a95f249fc

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_frontier_hausdorff_finite
import Theorems.Thm_RoughSurfaceScattering_outwardNormal_continuousOn

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 1
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 1
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma dipole0_continuousOn (z ν : R2) :
    ContinuousOn (dipoleSource 0 z ν) {x | x ≠ z} := by
  have hfd := (phi0_contDiffOn z).continuousOn_fderiv_of_isOpen isOpen_ne le_rfl
  exact (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
    |>.congr (fun x _ => rfl)

lemma dipole0_formula (z ν x : R2) (hx : x ≠ z) :
    dipoleSource 0 z ν x =
      ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (x - z) ν / ‖x - z‖ ^ 2) : ℝ) : ℂ) := by
  have hy : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ‖x - z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hfun : (fun x' : R2 => Phi 0 x' z) =
      fun x' => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ) := by
    funext x'
    simp only [Phi, if_true, one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hsq : HasFDerivAt (fun x' : R2 => ‖x' - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ R2)) x :=
    ((hasFDerivAt_id x).sub_const z).norm_sq
  have hlog := (hsq.log hn).const_mul (-(1 / (4 * Real.pi)))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hlog
  unfold dipoleSource
  rw [hfun]
  rw [show (fun x' : R2 => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun x' => (-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2)) from rfl,
    hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, nsmul_eq_mul]
  congr 1
  field_simp
  ring

/-- The kernel `∂Φ₀(x,y)/∂ν(y)` is the Laplace dipole with pole `x`, evaluated at `y`. -/
lemma kernel_eq (x y v : R2) :
    fderiv ℝ (fun y' => Phi 0 x y') y v = dipoleSource 0 x v y := by
  have : (fun y' => Phi 0 x y') = fun y' => Phi 0 y' x := by
    funext y'; simp [Phi, norm_sub_rev]
  rw [this]; rfl

lemma norm_outwardNormal_le (D : Set R2) (y : R2) : ‖outwardNormal D y‖ ≤ 1 := by
  unfold outwardNormal
  split_ifs with h
  · exact h.choose_spec.1.le
  · simp

/-- derivative in `x` of `⟨y - x, n⟩ / ‖y - x‖²` -/
noncomputable def Lx (x y n : R2) : R2 →L[ℝ] ℝ :=
  (‖y - x‖ ^ 2)⁻¹ • ((2 * (@inner ℝ R2 _ (y - x) n / ‖y - x‖ ^ 2)) • innerSL ℝ (y - x) -
    innerSL ℝ n)

lemma kappa_hasFDerivAt (x y n : R2) (hxy : x ≠ y) :
    HasFDerivAt (fun x => @inner ℝ R2 _ (y - x) n / ‖y - x‖ ^ 2) (Lx x y n) x := by
  have hw : HasFDerivAt (fun x : R2 => y - x) (-(ContinuousLinearMap.id ℝ R2)) x :=
    (hasFDerivAt_id x).const_sub y
  have hp := hw.inner ℝ (hasFDerivAt_const n x)
  have hq := hw.norm_sq
  have hne : ‖y - x‖ ^ 2 ≠ 0 := by
    have : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    positivity
  have hd := hp.mul ((hasDerivAt_inv hne).comp_hasFDerivAt x hq)
  rw [show (fun x => @inner ℝ R2 _ (y - x) n / ‖y - x‖ ^ 2) =
    fun x => @inner ℝ R2 _ (y - x) n * (‖y - x‖ ^ 2)⁻¹ from by funext x; rw [div_eq_mul_inv]]
  refine hd.congr_fderiv ?_
  ext h
  simp [Lx, fderivInnerCLM_apply, inner_neg_left]
  have hw0 : ‖y - x‖ ≠ 0 := by
    have : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    exact norm_ne_zero_iff.mpr this
  rw [real_inner_comm h n]
  field_simp
  ring

lemma Lx_norm_le (x y n : R2) (hxy : x ≠ y) (hn : ‖n‖ ≤ 1) :
    ‖Lx x y n‖ ≤ 3 / ‖y - x‖ ^ 2 := by
  have hw0 : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  simp only [Lx, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    innerSL_apply_apply, smul_eq_mul]
  have h1 := abs_real_inner_le_norm (y - x) n
  have h2 := abs_real_inner_le_norm (y - x) h
  have h3 := abs_real_inner_le_norm n h
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
  have hh := norm_nonneg h
  have key : |2 * (@inner ℝ R2 _ (y - x) n / ‖y - x‖ ^ 2) * @inner ℝ R2 _ (y - x) h -
      @inner ℝ R2 _ n h| ≤ 3 * ‖h‖ := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_div, abs_two, abs_of_pos (by positivity : (0:ℝ) < ‖y - x‖ ^ 2)]
    have e1 : |@inner ℝ R2 _ (y - x) n| / ‖y - x‖ ^ 2 ≤ 1 / ‖y - x‖ := by
      rw [div_le_div_iff₀ (by positivity) hw0]
      nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (y - x))]
    calc 2 * (|@inner ℝ R2 _ (y - x) n| / ‖y - x‖ ^ 2) * |@inner ℝ R2 _ (y - x) h| +
          |@inner ℝ R2 _ n h|
        ≤ 2 * (1 / ‖y - x‖) * (‖y - x‖ * ‖h‖) + ‖n‖ * ‖h‖ := by gcongr
      _ ≤ 2 * (1 / ‖y - x‖) * (‖y - x‖ * ‖h‖) + 1 * ‖h‖ := by gcongr
      _ = 3 * ‖h‖ := by field_simp; ring
  calc (‖y - x‖ ^ 2)⁻¹ * |_| ≤ (‖y - x‖ ^ 2)⁻¹ * (3 * ‖h‖) := by gcongr
    _ = 3 / ‖y - x‖ ^ 2 * ‖h‖ := by ring

lemma Lx_continuousOn {X : Type*} [TopologicalSpace X] (fx fy fn : X → R2) (s : Set X)
    (hx : ContinuousOn fx s) (hy : ContinuousOn fy s) (hn : ContinuousOn fn s)
    (hne : ∀ t ∈ s, fx t ≠ fy t) : ContinuousOn (fun t => Lx (fx t) (fy t) (fn t)) s := by
  have hd : ContinuousOn (fun t => fy t - fx t) s := hy.sub hx
  have hsq : ContinuousOn (fun t => ‖fy t - fx t‖ ^ 2) s := (hd.norm).pow 2
  have hsq0 : ∀ t ∈ s, ‖fy t - fx t‖ ^ 2 ≠ 0 := fun t ht => by
    have : fy t - fx t ≠ 0 := sub_ne_zero.mpr (Ne.symm (hne t ht))
    positivity
  have hI := (innerSL ℝ (E := R2)).continuous
  unfold Lx
  refine (hsq.inv₀ hsq0).smul (ContinuousOn.sub ?_ (hI.comp_continuousOn hn))
  refine ContinuousOn.smul (f := fun t => (2:ℝ) * (@inner ℝ R2 _ (fy t - fx t) (fn t) / ‖fy t - fx t‖ ^ 2)) ?_ (hI.comp_continuousOn hd)
  exact continuousOn_const.mul ((hd.inner hn).div hsq hsq0)

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (μ : ℝ) (D0 : Set R2)
    (hD0 : IsC2LambdaDomain lam D0) (n0 xj yj : R2) (hxj : xj ∉ frontier D0)
    (hyj : yj ∉ frontier D0) :
    ContDiffOn ℝ 1 (vCorr μ D0 n0 xj yj) D0 := by
  set S := frontier D0 with hS
  set ν : Measure R2 := (Measure.hausdorffMeasure 1 : Measure R2).restrict S with hν
  have hSc : IsClosed S := isClosed_frontier
  have hScpt : IsCompact S := isCompact_of_isClosed_isBounded hSc
    (hD0.2.2.1.closure.subset frontier_subset_closure)
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (frontier_hausdorff_finite lam D0 hD0)⟩
  have hN := outwardNormal_continuousOn lam D0 hD0
  set nS := outwardNormal D0 with hnS
  set G : R2 → ℂ := fun y => dipoleSource 0 xj n0 y + dipoleSource 0 yj n0 y with hG
  have hGc : ContinuousOn G S :=
    ((dipole0_continuousOn xj n0).mono fun y hy h => hxj (h ▸ hy)).add
      ((dipole0_continuousOn yj n0).mono fun y hy h => hyj (h ▸ hy))
  obtain ⟨MG0, hMG0⟩ := hScpt.exists_bound_of_continuousOn hGc
  set MG := max MG0 0
  have hMG : ∀ y ∈ S, ‖G y‖ ≤ MG := fun y hy => (hMG0 y hy).trans (le_max_left _ _)
  have hMGnn : 0 ≤ MG := le_max_right _ _
  set c1 : ℝ := -(1 / (2 * Real.pi)) with hc1
  set c0 : ℂ := ((2 * μ * (1 - μ) / (μ + 1) ^ 2 : ℝ) : ℂ)
  set Kexp : R2 → R2 → ℂ := fun x y =>
    ((c1 * (@inner ℝ R2 _ (y - x) (nS y) / ‖y - x‖ ^ 2) : ℝ) : ℂ) * G y with hKexp
  set K' : R2 → R2 → (R2 →L[ℝ] ℂ) := fun x y =>
    G y • (Complex.ofRealCLM.comp (c1 • Lx x y (nS y))) with hK'
  set Vexp : R2 → ℂ := fun x => c0 * ∫ y, Kexp x y ∂ν with hVexp
  set U : Set R2 := Sᶜ
  have hU : IsOpen U := hSc.isOpen_compl
  have hderiv1 : ∀ y x : R2, x ≠ y → HasFDerivAt (fun x => Kexp x y) (K' x y) x := by
    intro y x hxy
    have h := (Complex.ofRealCLM.hasFDerivAt.comp x
      ((kappa_hasFDerivAt x y (nS y) hxy).const_mul c1)).mul_const (G y)
    exact h
  have hcompL := (ContinuousLinearMap.compL ℝ R2 ℝ ℂ Complex.ofRealCLM).continuous
  -- local geometry near a point off `S`
  have hgeom : ∀ x0 ∈ U, ∃ ε > (0 : ℝ), ∀ x ∈ ball x0 (ε / 2), ∀ y ∈ S, ε / 2 ≤ ‖y - x‖ := by
    intro x0 hx0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x0 hx0
    refine ⟨ε, hε, fun x hx y hy => ?_⟩
    have h1 : ε ≤ dist y x0 := by
      by_contra h; push Not at h
      exact hball (by rwa [mem_ball]) hy
    rw [mem_ball] at hx
    have := dist_triangle y x x0
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at this
    rw [dist_eq_norm] at h1 hx
    linarith
  have hne_of : ∀ (ε : ℝ) (x y : R2), 0 < ε → ε / 2 ≤ ‖y - x‖ → x ≠ y := fun ε x y hε h hxy => by
    rw [hxy, sub_self, norm_zero] at h; linarith
  have hKcont : ∀ x ∉ S, ContinuousOn (Kexp x) S := by
    intro x hx
    refine ContinuousOn.mul ?_ hGc
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    have hne : ∀ y ∈ S, ‖y - x‖ ^ 2 ≠ 0 := fun y hy => by
      have : y - x ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hy)
      positivity
    exact continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).inner hN).div
      (by fun_prop) hne)
  have hK'cont : ∀ x ∉ S, ContinuousOn (K' x) S := by
    intro x hx
    have hL := Lx_continuousOn (fun _ => x) id nS S continuousOn_const continuousOn_id hN
      (fun t ht h => hx (h ▸ ht))
    exact hGc.smul (hcompL.comp_continuousOn (hL.const_smul c1))
  have hK'bound : ∀ (ε : ℝ), 0 < ε → ∀ x y, y ∈ S → ε / 2 ≤ ‖y - x‖ →
      ‖K' x y‖ ≤ MG * (1 / (2 * Real.pi)) * (3 / (ε / 2) ^ 2) := by
    intro ε hε x y hy hd
    have hxy := hne_of ε x y hε hd
    have hdpos : 0 < ‖y - x‖ := by linarith
    have hLb := Lx_norm_le x y (nS y) hxy (norm_outwardNormal_le D0 y)
    have hL2 : ‖Lx x y (nS y)‖ ≤ 3 / (ε / 2) ^ 2 := hLb.trans (by gcongr)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    simp only [hK', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpi : |c1| = 1 / (2 * Real.pi) := by
      rw [hc1, abs_neg, abs_of_pos (by positivity)]
    rw [hpi]
    have hh := (Lx x y (nS y)).le_opNorm h
    rw [Real.norm_eq_abs] at hh
    have := hMG y hy
    calc ‖G y‖ * (1 / (2 * Real.pi) * |Lx x y (nS y) h|) ≤
        MG * (1 / (2 * Real.pi) * (3 / (ε / 2) ^ 2 * ‖h‖)) := by
          gcongr
          exact hh.trans (by gcongr)
      _ = _ := by ring
  have hKbound : ∀ (ε : ℝ), 0 < ε → ∀ x y, y ∈ S → ε / 2 ≤ ‖y - x‖ →
      ‖Kexp x y‖ ≤ 1 / (2 * Real.pi) * (2 / ε) * MG := by
    intro ε hε x y hy hd
    have hdpos : 0 < ‖y - x‖ := by linarith
    simp only [hKexp]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hin : |@inner ℝ R2 _ (y - x) (nS y)| ≤ ‖y - x‖ := by
      calc _ ≤ ‖y - x‖ * ‖nS y‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖y - x‖ * 1 := by gcongr; exact norm_outwardNormal_le D0 y
        _ = _ := mul_one _
    have hk : |c1 * (@inner ℝ R2 _ (y - x) (nS y) / ‖y - x‖ ^ 2)| ≤ 1 / (2 * Real.pi) * (2 / ε) := by
      have hpi : 0 < 1 / (2 * Real.pi) := by positivity
      rw [abs_mul, hc1, abs_neg, abs_of_pos hpi, abs_div, abs_of_pos (pow_pos hdpos 2)]
      refine mul_le_mul_of_nonneg_left ?_ hpi.le
      have h1 : |@inner ℝ R2 _ (y - x) (nS y)| / ‖y - x‖ ^ 2 ≤ 1 / ‖y - x‖ := by
        rw [div_le_div_iff₀ (pow_pos hdpos 2) hdpos]; nlinarith [hin]
      have h2 : 1 / ‖y - x‖ ≤ 2 / ε := by
        rw [div_le_div_iff₀ hdpos hε]; linarith
      exact h1.trans h2
    exact mul_le_mul hk (hMG y hy) (norm_nonneg _) (by positivity)
  -- differentiability of the explicit potential
  have hVd : ∀ x0 ∈ U, HasFDerivAt Vexp (c0 • ∫ y, K' x0 y ∂ν) x0 := by
    intro x0 hx0
    obtain ⟨ε, hε, hfar⟩ := hgeom x0 hx0
    have hx0S : x0 ∉ S := hx0
    have hball := ball_mem_nhds x0 (by positivity : 0 < ε / 2)
    have hnotS : ∀ x ∈ ball x0 (ε / 2), x ∉ S := fun x hx hxS => by
      have := hfar x hx x hxS; rw [sub_self, norm_zero] at this; linarith
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := Kexp) (F' := K')
      (x₀ := x0) (bound := fun _ => MG * (1 / (2 * Real.pi)) * (3 / (ε / 2) ^ 2)) hball
      (by
        filter_upwards [hball] with x hx
        exact (hKcont x (hnotS x hx)).aestronglyMeasurable hSc.measurableSet)
      (by
        refine Integrable.mono' (integrable_const (1 / (2 * Real.pi) * (2 / ε) * MG))
          ((hKcont x0 hx0S).aestronglyMeasurable hSc.measurableSet) ?_
        filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
        exact hKbound ε hε x0 y hy (hfar x0 (mem_ball_self (by positivity)) y hy))
      ((hK'cont x0 hx0S).aestronglyMeasurable hSc.measurableSet)
      (by
        filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
        intro x hx
        exact hK'bound ε hε x y hy (hfar x hx y hy))
      (integrable_const _)
      (by
        filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
        intro x hx
        exact hderiv1 y x (hne_of ε x y hε (hfar x hx y hy)))
    exact h.const_mul c0
  have hVc : ContDiffOn ℝ 1 Vexp U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hVd x hx).differentiableAt.differentiableWithinAt,
      by simp, contDiffOn_zero.mpr fun x0 hx0 => ?_⟩
    obtain ⟨ε, hε, hfar⟩ := hgeom x0 hx0
    have hball := ball_mem_nhds x0 (by positivity : 0 < ε / 2)
    have hnotS : ∀ x ∈ ball x0 (ε / 2), x ∉ S := fun x hx hxS => by
      have := hfar x hx x hxS; rw [sub_self, norm_zero] at this; linarith
    have hint : ContinuousAt (fun x => ∫ y, K' x y ∂ν) x0 := by
      apply continuousAt_of_dominated (bound := fun _ => MG * (1 / (2 * Real.pi)) * (3 / (ε / 2) ^ 2))
      · filter_upwards [hball] with x hx
        exact (hK'cont x (hnotS x hx)).aestronglyMeasurable hSc.measurableSet
      · filter_upwards [hball] with x hx
        filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
        exact hK'bound ε hε x y hy (hfar x hx y hy)
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
        have hyx0 : y ≠ x0 := fun h => hnotS x0 (mem_ball_self (by positivity)) (h ▸ hy)
        have hL := Lx_continuousOn id (fun _ => y) (fun _ => nS y) {x | x ≠ y} continuousOn_id
          continuousOn_const continuousOn_const (fun t ht => ht)
        have hc : ContinuousOn (fun x => K' x y) {x | x ≠ y} := by
          simp only [hK']
          exact (hcompL.comp_continuousOn (hL.const_smul c1)).const_smul (G y)
        exact hc.continuousAt (isOpen_ne.mem_nhds (Ne.symm hyx0))
    have hfd : (fderiv ℝ Vexp) =ᶠ[𝓝 x0] fun x => c0 • ∫ y, K' x y ∂ν := by
      filter_upwards [hU.mem_nhds hx0] with x hx
      exact (hVd x hx).fderiv
    exact ((hint.const_smul c0).congr hfd.symm).continuousWithinAt
  -- `vCorr` agrees with the explicit potential on `D₀`
  have hDU : D0 ⊆ U := fun x hx hxS => by
    rw [hS, hD0.1.frontier_eq] at hxS; exact hxS.2 hx
  refine (hVc.mono hDU).congr fun x hx => ?_
  have hxS : x ∉ S := hDU hx
  have hv : vCorr μ D0 n0 xj yj x = c0 * ∫ y, fderiv ℝ (fun y' => Phi 0 x y') y (nS y) * G y ∂ν :=
    rfl
  rw [hv]
  simp only [hVexp]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hSc.measurableSet] with y hy
  have hyx : y ≠ x := fun h => hxS (h ▸ hy)
  simp only [hKexp]
  rw [kernel_eq, dipole0_formula _ _ _ hyx]
