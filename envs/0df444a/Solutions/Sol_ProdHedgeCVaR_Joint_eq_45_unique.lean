-- Prove2me | solution 1 for ProdHedgeCVaR.Joint.eq_45_unique
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:13:50.826864+00:00
-- url     : https://prove2.me/submissions/eec3c483-42e1-4300-967e-41949b0a697e

import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux45

open BlackScholesModel

noncomputable abbrev phi (z : ℝ) : ℝ := Real.exp (-z ^ 2 / 2)

lemma phi_eq : phi = fun z => Real.exp (-(1 / 2 : ℝ) * z ^ 2) := by
  funext z; unfold phi; congr 1; ring

lemma phi_int : Integrable phi := by
  rw [phi_eq]; exact integrable_exp_neg_mul_sq (by norm_num)

lemma phi_total : ∫ z, phi z = Real.sqrt (2 * Real.pi) := by
  rw [phi_eq, integral_gaussian]; congr 1; ring

lemma phi_norm_le (s : Set ℝ) (z : ℝ) : ‖s.indicator phi z‖ ≤ phi z :=
  (norm_indicator_le_norm_self _ _).trans (le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le))

lemma cdf_eq (x : ℝ) :
    stdNormalCDF x = (1 / Real.sqrt (2 * Real.pi)) * ∫ z, (Set.Iic x).indicator phi z := by
  unfold stdNormalCDF; rw [integral_indicator measurableSet_Iic]

lemma sqrt_pos' : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)

lemma cdf_tendsto_top : Tendsto stdNormalCDF atTop (𝓝 1) := by
  have h : Tendsto (fun x => ∫ z, (Set.Iic x).indicator phi z) atTop (𝓝 (∫ z, phi z)) := by
    refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ phi_int ?_
    · exact Eventually.of_forall (fun x => (phi_int.indicator measurableSet_Iic).aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => Eventually.of_forall (fun z => phi_norm_le _ z))
    · refine Eventually.of_forall (fun z => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop z] with x hx
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx)]
  have h2 : (1 / Real.sqrt (2 * Real.pi)) * ∫ z, phi z = 1 := by
    rw [phi_total]; have := sqrt_pos'; field_simp
  rw [← h2]
  have h3 := h.const_mul (1 / Real.sqrt (2 * Real.pi))
  refine h3.congr (fun x => ?_)
  rw [cdf_eq]

lemma cdf_tendsto_bot : Tendsto stdNormalCDF atBot (𝓝 0) := by
  have h : Tendsto (fun x => ∫ z, (Set.Iic x).indicator phi z) atBot (𝓝 (∫ _z : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ phi_int ?_
    · exact Eventually.of_forall (fun x => (phi_int.indicator measurableSet_Iic).aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => Eventually.of_forall (fun z => phi_norm_le _ z))
    · refine Eventually.of_forall (fun z => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_atBot z] with x hx
      rw [Set.indicator_of_notMem (fun h => absurd (Set.mem_Iic.mp h) (not_le.mpr hx))]
  have h3 := h.const_mul (1 / Real.sqrt (2 * Real.pi))
  rw [integral_zero, mul_zero] at h3
  refine h3.congr (fun x => ?_)
  rw [cdf_eq]

lemma cdf_sub (x y : ℝ) (hxy : x ≤ y) :
    stdNormalCDF y - stdNormalCDF x = (1 / Real.sqrt (2 * Real.pi)) * ∫ z in x..y, phi z := by
  unfold stdNormalCDF
  rw [← mul_sub, intervalIntegral.integral_of_le hxy, ← Set.Iic_union_Ioc_eq_Iic hxy,
    setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc phi_int.integrableOn
      phi_int.integrableOn]
  ring

lemma cdf_strictMono : StrictMono stdNormalCDF := by
  intro x y hxy
  have h := cdf_sub x y hxy.le
  have hpos : 0 < ∫ z in x..y, phi z :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (phi_int.intervalIntegrable)
      (fun z _ => Real.exp_pos _) hxy
  have hc : 0 < 1 / Real.sqrt (2 * Real.pi) := by have := sqrt_pos'; positivity
  nlinarith [mul_pos hc hpos]

lemma cdf_lip (x y : ℝ) : |stdNormalCDF x - stdNormalCDF y| ≤ |x - y| := by
  have hc1 : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := by
    have : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
    rw [div_le_one sqrt_pos']; exact this
  have hc0 : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by have := sqrt_pos'; positivity
  have key : ∀ a b : ℝ, a ≤ b → stdNormalCDF b - stdNormalCDF a ≤ b - a := by
    intro a b hab
    rw [cdf_sub a b hab]
    have hI : ∫ z in a..b, phi z ≤ ∫ _z in a..b, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hab phi_int.intervalIntegrable
        intervalIntegrable_const (fun z _ => ?_)
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hI
    have hI0 : 0 ≤ ∫ z in a..b, phi z :=
      intervalIntegral.integral_nonneg hab (fun z _ => (Real.exp_pos _).le)
    nlinarith
  rcases le_total x y with h | h
  · have := key x y h
    have := cdf_strictMono.monotone h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := key y x h
    have := cdf_strictMono.monotone h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma cdf_cont : Continuous stdNormalCDF :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]; exact cdf_lip a b).continuous

lemma cdf_nonneg (x : ℝ) : 0 ≤ stdNormalCDF x :=
  cdf_strictMono.monotone.le_of_tendsto cdf_tendsto_bot x

lemma cdf_lt_one (x : ℝ) : stdNormalCDF x < 1 :=
  lt_of_lt_of_le (cdf_strictMono (lt_add_one x))
    (cdf_strictMono.monotone.ge_of_tendsto cdf_tendsto_top (x + 1))

end Aux45

open Aux45 BlackScholesModel


lemma aux45_Z_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (ω : Ω) : 0 < M.Z ω := Real.exp_pos _

lemma aux45_W_meas {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) : Measurable M.W :=
  hM.W_meas.mono hM.G_le le_rfl

lemma aux45_A_meas {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) : Measurable M.A :=
  hM.A_meas.mono hM.G_le le_rfl

lemma aux45_Z_int {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) : Integrable M.Z M.P ∧ ∫ ω, M.Z ω ∂M.P = 1 := by
  haveI := hM.isProb
  have hZeq : ∀ ω, M.Z ω = Real.exp (-M.θ.eta ^ 2 * M.θ.T / 2) *
      Real.exp ((-M.θ.eta) * M.W ω) := by
    intro ω
    unfold Model.Z
    rw [← Real.exp_add]; congr 1; ring
  have hmgf := mgf_gaussianReal hM.W_law (-M.θ.eta)
  have hTnn : ((M.θ.T.toNNReal : NNReal) : ℝ) = M.θ.T :=
    Real.coe_toNNReal _ hM.params.T_pos.le
  have hexpInt : Integrable (fun ω => Real.exp ((-M.θ.eta) * M.W ω)) M.P := by
    have : 0 < mgf M.W M.P (-M.θ.eta) := by rw [hmgf]; exact Real.exp_pos _
    exact (mgf_pos_iff.mp this)
  constructor
  · have : M.Z = fun ω => Real.exp (-M.θ.eta ^ 2 * M.θ.T / 2) *
        Real.exp ((-M.θ.eta) * M.W ω) := funext hZeq
    rw [this]; exact hexpInt.const_mul _
  · simp_rw [hZeq]
    rw [integral_const_mul]
    have : ∫ ω, Real.exp ((-M.θ.eta) * M.W ω) ∂M.P = mgf M.W M.P (-M.θ.eta) := rfl
    rw [this, hmgf, hTnn, ← Real.exp_add]
    rw [show -M.θ.eta ^ 2 * M.θ.T / 2 + (0 * -M.θ.eta + M.θ.T * (-M.θ.eta) ^ 2 / 2) = 0 by ring]
    simp

lemma aux45_W_open {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) :
    0 < M.P (M.W ⁻¹' S) := by
  have hT : M.θ.T.toNNReal ≠ 0 := by
    simp [Real.toNNReal_eq_zero, not_le.mpr hM.params.T_pos]
  rw [← Measure.map_apply (aux45_W_meas M hM) hS.measurableSet, hM.W_law]
  have h2 : 0 < volume S := hS.measure_pos volume hne
  exact pos_iff_ne_zero.mpr (fun h => h2.ne' ((gaussianReal_absolutelyContinuous' 0 hT) h))

lemma aux45_Z_lt {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) {c : ℝ} (hc : 0 < c) :
    0 < M.P {ω | M.Z ω < c} := by
  have hη : -M.θ.eta ≠ 0 := neg_ne_zero.mpr hM.params.eta_ne
  have hTT : 0 ≤ M.θ.eta ^ 2 * M.θ.T := by have := hM.params.T_pos; positivity
  show 0 < M.P (M.W ⁻¹' {w | Real.exp (-M.θ.eta * w - M.θ.eta ^ 2 * M.θ.T / 2) < c})
  refine aux45_W_open M hM (isOpen_lt (by fun_prop) continuous_const) ?_
  refine ⟨(Real.log c - M.θ.eta ^ 2 * M.θ.T / 2 - 1) / (-M.θ.eta), ?_⟩
  show Real.exp (-M.θ.eta * ((Real.log c - M.θ.eta ^ 2 * M.θ.T / 2 - 1) / (-M.θ.eta))
    - M.θ.eta ^ 2 * M.θ.T / 2) < c
  rw [mul_div_cancel₀ _ hη]
  calc Real.exp _ < Real.exp (Real.log c) := Real.exp_lt_exp.mpr (by linarith)
    _ = c := Real.exp_log hc

lemma aux45_Z_gt {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) {c : ℝ} (hc : 0 < c) :
    0 < M.P {ω | c < M.Z ω} := by
  have hη : -M.θ.eta ≠ 0 := neg_ne_zero.mpr hM.params.eta_ne
  show 0 < M.P (M.W ⁻¹' {w | c < Real.exp (-M.θ.eta * w - M.θ.eta ^ 2 * M.θ.T / 2)})
  refine aux45_W_open M hM (isOpen_lt continuous_const (by fun_prop)) ?_
  refine ⟨(Real.log c + M.θ.eta ^ 2 * M.θ.T / 2 + 1) / (-M.θ.eta), ?_⟩
  show c < Real.exp (-M.θ.eta * ((Real.log c + M.θ.eta ^ 2 * M.θ.T / 2 + 1) / (-M.θ.eta))
    - M.θ.eta ^ 2 * M.θ.T / 2)
  rw [mul_div_cancel₀ _ hη]
  calc c = Real.exp (Real.log c) := (Real.exp_log hc).symm
    _ < Real.exp _ := Real.exp_lt_exp.mpr (by linarith)

theorem eq_45_unique {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∃! lam, M.IsLamC α lam) ∧
    (∀ lam, M.IsLamC α lam → 0 ≤ lam) ∧
    (M.beta 0 = 1 ∧ StrictAntiOn M.beta (Set.Ici 0) ∧ Tendsto M.beta atTop (𝓝 0)) ∧
    (∀ ω, Tendsto (fun Q => M.Delta Q ω) atTop (𝓝 1)) ∧
    ∀ lam, M.IsLamC α lam →
      (∃! Q, M.IsQC α lam Q) ∧
      StrictMono (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) ∧
      Tendsto (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) atTop
        (𝓝 ((M.θ.p + M.θ.c) * (1 - α))) ∧
      ∫ ω, min 1 (lam * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P ∧
      ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P = 1 - α := by
  haveI := hM.isProb
  obtain ⟨hZint, hZ1⟩ := aux45_Z_int M hM
  have hWm := aux45_W_meas M hM
  have hAm := aux45_A_meas M hM
  have hZpos := aux45_Z_pos M
  have hZmeas : Measurable M.Z := by unfold Model.Z; fun_prop
  have bint : ∀ lam : ℝ, Integrable (fun ω => max (1 - lam * M.Z ω) 0) M.P := fun lam =>
    ((integrable_const 1).sub (hZint.const_mul lam)).sup (integrable_const 0)
  have beta_lip : ∀ a b : ℝ, |M.beta a - M.beta b| ≤ |a - b| := by
    intro a b
    unfold Model.beta
    rw [← integral_sub (bint a) (bint b)]
    calc |∫ ω, (max (1 - a * M.Z ω) 0 - max (1 - b * M.Z ω) 0) ∂M.P|
        ≤ ∫ ω, |a - b| * M.Z ω ∂M.P := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (hZint.const_mul _) (Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]
          calc |max (1 - a * M.Z ω) 0 - max (1 - b * M.Z ω) 0|
              ≤ |(1 - a * M.Z ω) - (1 - b * M.Z ω)| := abs_max_sub_max_le_abs _ _ _
            _ = |a - b| * M.Z ω := by
              rw [show (1 - a * M.Z ω) - (1 - b * M.Z ω) = (b - a) * M.Z ω by ring, abs_mul,
                abs_of_pos (hZpos ω), abs_sub_comm]
      _ = |a - b| := by rw [integral_const_mul, hZ1, mul_one]
  have beta_cont : Continuous M.beta :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]; exact beta_lip a b).continuous
  have beta_zero : M.beta 0 = 1 := by simp [Model.beta]
  have beta_neg : ∀ lam : ℝ, lam < 0 → M.beta lam = 1 - lam := by
    intro lam hlam
    unfold Model.beta
    have : (fun ω => max (1 - lam * M.Z ω) 0) = fun ω => 1 - lam * M.Z ω := by
      funext ω; apply max_eq_left
      have : lam * M.Z ω < 0 := mul_neg_of_neg_of_pos hlam (hZpos ω)
      linarith
    rw [this, integral_sub (integrable_const 1) (hZint.const_mul lam), integral_const_mul, hZ1]
    simp
  have beta_anti : StrictAntiOn M.beta (Set.Ici 0) := by
    intro a ha b hb hab
    have hb0 : 0 < b := lt_of_le_of_lt ha hab
    have hg : 0 < ∫ ω, (max (1 - a * M.Z ω) 0 - max (1 - b * M.Z ω) 0) ∂M.P := by
      rw [integral_pos_iff_support_of_nonneg_ae (f := fun ω => max (1 - a * M.Z ω) 0 - max (1 - b * M.Z ω) 0) (Eventually.of_forall fun ω => ?_)
        ((bint a).sub (bint b))]
      · refine lt_of_lt_of_le (aux45_Z_lt M hM (c := 1 / b) (by positivity)) (measure_mono ?_)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        have h1 : b * M.Z ω < 1 := by
          rw [lt_div_iff₀ hb0] at hω; linarith
        have h2 : a * M.Z ω < b * M.Z ω := mul_lt_mul_of_pos_right hab (hZpos ω)
        rw [Function.mem_support, max_eq_left (by linarith), max_eq_left (by linarith)]
        exact (by linarith : (0 : ℝ) < _).ne'
      · have h1 : a * M.Z ω ≤ b * M.Z ω := mul_le_mul_of_nonneg_right hab.le (hZpos ω).le
        have := max_le_max (show 1 - b * M.Z ω ≤ 1 - a * M.Z ω by linarith) (le_refl (0 : ℝ))
        show (0 : ℝ) ≤ _
        linarith
    unfold Model.beta
    rw [integral_sub (bint a) (bint b)] at hg
    linarith
  have beta_lim : Tendsto M.beta atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := M.P) (l := atTop)
      (F := fun lam ω => max (1 - lam * M.Z ω) 0) (f := fun _ => (0 : ℝ)) (fun _ => 1)
      (Eventually.of_forall fun lam => (bint lam).aestronglyMeasurable) ?_ (integrable_const 1) ?_
    · rw [integral_zero] at h; exact h
    · filter_upwards [eventually_ge_atTop 0] with lam hlam
      exact Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [mul_nonneg hlam (hZpos ω).le]) zero_le_one
    · exact Eventually.of_forall fun ω => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (1 / M.Z ω)] with lam hlam
        have : 1 ≤ lam * M.Z ω := by rwa [div_le_iff₀ (hZpos ω)] at hlam
        rw [max_eq_right (by linarith)]
  have root_nonneg : ∀ lam, M.IsLamC α lam → 0 ≤ lam := by
    intro lam h
    by_contra hneg
    push_neg at hneg
    have := beta_neg lam hneg
    unfold Model.IsLamC at h
    linarith
  have hs : 0 < M.θ.sigT * Real.sqrt M.θ.T :=
    mul_pos hM.params.sigT_pos (Real.sqrt_pos.mpr hM.params.T_pos)
  have hpc : 0 < M.θ.p + M.θ.c := add_pos hM.params.p_pos hM.params.c_pos
  have Delta_eq : ∀ Q ω, M.Delta Q ω = stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) :=
    fun Q ω => rfl
  have Delta_top : ∀ ω, Tendsto (fun Q => M.Delta Q ω) atTop (𝓝 1) := by
    intro ω
    have h1 : Tendsto (fun Q : ℝ => Q - M.A ω) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-M.A ω) tendsto_id).congr
        (fun Q => (sub_eq_add_neg _ _).symm)
    exact cdf_tendsto_top.comp (h1.atTop_div_const hs)
  have Delta_bot : ∀ ω, Tendsto (fun Q => M.Delta Q ω) atBot (𝓝 0) := by
    intro ω
    have h1 : Tendsto (fun Q : ℝ => Q - M.A ω) atBot atBot :=
      (tendsto_atBot_add_const_right _ (-M.A ω) tendsto_id).congr
        (fun Q => (sub_eq_add_neg _ _).symm)
    exact cdf_tendsto_bot.comp (h1.atBot_div_const hs)
  have Delta_meas : ∀ Q, Measurable (M.Delta Q) := by
    intro Q
    have : M.Delta Q = fun ω => stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) := rfl
    rw [this]
    exact cdf_cont.measurable.comp (by fun_prop)
  have min_id : ∀ lam : ℝ, ∫ ω, min 1 (lam * M.Z ω) ∂M.P
      = ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P := by
    intro lam
    congr 1; funext ω
    rcases le_total 1 (lam * M.Z ω) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have one_sub : ∀ lam : ℝ, M.IsLamC α lam → ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P = 1 - α := by
    intro lam h
    rw [integral_sub (integrable_const 1) (bint lam)]
    have : ∫ ω, max (1 - lam * M.Z ω) 0 ∂M.P = α := h
    rw [this]; simp
  refine ⟨?_, root_nonneg, ⟨beta_zero, beta_anti, beta_lim⟩, Delta_top, ?_⟩
  · obtain ⟨L0, hL0, hL00⟩ :=
      ((beta_lim.eventually (gt_mem_nhds hα0)).and (eventually_ge_atTop 0)).exists
    obtain ⟨lam, hlam, hβ⟩ := intermediate_value_Icc' hL00 beta_cont.continuousOn
      (show α ∈ Set.Icc (M.beta L0) (M.beta 0) from ⟨hL0.le, by rw [beta_zero]; exact hα1.le⟩)
    refine ⟨lam, hβ, fun lam' h' => ?_⟩
    exact beta_anti.injOn (root_nonneg lam' h') hlam.1 (h'.trans hβ.symm)
  · intro lam hlam
    have hl0 := root_nonneg lam hlam
    have hlpos : 0 < lam := by
      rcases hl0.lt_or_eq with h | h
      · exact h
      · exfalso; unfold Model.IsLamC at hlam; rw [← h, beta_zero] at hlam; linarith
    have Fbd : ∀ Q ω, ‖min (lam * M.Z ω) (M.Delta Q ω)‖ ≤ 1 := by
      intro Q ω
      have h0 : 0 ≤ min (lam * M.Z ω) (M.Delta Q ω) :=
        le_min (mul_nonneg hl0 (hZpos ω).le) (by rw [Delta_eq]; exact cdf_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact (min_le_right _ _).trans (by rw [Delta_eq]; exact (cdf_lt_one _).le)
    have Fmeas : ∀ Q, AEStronglyMeasurable (fun ω => min (lam * M.Z ω) (M.Delta Q ω)) M.P :=
      fun Q => ((hZmeas.const_mul lam).min (Delta_meas Q)).aestronglyMeasurable
    have Fint : ∀ Q, Integrable (fun ω => min (lam * M.Z ω) (M.Delta Q ω)) M.P :=
      fun Q => (integrable_const (1 : ℝ)).mono' (Fmeas Q) (Eventually.of_forall (Fbd Q))
    set h : ℝ → ℝ := fun Q => ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P with hh
    have h_mono : StrictMono h := by
      intro Q1 Q2 hQ
      have hD : ∀ ω, M.Delta Q1 ω < M.Delta Q2 ω := by
        intro ω
        rw [Delta_eq, Delta_eq]
        exact cdf_strictMono (div_lt_div_of_pos_right (by linarith) hs)
      have hg : 0 < ∫ ω, (min (lam * M.Z ω) (M.Delta Q2 ω) - min (lam * M.Z ω) (M.Delta Q1 ω))
          ∂M.P := by
        rw [integral_pos_iff_support_of_nonneg_ae (f := fun ω => min (lam * M.Z ω) (M.Delta Q2 ω) - min (lam * M.Z ω) (M.Delta Q1 ω)) (Eventually.of_forall fun ω => ?_)
          ((Fint Q2).sub (Fint Q1))]
        · refine lt_of_lt_of_le (aux45_Z_gt M hM (c := 1 / lam) (by positivity)) (measure_mono ?_)
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω
          have h1 : 1 < lam * M.Z ω := by
            rw [div_lt_iff₀ hlpos] at hω; linarith
          have h2 : M.Delta Q2 ω < 1 := by rw [Delta_eq]; exact cdf_lt_one _
          rw [Function.mem_support, min_eq_right (by linarith), min_eq_right (by linarith [hD ω])]
          exact (by linarith [hD ω] : (0 : ℝ) < _).ne'
        · have := min_le_min (le_refl (lam * M.Z ω)) (hD ω).le
          show (0 : ℝ) ≤ _
          linarith
      rw [integral_sub (Fint Q2) (Fint Q1)] at hg
      show h Q1 < h Q2
      simp only [hh]
      linarith
    have h_cont : Continuous h := by
      refine continuous_of_dominated Fmeas (fun Q => Eventually.of_forall (Fbd Q))
        (integrable_const (1 : ℝ)) (Eventually.of_forall fun ω => ?_)
      have : (fun Q => min (lam * M.Z ω) (M.Delta Q ω)) =
          fun Q => min (lam * M.Z ω) (stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T))) :=
        rfl
      rw [this]
      exact continuous_const.min (cdf_cont.comp (by fun_prop))
    have h_top : Tendsto h atTop (𝓝 (1 - α)) := by
      have hlim := tendsto_integral_filter_of_dominated_convergence (μ := M.P) (l := atTop)
        (F := fun Q ω => min (lam * M.Z ω) (M.Delta Q ω)) (f := fun ω => min (lam * M.Z ω) 1)
        (fun _ => 1) (Eventually.of_forall Fmeas) (Eventually.of_forall fun Q =>
          Eventually.of_forall (Fbd Q)) (integrable_const 1)
        (Eventually.of_forall fun ω => tendsto_const_nhds.min (Delta_top ω))
      have : ∫ ω, min (lam * M.Z ω) 1 ∂M.P = 1 - α := by
        simp_rw [min_comm (lam * M.Z _) 1]
        rw [min_id, one_sub lam hlam]
      rw [this] at hlim
      exact hlim
    have h_bot : Tendsto h atBot (𝓝 0) := by
      have hlim := tendsto_integral_filter_of_dominated_convergence (μ := M.P) (l := atBot)
        (F := fun Q ω => min (lam * M.Z ω) (M.Delta Q ω)) (f := fun ω => min (lam * M.Z ω) 0)
        (fun _ => 1) (Eventually.of_forall Fmeas) (Eventually.of_forall fun Q =>
          Eventually.of_forall (Fbd Q)) (integrable_const 1)
        (Eventually.of_forall fun ω => tendsto_const_nhds.min (Delta_bot ω))
      have : ∫ ω, min (lam * M.Z ω) 0 ∂M.P = 0 := by
        have : (fun ω => min (lam * M.Z ω) 0) = fun _ => (0 : ℝ) := by
          funext ω; exact min_eq_right (mul_nonneg hl0 (hZpos ω).le)
        rw [this, integral_zero]
      rw [this] at hlim
      exact hlim
    have g_mono : StrictMono (fun Q => (M.θ.p + M.θ.c) * h Q) :=
      fun Q1 Q2 hQ => mul_lt_mul_of_pos_left (h_mono hQ) hpc
    refine ⟨?_, g_mono, h_top.const_mul _, min_id lam, one_sub lam hlam⟩
    have ht0 : 0 < M.θ.p * (1 - α) := mul_pos hM.params.p_pos (by linarith)
    have ht1 : M.θ.p * (1 - α) < (M.θ.p + M.θ.c) * (1 - α) :=
      mul_lt_mul_of_pos_right (by linarith [hM.params.c_pos]) (by linarith)
    have gbot : Tendsto (fun Q => (M.θ.p + M.θ.c) * h Q) atBot (𝓝 0) := by
      have := h_bot.const_mul (M.θ.p + M.θ.c); rwa [mul_zero] at this
    obtain ⟨Q1, hQ1⟩ := (gbot.eventually (gt_mem_nhds ht0)).exists
    obtain ⟨Q2, hQ2, hQ12⟩ :=
      (((h_top.const_mul (M.θ.p + M.θ.c)).eventually (lt_mem_nhds ht1)).and
        (eventually_ge_atTop Q1)).exists
    obtain ⟨Q, -, hQ⟩ := intermediate_value_Icc hQ12
      (continuous_const.mul h_cont).continuousOn
      (show M.θ.p * (1 - α) ∈ Set.Icc ((M.θ.p + M.θ.c) * h Q1) ((M.θ.p + M.θ.c) * h Q2) from
        ⟨hQ1.le, hQ2.le⟩)
    refine ⟨Q, hQ, fun Q' hQ' => g_mono.injective ?_⟩
    exact (hQ' : (M.θ.p + M.θ.c) * h Q' = M.θ.p * (1 - α)).trans hQ.symm

end ProdHedgeCVaR.Joint


namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (45), p. 18: the first equation β(λ) = α has a unique root λ°, which is non-negative,
because β decreases from 1 to 0 as λ increases from 0 to ∞; for it the second equation has a unique
root Q°, because ∆(Q) → 1 as Q → ∞ and the left-hand side increases to (p + c)(1 − α), since
E(1 ∧ λ°Z_T) = E[1 − (1 − λ°Z_T)⁺] = 1 − α. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∃! lam, M.IsLamC α lam) ∧
    (∀ lam, M.IsLamC α lam → 0 ≤ lam) ∧
    (M.beta 0 = 1 ∧ StrictAntiOn M.beta (Set.Ici 0) ∧ Tendsto M.beta atTop (𝓝 0)) ∧
    (∀ ω, Tendsto (fun Q => M.Delta Q ω) atTop (𝓝 1)) ∧
    ∀ lam, M.IsLamC α lam →
      (∃! Q, M.IsQC α lam Q) ∧
      StrictMono (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) ∧
      Tendsto (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) atTop
        (𝓝 ((M.θ.p + M.θ.c) * (1 - α))) ∧
      ∫ ω, min 1 (lam * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P ∧
      ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P = 1 - α := by
  apply @ProdHedgeCVaR.Joint.eq_45_unique <;> assumption

end ProdHedgeCVaR.Joint
