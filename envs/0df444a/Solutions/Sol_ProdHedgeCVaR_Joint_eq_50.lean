-- Prove2me | solution 1 for ProdHedgeCVaR.Joint.eq_50
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:21:39.206654+00:00
-- url     : https://prove2.me/submissions/852eb438-36d1-4eca-aa8d-9f86ec9d4230

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

namespace Aux45

open BlackScholesModel

lemma inv_le_iff {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    stdNormalInv u ≤ y ↔ u ≤ stdNormalCDF y := by
  have hne : ({x | stdNormalCDF x ≤ u} : Set ℝ).Nonempty := by
    obtain ⟨x, hx⟩ := (cdf_tendsto_bot.eventually (gt_mem_nhds hu0)).exists
    exact ⟨x, hx.le⟩
  have hbdd : BddAbove ({x | stdNormalCDF x ≤ u} : Set ℝ) := by
    obtain ⟨b, hb⟩ := (cdf_tendsto_top.eventually (lt_mem_nhds hu1)).exists
    refine ⟨b, fun x hx => ?_⟩
    by_contra h
    have h2 := cdf_strictMono (not_le.mp h)
    have hx2 : stdNormalCDF x ≤ u := hx
    linarith
  unfold stdNormalInv
  rw [csSup_le_iff hbdd hne]
  constructor
  · intro h
    by_contra hlt
    have hlt2 : stdNormalCDF y < u := not_le.mp hlt
    have hdpos : 0 < (u - stdNormalCDF y) / 2 := by linarith
    have hl := cdf_lip (y + (u - stdNormalCDF y) / 2) y
    rw [show y + (u - stdNormalCDF y) / 2 - y = (u - stdNormalCDF y) / 2 by ring,
      abs_of_pos hdpos] at hl
    have hmem : stdNormalCDF (y + (u - stdNormalCDF y) / 2) ≤ u := by
      have := (abs_le.mp hl).2; linarith
    have := h _ hmem
    linarith
  · intro h x hx
    by_contra hlt
    have h2 := cdf_strictMono (not_le.mp hlt)
    have hx2 : stdNormalCDF x ≤ u := hx
    linarith

lemma put_cases (Q : ℝ) (d : EReal) (hd : 0 ≤ d) :
    (d = ⊤ ∧ (max ((Q : EReal) - d) 0).toReal = 0) ∨
      ∃ r : ℝ, 0 ≤ r ∧ d = (r : EReal) ∧ (max ((Q : EReal) - d) 0).toReal = max (Q - r) 0 := by
  induction d using EReal.rec with
  | bot => exact absurd hd (by simp)
  | coe r =>
    right
    refine ⟨r, EReal.coe_nonneg.mp hd, rfl, ?_⟩
    rw [← EReal.coe_sub]
    rcases le_total (Q - r) 0 with h | h
    · rw [max_eq_right (by exact_mod_cast h), max_eq_right h]; exact EReal.toReal_zero
    · rw [max_eq_left (by exact_mod_cast h), max_eq_left h, EReal.toReal_coe]
  | top =>
    left
    refine ⟨rfl, ?_⟩
    rw [EReal.sub_top, max_eq_right bot_le]; exact EReal.toReal_zero

lemma put_nonneg (Q : ℝ) (d : EReal) (hd : 0 ≤ d) : 0 ≤ (max ((Q : EReal) - d) 0).toReal := by
  rcases put_cases Q d hd with ⟨-, h⟩ | ⟨r, -, -, h⟩ <;> rw [h]
  exact le_max_right _ _

lemma put_le (Q : ℝ) (d : EReal) (hd : 0 ≤ d) : (max ((Q : EReal) - d) 0).toReal ≤ max Q 0 := by
  rcases put_cases Q d hd with ⟨-, h⟩ | ⟨r, hr, -, h⟩ <;> rw [h]
  · exact le_max_right _ _
  · exact max_le_max (by linarith) le_rfl

lemma put_zero (Q : ℝ) (d : EReal) (hd : 0 ≤ d) (hlt : ¬ d ≤ (Q : EReal)) :
    (max ((Q : EReal) - d) 0).toReal = 0 := by
  rcases put_cases Q d hd with ⟨-, h⟩ | ⟨r, -, hdr, h⟩
  · exact h
  · rw [h]
    rw [hdr, EReal.coe_le_coe_iff, not_le] at hlt
    exact max_eq_right (by linarith)

end Aux45

theorem eq_47 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) :
    M.CC lamC QC ≤ M.θ.p * max QC 0 ∧
    (QC ≤ 0 → M.CC lamC QC = 0 ∧ M.θ.p * max QC 0 = 0) ∧
    (∀ Q lam : ℝ, 0 ≤ Q → 0 ≤ lam →
      {ω | M.DhatPos lam ω ≤ (Q : EReal)} = {ω | lam * M.Z ω ≤ M.Delta Q ω}) ∧
    (0 ≤ QC →
      M.CC lamC QC ≤ (M.θ.p + M.θ.c) * QC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω} ∧
      (M.θ.p + M.θ.c) * QC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω}
        ≤ M.θ.p * QC * (1 - α) / lamC ∧
      M.θ.p * QC * (1 - α) / lamC ≤ M.θ.p * QC) ∧
    (∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
        ≤ ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P ∧
      ∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
        = lamC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω}) := by
  haveI := hM.isProb
  obtain ⟨hZint, hZ1⟩ := aux45_Z_int M hM
  have hWm := aux45_W_meas M hM
  have hAm := aux45_A_meas M hM
  have hZpos := aux45_Z_pos M
  have hZmeas : Measurable M.Z := by unfold Model.Z; fun_prop
  have hs : 0 < M.θ.sigT * Real.sqrt M.θ.T :=
    mul_pos hM.params.sigT_pos (Real.sqrt_pos.mpr hM.params.T_pos)
  have hpc : 0 < M.θ.p + M.θ.c := add_pos hM.params.p_pos hM.params.c_pos
  have Delta_eq : ∀ Q ω, M.Delta Q ω = stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) :=
    fun Q ω => rfl
  have Delta_meas : ∀ Q, Measurable (M.Delta Q) := by
    intro Q
    have : M.Delta Q = fun ω => stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) := rfl
    rw [this]
    exact cdf_cont.measurable.comp (by fun_prop)
  have bint : ∀ lam : ℝ, Integrable (fun ω => max (1 - lam * M.Z ω) 0) M.P := fun lam =>
    ((integrable_const 1).sub (hZint.const_mul lam)).sup (integrable_const 0)
  have hlam_ge : 1 - α ≤ lamC := by
    have h1 : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P = 1 - α := by
      have : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P := by
        congr 1; funext ω
        rcases le_total 1 (lamC * M.Z ω) with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
      rw [this, integral_sub (integrable_const 1) (bint lamC)]
      have h2 : ∫ ω, max (1 - lamC * M.Z ω) 0 ∂M.P = α := hlamC
      rw [h2]; simp
    have h3 : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ≤ ∫ ω, lamC * M.Z ω ∂M.P :=
      integral_mono ((integrable_const 1).inf (hZint.const_mul lamC)) (hZint.const_mul lamC)
        (fun ω => min_le_right _ _)
    rw [integral_const_mul, hZ1, mul_one] at h3
    linarith
  have hlpos : 0 < lamC := by linarith
  have hd0 : ∀ lam ω, 0 ≤ M.DhatPos lam ω := fun _ _ => le_max_right _ _
  have hset : ∀ Q lam : ℝ, 0 ≤ Q → 0 ≤ lam →
      {ω | M.DhatPos lam ω ≤ (Q : EReal)} = {ω | lam * M.Z ω ≤ M.Delta Q ω} := by
    intro Q lam hQ hlam
    ext ω
    simp only [Set.mem_setOf_eq]
    have hD0 : 0 ≤ M.Delta Q ω := by rw [Delta_eq]; exact cdf_nonneg _
    have hD1 : M.Delta Q ω < 1 := by rw [Delta_eq]; exact cdf_lt_one _
    unfold Model.DhatPos Model.Dhat
    split_ifs with h1 h2
    · rw [max_eq_right bot_le]
      exact ⟨fun _ => h1.trans hD0, fun _ => EReal.coe_nonneg.mpr hQ⟩
    · rw [max_eq_left le_top]
      constructor
      · intro h; exact absurd (top_le_iff.mp h) (EReal.coe_ne_top Q)
      · intro h; exfalso; linarith
    · have hu0 : 0 < lam * M.Z ω := not_le.mp h1
      have hu1 : lam * M.Z ω < 1 := not_le.mp h2
      rw [max_le_iff, EReal.coe_le_coe_iff, Delta_eq, ← inv_le_iff hu0 hu1, le_div_iff₀ hs]
      constructor
      · rintro ⟨h, -⟩; linarith
      · intro h; exact ⟨by linarith, EReal.coe_nonneg.mpr hQ⟩
  have hb : QC ≤ 0 → M.CC lamC QC = 0 ∧ M.θ.p * max QC 0 = 0 := by
    intro hQ
    have hz : ∀ ω, M.putHat lamC QC ω = 0 := fun ω =>
      le_antisymm ((put_le QC _ (hd0 lamC ω)).trans (by rw [max_eq_right hQ]))
        (put_nonneg QC _ (hd0 lamC ω))
    refine ⟨?_, by rw [max_eq_right hQ, mul_zero]⟩
    unfold Model.CC Model.EM
    simp [hz]
  set S := {ω | lamC * M.Z ω ≤ M.Delta QC ω} with hSdef
  have hS : MeasurableSet S := measurableSet_le (hZmeas.const_mul _) (Delta_meas QC)
  have hind : (fun ω => lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0)) =
      S.indicator (fun ω => lamC * M.Z ω) := by
    funext ω
    by_cases h : lamC * M.Z ω ≤ M.Delta QC ω
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ S from h), mul_one]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ S from h), mul_zero]
  have hPM : M.PM S = ∫ ω in S, M.Z ω ∂M.P := rfl
  have he2 : ∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
      = lamC * M.PM S := by
    rw [hind, integral_indicator hS, integral_const_mul, hPM]
  have Fint : Integrable (fun ω => min (lamC * M.Z ω) (M.Delta QC ω)) M.P := by
    refine (integrable_const (1 : ℝ)).mono'
      ((hZmeas.const_mul lamC).min (Delta_meas QC)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have h0 : 0 ≤ min (lamC * M.Z ω) (M.Delta QC ω) :=
      le_min (mul_nonneg hlpos.le (hZpos ω).le) (by rw [Delta_eq]; exact cdf_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact (min_le_right _ _).trans (by rw [Delta_eq]; exact (cdf_lt_one _).le)
  have he1 : ∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
      ≤ ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P := by
    rw [hind]
    refine integral_mono ((hZint.const_mul lamC).indicator hS) Fint (fun ω => ?_)
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, min_eq_left (show lamC * M.Z ω ≤ M.Delta QC ω from h)]
    · rw [Set.indicator_of_notMem h]
      exact le_min (mul_nonneg hlpos.le (hZpos ω).le) (by rw [Delta_eq]; exact cdf_nonneg _)
  have hd : 0 ≤ QC →
      M.CC lamC QC ≤ (M.θ.p + M.θ.c) * QC * M.PM S ∧
      (M.θ.p + M.θ.c) * QC * M.PM S ≤ M.θ.p * QC * (1 - α) / lamC ∧
      M.θ.p * QC * (1 - α) / lamC ≤ M.θ.p * QC := by
    intro hQ
    refine ⟨?_, ?_, ?_⟩
    · have hle : ∫ ω, M.Z ω * M.putHat lamC QC ω ∂M.P ≤ ∫ ω, QC * S.indicator M.Z ω ∂M.P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => ?_)
          ((hZint.indicator hS).const_mul QC) (Eventually.of_forall fun ω => ?_)
        · exact mul_nonneg (hZpos ω).le (put_nonneg QC _ (hd0 lamC ω))
        · show M.Z ω * M.putHat lamC QC ω ≤ QC * S.indicator M.Z ω
          by_cases h : ω ∈ S
          · rw [Set.indicator_of_mem h, mul_comm QC]
            refine mul_le_mul_of_nonneg_left ?_ (hZpos ω).le
            exact (put_le QC _ (hd0 lamC ω)).trans (le_of_eq (max_eq_left hQ))
          · rw [Set.indicator_of_notMem h, mul_zero]
            have hn : ¬ M.DhatPos lamC ω ≤ (QC : EReal) := by
              intro h2
              have hmem : ω ∈ {ω | M.DhatPos lamC ω ≤ (QC : EReal)} := h2
              rw [hset QC lamC hQ hlpos.le] at hmem
              exact h hmem
            have hp0 : M.putHat lamC QC ω = 0 := put_zero QC _ (hd0 lamC ω) hn
            rw [hp0, mul_zero]
      rw [integral_const_mul, integral_indicator hS, ← hPM] at hle
      unfold Model.CC Model.EM
      calc (M.θ.p + M.θ.c) * ∫ ω, M.Z ω * M.putHat lamC QC ω ∂M.P
          ≤ (M.θ.p + M.θ.c) * (QC * M.PM S) := mul_le_mul_of_nonneg_left hle hpc.le
        _ = (M.θ.p + M.θ.c) * QC * M.PM S := by ring
    · have hq : (M.θ.p + M.θ.c) * ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P
          = M.θ.p * (1 - α) := hQC
      have H : (M.θ.p + M.θ.c) * (lamC * M.PM S) ≤ M.θ.p * (1 - α) := by
        rw [← he2, ← hq]; exact mul_le_mul_of_nonneg_left he1 hpc.le
      rw [le_div_iff₀ hlpos]
      have hmul := mul_le_mul_of_nonneg_left H hQ
      calc (M.θ.p + M.θ.c) * QC * M.PM S * lamC
          = QC * ((M.θ.p + M.θ.c) * (lamC * M.PM S)) := by ring
        _ ≤ QC * (M.θ.p * (1 - α)) := hmul
        _ = M.θ.p * QC * (1 - α) := by ring
    · rw [div_le_iff₀ hlpos]
      have hpq : 0 ≤ M.θ.p * QC := mul_nonneg hM.params.p_pos.le hQ
      have hmul := mul_le_mul_of_nonneg_left hlam_ge hpq
      linarith
  refine ⟨?_, hb, hset, hd, he1, he2⟩
  rcases le_total QC 0 with hQ | hQ
  · rw [(hb hQ).1, (hb hQ).2]
  · obtain ⟨h1, h2, h3⟩ := hd hQ
    rw [max_eq_left hQ]
    linarith


theorem eq_50 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) :
    (∀ m, M.Eq35 m (max QC 0) lamC ↔ m = M.mC lamC QC) ∧
    M.mC lamC QC = M.θ.p * max QC 0 - M.CC lamC QC
      + (M.θ.C - M.CC lamC QC) * (1 / M.PM {ω | lamC * M.Z ω ≤ 1} - 1) ∧
    (M.CC lamC QC ≤ M.θ.C →
      0 ≤ M.mC lamC QC ∧ 0 ≤ M.mC lamC QC - M.θ.p * max QC 0 + M.θ.C) := by
  haveI := hM.isProb
  obtain ⟨hZint, hZ1⟩ := aux45_Z_int M hM
  have hZpos := aux45_Z_pos M
  have hWm := aux45_W_meas M hM
  have hZmeas : Measurable M.Z := by unfold Model.Z; fun_prop
  have hpc : 0 < M.θ.p + M.θ.c := add_pos hM.params.p_pos hM.params.c_pos
  have hCC : M.CC lamC QC ≤ M.θ.p * max QC 0 := (eq_47 M hM α hα0 hα1 lamC QC hlamC hQC).1
  have bint : ∀ lam : ℝ, Integrable (fun ω => max (1 - lam * M.Z ω) 0) M.P := fun lam =>
    ((integrable_const 1).sub (hZint.const_mul lam)).sup (integrable_const 0)
  have hlam_ge : 1 - α ≤ lamC := by
    have h1 : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P = 1 - α := by
      have : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P := by
        congr 1; funext ω
        rcases le_total 1 (lamC * M.Z ω) with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]; ring
      rw [this, integral_sub (integrable_const 1) (bint lamC)]
      have h2 : ∫ ω, max (1 - lamC * M.Z ω) 0 ∂M.P = α := hlamC
      rw [h2]; simp
    have h3 : ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ≤ ∫ ω, lamC * M.Z ω ∂M.P :=
      integral_mono ((integrable_const 1).inf (hZint.const_mul lamC)) (hZint.const_mul lamC)
        (fun ω => min_le_right _ _)
    rw [integral_const_mul, hZ1, mul_one] at h3
    linarith
  have hlpos : 0 < lamC := by linarith
  have hT : MeasurableSet {ω | lamC * M.Z ω ≤ 1} :=
    measurableSet_le (hZmeas.const_mul _) measurable_const
  have hP0pos : 0 < M.PM {ω | lamC * M.Z ω ≤ 1} := by
    show 0 < ∫ ω in {ω | lamC * M.Z ω ≤ 1}, M.Z ω ∂M.P
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun ω => (hZpos ω).le) hZint.integrableOn]
    refine lt_of_lt_of_le (aux45_Z_lt M hM (c := 1 / lamC) (by positivity)) (measure_mono ?_)
    intro ω hω
    have hω' : M.Z ω < 1 / lamC := hω
    refine ⟨(hZpos ω).ne', ?_⟩
    show lamC * M.Z ω ≤ 1
    rw [lt_div_iff₀ hlpos] at hω'
    linarith
  have hP0le : M.PM {ω | lamC * M.Z ω ≤ 1} ≤ 1 := by
    show ∫ ω in {ω | lamC * M.Z ω ≤ 1}, M.Z ω ∂M.P ≤ 1
    rw [← hZ1]
    exact setIntegral_le_integral hZint (Eventually.of_forall fun ω => (hZpos ω).le)
  have hP0ne : M.PM {ω | lamC * M.Z ω ≤ 1} ≠ 0 := hP0pos.ne'
  have hd0 : ∀ lam ω, 0 ≤ M.DhatPos lam ω := fun _ _ => le_max_right _ _
  have hput : ∀ ω, M.putHat lamC (max QC 0) ω = M.putHat lamC QC ω := by
    intro ω
    rcases le_total QC 0 with h | h
    · rw [max_eq_right h]
      have e1 : M.putHat lamC 0 ω = 0 :=
        le_antisymm ((put_le 0 _ (hd0 lamC ω)).trans (le_of_eq (max_self 0)))
          (put_nonneg 0 _ (hd0 lamC ω))
      have e2 : M.putHat lamC QC ω = 0 :=
        le_antisymm ((put_le QC _ (hd0 lamC ω)).trans (le_of_eq (max_eq_right h)))
          (put_nonneg QC _ (hd0 lamC ω))
      rw [e1, e2]
    · rw [max_eq_left h]
  have hEM : M.EM (M.putHat lamC (max QC 0)) = M.EM (M.putHat lamC QC) := by
    unfold Model.EM; congr 1; funext ω; rw [hput ω]
  have hCCdef : M.CC lamC QC = (M.θ.p + M.θ.c) * M.EM (M.putHat lamC QC) := rfl
  have hform : M.mC lamC QC = M.θ.p * max QC 0 - M.CC lamC QC
      + (M.θ.C - M.CC lamC QC) * (1 / M.PM {ω | lamC * M.Z ω ≤ 1} - 1) := by
    unfold Model.mC; ring
  refine ⟨fun m => ?_, hform, fun hC => ?_⟩
  · have hKv : (M.θ.p + M.θ.c) * M.K m (max QC 0) = m + M.θ.C + M.θ.c * max QC 0 :=
      mul_div_cancel₀ _ hpc.ne'
    have hK : (M.θ.p + M.θ.c) * ((M.K m (max QC 0) - max QC 0) * M.PM {ω | lamC * M.Z ω ≤ 1}
          + M.EM (M.putHat lamC (max QC 0)))
        = (m + M.θ.C - M.θ.p * max QC 0) * M.PM {ω | lamC * M.Z ω ≤ 1} + M.CC lamC QC := by
      rw [hEM, hCCdef]
      linear_combination M.PM {ω | lamC * M.Z ω ≤ 1} * hKv
    unfold Model.Eq35 Model.mC
    rw [hK]
    constructor
    · rintro ⟨-, h⟩
      have h2 : (M.θ.C - M.CC lamC QC) / M.PM {ω | lamC * M.Z ω ≤ 1}
          = m + M.θ.C - M.θ.p * max QC 0 := by
        rw [div_eq_iff hP0ne]; linarith
      linarith
    · intro h
      refine ⟨hlpos.le, ?_⟩
      have h2 : (m + M.θ.C - M.θ.p * max QC 0) * M.PM {ω | lamC * M.Z ω ≤ 1}
          = M.θ.C - M.CC lamC QC := by
        rw [h, show M.θ.p * max QC 0 - M.θ.C + (M.θ.C - M.CC lamC QC) /
            M.PM {ω | lamC * M.Z ω ≤ 1} + M.θ.C - M.θ.p * max QC 0
            = (M.θ.C - M.CC lamC QC) / M.PM {ω | lamC * M.Z ω ≤ 1} by ring]
        exact div_mul_cancel₀ _ hP0ne
      linarith
  · have hinv : 1 ≤ 1 / M.PM {ω | lamC * M.Z ω ≤ 1} := by
      rw [le_div_iff₀ hP0pos]; linarith
    have hCm : 0 ≤ M.θ.C - M.CC lamC QC := by linarith
    refine ⟨?_, ?_⟩
    · rw [hform]
      have := mul_nonneg hCm (show (0 : ℝ) ≤ 1 / M.PM {ω | lamC * M.Z ω ≤ 1} - 1 by linarith)
      linarith
    · unfold Model.mC
      have := div_nonneg hCm hP0pos.le
      linarith

end ProdHedgeCVaR.Joint


namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (50), p. 19: the solution m of (35) with Q = (Q°)⁺ and λ = λ° is unique and
equals m° = p(Q°)⁺ − C + (C − C°)/P^M(λ°Z_T ≤ 1)
    = p(Q°)⁺ − C° + (C − C°)(1/P^M(λ°Z_T ≤ 1) − 1);
if C ≥ C°, then m° ≥ 0 and the constraint m° − p(Q°)⁺ + C ≥ 0 of (36) is met. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) :
    (∀ m, M.Eq35 m (max QC 0) lamC ↔ m = M.mC lamC QC) ∧
    M.mC lamC QC = M.θ.p * max QC 0 - M.CC lamC QC
      + (M.θ.C - M.CC lamC QC) * (1 / M.PM {ω | lamC * M.Z ω ≤ 1} - 1) ∧
    (M.CC lamC QC ≤ M.θ.C →
      0 ≤ M.mC lamC QC ∧ 0 ≤ M.mC lamC QC - M.θ.p * max QC 0 + M.θ.C) := by
  apply @ProdHedgeCVaR.Joint.eq_50 <;> assumption

end ProdHedgeCVaR.Joint
