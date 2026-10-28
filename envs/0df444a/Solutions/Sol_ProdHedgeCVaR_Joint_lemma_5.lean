-- Prove2me | solution 1 for ProdHedgeCVaR.Joint.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:28:56.862794+00:00
-- url     : https://prove2.me/submissions/5bd0e0c5-9b8f-44cf-b412-d2443dd1106f

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


namespace Aux45

open BlackScholesModel

lemma cdf_inv {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : stdNormalCDF (stdNormalInv u) = u := by
  have h1 : u ≤ stdNormalCDF (stdNormalInv u) := (inv_le_iff hu0 hu1 _).mp le_rfl
  refine le_antisymm ?_ h1
  by_contra hlt
  have hgt : u < stdNormalCDF (stdNormalInv u) := not_le.mp hlt
  have hdpos : 0 < (stdNormalCDF (stdNormalInv u) - u) / 2 := by linarith
  have hl := cdf_lip (stdNormalInv u - (stdNormalCDF (stdNormalInv u) - u) / 2) (stdNormalInv u)
  rw [show stdNormalInv u - (stdNormalCDF (stdNormalInv u) - u) / 2 - stdNormalInv u
      = -((stdNormalCDF (stdNormalInv u) - u) / 2) by ring, abs_neg, abs_of_pos hdpos] at hl
  have hle : u ≤ stdNormalCDF (stdNormalInv u - (stdNormalCDF (stdNormalInv u) - u) / 2) := by
    have := (abs_le.mp hl).1; linarith
  have := (inv_le_iff hu0 hu1 _).mpr hle
  linarith

lemma invE_mono : Monotone stdNormalInvE := by
  intro a b hab
  unfold stdNormalInvE
  by_cases ha0 : a ≤ 0
  · rw [if_pos ha0]; exact bot_le
  by_cases hb1 : 1 ≤ b
  · rw [if_neg (show ¬ b ≤ 0 by linarith), if_pos hb1]; exact le_top
  have ha1 : ¬ 1 ≤ a := fun h => hb1 (h.trans hab)
  have hb0 : ¬ b ≤ 0 := fun h => ha0 (hab.trans h)
  rw [if_neg ha0, if_neg ha1, if_neg hb0, if_neg hb1, EReal.coe_le_coe_iff]
  have hb0' : 0 < b := not_le.mp hb0
  have hb1' : b < 1 := not_le.mp hb1
  rw [inv_le_iff (not_le.mp ha0) (not_le.mp ha1), cdf_inv hb0' hb1']
  exact hab

noncomputable def PhiE (e : EReal) : ℝ :=
  if e = ⊥ then 0 else if e = ⊤ then 1 else stdNormalCDF e.toReal

lemma PhiE_bot : PhiE ⊥ = 0 := by simp [PhiE]
lemma PhiE_top : PhiE ⊤ = 1 := by simp [PhiE]
lemma PhiE_coe (r : ℝ) : PhiE (r : EReal) = stdNormalCDF r := by simp [PhiE]

lemma cdf_le_one (x : ℝ) : stdNormalCDF x ≤ 1 := (cdf_lt_one x).le

lemma PhiE_mono : Monotone PhiE := by
  intro a b hab
  induction a using EReal.rec with
  | bot =>
    rw [PhiE_bot]
    induction b using EReal.rec with
    | bot => rw [PhiE_bot]
    | coe s => rw [PhiE_coe]; exact cdf_nonneg s
    | top => rw [PhiE_top]; exact zero_le_one
  | coe r =>
    induction b using EReal.rec with
    | bot => exact absurd hab (by simp)
    | coe s =>
      rw [PhiE_coe, PhiE_coe]
      exact cdf_strictMono.monotone (EReal.coe_le_coe_iff.mp hab)
    | top => rw [PhiE_coe, PhiE_top]; exact cdf_le_one r
  | top =>
    induction b using EReal.rec with
    | bot => exact absurd hab (by simp)
    | coe s => exact absurd hab (by simp)
    | top => exact le_rfl

lemma PhiE_nonneg (e : EReal) : 0 ≤ PhiE e := by
  have := PhiE_mono (bot_le : ⊥ ≤ e); rwa [PhiE_bot] at this

lemma PhiE_le_one (e : EReal) : PhiE e ≤ 1 := by
  have := PhiE_mono (le_top : e ≤ ⊤); rwa [PhiE_top] at this

lemma PhiE_invE {u : ℝ} (hu : 0 ≤ u) : PhiE (stdNormalInvE u) = min 1 u := by
  unfold stdNormalInvE
  by_cases h0 : u ≤ 0
  · rw [if_pos h0, PhiE_bot, show u = 0 by linarith]; simp
  by_cases h1 : 1 ≤ u
  · rw [if_neg h0, if_pos h1, PhiE_top, min_eq_left h1]
  rw [if_neg h0, if_neg h1, PhiE_coe, cdf_inv (not_le.mp h0) (not_le.mp h1),
    min_eq_right (not_le.mp h1).le]

lemma gauss_Iic (r : ℝ) : gaussianReal 0 1 (Set.Iic r) = ENNReal.ofReal (stdNormalCDF r) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  congr 1
  unfold stdNormalCDF
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div]

lemma gauss_le (e : EReal) :
    gaussianReal 0 1 {a : ℝ | (a : EReal) ≤ e} = ENNReal.ofReal (PhiE e) := by
  induction e using EReal.rec with
  | bot =>
    have : {a : ℝ | (a : EReal) ≤ ⊥} = ∅ := by ext a; simp
    rw [this, PhiE_bot]; simp
  | coe r =>
    have : {a : ℝ | (a : EReal) ≤ r} = Set.Iic r := by ext a; simp
    rw [this, PhiE_coe, gauss_Iic]
  | top =>
    have : {a : ℝ | (a : EReal) ≤ ⊤} = Set.univ := by ext a; simp
    rw [this, PhiE_top]; simp

end Aux45

lemma aux45_prob_xi_le {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (c : Ω → EReal) (hc : Measurable[M.G] c) :
    M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤ c ω} = ∫ ω, PhiE (c ω) ∂M.P := by
  haveI := hM.isProb
  have hc' : Measurable c := hc.mono hM.G_le le_rfl
  have hind : IndepFun M.xi c M.P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right hM.xi_indep hc.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hM.xi_meas.aemeasurable
    hc'.aemeasurable).mp hind
  have hS : MeasurableSet {p : ℝ × EReal | ((p.1 : ℝ) : EReal) ≤ p.2} :=
    measurableSet_le (measurable_coe_real_ereal.comp measurable_fst) measurable_snd
  have hPhi : Measurable PhiE := PhiE_mono.measurable
  have h1 : M.P {ω | ((M.xi ω : ℝ) : EReal) ≤ c ω}
      = ∫⁻ ω, ENNReal.ofReal (PhiE (c ω)) ∂M.P := by
    have e1 : {ω | ((M.xi ω : ℝ) : EReal) ≤ c ω}
        = (fun ω => (M.xi ω, c ω)) ⁻¹' {p : ℝ × EReal | ((p.1 : ℝ) : EReal) ≤ p.2} := rfl
    rw [e1, ← Measure.map_apply (hM.xi_meas.prodMk hc') hS, hmap, Measure.prod_apply_symm hS,
      hM.xi_law]
    have hfun : (fun y : EReal => gaussianReal 0 1 ((fun x => (x, y)) ⁻¹'
        {p : ℝ × EReal | ((p.1 : ℝ) : EReal) ≤ p.2})) = fun y => ENNReal.ofReal (PhiE y) :=
      funext fun y => gauss_le y
    rw [hfun]
    exact lintegral_map (ENNReal.measurable_ofReal.comp hPhi) hc'
  rw [measureReal_def, h1, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => PhiE_nonneg _) (hPhi.comp hc').aestronglyMeasurable]

theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : ℝ) :
    M.P.real {ω | ((M.D ω : ℝ) : EReal) ≤ M.Dhat lam ω} = 1 - M.beta lam ∧
    1 - M.beta lam = lam - M.psi lam ∧
    lam * M.PM {ω | lam * M.Z ω ≤ 1} + M.P.real {ω | 1 ≤ lam * M.Z ω} = 1 - M.beta lam ∧
    M.P.real (M.Dset lam Q) =
      M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} ∧
    M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} =
      ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P := by
  haveI := hM.isProb
  obtain ⟨hZint, hZ1⟩ := aux45_Z_int M hM
  have hZpos := aux45_Z_pos M
  have hWm := aux45_W_meas M hM
  have hZmeas : Measurable M.Z := by unfold Model.Z; fun_prop
  have hs : 0 < M.θ.sigT * Real.sqrt M.θ.T :=
    mul_pos hM.params.sigT_pos (Real.sqrt_pos.mpr hM.params.T_pos)
  have hZG : Measurable[M.G] M.Z :=
    (by fun_prop : Measurable fun w : ℝ => Real.exp (-M.θ.eta * w - M.θ.eta ^ 2 * M.θ.T / 2)).comp
      hM.W_meas
  have hcG : Measurable[M.G] (fun ω => stdNormalInvE (lam * M.Z ω)) :=
    invE_mono.measurable.comp (hZG.const_mul lam)
  have bint : ∀ l : ℝ, Integrable (fun ω => max (1 - l * M.Z ω) 0) M.P := fun l =>
    ((integrable_const 1).sub (hZint.const_mul l)).sup (integrable_const 0)
  have hlZ : ∀ ω, 0 ≤ lam * M.Z ω := fun ω => mul_nonneg hlam (hZpos ω).le
  have one_sub_beta : 1 - M.beta lam = ∫ ω, min 1 (lam * M.Z ω) ∂M.P := by
    have : ∫ ω, min 1 (lam * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P := by
      congr 1; funext ω
      rcases le_total 1 (lam * M.Z ω) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    rw [this, integral_sub (integrable_const 1) (bint lam)]
    simp [Model.beta]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hset : {ω | ((M.D ω : ℝ) : EReal) ≤ M.Dhat lam ω}
        = {ω | ((M.xi ω : ℝ) : EReal) ≤ stdNormalInvE (lam * M.Z ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      unfold Model.Dhat stdNormalInvE Model.D
      split_ifs with h1 h2
      · exact ⟨fun h => absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _), fun h => absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)⟩
      · simp
      · rw [EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
        constructor
        · intro h
          exact le_of_mul_le_mul_left (by linarith) hs
        · intro h
          have := mul_le_mul_of_nonneg_left h hs.le
          linarith
    rw [hset, aux45_prob_xi_le M hM _ hcG, one_sub_beta]
    congr 1; funext ω
    exact PhiE_invE (hlZ ω)
  · have hpint : Integrable (fun ω => max (lam * M.Z ω - 1) 0) M.P :=
      ((hZint.const_mul lam).sub (integrable_const 1)).sup (integrable_const 0)
    have h : M.beta lam - M.psi lam = 1 - lam := by
      unfold Model.beta Model.psi
      rw [← integral_sub (bint lam) hpint]
      have : (fun ω => max (1 - lam * M.Z ω) 0 - max (lam * M.Z ω - 1) 0)
          = fun ω => 1 - lam * M.Z ω := by
        funext ω
        rcases le_total 1 (lam * M.Z ω) with h | h
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      rw [this, integral_sub (integrable_const 1) (hZint.const_mul lam), integral_const_mul, hZ1]
      simp
    linarith
  · have hT1 : MeasurableSet {ω | lam * M.Z ω ≤ 1} :=
      measurableSet_le (hZmeas.const_mul _) measurable_const
    have hT2 : MeasurableSet {ω | 1 < lam * M.Z ω} :=
      measurableSet_lt measurable_const (hZmeas.const_mul _)
    have h0 : M.P {ω | lam * M.Z ω = 1} = 0 := by
      rcases hlam.lt_or_eq with hpos | hzero
      · have hT : M.θ.T.toNNReal ≠ 0 := by
          simp [Real.toNNReal_eq_zero, not_le.mpr hM.params.T_pos]
        have hη : -M.θ.eta ≠ 0 := neg_ne_zero.mpr hM.params.eta_ne
        have e1 : {ω | lam * M.Z ω = 1} = M.W ⁻¹'
            {w | lam * Real.exp (-M.θ.eta * w - M.θ.eta ^ 2 * M.θ.T / 2) = 1} := rfl
        have hcl : IsClosed {w : ℝ | lam * Real.exp (-M.θ.eta * w - M.θ.eta ^ 2 * M.θ.T / 2) = 1} :=
          isClosed_eq (by fun_prop) continuous_const
        rw [e1, ← Measure.map_apply hWm hcl.measurableSet, hM.W_law]
        refine gaussianReal_absolutelyContinuous 0 hT (Set.Subsingleton.measure_zero ?_ volume)
        intro w1 hw1 w2 hw2
        have hw1' : lam * Real.exp (-M.θ.eta * w1 - M.θ.eta ^ 2 * M.θ.T / 2) = 1 := hw1
        have hw2' : lam * Real.exp (-M.θ.eta * w2 - M.θ.eta ^ 2 * M.θ.T / 2) = 1 := hw2
        have e2 := mul_left_cancel₀ hpos.ne' (hw1'.trans hw2'.symm)
        have e3 := Real.exp_injective e2
        have e4 : -M.θ.eta * w1 = -M.θ.eta * w2 := by linarith
        exact mul_left_cancel₀ hη e4
      · have : {ω | lam * M.Z ω = 1} = ∅ := by
          ext ω; simp [← hzero]
        rw [this, measure_empty]
    have hdec : (fun ω => min 1 (lam * M.Z ω)) = fun ω =>
        {ω | lam * M.Z ω ≤ 1}.indicator (fun ω => lam * M.Z ω) ω
          + {ω | 1 < lam * M.Z ω}.indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h : lam * M.Z ω ≤ 1
      · rw [Set.indicator_of_mem (show ω ∈ {ω | lam * M.Z ω ≤ 1} from h),
          Set.indicator_of_notMem (show ω ∉ {ω | 1 < lam * M.Z ω} from not_lt.mpr h),
          min_eq_right h, add_zero]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | lam * M.Z ω ≤ 1} from h),
          Set.indicator_of_mem (show ω ∈ {ω | 1 < lam * M.Z ω} from not_le.mp h),
          min_eq_left (not_le.mp h).le, zero_add]
    have hP : M.P {ω | 1 ≤ lam * M.Z ω} = M.P {ω | 1 < lam * M.Z ω} := by
      refine le_antisymm ?_ (measure_mono fun ω (h : 1 < lam * M.Z ω) => h.le)
      calc M.P {ω | 1 ≤ lam * M.Z ω}
          ≤ M.P ({ω | 1 < lam * M.Z ω} ∪ {ω | lam * M.Z ω = 1}) := by
            refine measure_mono fun ω (h : 1 ≤ lam * M.Z ω) => ?_
            rcases h.lt_or_eq with h' | h'
            · exact Or.inl h'
            · exact Or.inr h'.symm
        _ ≤ M.P {ω | 1 < lam * M.Z ω} + M.P {ω | lam * M.Z ω = 1} := measure_union_le _ _
        _ = M.P {ω | 1 < lam * M.Z ω} := by rw [h0, add_zero]
    rw [one_sub_beta, hdec, integral_add ((hZint.const_mul lam).indicator hT1)
      ((integrable_const (1 : ℝ)).indicator hT2), integral_indicator hT1, integral_indicator hT2,
      integral_const_mul, measureReal_def, hP]
    simp [Model.PM, measureReal_def]
  · have hset : M.Dset lam Q = {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} := by
      ext ω
      unfold Model.Dset Model.Dhat stdNormalInvE Model.D
      simp only [Set.mem_setOf_eq]
      split_ifs with h1 h2
      · rw [min_eq_right bot_le, min_eq_left bot_le]
        exact ⟨fun h => absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _), fun h => absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)⟩
      · rw [min_eq_left le_top, min_eq_right le_top, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
          le_div_iff₀ hs]
        constructor <;> intro h <;> linarith
      · rw [le_min_iff, le_min_iff, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
          EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ hs]
        constructor
        · rintro ⟨h3, h4⟩
          exact ⟨le_of_mul_le_mul_left (by linarith) hs, by linarith⟩
        · rintro ⟨h3, h4⟩
          have := mul_le_mul_of_nonneg_left h3 hs.le
          exact ⟨by linarith, by linarith⟩
    rw [hset]
  · have hyG : Measurable[M.G] (fun ω =>
        (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)) :=
      measurable_coe_real_ereal.comp ((hM.A_meas.const_sub Q).div_const _)
    rw [aux45_prob_xi_le M hM _ (hcG.min hyG)]
    congr 1; funext ω
    rw [PhiE_mono.map_min, PhiE_invE (hlZ ω), PhiE_coe]
    have hD1 : stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) < 1 := cdf_lt_one _
    have hDe : M.Delta Q ω = stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T)) := rfl
    rw [hDe]
    by_cases h : lam * M.Z ω ≤ 1
    · rw [min_eq_right h]
    · rw [min_eq_left (not_le.mp h).le, min_eq_right hD1.le,
        min_eq_right (hD1.trans (not_le.mp h)).le]

end ProdHedgeCVaR.Joint


namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Lemma 5, p. 17: (38) and (39), for every λ ≥ 0 and every Q. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : ℝ) :
    M.P.real {ω | ((M.D ω : ℝ) : EReal) ≤ M.Dhat lam ω} = 1 - M.beta lam ∧
    1 - M.beta lam = lam - M.psi lam ∧
    lam * M.PM {ω | lam * M.Z ω ≤ 1} + M.P.real {ω | 1 ≤ lam * M.Z ω} = 1 - M.beta lam ∧
    M.P.real (M.Dset lam Q) =
      M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} ∧
    M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} =
      ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P := by
  apply @ProdHedgeCVaR.Joint.lemma_5 <;> assumption

end ProdHedgeCVaR.Joint
