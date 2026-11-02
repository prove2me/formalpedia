-- Prove2me | solution 1 for ValueTrial.Asymptotic.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:51:44.38136+00:00
-- url     : https://prove2.me/submissions/4aa72ab1-a6ef-4f66-ac0e-aebb4e0f3931

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model
import Theorems.Thm_InventoryControl_normal_loss_deriv
import Theorems.Thm_ValueTrial_Asymptotic_equation_8

open MeasureTheory ProbabilityTheory Filter Set

namespace VBCTL





lemma phi_eq (x : ℝ) : (gaussianPDFReal 0 1) x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

lemma phi_pos (x : ℝ) : 0 < (gaussianPDFReal 0 1) x := gaussianPDFReal_pos 0 1 x one_ne_zero

lemma phi_deriv (x : ℝ) : HasDerivAt (gaussianPDFReal 0 1) (-x * (gaussianPDFReal 0 1) x) x := by
  have h : (gaussianPDFReal 0 1) = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := funext phi_eq
  rw [h]
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine this.congr_deriv ?_
    simp; ring
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine h2.congr_deriv ?_
  ring

lemma phi_tendsto_atTop : Tendsto (gaussianPDFReal 0 1) atTop (nhds 0) := by
  have h : (gaussianPDFReal 0 1) = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := funext phi_eq
  rw [h]
  have : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot := by
    have h2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have h3 := tendsto_neg_atTop_atBot.comp (h2.atTop_mul_const (show (0:ℝ) < 1 / 2 by norm_num))
    refine h3.congr fun x => ?_
    simp; ring
  have := (Real.tendsto_exp_atBot.comp this).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  simpa using this

lemma integrable_phi : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1

lemma integrable_mul_phi : Integrable (fun v => v * (gaussianPDFReal 0 1) v) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only
  rw [phi_eq]; ring_nf

lemma tail_eq (x : ℝ) : ∫ v in Ioi x, (gaussianPDFReal 0 1) v = 1 - (cdf (gaussianReal 0 1)) x := by
  rw [cdf_eq_real]
  have h1 : (gaussianReal 0 1).real (Ioi x) = 1 - (gaussianReal 0 1).real (Iic x) := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic]; simp
  rw [← h1, ← integral_indicator_one measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_indicator measurableSet_Ioi]
  congr 1; funext v
  simp only [indicator, mem_Ioi, smul_eq_mul, Pi.one_apply]
  split_ifs <;> simp

lemma first_moment (x : ℝ) : ∫ v in Ioi x, v * (gaussianPDFReal 0 1) v = (gaussianPDFReal 0 1) x := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun v => -(gaussianPDFReal 0 1) v) (f' := fun v => v * (gaussianPDFReal 0 1) v)
    (a := x) (m := 0) (by
      exact ((phi_deriv x).continuousAt.neg).continuousWithinAt)
    (fun v _ => by
      show HasDerivAt (fun v => -(gaussianPDFReal 0 1) v) _ _
      exact (phi_deriv v).neg.congr_deriv (by ring))
    integrable_mul_phi.integrableOn (by simpa using phi_tendsto_atTop.neg)
  simpa using this

lemma psi_closed (x : ℝ) : InventoryControl.normalLoss x = (gaussianPDFReal 0 1) x - x * (1 - (cdf (gaussianReal 0 1)) x) := by
  rw [InventoryControl.normalLoss, ← first_moment x, ← tail_eq x, ← integral_const_mul,
    ← integral_sub integrable_mul_phi.integrableOn (integrable_phi.integrableOn.const_mul x)]
  congr 1; funext v; ring

lemma psi_deriv (x : ℝ) : HasDerivAt InventoryControl.normalLoss ((cdf (gaussianReal 0 1)) x - 1) x := InventoryControl.normal_loss_deriv x

lemma psi_cont : Continuous InventoryControl.normalLoss :=
  continuous_iff_continuousAt.mpr fun x => (psi_deriv x).continuousAt

lemma integrable_pos (x : ℝ) :
    Integrable (fun v : ℝ => max (v - x) 0) (gaussianReal 0 1) := by
  have h1 : Integrable (fun v : ℝ => v) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  exact (h1.sub (integrable_const x)).pos_part

lemma nl_eq (x : ℝ) : InventoryControl.normalLoss x = ∫ v, max (v - x) 0 ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, InventoryControl.normalLoss]
  have h1 : ∫ v in Set.Ioi x, (v - x) * gaussianPDFReal 0 1 v
      = ∫ v in Set.Ioi x, gaussianPDFReal 0 1 v • max (v - x) 0 := by
    refine setIntegral_congr_fun (measurableSet_Ioi (a := x)) ?_
    intro v hv
    simp only [Set.mem_Ioi] at hv
    simp only [smul_eq_mul]
    rw [max_eq_left (by linarith)]; ring
  rw [h1]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro v hv
  simp only [Set.mem_Ioi, not_lt] at hv
  rw [max_eq_right (by linarith : v - x ≤ 0)]; simp

lemma psi_anti : Antitone InventoryControl.normalLoss := by
  intro x y hxy
  rw [nl_eq, nl_eq]
  exact integral_mono (integrable_pos y) (integrable_pos x) fun v => by
    simp only; exact max_le_max (by linarith) le_rfl

/-- `InventoryControl.normalLoss` is 1-Lipschitz from below: `InventoryControl.normalLoss y ≥ InventoryControl.normalLoss x - (y - x)` for `x ≤ y`. -/
lemma psi_lip {x y : ℝ} (hxy : x ≤ y) : InventoryControl.normalLoss x - (y - x) ≤ InventoryControl.normalLoss y := by
  rw [nl_eq, nl_eq]
  have : ∫ v, max (v - x) 0 ∂(gaussianReal 0 1) - (y - x)
      = ∫ v, (max (v - x) 0 - (y - x)) ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_pos x) (integrable_const _)]; simp
  rw [this]
  exact integral_mono ((integrable_pos x).sub (integrable_const _)) (integrable_pos y) fun v => by
    simp only
    rcases le_total v y with h | h
    · rw [max_eq_right (by linarith : v - y ≤ 0)]
      rcases le_total v x with h' | h'
      · rw [max_eq_right (by linarith)]; linarith
      · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith : 0 ≤ v - y), max_eq_left (by linarith)]; linarith

lemma nl_neg (x : ℝ) : InventoryControl.normalLoss (-x) = InventoryControl.normalLoss x + x := by
  rw [psi_closed, psi_closed]
  have h1 : (gaussianPDFReal 0 1) (-x) = (gaussianPDFReal 0 1) x := by rw [phi_eq, phi_eq]; ring_nf
  have h2 : (cdf (gaussianReal 0 1)) (-x) = 1 - (cdf (gaussianReal 0 1)) x := by
    have := tail_eq x
    rw [cdf_eq_real, cdf_eq_real] at *
    -- symmetry of the standard normal
    have hs : (gaussianReal 0 1).real (Iic (-x)) = (gaussianReal 0 1).real (Ici x) := by
      have hm : (gaussianReal 0 1).map (fun z => -z) = gaussianReal 0 1 := by
        rw [gaussianReal_map_neg, neg_zero]
      conv_lhs => rw [← hm]
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
      congr 1
      ext z
      simp only [mem_preimage, mem_Iic, mem_Ici]
      constructor <;> intro h <;> linarith
    have hc : (gaussianReal 0 1).real (Ici x) = (gaussianReal 0 1).real (Ioi x) := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton x)).symm
    rw [hs, hc, ← compl_Iic, measureReal_compl measurableSet_Iic]; simp
  rw [h1, h2]; ring

lemma nl_pos (x : ℝ) : 0 < InventoryControl.normalLoss x := by
  rw [nl_eq, integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hint : Integrable (fun v : ℝ => gaussianPDFReal 0 1 v • max (v - x) 0) := by
    have := integrable_pos x
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero] at this
    rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at this
    simpa only [toReal_gaussianPDF] using this
  rw [integral_pos_iff_support_of_nonneg _ hint]
  · have hsupp : Function.support (fun v : ℝ => gaussianPDFReal 0 1 v • max (v - x) 0)
        = Set.Ioi x := by
      ext v
      simp only [Function.mem_support, smul_eq_mul, Set.mem_Ioi, ne_eq, mul_eq_zero, not_or]
      constructor
      · rintro ⟨_, h⟩
        by_contra hv
        exact h (max_eq_right (by linarith [not_lt.mp hv]))
      · intro hv
        refine ⟨(gaussianPDFReal_pos 0 1 v one_ne_zero).ne', ?_⟩
        rw [max_eq_left (by linarith)]; linarith
    rw [hsupp, Real.volume_Ioi]; simp
  · intro v
    exact smul_nonneg (gaussianPDFReal_nonneg 0 1 v) (le_max_right _ _)

/-- `ℓ(s) = s InventoryControl.normalLoss(μ/s)` has derivative `(gaussianPDFReal 0 1)(μ/s)` for `s > 0`. -/
lemma ell_deriv (μ s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => s * InventoryControl.normalLoss (μ / s)) ((gaussianPDFReal 0 1) (μ / s)) s := by
  have h1 : HasDerivAt (fun s : ℝ => μ / s) (-μ / s ^ 2) s := by
    have := (hasDerivAt_const s μ).div (hasDerivAt_id s) hs.ne'
    refine this.congr_deriv ?_
    simp
  have h2 := (psi_deriv (μ / s)).comp s h1
  have h3 := (hasDerivAt_id s).mul h2
  refine h3.congr_deriv ?_
  simp only [id, Function.comp]
  rw [psi_closed]
  field_simp
  ring

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set ValueTrial.Asymptotic

namespace VBCTL




/-- `ℓ(s) = s InventoryControl.normalLoss(μ/s)`. -/
noncomputable def ell (μ s : ℝ) : ℝ := s * InventoryControl.normalLoss (μ / s)

lemma ell_hasDeriv (μ s : ℝ) (hs : 0 < s) : HasDerivAt (ell μ) ((gaussianPDFReal 0 1) (μ / s)) s :=
  ell_deriv μ s hs

lemma phi_anti_sq {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) : (gaussianPDFReal 0 1) b ≤ (gaussianPDFReal 0 1) a := by
  rw [phi_eq, phi_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  linarith

lemma sq_div_le (μ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (μ / b) ^ 2 ≤ (μ / a) ^ 2 := by
  rw [div_pow, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ ha.le hab 2)

lemma ell_bounds (μ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (gaussianPDFReal 0 1) (μ / a) * (b - a) ≤ ell μ b - ell μ a ∧ ell μ b - ell μ a ≤ (gaussianPDFReal 0 1) (μ / b) * (b - a) := by
  rcases hab.lt_or_eq with hlt | heq
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (ell μ) (fun s => (gaussianPDFReal 0 1) (μ / s)) hlt
      (fun s hs => (ell_hasDeriv μ s (by linarith [hs.1])).continuousAt.continuousWithinAt)
      (fun s hs => ell_hasDeriv μ s (by linarith [hs.1]))
    have hba : 0 < b - a := by linarith
    have e : ell μ b - ell μ a = (gaussianPDFReal 0 1) (μ / ξ) * (b - a) := by
      rw [hd]; field_simp
    rw [e]
    constructor
    · exact mul_le_mul_of_nonneg_right (phi_anti_sq (sq_div_le μ ha hξ.1.le)) hba.le
    · exact mul_le_mul_of_nonneg_right
        (phi_anti_sq (sq_div_le μ (by linarith [hξ.1]) hξ.2.le)) hba.le
  · subst heq; simp

lemma ell_mono (μ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ell μ a ≤ ell μ b := by
  have := (ell_bounds μ ha hab).1
  have : 0 ≤ (gaussianPDFReal 0 1) (μ / a) * (b - a) := mul_nonneg (phi_pos _).le (by linarith)
  linarith

section model

variable (θ : Params)

lemma sig0_pos (hS : θ.Standing) : 0 < sig0 θ :=
  div_pos hS.2.2.1 (Real.sqrt_pos.mpr hS.2.2.2.1)

/-- `u(Q) = √(Q/(n0+Q))`. -/
noncomputable def uQ (Q : ℝ) : ℝ := Real.sqrt (Q / (θ.n0 + Q))

lemma sigZ_eq (hS : θ.Standing) {Q : ℝ} (hQ : 0 ≤ Q) : sigZ θ Q = sig0 θ * uQ θ Q := by
  have hn0 := hS.2.2.2.1
  have hsX := hS.2.2.1
  rw [sigZ, sig0, uQ]
  have h1 : θ.sigX / Real.sqrt θ.n0 = Real.sqrt (θ.sigX ^ 2 / θ.n0) := by
    rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq hsX.le]
  rw [h1, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

lemma uQ_sq (hS : θ.Standing) {Q : ℝ} (hQ : 0 ≤ Q) : uQ θ Q ^ 2 = Q / (θ.n0 + Q) := by
  have hn0 := hS.2.2.2.1
  rw [uQ, Real.sq_sqrt (by positivity)]

lemma uQ_nonneg (Q : ℝ) : 0 ≤ uQ θ Q := Real.sqrt_nonneg _

lemma uQ_lt_one (hS : θ.Standing) {Q : ℝ} (hQ : 0 ≤ Q) : uQ θ Q < 1 := by
  have hn0 := hS.2.2.2.1
  rw [uQ, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
  linarith

lemma uQ_pos (hS : θ.Standing) {Q : ℝ} (hQ : 0 < Q) : 0 < uQ θ Q := by
  have hn0 := hS.2.2.2.1
  rw [uQ]; apply Real.sqrt_pos.mpr; positivity

lemma uQ_mono (hS : θ.Standing) {Q1 Q2 : ℝ} (h1 : 0 ≤ Q1) (h12 : Q1 ≤ Q2) :
    uQ θ Q1 ≤ uQ θ Q2 := by
  have hn0 := hS.2.2.2.1
  rw [uQ, uQ]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma gap_eq (hS : θ.Standing) {Q : ℝ} (hQ : 0 ≤ Q) :
    sig0 θ - sigZ θ Q = sig0 θ * θ.n0 / ((θ.n0 + Q) * (1 + uQ θ Q)) := by
  have hn0 := hS.2.2.2.1
  rw [sigZ_eq θ hS hQ]
  have hu := uQ_sq θ hS hQ
  have hu0 := uQ_nonneg θ Q
  have h1 : (0:ℝ) < 1 + uQ θ Q := by linarith
  have h2 : (0:ℝ) < θ.n0 + Q := by linarith
  rw [eq_div_iff (by positivity)]
  have : uQ θ Q ^ 2 * (θ.n0 + Q) = Q := by rw [hu]; field_simp
  linear_combination (-sig0 θ) * this

lemma uQ_tendsto (hS : θ.Standing) : Tendsto (uQ θ) atTop (nhds 1) := by
  have hn0 := hS.2.2.2.1
  have h1 : Tendsto (fun Q : ℝ => Q / (θ.n0 + Q)) atTop (nhds 1) := by
    have h2 : Tendsto (fun Q : ℝ => 1 - θ.n0 / (θ.n0 + Q)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _
        tendsto_id))
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    field_simp; ring
  have := (Real.continuous_sqrt.tendsto 1).comp h1
  rw [Real.sqrt_one] at this
  exact this

lemma sigZ_tendsto (hS : θ.Standing) : Tendsto (sigZ θ) atTop (nhds (sig0 θ)) := by
  have := (uQ_tendsto θ hS).const_mul (sig0 θ)
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with Q hQ
  rw [sigZ_eq θ hS hQ]

lemma Qgap_tendsto (hS : θ.Standing) :
    Tendsto (fun Q => Q * (sig0 θ - sigZ θ Q)) atTop (nhds (sig0 θ * θ.n0 / 2)) := by
  have hn0 := hS.2.2.2.1
  have h1 : Tendsto (fun Q : ℝ => Q / (θ.n0 + Q)) atTop (nhds 1) := by
    have h2 : Tendsto (fun Q : ℝ => 1 - θ.n0 / (θ.n0 + Q)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _
        tendsto_id))
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    field_simp; ring
  have h3 := (h1.const_mul (sig0 θ * θ.n0)).div (tendsto_const_nhds.add (uQ_tendsto θ hS))
    (by norm_num : (1:ℝ) + 1 ≠ 0)
  rw [mul_one, show (1:ℝ) + 1 = 2 by norm_num] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  rw [gap_eq θ hS hQ.le]
  have := uQ_nonneg θ Q
  simp only [Pi.div_apply]
  field_simp

/-- The value deficit `D(Q) = ℓ(σ0) - ℓ(σZ(Q))`. -/
noncomputable def Dq (Q : ℝ) : ℝ := ell θ.mu0 (sig0 θ) - ell θ.mu0 (sigZ θ Q)

lemma sigZ_pos (hS : θ.Standing) {Q : ℝ} (hQ : 0 < Q) : 0 < sigZ θ Q := by
  rw [sigZ_eq θ hS hQ.le]; exact mul_pos (sig0_pos θ hS) (uQ_pos θ hS hQ)

lemma sigZ_le (hS : θ.Standing) {Q : ℝ} (hQ : 0 ≤ Q) : sigZ θ Q ≤ sig0 θ := by
  rw [sigZ_eq θ hS hQ]
  have := uQ_lt_one θ hS hQ
  have := sig0_pos θ hS
  nlinarith [uQ_nonneg θ Q]

lemma Dq_bounds (hS : θ.Standing) {Q : ℝ} (hQ : 0 < Q) :
    (gaussianPDFReal 0 1) (θ.mu0 / sigZ θ Q) * (sig0 θ - sigZ θ Q) ≤ Dq θ Q ∧
      Dq θ Q ≤ (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ - sigZ θ Q) :=
  ell_bounds θ.mu0 (sigZ_pos θ hS hQ) (sigZ_le θ hS hQ.le)

lemma Dq_pos (hS : θ.Standing) {Q : ℝ} (hQ : 0 < Q) : 0 < Dq θ Q := by
  have h := (Dq_bounds θ hS hQ).1
  have hg : 0 < sig0 θ - sigZ θ Q := by
    rw [gap_eq θ hS hQ.le]
    have := sig0_pos θ hS
    have := hS.2.2.2.1
    have := uQ_nonneg θ Q
    positivity
  exact lt_of_lt_of_le (mul_pos (phi_pos _) hg) h

lemma Dq_anti (hS : θ.Standing) {Q1 Q2 : ℝ} (h1 : 0 < Q1) (h12 : Q1 ≤ Q2) :
    Dq θ Q2 ≤ Dq θ Q1 := by
  have hs : sigZ θ Q1 ≤ sigZ θ Q2 := by
    rw [sigZ_eq θ hS h1.le, sigZ_eq θ hS (by linarith)]
    exact mul_le_mul_of_nonneg_left (uQ_mono θ hS h1.le h12) (sig0_pos θ hS).le
  have := ell_mono θ.mu0 (sigZ_pos θ hS h1) hs
  unfold Dq; linarith

lemma Dq_upper (hS : θ.Standing) {Q : ℝ} (hQ : 0 < Q) :
    Dq θ Q ≤ (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * sig0 θ * θ.n0 / Q := by
  have h := (Dq_bounds θ hS hQ).2
  have hg : sig0 θ - sigZ θ Q ≤ sig0 θ * θ.n0 / Q := by
    rw [gap_eq θ hS hQ.le]
    have := sig0_pos θ hS
    have := hS.2.2.2.1
    have := uQ_nonneg θ Q
    apply div_le_div_of_nonneg_left (by positivity) hQ
    nlinarith
  calc Dq θ Q ≤ (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ - sigZ θ Q) := h
    _ ≤ (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ * θ.n0 / Q) :=
        mul_le_mul_of_nonneg_left hg (phi_pos _).le
    _ = _ := by ring

lemma QDq_tendsto (hS : θ.Standing) :
    Tendsto (fun Q => Q * Dq θ Q) atTop
      (nhds ((gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ * θ.n0 / 2))) := by
  have hg := Qgap_tendsto θ hS
  have hlow : Tendsto (fun Q => (gaussianPDFReal 0 1) (θ.mu0 / sigZ θ Q) * (Q * (sig0 θ - sigZ θ Q))) atTop
      (nhds ((gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ * θ.n0 / 2))) := by
    refine Tendsto.mul ?_ hg
    have hc : Continuous (gaussianPDFReal 0 1) := by
      rw [show (gaussianPDFReal 0 1) = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) from
        funext phi_eq]
      fun_prop
    exact (hc.tendsto _).comp (tendsto_const_nhds.div (sigZ_tendsto θ hS) (sig0_pos θ hS).ne')
  have hup := hg.const_mul ((gaussianPDFReal 0 1) (θ.mu0 / sig0 θ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with Q hQ
    have := (Dq_bounds θ hS hQ).1
    calc (gaussianPDFReal 0 1) (θ.mu0 / sigZ θ Q) * (Q * (sig0 θ - sigZ θ Q))
        = Q * ((gaussianPDFReal 0 1) (θ.mu0 / sigZ θ Q) * (sig0 θ - sigZ θ Q)) := by ring
      _ ≤ Q * Dq θ Q := mul_le_mul_of_nonneg_left this hQ.le
  · filter_upwards [eventually_gt_atTop 0] with Q hQ
    have := (Dq_bounds θ hS hQ).2
    calc Q * Dq θ Q ≤ Q * ((gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ - sigZ θ Q)) :=
          mul_le_mul_of_nonneg_left this hQ.le
      _ = _ := by ring

end model

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set ValueTrial.Asymptotic

namespace VBCTL




section model2

variable (θ : Params)

lemma vInf_eq (hS : θ.Standing) : vInf θ = ell θ.mu0 (sig0 θ) + (1 - θ.pN) * θ.mu0 := by
  have h0 := (sig0_pos θ hS).ne'
  rw [vInf, ell, nl_neg]
  field_simp
  ring

lemma ell_pos (hS : θ.Standing) : 0 < ell θ.mu0 (sig0 θ) :=
  mul_pos (sig0_pos θ hS) (nl_pos _)

/-- the value with no trial is at most `P * M0`. -/
noncomputable def M0 : ℝ := max 0 (max ((1 - θ.pN) * θ.mu0) (-(θ.pN * θ.mu0)))

lemma M0_lt (hS : θ.Standing) : M0 θ < vInf θ := by
  have hpN0 := hS.1
  have hpN1 := hS.2.1
  have h0 := (sig0_pos θ hS).ne'
  have hv := vInf_eq θ hS
  have he := ell_pos θ hS
  have hpos : 0 < vInf θ := by
    rw [vInf]
    have := nl_pos (-(θ.mu0 / sig0 θ))
    have := nl_pos (θ.mu0 / sig0 θ)
    have := sig0_pos θ hS
    have : 0 < 1 - θ.pN := by linarith
    positivity
  have h2 : -(θ.pN * θ.mu0) < vInf θ := by
    -- ell(σ0) + μ0 = σ0 InventoryControl.normalLoss(-m) > 0
    have h3 : ell θ.mu0 (sig0 θ) + θ.mu0 = sig0 θ * InventoryControl.normalLoss (-(θ.mu0 / sig0 θ)) := by
      rw [ell, nl_neg]; field_simp
    have := mul_pos (sig0_pos θ hS) (nl_pos (-(θ.mu0 / sig0 θ)))
    rw [hv]; nlinarith
  unfold M0
  apply max_lt hpos (max_lt (by rw [hv]; linarith) h2)

lemma V_zero_le (hS : θ.Standing) (hρ : θ.rho = 0) (ccap Ppop : ℝ → ℝ) (x : ℝ × ℝ)
    (hx : x.1 * x.2 = 0) (hP : 0 ≤ Ppop 0) : V θ ccap Ppop x ≤ Ppop 0 * M0 θ := by
  obtain ⟨hpN0, hpN1, -, -, -, -, hIN, hIS, -⟩ := hS
  simp only [V, hx, if_true, Prho, hρ]
  unfold M0
  rw [mul_max_of_nonneg _ _ hP, mul_max_of_nonneg _ _ hP, mul_zero]
  apply max_le_max le_rfl (max_le_max (by nlinarith) (by nlinarith))

lemma V_bounds (hS : θ.Standing) (hρ : θ.rho = 0) (ccap Ppop : ℝ → ℝ) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hPT : 0 < Ppop T) :
    Ppop T * vInf θ - ccap r - 2 * Cnet θ * (T * r / 2) - Ppop T * Dq θ (T * r / 2)
        - (θ.IN + θ.IS) ≤ V θ ccap Ppop (T, r) ∧
      V θ ccap Ppop (T, r)
        ≤ Ppop T * vInf θ - ccap r - 2 * Cnet θ * (T * r / 2) - Ppop T * Dq θ (T * r / 2) := by
  have h8 := equation_8 θ hS ccap Ppop T r hT hr hPT.le
  simp only [Prho, Ttil, hρ, if_true, neg_zero, zero_mul, Real.exp_zero, one_mul] at h8
  rw [h8]
  obtain ⟨hpN0, hpN1, hsX, hn0, hc0, hdon, hIN, hIS, hzeta, hDel, hrho0, hrho1⟩ := hS
  have hS' : θ.Standing :=
    ⟨hpN0, hpN1, hsX, hn0, hc0, hdon, hIN, hIS, hzeta, hDel, hrho0, hrho1⟩
  have hQ : 0 < T * r / 2 := by positivity
  set Q := T * r / 2 with hQdef
  set s := sigZ θ Q with hsdef
  set P := Ppop T with hPdef
  have hs : 0 < s := sigZ_pos θ hS' hQ
  set aN := θ.IN / ((1 - θ.pN) * P) with haN
  set aS := θ.IS / (θ.pN * P) with haS
  have h1p : 0 < 1 - θ.pN := by linarith
  have haN0 : 0 ≤ aN := div_nonneg hIN (by positivity)
  have haS0 : 0 ≤ aS := div_nonneg hIS (by positivity)
  have hPaN : P * (1 - θ.pN) * aN = θ.IN := by rw [haN]; field_simp
  have hPaS0 : 0 ≤ P * θ.pN * aS := by positivity
  have hPaS : P * θ.pN * aS ≤ θ.IS := by
    rcases hpN0.lt_or_eq with h | h
    · rw [show P * θ.pN * aS = θ.IS by rw [haS]; field_simp]
    · rw [← h, mul_zero, zero_mul]; exact hIS
  -- bounds on InventoryControl.normalLoss terms
  set m := θ.mu0 / s with hm
  have hX1 : InventoryControl.normalLoss ((aN - θ.mu0) / s) ≤ InventoryControl.normalLoss (-m) :=
    psi_anti (by rw [hm, sub_div]; linarith [div_nonneg haN0 hs.le])
  have hX2 : InventoryControl.normalLoss (-m) - aN / s ≤ InventoryControl.normalLoss ((aN - θ.mu0) / s) := by
    have := psi_lip (x := -m) (y := (aN - θ.mu0) / s) (by
      rw [hm, sub_div]; linarith [div_nonneg haN0 hs.le])
    have e : (aN - θ.mu0) / s - -m = aN / s := by rw [hm]; ring
    linarith
  have hY1 : InventoryControl.normalLoss ((aS + θ.mu0) / s) ≤ InventoryControl.normalLoss m :=
    psi_anti (by rw [hm, add_div]; linarith [div_nonneg haS0 hs.le])
  have hY2 : InventoryControl.normalLoss m - aS / s ≤ InventoryControl.normalLoss ((aS + θ.mu0) / s) := by
    have := psi_lip (x := m) (y := (aS + θ.mu0) / s) (by
      rw [hm, add_div]; linarith [div_nonneg haS0 hs.le])
    have e : (aS + θ.mu0) / s - m = aS / s := by rw [hm]; ring
    linarith
  have hneg : InventoryControl.normalLoss (-m) = InventoryControl.normalLoss m + m := nl_neg m
  have hell : ell θ.mu0 s = s * InventoryControl.normalLoss m := rfl
  have hv := vInf_eq θ hS'
  have hD : Dq θ Q = ell θ.mu0 (sig0 θ) - ell θ.mu0 s := rfl
  have hsm : s * m = θ.mu0 := by rw [hm]; field_simp
  -- products
  have hA : 0 ≤ P * s * (1 - θ.pN) := by positivity
  have hB : 0 ≤ P * s * θ.pN := by positivity
  have e1 := mul_le_mul_of_nonneg_left hX1 hA
  have e2 := mul_le_mul_of_nonneg_left hX2 hA
  have e3 := mul_le_mul_of_nonneg_left hY1 hB
  have e4 := mul_le_mul_of_nonneg_left hY2 hB
  have f2 : P * s * (1 - θ.pN) * (InventoryControl.normalLoss (-m) - aN / s) = P * s * (1 - θ.pN) * InventoryControl.normalLoss (-m) - θ.IN := by
    rw [← hPaN]; field_simp
  have f4 : P * s * θ.pN * (InventoryControl.normalLoss m - aS / s) = P * s * θ.pN * InventoryControl.normalLoss m - P * θ.pN * aS := by
    field_simp
  have f5 : P * s * (1 - θ.pN) * InventoryControl.normalLoss (-m) + P * s * θ.pN * InventoryControl.normalLoss m
      = P * (ell θ.mu0 s + (1 - θ.pN) * θ.mu0) := by
    rw [hneg, hell, ← hsm]; ring
  have hC : Cnet θ = θ.c - θ.don * (1 - 2 * θ.pN) * θ.mu0 / 2 := rfl
  have i1 : -(ccap r + θ.c * T * r) + θ.don * Q * (1 - 2 * θ.pN) * θ.mu0
      + P * s * ((1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / s) + θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / s))
      = -ccap r - 2 * Cnet θ * Q + P * s * (1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / s)
        + P * s * θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / s) := by
    rw [hC, hQdef]; ring
  have g1 : P * vInf θ - P * Dq θ Q = P * (ell θ.mu0 s + (1 - θ.pN) * θ.mu0) := by
    rw [hv, hD]; ring
  rw [i1]
  constructor
  · linarith [e2, e4, f2, f4, f5, hPaS, g1]
  · linarith [e1, e3, f5, g1]

end model2

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set Topology

namespace VBCTL

/-- Abstract asymptotic core: if `Q*` nearly minimizes `2CQ + S·D(Q)` (up to an `o(√S)` error),
with `Q·D(Q) → A`, then `Q*/√S → √(A/(2C))`. -/
lemma core {ι : Type*} (l : Filter ι) (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (D : ℝ → ℝ) (hDpos : ∀ Q, 0 < Q → 0 < D Q)
    (hDanti : ∀ Q1 Q2, 0 < Q1 → Q1 ≤ Q2 → D Q2 ≤ D Q1)
    (hQD : Tendsto (fun Q => Q * D Q) atTop (𝓝 A))
    (S : ι → ℝ) (hS : Tendsto S l atTop) (Qs Kerr : ι → ℝ)
    (hK : Tendsto (fun p => Kerr p / Real.sqrt (S p)) l (𝓝 0))
    (hQpos : ∀ᶠ p in l, 0 < Qs p)
    (hineq : ∀ᶠ p in l, 2 * C * Qs p + S p * D (Qs p) ≤
      2 * C * (Real.sqrt (A / (2 * C)) * Real.sqrt (S p))
        + S p * D (Real.sqrt (A / (2 * C)) * Real.sqrt (S p)) + Kerr p) :
    Tendsto (fun p => Qs p / Real.sqrt (S p)) l (𝓝 (Real.sqrt (A / (2 * C)))) ∧
      Tendsto Qs l atTop := by
  set q0 := Real.sqrt (A / (2 * C)) with hq0
  have hq0pos : 0 < q0 := Real.sqrt_pos.mpr (by positivity)
  have hq0sq : q0 ^ 2 = A / (2 * C) := Real.sq_sqrt (by positivity)
  have hAq : A / q0 = 2 * C * q0 := by
    field_simp; rw [hq0sq]; field_simp
  have hs : Tendsto (fun p => Real.sqrt (S p)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hS
  have hSpos : ∀ᶠ p in l, 0 < S p := hS.eventually_gt_atTop 0
  -- R(p)
  set R : ι → ℝ := fun p => 2 * C * q0 + Real.sqrt (S p) * D (q0 * Real.sqrt (S p))
    + Kerr p / Real.sqrt (S p) with hR
  have hR_lim : Tendsto R l (𝓝 (2 * C * q0 + A / q0 + 0)) := by
    refine (tendsto_const_nhds.add ?_).add hK
    have h1 : Tendsto (fun p => q0 * Real.sqrt (S p)) l atTop :=
      hs.const_mul_atTop hq0pos
    have h2 := ((hQD.comp h1).div_const q0)
    refine h2.congr' ?_
    filter_upwards [hSpos] with p hp
    simp only [Function.comp]
    field_simp
  rw [add_zero] at hR_lim
  -- the divided inequality
  have hdiv : ∀ᶠ p in l, 2 * C * (Qs p / Real.sqrt (S p)) + Real.sqrt (S p) * D (Qs p) ≤ R p := by
    filter_upwards [hineq, hSpos] with p hp hSp
    have hsq : 0 < Real.sqrt (S p) := Real.sqrt_pos.mpr hSp
    have hss : Real.sqrt (S p) * Real.sqrt (S p) = S p := Real.mul_self_sqrt hSp.le
    simp only [hR]
    set u := Real.sqrt (S p) with hu
    rw [← hss] at hp
    rw [← sub_nonneg]
    have : 0 ≤ (2 * C * (q0 * u) + u * u * D (q0 * u) + Kerr p)
        - (2 * C * Qs p + u * u * D (Qs p)) := by linarith
    have e : (2 * C * q0 + u * D (q0 * u) + Kerr p / u)
        - (2 * C * (Qs p / u) + u * D (Qs p))
        = ((2 * C * (q0 * u) + u * u * D (q0 * u) + Kerr p)
          - (2 * C * Qs p + u * u * D (Qs p))) / u := by
      field_simp
    rw [e]; positivity
  -- Q* → ∞
  have hRb : ∀ᶠ p in l, R p ≤ 2 * C * q0 + A / q0 + 1 :=
    hR_lim.eventually (ge_mem_nhds (by linarith))
  have hQinf : Tendsto Qs l atTop := by
    rw [tendsto_atTop]
    intro b
    set M := max b 1 with hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hDM := hDpos M hMpos
    have hsl : ∀ᶠ p in l, (2 * C * q0 + A / q0 + 1) / D M < Real.sqrt (S p) :=
      hs.eventually_gt_atTop _
    filter_upwards [hdiv, hRb, hsl, hQpos, hSpos] with p h1 h2 h3 h4 h5
    have hsq : 0 < Real.sqrt (S p) := Real.sqrt_pos.mpr h5
    by_contra hcon
    push Not at hcon
    have hQM : Qs p ≤ M := le_trans hcon.le (le_max_left _ _)
    have hD := hDanti (Qs p) M h4 hQM
    have ht : 0 ≤ 2 * C * (Qs p / Real.sqrt (S p)) := by positivity
    have : Real.sqrt (S p) * D M ≤ 2 * C * q0 + A / q0 + 1 := by
      have := mul_le_mul_of_nonneg_left hD hsq.le
      linarith
    rw [div_lt_iff₀ hDM] at h3
    linarith
  refine ⟨?_, hQinf⟩
  -- a(p) = Q* D(Q*) → A
  have ha : Tendsto (fun p => Qs p * D (Qs p)) l (𝓝 A) := hQD.comp hQinf
  set t : ι → ℝ := fun p => Qs p / Real.sqrt (S p) with ht
  -- (4Ct - R)^2 ≤ R^2 - 8 C a
  have hsqineq : ∀ᶠ p in l, (4 * C * t p - R p) ^ 2 ≤ R p ^ 2 - 8 * C * (Qs p * D (Qs p)) := by
    filter_upwards [hdiv, hQpos, hSpos] with p h1 h2 h3
    have hsq : 0 < Real.sqrt (S p) := Real.sqrt_pos.mpr h3
    have htp : 0 < t p := div_pos h2 hsq
    have e : Real.sqrt (S p) * D (Qs p) = Qs p * D (Qs p) / t p := by
      simp only [ht]; field_simp
    rw [e] at h1
    have h1' : 2 * C * t p * t p + Qs p * D (Qs p) ≤ R p * t p := by
      have := mul_le_mul_of_nonneg_right h1 htp.le
      rw [add_mul, div_mul_cancel₀ _ htp.ne'] at this
      linarith
    nlinarith
  have hlim0 : Tendsto (fun p => R p ^ 2 - 8 * C * (Qs p * D (Qs p))) l (𝓝 0) := by
    have := (hR_lim.pow 2).sub (ha.const_mul (8 * C))
    have hval : (2 * C * q0 + A / q0) ^ 2 - 8 * C * A = 0 := by
      rw [hAq, show (2 * C * q0 + 2 * C * q0) ^ 2 = 16 * C ^ 2 * q0 ^ 2 by ring, hq0sq]
      field_simp; ring
    rw [hval] at this
    exact this
  have hdiff : Tendsto (fun p => 4 * C * t p - R p) l (𝓝 0) := by
    have hsq0 := (Real.continuous_sqrt.tendsto 0).comp hlim0
    rw [Real.sqrt_zero] at hsq0
    refine squeeze_zero_norm' ?_ hsq0
    filter_upwards [hsqineq] with p hp
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hp
  have hfin := (hdiff.add hR_lim).div_const (4 * C)
  have hval2 : (0 + (2 * C * q0 + A / q0)) / (4 * C) = q0 := by
    rw [hAq]; field_simp; ring
  rw [hval2] at hfin
  refine hfin.congr' (Eventually.of_forall fun p => ?_)
  simp only [ht]
  field_simp
  ring

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set Topology ValueTrial.Asymptotic

namespace VBCTL




lemma eventually_lin_lt (a b c : ℝ) (hc : 0 < c) :
    ∀ᶠ P in atTop, a * Real.sqrt P + b < c * P := by
  have hs : Tendsto (fun P : ℝ => Real.sqrt P) atTop atTop := Real.tendsto_sqrt_atTop
  filter_upwards [hs.eventually_ge_atTop (max 1 ((|a| + |b| + 1) / c)), eventually_ge_atTop 0]
    with P hP hP0
  have h1 : 1 ≤ Real.sqrt P := le_trans (le_max_left _ _) hP
  have h2 : (|a| + |b| + 1) / c ≤ Real.sqrt P := le_trans (le_max_right _ _) hP
  have hss : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0
  have h3 : |a| + |b| + 1 ≤ c * Real.sqrt P := by
    rw [div_le_iff₀ hc] at h2; linarith
  have h4 : a * Real.sqrt P ≤ |a| * Real.sqrt P :=
    mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith)
  have h5 : b ≤ |b| * Real.sqrt P := by
    have := le_abs_self b
    nlinarith [abs_nonneg b]
  have h6 : (|a| + |b| + 1) * Real.sqrt P ≤ c * Real.sqrt P * Real.sqrt P :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  rw [mul_assoc, hss] at h6
  nlinarith

section model3

variable (θ : Params)

lemma sigZ_contOn (hS : θ.Standing) : ContinuousOn (sigZ θ) (Ioi 0) := by
  have hn0 := hS.2.2.2.1
  intro Q hQ
  simp only [mem_Ioi] at hQ
  apply ContinuousAt.continuousWithinAt
  unfold sigZ
  apply Real.continuous_sqrt.continuousAt.comp
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  have : 0 < θ.n0 * (θ.n0 + Q) := by positivity
  exact this.ne'

/-- The closed form of the post-adoption term as a function of `(P, Q)`. -/
noncomputable def Gpost (P Q : ℝ) : ℝ :=
  P * sigZ θ Q * ((1 - θ.pN) * InventoryControl.normalLoss ((θ.IN / ((1 - θ.pN) * P) - θ.mu0) / sigZ θ Q)
    + θ.pN * InventoryControl.normalLoss ((θ.IS / (θ.pN * P) + θ.mu0) / sigZ θ Q))

lemma Gpost_contAt (hS : θ.Standing) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    ContinuousAt (fun z : ℝ × ℝ => Gpost θ z.1 z.2) (P, Q) := by
  have hs0 : ContinuousAt (sigZ θ) Q := (sigZ_contOn θ hS).continuousAt (Ioi_mem_nhds hQ)
  have hs : ContinuousAt (fun z : ℝ × ℝ => sigZ θ z.2) (P, Q) :=
    ContinuousAt.comp (g := sigZ θ) (f := fun z : ℝ × ℝ => z.2) hs0 continuousAt_snd
  have hspos : sigZ θ Q ≠ 0 := (sigZ_pos θ hS hQ).ne'
  have h1 : ContinuousAt (fun z : ℝ × ℝ => θ.IN / ((1 - θ.pN) * z.1)) (P, Q) := by
    have : (fun z : ℝ × ℝ => θ.IN / ((1 - θ.pN) * z.1))
        = fun z : ℝ × ℝ => θ.IN / (1 - θ.pN) * z.1⁻¹ := by
      funext z; rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [this]
    exact continuousAt_const.mul (continuousAt_fst.inv₀ hP.ne')
  have h2 : ContinuousAt (fun z : ℝ × ℝ => θ.IS / (θ.pN * z.1)) (P, Q) := by
    have : (fun z : ℝ × ℝ => θ.IS / (θ.pN * z.1))
        = fun z : ℝ × ℝ => θ.IS / θ.pN * z.1⁻¹ := by
      funext z; rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [this]
    exact continuousAt_const.mul (continuousAt_fst.inv₀ hP.ne')
  unfold Gpost
  apply ContinuousAt.mul (continuousAt_fst.mul hs)
  apply ContinuousAt.add
  · exact continuousAt_const.mul (psi_cont.continuousAt.comp
      ((h1.sub continuousAt_const).div hs hspos))
  · exact continuousAt_const.mul (psi_cont.continuousAt.comp
      ((h2.add continuousAt_const).div hs hspos))

lemma V_eq_G (hS : θ.Standing) (hρ : θ.rho = 0) (ccap Ppop : ℝ → ℝ) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hPT : 0 < Ppop T) :
    V θ ccap Ppop (T, r) = -(ccap r + θ.c * T * r) + θ.don * (T * r / 2) * (1 - 2 * θ.pN) * θ.mu0
      + Gpost θ (Ppop T) (T * r / 2) := by
  have h8 := equation_8 θ hS ccap Ppop T r hT hr hPT.le
  simp only [Prho, Ttil, hρ, if_true, neg_zero, zero_mul, Real.exp_zero, one_mul] at h8
  rw [h8, Gpost]

/-- `V` depends on `(T, r)` only through `T r` for a constant setup cost and a fixed pool. -/
lemma V_prod (hρ : θ.rho = 0) (k P : ℝ) (x y : ℝ × ℝ) (hxy : x.1 * x.2 = y.1 * y.2) :
    V θ (fun _ => k) (fixedPool P) x = V θ (fun _ => k) (fixedPool P) y := by
  simp only [V, Ttil, Prho, hρ, if_true, fixedPool, zero_mul, neg_zero, Real.exp_zero, one_mul]
  rw [hxy, show θ.c * x.1 * x.2 = θ.c * (y.1 * y.2) by rw [← hxy]; ring,
    show θ.c * y.1 * y.2 = θ.c * (y.1 * y.2) by ring]

lemma sqrt_n0_sigX (hS : θ.Standing) : Real.sqrt (θ.n0 * θ.sigX ^ 2) = sig0 θ * θ.n0 := by
  have hn0 := hS.2.2.2.1
  have hsX := hS.2.2.1
  rw [Real.sqrt_mul hn0.le, Real.sqrt_sq hsX.le, sig0]
  have h := Real.mul_self_sqrt hn0.le
  have h2 := Real.sqrt_pos.mpr hn0
  field_simp
  linarith

end model3

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set Topology ValueTrial.Asymptotic

namespace VBCTL

/-- Generic asymptotic optimization over a one-parameter family of designs. -/
theorem gen (S : ℝ → ℝ) (hS : Tendsto S atTop atTop)
    (Dset : ℝ → Set (ℝ × ℝ)) (F : ℝ → ℝ × ℝ → ℝ) (Qf : ℝ × ℝ → ℝ) (g : ℝ → ℝ → ℝ × ℝ)
    (v M0 k C K1 K2 M1 A Bc n0 c0 : ℝ) (hM0 : M0 < v) (hC : 0 < C) (hA : 0 < A)
    (hn0 : 0 < n0) (hc0 : 0 < c0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (D : ℝ → ℝ) (hDpos : ∀ Q, 0 < Q → 0 < D Q)
    (hDanti : ∀ Q1 Q2, 0 < Q1 → Q1 ≤ Q2 → D Q2 ≤ D Q1)
    (hQD : Tendsto (fun Q => Q * D Q) atTop (𝓝 A))
    (hDup : ∀ Q, 0 < Q → D Q ≤ Bc / Q)
    (hQnn : ∀ᶠ H in atTop, ∀ x ∈ Dset H, 0 ≤ Qf x)
    (hup : ∀ᶠ H in atTop, ∀ x ∈ Dset H, 0 < Qf x →
      F H x ≤ S H * v - k - 2 * C * Qf x - S H * D (Qf x) + K2)
    (hzero : ∀ᶠ H in atTop, ∀ x ∈ Dset H, Qf x = 0 → F H x ≤ S H * M0 + M1)
    (hg : ∀ᶠ H in atTop, ∀ Q, 0 < Q → Q ≤ c0 * S H →
      g H Q ∈ Dset H ∧ Qf (g H Q) = Q ∧ S H * v - k - 2 * C * Q - S H * D Q - K1 ≤ F H (g H Q))
    (hcont : ∀ᶠ H in atTop, ContinuousOn (fun Q => F H (g H Q)) (Ioc 0 (c0 * S H)))
    (hrep : ∀ᶠ H in atTop, ∀ x ∈ Dset H, 0 < Qf x → Qf x ≤ c0 * S H →
      F H x ≤ F H (g H (Qf x))) :
    (∀ᶠ H in atTop, ∃ x, IsOptOn (F H) (Dset H) x) ∧
    ∀ xs : ℝ → ℝ × ℝ, (∀ᶠ H in atTop, IsOptOn (F H) (Dset H) (xs H)) →
      Tendsto (fun H => Qf (xs H) / Real.sqrt (S H)) atTop (𝓝 (Real.sqrt (A / (2 * C)))) ∧
      Tendsto (fun H => F H (xs H) / S H) atTop (𝓝 v) := by
  have hBc : 0 ≤ Bc := by
    have h1 := hDpos 1 one_pos
    have h2 := hDup 1 one_pos
    rw [div_one] at h2; linarith
  set d1 := D n0 with hd1def
  have hd1 : 0 < d1 := hDpos n0 hn0
  have hgap : 0 < v - M0 := by linarith
  set W0 : ℝ → ℝ := fun H => S H * v - k - (2 * C + Bc) * Real.sqrt (S H) - K1 with hW0def
  set b : ℝ → ℝ := fun H => ((2 * C + Bc) * Real.sqrt (S H) + K1 + K2) / (2 * C) + 1 with hbdef
  have hs : Tendsto (fun H => Real.sqrt (S H)) atTop atTop := Real.tendsto_sqrt_atTop.comp hS
  have hgood : ∀ᶠ H in atTop, 0 < S H ∧ n0 ≤ Real.sqrt (S H) ∧ 1 / c0 ≤ Real.sqrt (S H) ∧
      (2 * C + Bc) * Real.sqrt (S H) + (K1 + K2) < d1 * S H ∧
      (2 * C + Bc) * Real.sqrt (S H) + (k + K1 + M1) < (v - M0) * S H ∧
      (1 / (2 * C)) * ((2 * C + Bc) * Real.sqrt (S H)) + ((K1 + K2) / (2 * C) + 1) < c0 * S H := by
    filter_upwards [hS.eventually_gt_atTop 0, hs.eventually_ge_atTop n0,
      hs.eventually_ge_atTop (1 / c0),
      hS.eventually (eventually_lin_lt (2 * C + Bc) (K1 + K2) d1 hd1),
      hS.eventually (eventually_lin_lt (2 * C + Bc) (k + K1 + M1) _ hgap),
      hS.eventually (eventually_lin_lt ((1 / (2 * C)) * (2 * C + Bc)) ((K1 + K2) / (2 * C) + 1)
        c0 hc0)] with H h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    linarith [show (1 / (2 * C)) * ((2 * C + Bc) * Real.sqrt (S H))
      = (1 / (2 * C)) * (2 * C + Bc) * Real.sqrt (S H) by ring]
  have hall := ((((((hgood.and hQnn).and hup).and hzero).and hg).and hcont).and hrep)
  -- consequences
  have hsle : ∀ H, 0 < S H → 1 / c0 ≤ Real.sqrt (S H) → Real.sqrt (S H) ≤ c0 * S H := by
    intro H hSH h3
    have hss : Real.sqrt (S H) * Real.sqrt (S H) = S H := Real.mul_self_sqrt hSH.le
    rw [div_le_iff₀ hc0] at h3
    nlinarith [Real.sqrt_nonneg (S H)]
  have hbval : ∀ H, (1 / (2 * C)) * ((2 * C + Bc) * Real.sqrt (S H)) + ((K1 + K2) / (2 * C) + 1)
      = b H := by
    intro H; simp only [hbdef]; field_simp; ring
  refine ⟨?_, ?_⟩
  · -- existence
    filter_upwards [hall] with H hH
    obtain ⟨⟨⟨⟨⟨⟨⟨hS0, hn0s, hc0s, hG4, hG5, hG6⟩, hQnnH⟩, hupH⟩, hzeroH⟩, hgH⟩, hcontH⟩, hrepH⟩ := hH
    have hsP : 0 < Real.sqrt (S H) := Real.sqrt_pos.mpr hS0
    have hss : Real.sqrt (S H) * Real.sqrt (S H) = S H := Real.mul_self_sqrt hS0.le
    have hbc0 : b H ≤ c0 * S H := by rw [← hbval]; exact hG6.le
    -- W0 bound at √S
    have hW0 : W0 H ≤ F H (g H (Real.sqrt (S H))) := by
      have h := (hgH (Real.sqrt (S H)) hsP (hsle H hS0 hc0s)).2.2
      have hD := hDup _ hsP
      have hPD : S H * D (Real.sqrt (S H)) ≤ Bc * Real.sqrt (S H) := by
        have := mul_le_mul_of_nonneg_left hD hS0.le
        calc S H * D (Real.sqrt (S H)) ≤ S H * (Bc / Real.sqrt (S H)) := this
          _ = Bc * Real.sqrt (S H) := by
            rw [mul_div_assoc', mul_comm (S H), mul_div_assoc, Real.div_sqrt]
      simp only [hW0def]; nlinarith
    -- the maximization
    have hsub : Icc n0 (b H) ⊆ Ioc 0 (c0 * S H) := fun Q hQ =>
      ⟨lt_of_lt_of_le hn0 hQ.1, le_trans hQ.2 hbc0⟩
    have hsPI : Real.sqrt (S H) ∈ Icc n0 (b H) := by
      refine ⟨hn0s, ?_⟩
      rw [← hbval]
      have : Real.sqrt (S H) ≤ (1 / (2 * C)) * ((2 * C + Bc) * Real.sqrt (S H)) := by
        rw [← mul_assoc, show 1 / (2 * C) * (2 * C + Bc) = 1 + Bc / (2 * C) by field_simp]
        have : 0 ≤ Bc / (2 * C) * Real.sqrt (S H) := by positivity
        nlinarith
      have : 0 ≤ (K1 + K2) / (2 * C) := by positivity
      linarith
    obtain ⟨Qs, hQs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨_, hsPI⟩ (hcontH.mono hsub)
    have hQs0 : 0 < Qs := lt_of_lt_of_le hn0 hQs.1
    have hfQs : W0 H ≤ F H (g H Qs) := le_trans hW0 (hmax hsPI)
    refine ⟨g H Qs, (hgH Qs hQs0 (hsub hQs).2).1, ?_⟩
    intro y hy
    have hy0 := hQnnH y hy
    rcases hy0.lt_or_eq with hy0 | hy0
    · by_cases hs1 : Qf y ≤ n0
      · have h := hupH y hy hy0
        have hD := hDanti (Qf y) n0 hy0 hs1
        have hPD := mul_le_mul_of_nonneg_left hD hS0.le
        have : 0 ≤ 2 * C * Qf y := by positivity
        have : F H y < W0 H := by simp only [hW0def]; nlinarith
        linarith
      by_cases hs2 : b H ≤ Qf y
      · have h := hupH y hy hy0
        have hPD := mul_nonneg hS0.le (hDpos _ hy0).le
        have hb2 : (2 * C + Bc) * Real.sqrt (S H) + K1 + K2 + 2 * C ≤ 2 * C * Qf y := by
          have := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ) ≤ 2 * C by positivity)
          simp only [hbdef] at this
          rw [mul_add, mul_div_cancel₀ _ (by positivity : (2:ℝ) * C ≠ 0), mul_one] at this
          linarith
        have : F H y < W0 H := by simp only [hW0def]; nlinarith
        linarith
      push Not at hs1 hs2
      have hmem : Qf y ∈ Icc n0 (b H) := ⟨hs1.le, hs2.le⟩
      exact le_trans (hrepH y hy hy0 (hsub hmem).2) (hmax hmem)
    · have h := hzeroH y hy hy0.symm
      have : F H y < W0 H := by simp only [hW0def]; nlinarith
      linarith
  · -- asymptotics
    intro xs hxs
    have hev := hall.and hxs
    set Qs : ℝ → ℝ := fun H => Qf (xs H) with hQsdef
    set q0 := Real.sqrt (A / (2 * C)) with hq0
    have hq0pos : 0 < q0 := Real.sqrt_pos.mpr (by positivity)
    have hev2 := hev.and (hs.eventually_ge_atTop (q0 / c0))
    have hQpos : ∀ᶠ H in atTop, 0 < Qs H := by
      filter_upwards [hev] with H hH
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS0, hn0s, hc0s, hG4, hG5, hG6⟩, hQnnH⟩, hupH⟩, hzeroH⟩, hgH⟩, hcontH⟩,
        hrepH⟩, hmem, hopt⟩ := hH
      have hsP : 0 < Real.sqrt (S H) := Real.sqrt_pos.mpr hS0
      have hg1 := hgH (Real.sqrt (S H)) hsP (hsle H hS0 hc0s)
      have h1 := hopt _ hg1.1
      have hD := hDup _ hsP
      have hPD : S H * D (Real.sqrt (S H)) ≤ Bc * Real.sqrt (S H) := by
        have := mul_le_mul_of_nonneg_left hD hS0.le
        calc S H * D (Real.sqrt (S H)) ≤ S H * (Bc / Real.sqrt (S H)) := this
          _ = Bc * Real.sqrt (S H) := by
            rw [mul_div_assoc', mul_comm (S H), mul_div_assoc, Real.div_sqrt]
      rcases (hQnnH _ hmem).lt_or_eq with h | h
      · exact h
      · have := hzeroH _ hmem h.symm
        nlinarith [hg1.2.2]
    -- comparison with g(q0 √S)
    have hcmp : ∀ᶠ H in atTop, S H * v - k - 2 * C * (q0 * Real.sqrt (S H))
        - S H * D (q0 * Real.sqrt (S H)) - K1 ≤ F H (xs H) ∧
        F H (xs H) ≤ S H * v - k - 2 * C * Qs H - S H * D (Qs H) + K2 := by
      filter_upwards [hev2, hQpos] with H hH hQ
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS0, hn0s, hc0s, hG4, hG5, hG6⟩, hQnnH⟩, hupH⟩, hzeroH⟩, hgH⟩, hcontH⟩,
        hrepH⟩, hmem, hopt⟩, hq⟩ := hH
      have hsP : 0 < Real.sqrt (S H) := Real.sqrt_pos.mpr hS0
      have hss : Real.sqrt (S H) * Real.sqrt (S H) = S H := Real.mul_self_sqrt hS0.le
      have hqle : q0 * Real.sqrt (S H) ≤ c0 * S H := by
        rw [div_le_iff₀ hc0] at hq
        nlinarith
      have hg1 := hgH (q0 * Real.sqrt (S H)) (mul_pos hq0pos hsP) hqle
      exact ⟨le_trans hg1.2.2 (hopt _ hg1.1), hupH _ hmem hQ⟩
    have hineq : ∀ᶠ H in atTop, 2 * C * Qs H + S H * D (Qs H) ≤
        2 * C * (q0 * Real.sqrt (S H)) + S H * D (q0 * Real.sqrt (S H)) + (K1 + K2) := by
      filter_upwards [hcmp] with H h
      linarith [h.1, h.2]
    obtain ⟨hlim, hQinf⟩ := core atTop C A hC hA D hDpos hDanti hQD S hS Qs (fun _ => K1 + K2)
      (tendsto_const_nhds.div_atTop hs) hQpos hineq
    refine ⟨hlim, ?_⟩
    -- value
    have hSpos : ∀ᶠ H in atTop, 0 < S H := hS.eventually_gt_atTop 0
    have hDlim : Tendsto (fun H => D (Qs H)) atTop (𝓝 0) := by
      have h1 := (hQD.comp hQinf).mul (tendsto_inv_atTop_zero.comp hQinf)
      rw [mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [hQpos] with H hH
      simp only [Function.comp]
      field_simp
    have hq0inf : Tendsto (fun H => q0 * Real.sqrt (S H)) atTop atTop :=
      hs.const_mul_atTop hq0pos
    have hDlim2 : Tendsto (fun H => D (q0 * Real.sqrt (S H))) atTop (𝓝 0) := by
      have h1 := (hQD.comp hq0inf).mul (tendsto_inv_atTop_zero.comp hq0inf)
      rw [mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [hSpos] with H hH
      have : 0 < q0 * Real.sqrt (S H) := mul_pos hq0pos (Real.sqrt_pos.mpr hH)
      simp only [Function.comp]
      field_simp
    have hdivS : ∀ f : ℝ → ℝ, Tendsto (fun H => f H / Real.sqrt (S H)) atTop (𝓝 q0) →
        Tendsto (fun H => f H / S H) atTop (𝓝 0) := by
      intro f hf
      have h1 := hf.mul (tendsto_inv_atTop_zero.comp hs)
      rw [mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [hSpos] with H hH
      have hss : Real.sqrt (S H) * Real.sqrt (S H) = S H := Real.mul_self_sqrt hH.le
      simp only [Function.comp]
      rw [← div_eq_mul_inv, div_div, hss]
    have hQS : Tendsto (fun H => Qs H / S H) atTop (𝓝 0) := hdivS Qs hlim
    have hqS : Tendsto (fun H => q0 * Real.sqrt (S H) / S H) atTop (𝓝 0) := by
      apply hdivS
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hSpos] with H hH
      have : 0 < Real.sqrt (S H) := Real.sqrt_pos.mpr hH
      field_simp
    have hcS : ∀ c : ℝ, Tendsto (fun H => c / S H) atTop (𝓝 0) :=
      fun c => tendsto_const_nhds.div_atTop hS
    have hup' : Tendsto (fun H => v - k / S H - 2 * C * (Qs H / S H) - D (Qs H) + K2 / S H)
        atTop (𝓝 v) := by
      have := ((((tendsto_const_nhds (x := v)).sub (hcS k)).sub (hQS.const_mul (2 * C))).sub
        hDlim).add (hcS K2)
      simpa using this
    have hlow' : Tendsto (fun H => v - k / S H - 2 * C * (q0 * Real.sqrt (S H) / S H)
        - D (q0 * Real.sqrt (S H)) - K1 / S H) atTop (𝓝 v) := by
      have := ((((tendsto_const_nhds (x := v)).sub (hcS k)).sub (hqS.const_mul (2 * C))).sub
        hDlim2).sub (hcS K1)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow' hup' ?_ ?_
    · filter_upwards [hcmp, hSpos] with H h hH
      rw [le_div_iff₀ hH]
      have e : (v - k / S H - 2 * C * (q0 * Real.sqrt (S H) / S H) - D (q0 * Real.sqrt (S H))
          - K1 / S H) * S H = S H * v - k - 2 * C * (q0 * Real.sqrt (S H))
          - S H * D (q0 * Real.sqrt (S H)) - K1 := by
        field_simp
      rw [e]; exact h.1
    · filter_upwards [hcmp, hSpos] with H h hH
      rw [div_le_iff₀ hH]
      have e : (v - k / S H - 2 * C * (Qs H / S H) - D (Qs H) + K2 / S H) * S H
          = S H * v - k - 2 * C * Qs H - S H * D (Qs H) + K2 := by
        field_simp
      rw [e]; exact h.2

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set Topology ValueTrial.Asymptotic

namespace VBCTL




lemma vInf_eq2 (θ : Params) (hS : θ.Standing) :
    vInf θ = sig0 θ * (InventoryControl.normalLoss (θ.mu0 / sig0 θ) + (1 - θ.pN) * θ.mu0 / sig0 θ) := by
  have h0 := (sig0_pos θ hS).ne'
  rw [vInf_eq θ hS, ell]
  field_simp

lemma vInf_pos (θ : Params) (hS : θ.Standing) : 0 < vInf θ := by
  have := M0_lt θ hS
  have : 0 ≤ M0 θ := le_max_left _ _
  linarith

theorem ec3 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (cfix cr : ℝ)
    (hcfix : 0 ≤ cfix) (hcr : 0 < cr) (Tmax : ℝ) (hTmax : 0 < Tmax) (hC : 0 < Cnet θ) :
    (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | x.1 = Tmax ∧ 0 ≤ x.2} x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
          {x | x.1 = Tmax ∧ 0 ≤ x.2} (xs P)) →
      Tendsto (fun P => (xs P).2 / Real.sqrt P) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
            (Tmax * (θ.c * Tmax + cr - θ.don * (1 - 2 * θ.pN) * θ.mu0 * Tmax / 2))))) ∧
        Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
          (nhds (sig0 θ * (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
            + (1 - θ.pN) * θ.mu0 / sig0 θ))) := by
  have hn0 : 0 < θ.n0 := hS.2.2.2.1
  have hIN : 0 ≤ θ.IN := hS.2.2.2.2.2.2.1
  have hIS : 0 ≤ θ.IS := hS.2.2.2.2.2.2.2.1
  have hsig0 := sig0_pos θ hS
  set C' := Cnet θ + cr / Tmax with hC'
  have hC'pos : 0 < C' := by positivity
  set A := (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ * θ.n0 / 2) with hAdef
  have hA : 0 < A := by have := phi_pos (θ.mu0 / sig0 θ); positivity
  set Bc := (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * sig0 θ * θ.n0 with hBc
  set Dset : ℝ → Set (ℝ × ℝ) := fun _ => {x | x.1 = Tmax ∧ 0 ≤ x.2} with hDset
  set F : ℝ → ℝ × ℝ → ℝ := fun P => V θ (fun r => cfix + cr * r) (fixedPool P) with hF
  set Qf : ℝ × ℝ → ℝ := fun x => x.1 * x.2 / 2 with hQf
  set g : ℝ → ℝ → ℝ × ℝ := fun _ Q => (Tmax, 2 * Q / Tmax) with hg
  -- the value bounds rewritten with C'
  have hbd : ∀ P : ℝ, 0 < P → ∀ r : ℝ, 0 < r →
      P * vInf θ - cfix - 2 * C' * (Tmax * r / 2) - P * Dq θ (Tmax * r / 2) - (θ.IN + θ.IS)
        ≤ F P (Tmax, r) ∧
      F P (Tmax, r) ≤ P * vInf θ - cfix - 2 * C' * (Tmax * r / 2) - P * Dq θ (Tmax * r / 2) := by
    intro P hP r hr
    have h := V_bounds θ hS hρ (fun r => cfix + cr * r) (fixedPool P) Tmax r hTmax hr hP
    have e : cfix + cr * r + 2 * Cnet θ * (Tmax * r / 2) = cfix + 2 * C' * (Tmax * r / 2) := by
      rw [hC']; field_simp; ring
    simp only [fixedPool] at h
    simp only [hF]
    constructor <;> linarith [h.1, h.2]
  have hgen := gen (fun P => P) tendsto_id Dset F Qf g (vInf θ) (M0 θ) cfix C'
    (θ.IN + θ.IS) 0 0 A Bc θ.n0 1 (M0_lt θ hS) hC'pos hA hn0 one_pos (by positivity) le_rfl
    (Dq θ) (fun Q hQ => Dq_pos θ hS hQ) (fun Q1 Q2 h1 h12 => Dq_anti θ hS h1 h12)
    (QDq_tendsto θ hS) (fun Q hQ => by
      have := Dq_upper θ hS hQ; rw [hBc]; exact this)
    (Eventually.of_forall fun P x hx => by
      simp only [hDset, mem_setOf_eq] at hx
      simp only [hQf]; rw [hx.1]; have := hx.2; positivity)
    (by
      filter_upwards [eventually_gt_atTop 0] with P hP
      intro x hx hQ
      simp only [hDset, mem_setOf_eq] at hx
      obtain ⟨T, r⟩ := x
      simp only at hx
      obtain ⟨rfl, hr⟩ := hx
      have hr' : 0 < r := by
        simp only [hQf] at hQ
        rcases hr.lt_or_eq with h | h
        · exact h
        · rw [← h] at hQ; simp at hQ
      have := (hbd P hP r hr').2
      simp only [hQf]; linarith)
    (by
      filter_upwards [eventually_gt_atTop 0] with P hP
      intro x hx hQ
      have h := V_zero_le θ hS hρ (fun r => cfix + cr * r) (fixedPool P) x
        (by simp only [hQf] at hQ; linarith) hP.le
      simp only [hF, fixedPool] at h ⊢; linarith)
    (by
      filter_upwards [eventually_gt_atTop 0] with P hP
      intro Q hQ _
      have hr : 0 < 2 * Q / Tmax := by positivity
      refine ⟨⟨rfl, hr.le⟩, by simp only [hQf, hg]; field_simp, ?_⟩
      have := (hbd P hP (2 * Q / Tmax) hr).1
      rw [show Tmax * (2 * Q / Tmax) / 2 = Q by field_simp] at this
      simp only [hg]; linarith)
    (by
      filter_upwards [eventually_gt_atTop 0] with P hP
      intro Q hQ
      have hQ0 : 0 < Q := hQ.1
      apply ContinuousAt.continuousWithinAt
      have heq : (fun Q => F P (g P Q)) =ᶠ[𝓝 Q] fun Q =>
          -((cfix + cr * (2 * Q / Tmax)) + θ.c * Tmax * (2 * Q / Tmax))
          + θ.don * (Tmax * (2 * Q / Tmax) / 2) * (1 - 2 * θ.pN) * θ.mu0
          + Gpost θ P (Tmax * (2 * Q / Tmax) / 2) := by
        filter_upwards [Ioi_mem_nhds hQ0] with Q' hQ'
        simp only [hF, hg]
        exact V_eq_G θ hS hρ _ (fixedPool P) Tmax (2 * Q' / Tmax) hTmax
          (by simp at hQ'; positivity) hP
      refine ContinuousAt.congr ?_ heq.symm
      apply ContinuousAt.add (by fun_prop)
      have hG := Gpost_contAt θ hS hP (show 0 < Tmax * (2 * Q / Tmax) / 2 by positivity)
      exact ContinuousAt.comp (g := fun z : ℝ × ℝ => Gpost θ z.1 z.2)
        (f := fun Q : ℝ => (P, Tmax * (2 * Q / Tmax) / 2)) hG (by fun_prop))
    (Eventually.of_forall fun P x hx _ _ => by
      simp only [hDset, mem_setOf_eq] at hx
      obtain ⟨T, r⟩ := x
      simp only at hx
      obtain ⟨rfl, -⟩ := hx
      simp only [hg, hQf]
      rw [show 2 * (T * r / 2) / T = r by field_simp])
  obtain ⟨hex, hasym⟩ := hgen
  refine ⟨hex, fun xs hxs => ?_⟩
  obtain ⟨h1, h2⟩ := hasym xs hxs
  refine ⟨?_, by rw [← vInf_eq2 θ hS]; exact h2⟩
  have hconst : Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
      (Tmax * (θ.c * Tmax + cr - θ.don * (1 - 2 * θ.pN) * θ.mu0 * Tmax / 2)))
      = 2 / Tmax * Real.sqrt (A / (2 * C')) := by
    rw [show 2 / Tmax = Real.sqrt ((2 / Tmax) ^ 2) from (Real.sqrt_sq (by positivity)).symm,
      ← Real.sqrt_mul (sq_nonneg _), sqrt_n0_sigX θ hS, hAdef, phi0, hC', Cnet]
    congr 1
    field_simp
    ring
  rw [hconst]
  refine (h1.const_mul (2 / Tmax)).congr' ?_
  filter_upwards [hxs] with P hP
  have := hP.1.1
  simp only [hQf]
  rw [this]; field_simp

end VBCTL


open MeasureTheory ProbabilityTheory Filter Set Topology ValueTrial.Asymptotic

namespace VBCTL




/-- Upper bound valid also when the post-adoption population vanishes. -/
lemma V_upper0 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (ccap Ppop : ℝ → ℝ) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hPT : 0 ≤ Ppop T) :
    V θ ccap Ppop (T, r)
      ≤ Ppop T * vInf θ - ccap r - 2 * Cnet θ * (T * r / 2) - Ppop T * Dq θ (T * r / 2) := by
  rcases hPT.lt_or_eq with h | h
  · exact (V_bounds θ hS hρ ccap Ppop T r hT hr h).2
  · have h8 := equation_8 θ hS ccap Ppop T r hT hr hPT
    simp only [Prho, Ttil, hρ, if_true, neg_zero, zero_mul, Real.exp_zero, one_mul] at h8
    rw [h8, ← h, Cnet]
    simp only [zero_mul, add_zero, sub_zero]
    ring_nf; rfl

theorem ec2 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (k : ℝ) (hk : 0 ≤ k)
    (rmax : ℝ) (hrmax : 0 < rmax) (hrcap : rmax ≤ θ.zeta) (hC : 0 < Cnet θ) :
    (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ H in atTop, IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} (xs H)) →
      Tendsto (fun H => (xs H).1 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
            (Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ *
              (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
                + (1 - θ.pN) * θ.mu0 / sig0 θ))))) ∧
        Tendsto (fun H => V θ (fun _ => k) (fixedHorizon θ H) (xs H) / (θ.zeta * (H - θ.Del)))
          atTop (nhds (vInf θ)) := by
  have hn0 : 0 < θ.n0 := hS.2.2.2.1
  have hIN : 0 ≤ θ.IN := hS.2.2.2.2.2.2.1
  have hIS : 0 ≤ θ.IS := hS.2.2.2.2.2.2.2.1
  have hzeta : 0 < θ.zeta := hS.2.2.2.2.2.2.2.2.1
  have hDel : 0 ≤ θ.Del := hS.2.2.2.2.2.2.2.2.2.1
  have hsig0 := sig0_pos θ hS
  have hv := vInf_pos θ hS
  set v := vInf θ with hvdef
  set C' := Cnet θ + θ.zeta * v / rmax with hC'
  have hC'pos : 0 < C' := by positivity
  set A := (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * (sig0 θ * θ.n0 / 2) with hAdef
  have hA : 0 < A := by have := phi_pos (θ.mu0 / sig0 θ); positivity
  set Bc := (gaussianPDFReal 0 1) (θ.mu0 / sig0 θ) * sig0 θ * θ.n0 with hBc
  have hBc0 : 0 ≤ Bc := by have := phi_pos (θ.mu0 / sig0 θ); positivity
  set S : ℝ → ℝ := fun H => θ.zeta * (H - θ.Del) with hSdef
  have hSt : Tendsto S atTop atTop :=
    (tendsto_atTop_add_const_right _ (-θ.Del) tendsto_id).const_mul_atTop hzeta
  set Dset : ℝ → Set (ℝ × ℝ) := fun H => {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax}
    with hDset
  set F : ℝ → ℝ × ℝ → ℝ := fun H => V θ (fun _ => k) (fixedHorizon θ H) with hF
  set Qf : ℝ × ℝ → ℝ := fun x => x.1 * x.2 / 2 with hQf
  set g : ℝ → ℝ → ℝ × ℝ := fun _ Q => (2 * Q / rmax, rmax) with hg
  set K2 := 2 * θ.zeta / rmax * Bc with hK2
  have hPT : ∀ H T : ℝ, 0 < T → fixedHorizon θ H T = S H - θ.zeta * T := by
    intro H T hT; simp only [fixedHorizon, if_pos hT, hSdef]; ring
  have hQD : ∀ Q, 0 < Q → Q * Dq θ Q ≤ Bc := by
    intro Q hQ
    have := Dq_upper θ hS hQ
    rw [le_div_iff₀ hQ] at this
    rw [hBc]; linarith
  -- key two-sided estimate in terms of S
  have hkey : ∀ H T : ℝ, 0 < T → 0 ≤ fixedHorizon θ H T →
      F H (T, rmax) ≤ S H * v - k - 2 * C' * (T * rmax / 2) - S H * Dq θ (T * rmax / 2) + K2 := by
    intro H T hT hP
    have h := V_upper0 θ hS hρ (fun _ => k) (fixedHorizon θ H) T rmax hT hrmax hP
    rw [hPT H T hT] at h
    have hQ : 0 < T * rmax / 2 := by positivity
    have hq := hQD _ hQ
    have e : θ.zeta * T * Dq θ (T * rmax / 2) = 2 * θ.zeta / rmax * (T * rmax / 2 * Dq θ (T * rmax / 2)) := by
      field_simp
    have hle : θ.zeta * T * Dq θ (T * rmax / 2) ≤ K2 := by
      rw [e, hK2]; exact mul_le_mul_of_nonneg_left hq (by positivity)
    have e2 : θ.zeta * T * v = 2 * (θ.zeta * v / rmax) * (T * rmax / 2) := by field_simp
    simp only [hF]
    rw [hC']; nlinarith
  have hkeyL : ∀ H T : ℝ, 0 < T → 0 < fixedHorizon θ H T →
      S H * v - k - 2 * C' * (T * rmax / 2) - S H * Dq θ (T * rmax / 2) - (θ.IN + θ.IS)
        ≤ F H (T, rmax) := by
    intro H T hT hP
    have h := (V_bounds θ hS hρ (fun _ => k) (fixedHorizon θ H) T rmax hT hrmax hP).1
    rw [hPT H T hT] at h
    have hQ : 0 < T * rmax / 2 := by positivity
    have h0 : 0 ≤ θ.zeta * T * Dq θ (T * rmax / 2) :=
      mul_nonneg (by positivity) (Dq_pos θ hS hQ).le
    have e2 : θ.zeta * T * v = 2 * (θ.zeta * v / rmax) * (T * rmax / 2) := by field_simp
    simp only [hF]
    rw [hC']; nlinarith
  have hgen := gen S hSt Dset F Qf g v (M0 θ) k C' (θ.IN + θ.IS) K2 (θ.zeta * θ.Del * M0 θ)
    A Bc θ.n0 (rmax / (4 * θ.zeta)) (M0_lt θ hS) hC'pos hA hn0 (by positivity) (by positivity)
    (by positivity)
    (Dq θ) (fun Q hQ => Dq_pos θ hS hQ) (fun Q1 Q2 h1 h12 => Dq_anti θ hS h1 h12)
    (QDq_tendsto θ hS) (fun Q hQ => by
      have := Dq_upper θ hS hQ; rw [hBc]; exact this)
    (Eventually.of_forall fun H x hx => by
      simp only [hDset, mem_ofPred_eq] at hx
      simp only [hQf]; rw [hx.2.2]; have := hx.1; positivity)
    (Eventually.of_forall fun H x hx hQ => by
      simp only [hDset, mem_ofPred_eq] at hx
      obtain ⟨T, r⟩ := x
      simp only at hx
      obtain ⟨hT0, hTH, rfl⟩ := hx
      have hT : 0 < T := by
        simp only [hQf] at hQ
        rcases hT0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hQ; simp at hQ
      have hP : 0 ≤ fixedHorizon θ H T := by
        rw [hPT H T hT]; simp only [hSdef]; nlinarith
      exact hkey H T hT hP)
    (by
      filter_upwards [eventually_ge_atTop 0] with H hH
      intro x hx hQ
      have h := V_zero_le θ hS hρ (fun _ => k) (fixedHorizon θ H) x
        (by simp only [hQf] at hQ; linarith)
        (by simp only [fixedHorizon, lt_irrefl, if_false]; nlinarith)
      have hM := (le_max_left _ _ : (0:ℝ) ≤ M0 θ)
      simp only [hF, fixedHorizon, lt_irrefl, if_false] at h ⊢
      simp only [hSdef]
      nlinarith)
    (by
      filter_upwards [eventually_gt_atTop θ.Del] with H hH
      intro Q hQ hQc
      have hT : 0 < 2 * Q / rmax := by positivity
      have hTle : 2 * Q / rmax ≤ (H - θ.Del) / 2 := by
        have e : rmax / (4 * θ.zeta) * S H = rmax * (H - θ.Del) / 4 := by
          simp only [hSdef]; field_simp
        rw [e] at hQc
        rw [div_le_iff₀ hrmax]
        linarith
      have hP : 0 < fixedHorizon θ H (2 * Q / rmax) := by
        rw [hPT H _ hT]; simp only [hSdef]; nlinarith
      refine ⟨⟨hT.le, by linarith, rfl⟩, by simp only [hQf, hg]; field_simp, ?_⟩
      have := hkeyL H (2 * Q / rmax) hT hP
      rw [show 2 * Q / rmax * rmax / 2 = Q by field_simp] at this
      simp only [hg]; linarith)
    (by
      filter_upwards [eventually_gt_atTop θ.Del] with H hH
      intro Q hQ
      have hQ0 : 0 < Q := hQ.1
      have hT : 0 < 2 * Q / rmax := by positivity
      have hTle : 2 * Q / rmax ≤ (H - θ.Del) / 2 := by
        have hQc := hQ.2
        have e : rmax / (4 * θ.zeta) * S H = rmax * (H - θ.Del) / 4 := by
          simp only [hSdef]; field_simp
        rw [e] at hQc
        rw [div_le_iff₀ hrmax]
        linarith
      have hPpos : 0 < θ.zeta * (H - 2 * Q / rmax - θ.Del) := by nlinarith
      apply ContinuousAt.continuousWithinAt
      have hcP : ContinuousAt (fun Q : ℝ => θ.zeta * (H - 2 * Q / rmax - θ.Del)) Q := by fun_prop
      have heq : (fun Q => F H (g H Q)) =ᶠ[𝓝 Q] fun Q =>
          -(k + θ.c * (2 * Q / rmax) * rmax)
          + θ.don * (2 * Q / rmax * rmax / 2) * (1 - 2 * θ.pN) * θ.mu0
          + Gpost θ (θ.zeta * (H - 2 * Q / rmax - θ.Del)) (2 * Q / rmax * rmax / 2) := by
        filter_upwards [Ioi_mem_nhds hQ0, hcP.eventually (Ioi_mem_nhds hPpos)] with Q' hQ' hP'
        simp only [mem_Ioi] at hQ' hP'
        have hT' : 0 < 2 * Q' / rmax := by positivity
        have hfh : fixedHorizon θ H (2 * Q' / rmax) = θ.zeta * (H - 2 * Q' / rmax - θ.Del) := by
          simp only [fixedHorizon, if_pos hT']
        simp only [hF, hg]
        rw [V_eq_G θ hS hρ _ (fixedHorizon θ H) (2 * Q' / rmax) rmax hT' hrmax
          (by rw [hfh]; exact hP'), hfh]
      refine ContinuousAt.congr ?_ heq.symm
      apply ContinuousAt.add (by fun_prop)
      have hG := Gpost_contAt θ hS hPpos (show 0 < 2 * Q / rmax * rmax / 2 by positivity)
      exact ContinuousAt.comp (g := fun z : ℝ × ℝ => Gpost θ z.1 z.2)
        (f := fun Q : ℝ => (θ.zeta * (H - 2 * Q / rmax - θ.Del), 2 * Q / rmax * rmax / 2))
        hG (by fun_prop))
    (Eventually.of_forall fun H x hx _ _ => by
      simp only [hDset, mem_ofPred_eq] at hx
      obtain ⟨T, r⟩ := x
      simp only at hx
      obtain ⟨-, -, rfl⟩ := hx
      simp only [hg, hQf]
      rw [show 2 * (T * r / 2) / r = T by field_simp])
  obtain ⟨hex, hasym⟩ := hgen
  refine ⟨hex, fun xs hxs => ?_⟩
  obtain ⟨h1, h2⟩ := hasym xs hxs
  refine ⟨?_, h2⟩
  have hconst : Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
      (Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ *
        (InventoryControl.normalLoss (θ.mu0 / sig0 θ) + (1 - θ.pN) * θ.mu0 / sig0 θ)))
      = 2 / rmax * Real.sqrt (A / (2 * C')) := by
    rw [show 2 / rmax = Real.sqrt ((2 / rmax) ^ 2) from (Real.sqrt_sq (by positivity)).symm,
      ← Real.sqrt_mul (sq_nonneg _), sqrt_n0_sigX θ hS, hAdef, phi0, hC', hvdef,
      vInf_eq2 θ hS]
    congr 1
    field_simp
  rw [hconst]
  refine (h1.const_mul (2 / rmax)).congr' ?_
  filter_upwards [hxs] with H hH
  have := hH.1.2.2
  simp only [hQf, hSdef]
  rw [this]; field_simp

end VBCTL

open ValueTrial.Asymptotic

theorem solution (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (k : ℝ) (hk : 0 ≤ k)
    (rmax : ℝ) (hrmax : 0 < rmax) (hrcap : rmax ≤ θ.zeta) (hC : 0 < Cnet θ) :
    (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ H in atTop, IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} (xs H)) →
      Tendsto (fun H => (xs H).1 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
            (Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ *
              (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
                + (1 - θ.pN) * θ.mu0 / sig0 θ))))) ∧
        Tendsto (fun H => V θ (fun _ => k) (fixedHorizon θ H) (xs H) / (θ.zeta * (H - θ.Del)))
          atTop (nhds (vInf θ)) :=
  VBCTL.ec2 θ hS hρ k hk rmax hrmax hrcap hC
