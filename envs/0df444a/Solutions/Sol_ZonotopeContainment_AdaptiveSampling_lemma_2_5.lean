-- Prove2me | solution 1 for ZonotopeContainment.AdaptiveSampling.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:24:46.102569+00:00
-- url     : https://prove2.me/submissions/09f22610-43ed-47b4-aad7-b0bcd681e3a1

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped MatrixOrder
open ZonotopeContainment.AdaptiveSampling

namespace Lemma25Aux

noncomputable def phi (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- x ^ 2 / 2)

noncomputable def qDeriv (t : ℝ) : ℝ :=
  if |t| ≤ 1 then 0 else if 0 ≤ t then -(1 / t ^ 2) else 1 / t ^ 2

lemma phi_nonneg (x : ℝ) : 0 ≤ phi x := by
  unfold phi
  positivity

lemma phi_even (x : ℝ) : phi (-x) = phi x := by
  unfold phi
  rw [neg_sq]

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (- x * phi x) x := by
  have h1 : HasDerivAt (fun y : ℝ => - y ^ 2 / 2) (- x) x := by
    have hmul : HasDerivAt (fun y : ℝ => - (y * y) / 2) (- (1 * x + x * 1) / 2) x :=
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).neg).div_const (2 : ℝ)
    have hf : (fun y : ℝ => - (y * y) / 2) = (fun y : ℝ => - y ^ 2 / 2) := by
      ext y; simp [sq]
    have hd : - (1 * x + x * 1) / 2 = - x := by ring
    rwa [hf, hd] at hmul
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (- y ^ 2 / 2))
      (Real.exp (- x ^ 2 / 2) * (- x)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  have h3 := h2.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have heq2 : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (- x ^ 2 / 2) * (- x)) = - x * phi x := by
    unfold phi; ring
  rwa [heq2] at h3

lemma tendsto_phi_atTop : Tendsto phi atTop (𝓝 0) := by
  unfold phi
  have h1 : Tendsto (fun x : ℝ => - x ^ 2 / 2) atTop atBot := by
    have hp : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hneg : Tendsto (fun x : ℝ => - (x ^ 2)) atTop atBot := tendsto_neg_atTop_atBot.comp hp
    exact hneg.atBot_div_const (by norm_num)
  simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.sqrt (2 * Real.pi))⁻¹

lemma tendsto_phi_atBot : Tendsto phi atBot (𝓝 0) := by
  have : (phi : ℝ → ℝ) = fun x => phi (-x) := by ext x; rw [phi_even]
  rw [this]
  exact tendsto_phi_atTop.comp tendsto_neg_atBot_atTop

lemma pdf_eq_phi (x : ℝ) : gaussianPDFReal 0 1 x = phi x := by
  unfold gaussianPDFReal phi
  simp [div_eq_mul_inv, mul_comm]

lemma integral_gaussian_eq_phi {f : ℝ → ℝ} :
    (∫ x : ℝ, f x ∂gaussianReal 0 1) = ∫ x : ℝ, phi x * f x := by
  rw [integral_gaussianReal_eq_integral_smul (hv := one_ne_zero)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [pdf_eq_phi, smul_eq_mul]

lemma integrable_phi : Integrable phi := by
  have h : gaussianPDFReal 0 1 = phi := funext pdf_eq_phi
  exact h ▸ integrable_gaussianPDFReal 0 1

lemma integral_Ioi_x_phi :
    IntegrableOn (fun x => x * phi x) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), x * phi x) = phi 0 := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => - phi y) (x * phi x) x := by
    intro x _
    have h := (hasDerivAt_phi x).neg
    have heq : - (- x * phi x) = x * phi x := by ring
    rwa [heq] at h
  have hcont : ContinuousWithinAt (fun y => - phi y) (Ici 0) 0 :=
    (hasDerivAt_phi 0).continuousAt.neg.continuousWithinAt
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * phi x :=
    fun x hx => mul_nonneg (le_of_lt hx) (phi_nonneg x)
  have htend : Tendsto (fun y => - phi y) atTop (𝓝 0) := by
    simpa using tendsto_phi_atTop.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
  linarith

lemma integral_Iic_neg_x_phi :
    IntegrableOn (fun x => - x * phi x) (Iic 0) ∧
    (∫ x in Iic (0 : ℝ), - x * phi x) = phi 0 := by
  have h1 := integral_Ioi_x_phi.1
  have hIci_int : IntegrableOn (fun x => x * phi x) (Ici 0) :=
    h1.congr_set_ae Ioi_ae_eq_Ici.symm
  have hind : Integrable ((Ici (0 : ℝ)).indicator (fun y => y * phi y)) :=
    (integrable_indicator_iff measurableSet_Ici).mpr hIci_int
  have hind_neg : Integrable (fun x => (Ici (0 : ℝ)).indicator (fun y => y * phi y) (0 - x)) :=
    hind.comp_sub_left 0
  have hint_left : IntegrableOn (fun x => - x * phi x) (Iic 0) := by
    rw [← integrable_indicator_iff measurableSet_Iic]
    refine hind_neg.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [zero_sub]
    by_cases hx : x ≤ 0
    · have hx' : (-x) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
      have hx_mem : x ∈ Iic (0 : ℝ) := Set.mem_Iic.mpr hx
      rw [indicator_of_mem hx', indicator_of_mem hx_mem, phi_even]
    · have hx' : (-x) ∉ Ici (0 : ℝ) := by simp [Set.mem_Ici]; linarith
      have hx_nmem : x ∉ Iic (0 : ℝ) := hx
      rw [indicator_of_notMem hx', indicator_of_notMem hx_nmem]
  refine ⟨hint_left, ?_⟩
  have hderiv : ∀ x ∈ Iio (0 : ℝ), HasDerivAt phi (- x * phi x) x :=
    fun x _ => hasDerivAt_phi x
  have hcont : ContinuousWithinAt phi (Iic 0) 0 :=
    (hasDerivAt_phi 0).continuousAt.continuousWithinAt
  have hval := integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv hint_left tendsto_phi_atBot
  linarith

lemma integrable_abs_x_phi : Integrable (fun x => |x| * phi x) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine integral_Iic_neg_x_phi.1.congr_fun (fun x hx => ?_) measurableSet_Iic
    have hx0 : x ≤ 0 := hx
    simp [abs_of_nonpos hx0]
  · refine integral_Ioi_x_phi.1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 ≤ x := le_of_lt hx
    simp [abs_of_nonneg hx0]

lemma q_even (t : ℝ) : q (-t) = q t := by
  unfold q; rw [abs_neg]

lemma q_nonneg (t : ℝ) : 0 ≤ q t := by
  unfold q
  exact div_nonneg zero_le_one (le_trans zero_le_one (le_max_left 1 |t|))

lemma q_le_one (t : ℝ) : q t ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  exact (div_le_one hpos).mpr (le_max_left 1 |t|)

lemma abs_mul_q_le_one (t : ℝ) : |t * q t| ≤ 1 := by
  unfold q
  have hpos : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  rw [abs_mul, abs_div, abs_one, abs_of_pos hpos, mul_one_div]
  exact (div_le_one hpos).mpr (le_max_right 1 |t|)

lemma one_sub_q_le_abs_mul_q (t : ℝ) : 1 - q t ≤ |t| * q t := by
  unfold q
  by_cases ht : |t| ≤ 1
  · rw [max_eq_left ht, div_one, sub_self, mul_one]
    exact abs_nonneg t
  · have ht1 : 1 < |t| := not_le.mp ht
    have hpos : 0 < |t| := lt_trans zero_lt_one ht1
    rw [max_eq_right (le_of_lt ht1), mul_one_div, div_self (ne_of_gt hpos)]
    linarith [div_nonneg zero_le_one (le_of_lt hpos)]

lemma q_continuous : Continuous q := by
  unfold q
  exact continuous_const.div (continuous_const.max continuous_abs)
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |x|)))

lemma phi_measurable : Measurable phi := by
  unfold phi
  exact measurable_const.mul (Real.continuous_exp.measurable.comp
    ((measurable_id.pow_const 2).neg.div_const 2))

lemma qDeriv_measurable : Measurable qDeriv := by
  unfold qDeriv
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_le measurable_const measurable_id)
      (measurable_const.div (measurable_id.pow_const 2)).neg
      (measurable_const.div (measurable_id.pow_const 2)))

lemma abs_qDeriv_le_one (t : ℝ) : |qDeriv t| ≤ 1 := by
  unfold qDeriv
  split_ifs with h1 h2
  · simp
  · have ht1 : 1 < |t| := not_le.mp h1
    have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
    rw [abs_neg, abs_div, abs_one, abs_of_pos (by positivity : 0 < t ^ 2)]
    exact (div_le_one (by positivity)).mpr hsq
  · have ht1 : 1 < |t| := not_le.mp h1
    have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
    rw [abs_div, abs_one, abs_of_pos (by positivity : 0 < t ^ 2)]
    exact (div_le_one (by positivity)).mpr hsq

lemma qDeriv_odd (t : ℝ) : qDeriv (-t) = - qDeriv t := by
  unfold qDeriv
  rw [abs_neg]
  by_cases h1 : |t| ≤ 1
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    by_cases h0 : t = 0
    · subst h0; simp at h1
    · by_cases h2 : 0 ≤ t
      · have hneg : ¬ (0 ≤ -t) := by linarith [lt_of_le_of_ne h2 (Ne.symm h0)]
        simp [h2, hneg]
      · have hpos : 0 ≤ -t := by linarith [not_le.mp h2]
        simp [h2, hpos]

lemma gaussian_odd_shift_nonneg {m σ : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ)
    {H : ℝ → ℝ} (hodd : ∀ y, H (-y) = - H y) (hpos : ∀ y, 0 < y → 0 ≤ H y)
    (hint : Integrable (fun x => H (m + σ * x) * phi x)) :
    0 ≤ ∫ x : ℝ, H (m + σ * x) * phi x := by
  set c : ℝ := - (2 * m / σ)
  let F : ℝ → ℝ := fun x => H (m + σ * x) * phi x
  have hint_c : Integrable (fun x => F (c - x)) := hint.comp_sub_left c
  have hsum_eq : (∫ x : ℝ, F x + F (c - x)) = 2 * ∫ x : ℝ, F x := by
    rw [integral_add hint hint_c, integral_sub_left_eq_self F volume c]
    ring
  have hnn : ∀ x : ℝ, 0 ≤ F x + F (c - x) := by
    intro x
    set y : ℝ := m + σ * x
    have hcy : m + σ * (c - x) = - y := by
      dsimp [c, y]
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ
      field_simp [hσ_ne]
      ring
    have hF_rw : F x + F (c - x) = H y * (phi x - phi (c - x)) := by
      dsimp [F]
      rw [hcy, hodd y]
      ring
    rw [hF_rw]
    have hsq_diff : (c - x) ^ 2 - x ^ 2 = (4 * m / σ ^ 2) * y := by
      dsimp [c, y]
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ
      field_simp [hσ_ne]
      ring
    by_cases hy : 0 < y
    · have hHy : 0 ≤ H y := hpos y hy
      have hdiff_nn : 0 ≤ (c - x) ^ 2 - x ^ 2 := by rw [hsq_diff]; positivity
      have hexp_le : - (c - x) ^ 2 / 2 ≤ - x ^ 2 / 2 := by linarith
      have hphi_le : phi (c - x) ≤ phi x := by
        unfold phi
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by positivity)
      exact mul_nonneg hHy (sub_nonneg.mpr hphi_le)
    · by_cases hy0 : y = 0
      · have h0 := hodd 0
        rw [neg_zero] at h0
        have hH0 : H 0 = 0 := by linarith
        simp [hy0, hH0]
      · have hy_neg : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
        have hHy : H y ≤ 0 := by
          have := hpos (-y) (by linarith)
          linarith [hodd y]
        have hdiff_np : (c - x) ^ 2 - x ^ 2 ≤ 0 := by
          rw [hsq_diff]
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hy_neg)
        have hexp_ge : - x ^ 2 / 2 ≤ - (c - x) ^ 2 / 2 := by linarith
        have hphi_ge : phi x ≤ phi (c - x) := by
          unfold phi
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_ge) (by positivity)
        exact mul_nonneg_of_nonpos_of_nonpos hHy (sub_nonpos.mpr hphi_ge)
  have hint_nn : 0 ≤ ∫ x : ℝ, F x + F (c - x) := integral_nonneg hnn
  linarith

lemma gaussian_ibp_q {m σ L : ℝ} (hσ : 0 < σ) (hL : 1 ≤ L) :
    (∫ x : ℝ, x * q ((m + σ * x) / L) * phi x) =
      (σ / L) * ∫ x : ℝ, qDeriv ((m + σ * x) / L) * phi x := by
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlin_meas : Measurable (fun x : ℝ => (m + σ * x) / L) :=
    (measurable_const.add (measurable_const.mul measurable_id)).div_const L
  set a : ℝ := (- L - m) / σ
  set b : ℝ := (L - m) / σ
  have hab : a < b := div_lt_div_of_pos_right (by linarith) hσ
  let G : ℝ → ℝ := fun x =>
    ((σ / L) * qDeriv ((m + σ * x) / L) - x * q ((m + σ * x) / L)) * phi x
  have hG_meas : AEStronglyMeasurable G volume :=
    (((measurable_const.mul (qDeriv_measurable.comp hlin_meas)).sub
      (measurable_id.mul (q_continuous.measurable.comp hlin_meas))).mul
      phi_measurable).aestronglyMeasurable
  have hG_int : Integrable G := by
    refine (integrable_phi.const_mul (σ / L) |>.add integrable_abs_x_phi).mono' hG_meas ?_
    refine ae_of_all _ (fun x => ?_)
    simp only [G, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (phi_nonneg x)]
    have h1 : |(σ / L) * qDeriv ((m + σ * x) / L) - x * q ((m + σ * x) / L)| ≤
        (σ / L) + |x| := by
      have hqd : |(σ / L) * qDeriv ((m + σ * x) / L)| ≤ σ / L := by
        rw [abs_mul, abs_of_pos (div_pos hσ hL_pos)]
        calc
          (σ / L) * |qDeriv ((m + σ * x) / L)| ≤ (σ / L) * 1 :=
            mul_le_mul_of_nonneg_left (abs_qDeriv_le_one _) (le_of_lt (div_pos hσ hL_pos))
          _ = σ / L := mul_one _
      have hxq : |x * q ((m + σ * x) / L)| ≤ |x| := by
        rw [abs_mul, abs_of_nonneg (q_nonneg _)]
        calc
          |x| * q ((m + σ * x) / L) ≤ |x| * 1 :=
            mul_le_mul_of_nonneg_left (q_le_one _) (abs_nonneg x)
          _ = |x| := mul_one _
      linarith [abs_sub ((σ / L) * qDeriv ((m + σ * x) / L)) (x * q ((m + σ * x) / L))]
    calc
      |(σ / L) * qDeriv ((m + σ * x) / L) - x * q ((m + σ * x) / L)| * phi x
        ≤ ((σ / L) + |x|) * phi x := mul_le_mul_of_nonneg_right h1 (phi_nonneg x)
      _ = (σ / L) * phi x + |x| * phi x := by ring
  -- Part 1: (-∞, a]
  let f₁ : ℝ → ℝ := fun x => (- L / (m + σ * x)) * phi x
  have hIic : (∫ x in Iic a, G x) = phi a := by
    have hm_a : m + σ * a = - L := by dsimp [a]; field_simp [ne_of_gt hσ]; ring
    have hf₁_a : f₁ a = phi a := by dsimp [f₁]; rw [hm_a, div_self (by linarith)]; ring
    have hcont₁ : ContinuousWithinAt f₁ (Iic a) a := by
      refine ContinuousAt.continuousWithinAt ?_
      dsimp [f₁]
      refine (continuousAt_const.div ?_ (by rw [hm_a]; linarith)).mul
        (hasDerivAt_phi a).continuousAt
      exact continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    have hderiv₁ : ∀ x ∈ Iio a, HasDerivAt f₁ (G x) x := by
      intro x hx
      have hx_lt : x < a := hx
      have hmx_lt : m + σ * x < - L := by
        have := mul_lt_mul_of_pos_left hx_lt hσ; linarith [hm_a]
      have hmx_ne : m + σ * x ≠ 0 := by linarith
      have ht_lt : (m + σ * x) / L < -1 := by rw [div_lt_iff₀ hL_pos]; linarith
      have htabs : ¬ (|(m + σ * x) / L| ≤ 1) := fun habs => by linarith [(abs_le.mp habs).1]
      have htneg : ¬ (0 ≤ (m + σ * x) / L) := by linarith
      have hq_eq : q ((m + σ * x) / L) = - L / (m + σ * x) := by
        unfold q
        have hlt0 : (m + σ * x) / L < 0 := by linarith
        rw [abs_of_neg hlt0, max_eq_right (by linarith)]
        field_simp [ne_of_gt hL_pos, hmx_ne]
      have hqd_eq : (σ / L) * qDeriv ((m + σ * x) / L) = L * σ / (m + σ * x) ^ 2 := by
        unfold qDeriv
        rw [if_neg htabs, if_neg htneg]
        field_simp [ne_of_gt hL_pos, hmx_ne]
      have hd_lin : HasDerivAt (fun y => m + σ * y) σ x := by
        simpa using ((hasDerivAt_id x).const_mul σ).const_add m
      have hd_rat : HasDerivAt (fun y => - L / (m + σ * y)) (L * σ / (m + σ * x) ^ 2) x := by
        have h := (hasDerivAt_const x (- L)).div hd_lin hmx_ne
        have heq : (0 * (m + σ * x) - - L * σ) / (m + σ * x) ^ 2 =
            L * σ / (m + σ * x) ^ 2 := by ring
        rwa [heq] at h
      have hd_prod := hd_rat.mul (hasDerivAt_phi x)
      have heq_prod : L * σ / (m + σ * x) ^ 2 * phi x +
          - L / (m + σ * x) * (- x * phi x) = G x := by
        dsimp [G]; rw [hq_eq, hqd_eq]; ring
      rwa [heq_prod] at hd_prod
    have htend₁ : Tendsto f₁ atBot (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_phi_atBot.neg |> fun h => by simpa using h) tendsto_phi_atBot ?_ ?_
      · filter_upwards [eventually_le_atBot a] with x hx
        have hmx_le : m + σ * x ≤ - L := by
          have := mul_le_mul_of_nonneg_left hx (le_of_lt hσ); linarith [hm_a]
        have hrat_nn : 0 ≤ - L / (m + σ * x) :=
          div_nonneg_of_nonpos (by linarith) (by linarith)
        have : 0 ≤ f₁ x := mul_nonneg hrat_nn (phi_nonneg x)
        linarith [phi_nonneg x]
      · filter_upwards [eventually_le_atBot a] with x hx
        have hmx_le : m + σ * x ≤ - L := by
          have := mul_le_mul_of_nonneg_left hx (le_of_lt hσ); linarith [hm_a]
        have hrat_le : - L / (m + σ * x) ≤ 1 := by
          have hmx_ne : m + σ * x ≠ 0 := by linarith
          have hnmx_ne : - (m + σ * x) ≠ 0 := by linarith
          have h1 : - L / (m + σ * x) = L / (- (m + σ * x)) := by
            field_simp [hmx_ne, hnmx_ne]
          rw [h1]
          exact (div_le_one (by linarith)).mpr (by linarith)
        calc
          f₁ x ≤ 1 * phi x := mul_le_mul_of_nonneg_right hrat_le (phi_nonneg x)
          _ = phi x := one_mul _
    have hint₁ := integral_Iic_of_hasDerivAt_of_tendsto hcont₁ hderiv₁ hG_int.integrableOn htend₁
    rw [hint₁, hf₁_a, sub_zero]
  -- Part 2: (a, b]
  have hIoc : (∫ x in Ioc a b, G x) = phi b - phi a := by
    have hm_a : m + σ * a = - L := by dsimp [a]; field_simp [ne_of_gt hσ]; ring
    have hm_b : m + σ * b = L := by dsimp [b]; field_simp [ne_of_gt hσ]; ring
    have hcongr : (∫ x in Ioc a b, G x) = ∫ x in Ioc a b, (- x * phi x) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      have hmx_gt : - L < m + σ * x := by
        have := mul_lt_mul_of_pos_left hx.1 hσ; linarith [hm_a]
      have hmx_le : m + σ * x ≤ L := by
        have := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hσ); linarith [hm_b]
      have htabs : |(m + σ * x) / L| ≤ 1 := by
        rw [abs_le]
        exact ⟨(le_div_iff₀ hL_pos).mpr (by linarith), (div_le_iff₀ hL_pos).mpr (by linarith)⟩
      have hq1 : q ((m + σ * x) / L) = 1 := by unfold q; rw [max_eq_left htabs, div_one]
      have hqd0 : qDeriv ((m + σ * x) / L) = 0 := by unfold qDeriv; rw [if_pos htabs]
      dsimp [G]; rw [hq1, hqd0]; ring
    rw [hcongr, ← intervalIntegral.integral_of_le (le_of_lt hab)]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_phi x) ?_
    have hcont_neg : Continuous (fun x : ℝ => - x * phi x) :=
      (continuous_id.neg).mul (by
        unfold phi
        exact continuous_const.mul (Real.continuous_exp.comp
          ((continuous_pow 2).neg.div_const 2)))
    exact hcont_neg.intervalIntegrable a b
  -- Part 3: (b, ∞)
  let f₃ : ℝ → ℝ := fun x => (L / (m + σ * x)) * phi x
  have hIoi : (∫ x in Ioi b, G x) = - phi b := by
    have hm_b : m + σ * b = L := by dsimp [b]; field_simp [ne_of_gt hσ]; ring
    have hf₃_b : f₃ b = phi b := by dsimp [f₃]; rw [hm_b, div_self (ne_of_gt hL_pos), one_mul]
    have hcont₃ : ContinuousWithinAt f₃ (Ici b) b := by
      refine ContinuousAt.continuousWithinAt ?_
      dsimp [f₃]
      refine (continuousAt_const.div ?_ (by rw [hm_b]; exact ne_of_gt hL_pos)).mul
        (hasDerivAt_phi b).continuousAt
      exact continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    have hderiv₃ : ∀ x ∈ Ioi b, HasDerivAt f₃ (G x) x := by
      intro x hx
      have hx_gt : b < x := hx
      have hmx_gt : L < m + σ * x := by
        have := mul_lt_mul_of_pos_left hx_gt hσ; linarith [hm_b]
      have hmx_ne : m + σ * x ≠ 0 := by linarith
      have ht_gt : 1 < (m + σ * x) / L := (one_lt_div hL_pos).mpr hmx_gt
      have htabs : ¬ (|(m + σ * x) / L| ≤ 1) := fun habs => by linarith [(abs_le.mp habs).2]
      have htnn : 0 ≤ (m + σ * x) / L := by linarith
      have hq_eq : q ((m + σ * x) / L) = L / (m + σ * x) := by
        unfold q
        rw [abs_of_nonneg htnn, max_eq_right (le_of_lt ht_gt)]
        field_simp [ne_of_gt hL_pos, hmx_ne]
      have hqd_eq : (σ / L) * qDeriv ((m + σ * x) / L) = - (L * σ / (m + σ * x) ^ 2) := by
        unfold qDeriv
        rw [if_neg htabs, if_pos htnn]
        field_simp [ne_of_gt hL_pos, hmx_ne]
      have hd_lin : HasDerivAt (fun y => m + σ * y) σ x := by
        simpa using ((hasDerivAt_id x).const_mul σ).const_add m
      have hd_rat : HasDerivAt (fun y => L / (m + σ * y)) (- (L * σ / (m + σ * x) ^ 2)) x := by
        have h := (hasDerivAt_const x L).div hd_lin hmx_ne
        have heq : (0 * (m + σ * x) - L * σ) / (m + σ * x) ^ 2 =
            - (L * σ / (m + σ * x) ^ 2) := by ring
        rwa [heq] at h
      have hd_prod := hd_rat.mul (hasDerivAt_phi x)
      have heq_prod : - (L * σ / (m + σ * x) ^ 2) * phi x +
          L / (m + σ * x) * (- x * phi x) = G x := by
        dsimp [G]; rw [hq_eq, hqd_eq]; ring
      rwa [heq_prod] at hd_prod
    have htend₃ : Tendsto f₃ atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_phi_atTop.neg |> fun h => by simpa using h) tendsto_phi_atTop ?_ ?_
      · filter_upwards [eventually_ge_atTop b] with x hx
        have hmx_ge : L ≤ m + σ * x := by
          have := mul_le_mul_of_nonneg_left hx (le_of_lt hσ); linarith [hm_b]
        have hrat_nn : 0 ≤ L / (m + σ * x) := div_nonneg (le_of_lt hL_pos) (by linarith)
        have : 0 ≤ f₃ x := mul_nonneg hrat_nn (phi_nonneg x)
        linarith [phi_nonneg x]
      · filter_upwards [eventually_ge_atTop b] with x hx
        have hmx_ge : L ≤ m + σ * x := by
          have := mul_le_mul_of_nonneg_left hx (le_of_lt hσ); linarith [hm_b]
        have hrat_le : L / (m + σ * x) ≤ 1 := (div_le_one (by linarith)).mpr hmx_ge
        calc
          f₃ x ≤ 1 * phi x := mul_le_mul_of_nonneg_right hrat_le (phi_nonneg x)
          _ = phi x := one_mul _
    have hint₃ := integral_Ioi_of_hasDerivAt_of_tendsto hcont₃ hderiv₃ hG_int.integrableOn htend₃
    rw [hint₃, hf₃_b, zero_sub]
  -- Combine all three pieces
  have hG_zero : (∫ x : ℝ, G x) = 0 := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := b),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hG_int.integrableOn
        hG_int.integrableOn,
      ← Iic_union_Ioc_eq_Iic (le_of_lt hab),
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hG_int.integrableOn
        hG_int.integrableOn,
      hIic, hIoc, hIoi]
    ring
  have hint_qd : Integrable (fun x => (σ / L) * (qDeriv ((m + σ * x) / L) * phi x)) := by
    have hm_qd : AEStronglyMeasurable
        (fun x => (σ / L) * (qDeriv ((m + σ * x) / L) * phi x)) volume :=
      (measurable_const.mul ((qDeriv_measurable.comp hlin_meas).mul phi_measurable)).aestronglyMeasurable
    refine (integrable_phi.const_mul (σ / L)).mono' hm_qd (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (div_pos hσ hL_pos), abs_mul, abs_of_nonneg (phi_nonneg x)]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hσ hL_pos))
    calc
      |qDeriv ((m + σ * x) / L)| * phi x ≤ 1 * phi x :=
        mul_le_mul_of_nonneg_right (abs_qDeriv_le_one _) (phi_nonneg x)
      _ = phi x := one_mul _
  have hint_xq : Integrable (fun x => x * q ((m + σ * x) / L) * phi x) := by
    have hm_xq : AEStronglyMeasurable (fun x => x * q ((m + σ * x) / L) * phi x) volume :=
      ((measurable_id.mul (q_continuous.measurable.comp hlin_meas)).mul phi_measurable).aestronglyMeasurable
    refine integrable_abs_x_phi.mono' hm_xq (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (q_nonneg _), abs_of_nonneg (phi_nonneg x)]
    apply mul_le_mul_of_nonneg_right _ (phi_nonneg x)
    calc
      |x| * q ((m + σ * x) / L) ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (q_le_one _) (abs_nonneg x)
      _ = |x| := mul_one _
  have hsub : G = fun x =>
      (σ / L) * (qDeriv ((m + σ * x) / L) * phi x) - x * q ((m + σ * x) / L) * phi x := by
    ext x; dsimp [G]; ring
  rw [hsub, integral_sub hint_qd hint_xq, integral_const_mul] at hG_zero
  linarith

end Lemma25Aux

theorem solution (m σ L : ℝ) (hm : 0 ≤ m) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hL : 1 ≤ L) :
    m * (∫ x : ℝ, q ((m + σ * x) / L) ∂gaussianReal 0 1) ≤
      2 * (∫ x : ℝ, (m + σ * x) * q ((m + σ * x) / L) ∂gaussianReal 0 1) ∧
    (∫ x : ℝ, 1 - q ((m + σ * x) / L) ∂gaussianReal 0 1) ≤
      (1 + ∫ x : ℝ, (m + σ * x) * q ((m + σ * x) / L) ∂gaussianReal 0 1) / L := by
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  by_cases hσ0 : σ = 0
  · subst hσ0
    simp only [zero_mul, add_zero, integral_const, probReal_univ, one_smul]
    refine ⟨?_, ?_⟩
    · have hnn : 0 ≤ m * q (m / L) := mul_nonneg hm (Lemma25Aux.q_nonneg _)
      linarith
    · rw [le_div_iff₀ hL_pos]
      have h1 := Lemma25Aux.one_sub_q_le_abs_mul_q (m / L)
      rw [abs_of_nonneg (div_nonneg hm (le_of_lt hL_pos))] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
      have hrew : L * (m / L * q (m / L)) = m * q (m / L) := by field_simp [ne_of_gt hL_pos]
      linarith
  · have hσ_pos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
    have hphi_meas : Measurable Lemma25Aux.phi := Lemma25Aux.phi_measurable
    have hlin_meas : Measurable (fun x : ℝ => (m + σ * x) / L) :=
      (measurable_const.add (measurable_const.mul measurable_id)).div_const L
    have hint_q : Integrable (fun x => q ((m + σ * x) / L) * Lemma25Aux.phi x) := by
      refine Lemma25Aux.integrable_phi.mono'
        ((Lemma25Aux.q_continuous.measurable.comp hlin_meas).mul hphi_meas).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (Lemma25Aux.q_nonneg _),
        abs_of_nonneg (Lemma25Aux.phi_nonneg x)]
      calc
        q ((m + σ * x) / L) * Lemma25Aux.phi x ≤ 1 * Lemma25Aux.phi x :=
          mul_le_mul_of_nonneg_right (Lemma25Aux.q_le_one _) (Lemma25Aux.phi_nonneg x)
        _ = Lemma25Aux.phi x := one_mul _
    have hint_Yq : Integrable (fun x =>
        ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) := by
      refine (Lemma25Aux.integrable_phi.const_mul L).mono'
        (((measurable_const.add (measurable_const.mul measurable_id)).mul
          (Lemma25Aux.q_continuous.measurable.comp hlin_meas)).mul hphi_meas).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (Lemma25Aux.phi_nonneg x)]
      have hbnd : |(m + σ * x) * q ((m + σ * x) / L)| ≤ L := by
        have h1 := Lemma25Aux.abs_mul_q_le_one ((m + σ * x) / L)
        have h2 : (m + σ * x) * q ((m + σ * x) / L) =
            L * (((m + σ * x) / L) * q ((m + σ * x) / L)) := by field_simp [ne_of_gt hL_pos]
        rw [h2, abs_mul, abs_of_pos hL_pos]
        calc
          L * |((m + σ * x) / L) * q ((m + σ * x) / L)| ≤ L * 1 :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hL_pos)
          _ = L := mul_one L
      exact mul_le_mul_of_nonneg_right hbnd (Lemma25Aux.phi_nonneg x)
    have hint_qd : Integrable (fun x =>
        Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x) := by
      refine Lemma25Aux.integrable_phi.mono'
        ((Lemma25Aux.qDeriv_measurable.comp hlin_meas).mul hphi_meas).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (Lemma25Aux.phi_nonneg x)]
      calc
        |Lemma25Aux.qDeriv ((m + σ * x) / L)| * Lemma25Aux.phi x ≤ 1 * Lemma25Aux.phi x :=
          mul_le_mul_of_nonneg_right (Lemma25Aux.abs_qDeriv_le_one _) (Lemma25Aux.phi_nonneg x)
        _ = Lemma25Aux.phi x := one_mul _
    have hint_xq : Integrable (fun x => x * q ((m + σ * x) / L) * Lemma25Aux.phi x) := by
      refine Lemma25Aux.integrable_abs_x_phi.mono'
        (((measurable_id.mul (Lemma25Aux.q_continuous.measurable.comp hlin_meas)).mul
          hphi_meas).aestronglyMeasurable)
        (ae_of_all _ fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg (Lemma25Aux.q_nonneg _),
        abs_of_nonneg (Lemma25Aux.phi_nonneg x)]
      apply mul_le_mul_of_nonneg_right _ (Lemma25Aux.phi_nonneg x)
      calc
        |x| * q ((m + σ * x) / L) ≤ |x| * 1 :=
          mul_le_mul_of_nonneg_left (Lemma25Aux.q_le_one _) (abs_nonneg x)
        _ = |x| := mul_one _
    have hEq : (∫ x : ℝ, q ((m + σ * x) / L) ∂gaussianReal 0 1) =
        ∫ x : ℝ, q ((m + σ * x) / L) * Lemma25Aux.phi x := by
      rw [Lemma25Aux.integral_gaussian_eq_phi]
      exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have hEYq : (∫ x : ℝ, (m + σ * x) * q ((m + σ * x) / L) ∂gaussianReal 0 1) =
        ∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x := by
      rw [Lemma25Aux.integral_gaussian_eq_phi]
      exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have hEYq_nn : 0 ≤ ∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x := by
      refine Lemma25Aux.gaussian_odd_shift_nonneg hm hσ_pos (H := fun y => y * q (y / L))
        ?_ ?_ hint_Yq
      · intro y; rw [neg_div, Lemma25Aux.q_even]; ring
      · intro y hy; exact mul_nonneg (le_of_lt hy) (Lemma25Aux.q_nonneg _)
    have hqd_bound : - (∫ x : ℝ, Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x) ≤
        (1 / L) * ∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x := by
      let H₂ : ℝ → ℝ := fun y => (1 / L) * (y * q (y / L)) + Lemma25Aux.qDeriv (y / L)
      have hint_H₂ : Integrable (fun x => H₂ (m + σ * x) * Lemma25Aux.phi x) := by
        have hrew : (fun x => H₂ (m + σ * x) * Lemma25Aux.phi x) =
            fun x => (1 / L) * (((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) +
              Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x := by
          ext x; dsimp [H₂]; ring
        rw [hrew]
        exact (hint_Yq.const_mul (1 / L)).add hint_qd
      have hnn := Lemma25Aux.gaussian_odd_shift_nonneg hm hσ_pos (H := H₂) ?_ ?_ hint_H₂
      · have hrew : (∫ x : ℝ, H₂ (m + σ * x) * Lemma25Aux.phi x) =
            (1 / L) * (∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) +
              ∫ x : ℝ, Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x := by
          have hf : (fun x => H₂ (m + σ * x) * Lemma25Aux.phi x) =
              fun x => (1 / L) * (((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) +
                Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x := by
            ext x; dsimp [H₂]; ring
          rw [hf, integral_add (hint_Yq.const_mul (1 / L)) hint_qd, integral_const_mul]
        linarith
      · intro y
        dsimp [H₂]
        rw [neg_div, Lemma25Aux.q_even, Lemma25Aux.qDeriv_odd]
        ring
      · intro y hy
        dsimp [H₂]
        set t := y / L
        have ht_pos : 0 < t := div_pos hy hL_pos
        have hyt : (1 / L) * (y * q (y / L)) = t * q t := by dsimp [t]; ring
        rw [hyt]
        unfold Lemma25Aux.qDeriv q
        rw [abs_of_pos ht_pos]
        by_cases ht1 : t ≤ 1
        · simp [ht1, le_of_lt ht_pos]
        · have ht_gt1 : 1 < t := not_le.mp ht1
          rw [if_neg ht1, if_pos (le_of_lt ht_pos), max_eq_right (le_of_lt ht_gt1)]
          have ht_ne : t ≠ 0 := ne_of_gt ht_pos
          have h1 : t * (1 / t) + -(1 / t ^ 2) = 1 - 1 / t ^ 2 := by
            field_simp [ht_ne]; ring
          rw [h1]
          have hsq : 1 ≤ t ^ 2 := by nlinarith
          have : 1 / t ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
          linarith
    refine ⟨?_, ?_⟩
    · rw [hEq, hEYq]
      have decomp : (∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) =
          m * (∫ x : ℝ, q ((m + σ * x) / L) * Lemma25Aux.phi x) +
          σ * (∫ x : ℝ, x * q ((m + σ * x) / L) * Lemma25Aux.phi x) := by
        have hf : (fun x => ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x) =
            fun x => m * (q ((m + σ * x) / L) * Lemma25Aux.phi x) +
              σ * (x * q ((m + σ * x) / L) * Lemma25Aux.phi x) := by
          ext x; ring
        rw [hf, integral_add (hint_q.const_mul m) (hint_xq.const_mul σ),
          integral_const_mul, integral_const_mul]
      rw [Lemma25Aux.gaussian_ibp_q hσ_pos hL] at decomp
      set EY := ∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x
      set EQD := ∫ x : ℝ, Lemma25Aux.qDeriv ((m + σ * x) / L) * Lemma25Aux.phi x
      have h1 : m * (∫ x : ℝ, q ((m + σ * x) / L) * Lemma25Aux.phi x) =
          EY + (σ ^ 2 / L) * (- EQD) := by
        linarith [show σ * ((σ / L) * EQD) = (σ ^ 2 / L) * EQD by ring]
      have h2 : (σ ^ 2 / L) * (- EQD) ≤ (σ ^ 2 / L) * ((1 / L) * EY) :=
        mul_le_mul_of_nonneg_left hqd_bound (by positivity)
      have h3 : (σ ^ 2 / L) * ((1 / L) * EY) = (σ ^ 2 / L ^ 2) * EY := by ring
      have h4 : σ ^ 2 / L ^ 2 ≤ 1 := by
        have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
        have hL2 : 1 ≤ L ^ 2 := by nlinarith
        exact (div_le_one (by positivity)).mpr (le_trans hσ2 hL2)
      have h5 : (σ ^ 2 / L ^ 2) * EY ≤ 1 * EY := mul_le_mul_of_nonneg_right h4 hEYq_nn
      linarith
    · rw [Lemma25Aux.integral_gaussian_eq_phi, hEYq, le_div_iff₀ hL_pos]
      have hpwise : ∀ x : ℝ,
          Lemma25Aux.phi x * (1 - q ((m + σ * x) / L)) * L ≤
          ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x +
            2 * σ * (max (-x) 0 * Lemma25Aux.phi x) := by
        intro x
        set y := m + σ * x
        have h1 := Lemma25Aux.one_sub_q_le_abs_mul_q (y / L)
        have h1L : (1 - q (y / L)) * L ≤ |y| * q (y / L) := by
          have := mul_le_mul_of_nonneg_right h1 (le_of_lt hL_pos)
          calc
            (1 - q (y / L)) * L ≤ (|y / L| * q (y / L)) * L := this
            _ = |y| * q (y / L) := by
                rw [abs_div, abs_of_pos hL_pos]
                field_simp [ne_of_gt hL_pos]
        have habs_y : |y| = y + 2 * max (-y) 0 := by
          by_cases hy : 0 ≤ y
          · have : max (-y) 0 = 0 := max_eq_right (by linarith)
            rw [abs_of_nonneg hy, this]; ring
          · have : max (-y) 0 = -y := max_eq_left (by linarith)
            rw [abs_of_neg (not_le.mp hy), this]; ring
        have hmax_le : max (-y) 0 * q (y / L) ≤ σ * max (-x) 0 := by
          have hmy : max (-y) 0 ≤ σ * max (-x) 0 := by
            dsimp [y]
            by_cases hx0 : 0 ≤ -x
            · rw [max_eq_left hx0]
              exact max_le (by linarith) (mul_nonneg (le_of_lt hσ_pos) hx0)
            · have hx_pos : 0 < x := by linarith
              have hneg_y : -(m + σ * x) ≤ 0 := by nlinarith
              rw [max_eq_right hneg_y]
              exact mul_nonneg (le_of_lt hσ_pos) (le_max_right _ _)
          calc
            max (-y) 0 * q (y / L) ≤ max (-y) 0 * 1 :=
              mul_le_mul_of_nonneg_left (Lemma25Aux.q_le_one _) (le_max_right _ _)
            _ = max (-y) 0 := mul_one _
            _ ≤ σ * max (-x) 0 := hmy
        have hcomb : (1 - q (y / L)) * L ≤ y * q (y / L) + 2 * σ * max (-x) 0 := by
          rw [habs_y, add_mul] at h1L
          linarith
        have hmul := mul_le_mul_of_nonneg_right hcomb (Lemma25Aux.phi_nonneg x)
        linarith
      have hint_lhs : Integrable (fun x => Lemma25Aux.phi x * (1 - q ((m + σ * x) / L))) := by
        have hf : (fun x => Lemma25Aux.phi x * (1 - q ((m + σ * x) / L))) =
            fun x => Lemma25Aux.phi x - q ((m + σ * x) / L) * Lemma25Aux.phi x := by
          ext x; ring
        rw [hf]
        exact Lemma25Aux.integrable_phi.sub hint_q
      have hint_max : Integrable (fun x => max (-x) 0 * Lemma25Aux.phi x) := by
        refine Lemma25Aux.integrable_abs_x_phi.mono'
          (((measurable_id.neg.max measurable_const).mul hphi_meas).aestronglyMeasurable)
          (ae_of_all _ fun x => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_mul, abs_of_nonneg (le_max_right _ _),
          abs_of_nonneg (Lemma25Aux.phi_nonneg x)]
        apply mul_le_mul_of_nonneg_right _ (Lemma25Aux.phi_nonneg x)
        exact max_le (neg_le_abs x) (abs_nonneg x)
      have hint_rhs := hint_Yq.add (hint_max.const_mul (2 * σ))
      have hint_int : (∫ x : ℝ, Lemma25Aux.phi x * (1 - q ((m + σ * x) / L)) * L) ≤
          ∫ x : ℝ, ((m + σ * x) * q ((m + σ * x) / L)) * Lemma25Aux.phi x +
            2 * σ * (max (-x) 0 * Lemma25Aux.phi x) :=
        integral_mono (hint_lhs.mul_const L) hint_rhs hpwise
      rw [integral_mul_const, integral_add hint_Yq (hint_max.const_mul (2 * σ)),
        integral_const_mul] at hint_int
      have hmax_val : (∫ x : ℝ, max (-x) 0 * Lemma25Aux.phi x) = Lemma25Aux.phi 0 := by
        rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
          setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint_max.integrableOn
            hint_max.integrableOn]
        have hleft : (∫ x in Iic (0 : ℝ), max (-x) 0 * Lemma25Aux.phi x) = Lemma25Aux.phi 0 := by
          rw [← Lemma25Aux.integral_Iic_neg_x_phi.2]
          refine setIntegral_congr_fun measurableSet_Iic (fun x hx => ?_)
          have hx0 : x ≤ 0 := hx
          rw [max_eq_left (by linarith)]
        have hright : (∫ x in Ioi (0 : ℝ), max (-x) 0 * Lemma25Aux.phi x) = 0 := by
          have : (∫ x in Ioi (0 : ℝ), max (-x) 0 * Lemma25Aux.phi x) =
              ∫ _x in Ioi (0 : ℝ), (0 : ℝ) := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
            have hx0 : 0 < x := hx
            rw [max_eq_right (by linarith), zero_mul]
          rw [this, integral_zero]
        rw [hleft, hright, add_zero]
      have hphi0_le : Lemma25Aux.phi 0 ≤ 1 / 2 := by
        unfold Lemma25Aux.phi
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
          Real.exp_zero, mul_one]
        have hpi : 4 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        have hsqrt : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
          calc
            (2 : ℝ) = Real.sqrt 4 := by norm_num
            _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt hpi
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hsqrt
      have h2σ_le : 2 * σ * (∫ x : ℝ, max (-x) 0 * Lemma25Aux.phi x) ≤ 1 := by
        rw [hmax_val]
        calc
          2 * σ * Lemma25Aux.phi 0 ≤ 2 * 1 * (1 / 2) := by
            nlinarith [Lemma25Aux.phi_nonneg 0]
          _ = 1 := by ring
      linarith
