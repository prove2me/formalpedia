-- Prove2me | solution 1 for RybinAI2026.P01.h_sq_strict_concave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:55:11.868364+00:00
-- url     : https://prove2.me/submissions/1f9d6481-8a55-44d5-8490-9eeabdee6ba7

import Mathlib

set_option autoImplicit false

open MeasureTheory intervalIntegral

namespace HSq3567

noncomputable def Jf (a b : ℝ) : ℝ := ∫ t in (0:ℝ)..1, (a + (b - a) * t ^ 2)⁻¹
noncomputable def Mf (a b : ℝ) : ℝ := ∫ t in (0:ℝ)..1, t ^ 2 * ((a + (b - a) * t ^ 2) ^ 2)⁻¹
noncomputable def Kf (a b : ℝ) : ℝ := ∫ t in (0:ℝ)..1, t ^ 4 * ((a + (b - a) * t ^ 2) ^ 3)⁻¹

lemma D_lb {a b δ t : ℝ} (ha : δ ≤ a) (hb : δ ≤ b) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    δ ≤ a + (b - a) * t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 ht2), mul_nonneg (sub_nonneg.2 hb) ht0]

lemma D_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < a + (b - a) * t ^ 2 :=
  lt_of_lt_of_le (lt_min ha hb) (D_lb (min_le_left _ _) (min_le_right _ _) h0 h1)

lemma icont {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (m k : ℕ) :
    ContinuousOn (fun t : ℝ => t ^ m * ((a + (b - a) * t ^ 2) ^ k)⁻¹) (Set.uIcc 0 1) := by
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact pow_ne_zero _ (D_pos ha hb ht.1 ht.2).ne'

lemma icont0 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) (Set.uIcc 0 1) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact (D_pos ha hb ht.1 ht.2).ne'

lemma param_deriv {a : ℝ} (ha : 0 < a) (m j : ℕ) {b₀ : ℝ} (hb₀ : 0 < b₀) :
    HasDerivAt (fun b => ∫ t in (0:ℝ)..1, t ^ m * ((a + (b - a) * t ^ 2) ^ (j + 1))⁻¹)
      (-((j + 1 : ℝ) * ∫ t in (0:ℝ)..1, t ^ (m + 2) * ((a + (b₀ - a) * t ^ 2) ^ (j + 2))⁻¹))
      b₀ := by
  set δ := min a (b₀ / 2) with hδ
  have hδpos : 0 < δ := lt_min ha (by linarith)
  have hδa : δ ≤ a := min_le_left _ _
  have hδb : δ ≤ b₀ / 2 := min_le_right _ _
  have hball : ∀ x ∈ Metric.ball b₀ (b₀ / 2), δ ≤ x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    linarith [hx.1]
  have hmeas : ∀ x : ℝ, Measurable (fun t : ℝ => t ^ m * ((a + (x - a) * t ^ 2) ^ (j + 1))⁻¹) := by
    intro x; fun_prop
  have hmeas' : Measurable
      (fun t : ℝ => -((j + 1 : ℝ) * (t ^ (m + 2) * ((a + (b₀ - a) * t ^ 2) ^ (j + 2))⁻¹))) := by
    fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (x₀ := b₀)
    (F := fun b t => t ^ m * ((a + (b - a) * t ^ 2) ^ (j + 1))⁻¹)
    (F' := fun b t => -((j + 1 : ℝ) * (t ^ (m + 2) * ((a + (b - a) * t ^ 2) ^ (j + 2))⁻¹)))
    (bound := fun _ => (j + 1 : ℝ) * (δ ^ (j + 2))⁻¹)
    (Metric.ball_mem_nhds b₀ (by linarith : (0:ℝ) < b₀ / 2))
    (Filter.Eventually.of_forall fun x => (hmeas x).aestronglyMeasurable)
    ((icont ha hb₀ m (j + 1)).intervalIntegrable)
    hmeas'.aestronglyMeasurable
    (ae_of_all _ fun t ht x hx => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hD : δ ≤ a + (x - a) * t ^ 2 := D_lb hδa (hball x hx) ht.1.le ht.2
      have hDp : 0 < a + (x - a) * t ^ 2 := lt_of_lt_of_le hδpos hD
      have htm : t ^ (m + 2) ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have htm0 : 0 ≤ t ^ (m + 2) := pow_nonneg ht.1.le _
      have hinv : ((a + (x - a) * t ^ 2) ^ (j + 2))⁻¹ ≤ (δ ^ (j + 2))⁻¹ :=
        inv_anti₀ (pow_pos hδpos _) (pow_le_pow_left₀ hδpos.le hD _)
      have hinv0 : 0 ≤ ((a + (x - a) * t ^ 2) ^ (j + 2))⁻¹ := (inv_pos.2 (pow_pos hDp _)).le
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc t ^ (m + 2) * ((a + (x - a) * t ^ 2) ^ (j + 2))⁻¹
          ≤ 1 * ((a + (x - a) * t ^ 2) ^ (j + 2))⁻¹ := mul_le_mul_of_nonneg_right htm hinv0
        _ ≤ (δ ^ (j + 2))⁻¹ := by rw [one_mul]; exact hinv)
    intervalIntegrable_const
    (ae_of_all _ fun t ht x hx => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hD : δ ≤ a + (x - a) * t ^ 2 := D_lb hδa (hball x hx) ht.1.le ht.2
      have hDp : 0 < a + (x - a) * t ^ 2 := lt_of_lt_of_le hδpos hD
      have h1 : HasDerivAt (fun x => a + (x - a) * t ^ 2) (t ^ 2) x := by
        simpa using (((hasDerivAt_id x).sub_const a).mul_const (t ^ 2)).const_add a
      have h2 : HasDerivAt (fun x => (a + (x - a) * t ^ 2) ^ (j + 1)) _ x := h1.pow (j + 1)
      have h3 : HasDerivAt (fun x => ((a + (x - a) * t ^ 2) ^ (j + 1))⁻¹) _ x :=
        h2.inv (pow_ne_zero _ hDp.ne')
      have h4 : HasDerivAt (fun x => t ^ m * ((a + (x - a) * t ^ 2) ^ (j + 1))⁻¹) _ x :=
        h3.const_mul (t ^ m)
      refine h4.congr_deriv ?_
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring)
  have h := key.2
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
  exact h

lemma hasDerivJ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : HasDerivAt (Jf a) (-Mf a b) b := by
  have h := param_deriv ha 0 0 hb
  simp only [pow_zero, one_mul, zero_add, pow_one, Nat.cast_zero] at h
  exact h

lemma hasDerivM {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : HasDerivAt (Mf a) (-(2 * Kf a b)) b := by
  have h := param_deriv ha 2 1 hb
  norm_num at h
  exact h

lemma J_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < Jf a b := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (icont0 ha hb).intervalIntegrable _
    zero_lt_one
  intro t ht
  exact inv_pos.2 (D_pos ha hb ht.1.le ht.2.le)

lemma ibp1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Jf a b - 2 * (b - a) * Mf a b = b⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t * (a + (b - a) * t ^ 2)⁻¹)
        ((a + (b - a) * x ^ 2)⁻¹ - 2 * (b - a) * (x ^ 2 * ((a + (b - a) * x ^ 2) ^ 2)⁻¹)) x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hDp := D_pos ha hb hx.1 hx.2
    have hD : HasDerivAt (fun t : ℝ => a + (b - a) * t ^ 2) ((b - a) * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (b - a)).const_add a
    have hinv : HasDerivAt (fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) _ x := hD.inv hDp.ne'
    have hG : HasDerivAt (fun t : ℝ => t * (a + (b - a) * t ^ 2)⁻¹) _ x := (hasDerivAt_id' x).mul hinv
    refine hG.congr_deriv ?_
    have hD0 := hDp.ne'
    field_simp
    ring
  have hint1 := (icont0 ha hb).intervalIntegrable (μ := volume)
  have hint2 := ((icont ha hb 2 2).intervalIntegrable (μ := volume)).const_mul (2 * (b - a))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul] at this
  rw [Jf, Mf, this]
  simp

lemma ibp2 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    3 * Mf a b - 4 * (b - a) * Kf a b = (b ^ 2)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ 3 * ((a + (b - a) * t ^ 2) ^ 2)⁻¹)
        (3 * (x ^ 2 * ((a + (b - a) * x ^ 2) ^ 2)⁻¹)
          - 4 * (b - a) * (x ^ 4 * ((a + (b - a) * x ^ 2) ^ 3)⁻¹)) x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have hDp := D_pos ha hb hx.1 hx.2
    have hD : HasDerivAt (fun t : ℝ => a + (b - a) * t ^ 2) ((b - a) * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (b - a)).const_add a
    have hD2 : HasDerivAt (fun t : ℝ => (a + (b - a) * t ^ 2) ^ 2) _ x := hD.pow 2
    have hinv : HasDerivAt (fun t : ℝ => ((a + (b - a) * t ^ 2) ^ 2)⁻¹) _ x :=
      hD2.inv (pow_ne_zero _ hDp.ne')
    have hG : HasDerivAt (fun t : ℝ => t ^ 3 * ((a + (b - a) * t ^ 2) ^ 2)⁻¹) _ x :=
      (hasDerivAt_pow 3 x).mul hinv
    refine hG.congr_deriv ?_
    have hD0 := hDp.ne'
    field_simp
    ring
  have hint1 := ((icont ha hb 2 2).intervalIntegrable (μ := volume)).const_mul 3
  have hint2 := ((icont ha hb 4 3).intervalIntegrable (μ := volume)).const_mul (4 * (b - a))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at this
  rw [Mf, Kf, this]
  simp

lemma jensen_strict {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≠ a) :
    3 < (b + 2 * a) * Jf a b := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (b + 2 * a) / 3 := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; positivity
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun t : ℝ => (2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * t ^ 2)
    (g := fun t : ℝ => (a + (b - a) * t ^ 2)⁻¹) (a := 0) (b := 1) zero_lt_one
    (by fun_prop)
    (by rw [← Set.uIcc_of_le zero_le_one]; exact icont0 ha hb)
    (by
      intro t ht
      have hDp := D_pos ha hb ht.1.le ht.2
      show (2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * t ^ 2 ≤ (a + (b - a) * t ^ 2)⁻¹
      have e : (2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * t ^ 2
          = 2 / m - (a + (b - a) * t ^ 2) / m ^ 2 := by ring
      rw [e]
      generalize a + (b - a) * t ^ 2 = D at hDp ⊢
      rw [← sub_nonneg]
      have : D⁻¹ - (2 / m - D / m ^ 2) = (D - m) ^ 2 / (D * m ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity)
    ⟨0, by simp, by
      show (2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * 0 ^ 2 < (a + (b - a) * 0 ^ 2)⁻¹
      have hne : a - m ≠ 0 := by
        rw [hm]; intro h; apply hab; linarith
      rw [← sub_pos]
      have ha0 := ha.ne'
      have hm0 := hmpos.ne'
      have : (a + (b - a) * 0 ^ 2)⁻¹ - ((2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * 0 ^ 2)
          = (a - m) ^ 2 / (a * m ^ 2) := by
        norm_num
        field_simp
        ring
      rw [this]
      have h1 : 0 < (a - m) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      exact div_pos h1 (by positivity)⟩
  have hf : ∫ t in (0:ℝ)..1, ((2 / m - a / m ^ 2) + (-(b - a) / m ^ 2) * t ^ 2) = 3 / (b + 2 * a) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_pow 2).intervalIntegrable 0 1 |>.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
    have hb' : b = 3 * m - 2 * a := by rw [hm]; ring
    have hm0 := hmpos.ne'
    rw [hb']
    norm_num
    field_simp
    ring
  rw [hf] at hlt
  have h2 : 0 < b + 2 * a := by positivity
  rw [div_lt_iff₀ h2] at hlt
  unfold Jf
  linarith

lemma E_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    3 * Mf a b ^ 2 - 2 * Jf a b * Kf a b < 0 := by
  by_cases hab : b = a
  · subst hab
    have hJ : Jf b b = b⁻¹ := by simp [Jf]
    have hM : Mf b b = (b ^ 2)⁻¹ / 3 := by
      simp [Mf, intervalIntegral.integral_mul_const, integral_pow]
      ring
    have hK : Kf b b = (b ^ 3)⁻¹ / 5 := by
      simp [Kf, intervalIntegral.integral_mul_const, integral_pow]
      ring
    rw [hJ, hM, hK]
    have hb0 : b ≠ 0 := hb.ne'
    have : 3 * ((b ^ 2)⁻¹ / 3) ^ 2 - 2 * b⁻¹ * ((b ^ 3)⁻¹ / 5) = -(1 / 15) * (b ^ 4)⁻¹ := by
      field_simp
      ring
    rw [this]
    have : 0 < (b ^ 4)⁻¹ := by positivity
    linarith
  · have h1 := ibp1 ha hb
    have h2 := ibp2 ha hb
    have hj := jensen_strict ha hb hab
    have hb0 : b ≠ 0 := hb.ne'
    have P1 : b * Jf a b - 2 * (b - a) * b * Mf a b = 1 := by
      have : b * Jf a b - 2 * (b - a) * b * Mf a b = b * (Jf a b - 2 * (b - a) * Mf a b) := by
        ring
      rw [this, h1, mul_inv_cancel₀ hb0]
    have P2 : 3 * b ^ 2 * Mf a b - 4 * (b - a) * b ^ 2 * Kf a b = 1 := by
      have : 3 * b ^ 2 * Mf a b - 4 * (b - a) * b ^ 2 * Kf a b
          = b ^ 2 * (3 * Mf a b - 4 * (b - a) * Kf a b) := by ring
      rw [this, h2, mul_inv_cancel₀ (pow_ne_zero 2 hb0)]
    have hid : 4 * (b - a) ^ 2 * b ^ 2 * (3 * Mf a b ^ 2 - 2 * Jf a b * Kf a b)
        = 3 - (b + 2 * a) * Jf a b := by
      linear_combination (3 - 6 * (b - a) * b * Mf a b) * P1 + 2 * (b - a) * Jf a b * P2
    have hc : 0 < (b - a) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hab)))
    have hpos : 0 < 4 * (b - a) ^ 2 * b ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    have := mul_nonneg hpos.le hcon
    linarith

lemma hasDerivPhi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x => 2 * Mf a x / Jf a x ^ 3)
      (2 * (3 * Mf a b ^ 2 - 2 * Jf a b * Kf a b) / Jf a b ^ 4) b := by
  have hJp := J_pos ha hb
  have hJ3 : HasDerivAt (fun x => Jf a x ^ 3) _ b := (hasDerivJ ha hb).pow 3
  have hM2 : HasDerivAt (fun x => 2 * Mf a x) _ b := (hasDerivM ha hb).const_mul 2
  have hq : HasDerivAt (fun x => 2 * Mf a x / Jf a x ^ 3) _ b := hM2.div hJ3 (pow_ne_zero _ hJp.ne')
  refine hq.congr_deriv ?_
  have hJ0 := hJp.ne'
  field_simp
  ring

lemma hasDerivF {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x => (Jf a x)⁻¹ ^ 2) (2 * Mf a b / Jf a b ^ 3) b := by
  have hJp := J_pos ha hb
  have hinv : HasDerivAt (fun x => (Jf a x)⁻¹) _ b := (hasDerivJ ha hb).inv hJp.ne'
  have hp : HasDerivAt (fun x => (Jf a x)⁻¹ ^ 2) _ b := hinv.pow 2
  refine hp.congr_deriv ?_
  have hJ0 := hJp.ne'
  norm_num
  field_simp

end HSq3567

theorem solution (a : ℝ) (ha : 0 < a) :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun b => ((∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2)⁻¹)⁻¹) ^ 2) := by
  show StrictConcaveOn ℝ (Set.Ioi (0:ℝ)) (fun b => (HSq3567.Jf a b)⁻¹ ^ 2)
  have hcont : ContinuousOn (fun b => (HSq3567.Jf a b)⁻¹ ^ 2) (Set.Ioi 0) :=
    fun b hb => (HSq3567.hasDerivF ha hb).continuousAt.continuousWithinAt
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) hcont
  rw [interior_Ioi]
  have hphi : StrictAntiOn (fun x => 2 * HSq3567.Mf a x / HSq3567.Jf a x ^ 3) (Set.Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · exact fun b hb => (HSq3567.hasDerivPhi ha hb).continuousAt.continuousWithinAt
    · intro b hb
      rw [interior_Ioi] at hb
      rw [(HSq3567.hasDerivPhi ha hb).deriv]
      have hJp := HSq3567.J_pos ha hb
      exact div_neg_of_neg_of_pos (by linarith [HSq3567.E_neg ha hb]) (by positivity)
  exact hphi.congr (fun b hb => ((HSq3567.hasDerivF ha hb).deriv).symm)
