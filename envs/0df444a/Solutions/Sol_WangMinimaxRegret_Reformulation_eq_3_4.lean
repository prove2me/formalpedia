-- Prove2me | solution 1 for WangMinimaxRegret.Reformulation.eq_3_4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:08:12.883357+00:00
-- url     : https://prove2.me/submissions/b60da6d2-4e1c-43db-bc59-6145d22a02cb

import Definitions.Def_WangMinimaxRegret_Reformulation_Programs

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace WMS107eq34

open WangMinimaxRegret.Reformulation

noncomputable def d0 : Data where
  a := 1/2
  b := ((1:ℝ) : WithTop ℝ)
  nonneg_a := by norm_num
  ordered := by exact_mod_cast (by norm_num : (1/2:ℝ) ≤ 1)
  K := 1
  mu := fun _ => 1

lemma mem_int (x : ℝ) : x ∈ interval d0 ↔ 1/2 ≤ x ∧ x ≤ 1 := by
  simp only [interval, d0, mem_setOf_eq, WithTop.coe_le_coe]

noncomputable def mf : ℝ → ℝ := fun x => if 1 ≤ x then 1/4 else 0

lemma mf_mono : Monotone mf := by
  intro x y h
  unfold mf
  by_cases hx : 1 ≤ x
  · have hy : 1 ≤ y := le_trans hx h
    simp [hx, hy]
  · by_cases hy : 1 ≤ y <;> simp [hx, hy]

noncomputable def m0 : StieltjesFunction ℝ where
  toFun := mf
  mono' := mf_mono
  right_continuous' := by
    intro x
    by_cases hx : 1 ≤ x
    · apply (continuousWithinAt_const (b := (1/4 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simp [mf, le_trans hx (show x ≤ y from hy)]
      · simp [mf, hx]
    · push Not at hx
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [Ico_mem_nhdsGE hx] with y hy
        simp [mf, not_le.2 hy.2]
      · simp [mf, not_le.2 hx]

lemma m0_apply (x : ℝ) : m0 x = if 1 ≤ x then 1/4 else 0 := rfl

lemma mp_eq (lam : Fin d0.K → ℝ) (x : ℝ) :
    momentPolynomial d0 lam x = (x - 1) * lam ⟨0, Nat.one_pos⟩ := by
  change ∑ i : Fin 1, (x ^ (i.val + 1) - 1) * lam i = _
  simp
  left; rfl

lemma dual_le {θ : ℝ} {lam : Fin d0.K → ℝ} (h : DualFeasible d0 m0 (3/4) θ lam) :
    θ ≤ 0 := by
  obtain ⟨h1, h2⟩ := h
  set l := lam ⟨0, Nat.one_pos⟩ with hl
  have hl0 : 0 ≤ l := by
    have := h1 (1/2) ((mem_int _).2 (by norm_num)) (by norm_num)
    rw [mp_eq, m0_apply] at this
    norm_num at this
    linarith
  by_contra hθ
  push Not at hθ
  set δ := min (1/4 : ℝ) (θ / (2 * (l + 1))) with hδ
  have hpos : 0 < θ / (2 * (l + 1)) := by positivity
  have hδpos : 0 < δ := lt_min (by norm_num) hpos
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδ2 : δ ≤ θ / (2 * (l + 1)) := min_le_right _ _
  have := h2 (1 - δ) ((mem_int _).2 ⟨by linarith, by linarith⟩) (by linarith)
  rw [mp_eq, m0_apply, if_neg (by linarith)] at this
  have hk : δ * l ≤ θ / (2 * (l + 1)) * l := mul_le_mul_of_nonneg_right hδ2 hl0
  have hk2 : θ / (2 * (l + 1)) * l < θ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

lemma ae_eq_one (H : Measure ℝ) (hsupp : H (interval d0)ᶜ = 0)
    (hi : Integrable (fun x : ℝ => x ^ 1 - 1) H) (h0 : ∫ x, (x ^ 1 - 1) ∂H = 0) :
    ∀ᵐ x ∂H, x = 1 := by
  have hint : ∀ᵐ x ∂H, x ∈ interval d0 := by
    rw [ae_iff]; exact hsupp
  have hnn : 0 ≤ᵐ[H] (fun x : ℝ => -(x ^ 1 - 1)) := by
    filter_upwards [hint] with x hx
    rw [mem_int] at hx
    simp only [Pi.zero_apply, pow_one]
    linarith [hx.2]
  have hz : ∫ x, -(x ^ 1 - 1) ∂H = 0 := by rw [integral_neg, h0, neg_zero]
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hi.neg).1 hz
  filter_upwards [this] with x hx
  simp only [Pi.zero_apply, pow_one] at hx
  linarith

lemma rev_eq (H : Measure ℝ) (hae : ∀ᵐ x ∂H, x = 1) :
    ∫⁻ x, ENNReal.ofReal (m0 x) ∂H = ENNReal.ofReal (1/4) * H univ := by
  rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal (1/4))]
  · rw [lintegral_const]
  · filter_upwards [hae] with x hx
    rw [hx, m0_apply]
    simp

lemma value_ge : ENNReal.ofReal (1/4) ≤ (homogenizedLP d0 m0 (3/4)).value := by
  refine le_iInf₂ (fun H hH => ?_)
  obtain ⟨hfin, hsupp, htest⟩ := hH
  have hj := htest (some ⟨0, Nat.one_pos⟩)
  have hn := htest none
  have hae : ∀ᵐ x ∂H, x = 1 := ae_eq_one H hsupp hj.1 hj.2
  have hIci : H (Ici (3/4)) = 1 := by
    have h2 := hn.2
    change ∫ x, (Ici (3/4 : ℝ)).indicator (fun _ => (1 : ℝ)) x ∂H = 1 at h2
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_one,
      measureReal_def] at h2
    exact (ENNReal.toReal_eq_one_iff _).1 h2
  change ENNReal.ofReal (1/4) ≤ ∫⁻ x, ENNReal.ofReal (m0 x) ∂H
  rw [rev_eq H hae]
  calc ENNReal.ofReal (1/4) = ENNReal.ofReal (1/4) * H (Ici (3/4)) := by rw [hIci, mul_one]
    _ ≤ ENNReal.ofReal (1/4) * H univ := by gcongr; exact subset_univ _

lemma dual_nonpos : dualValue d0 m0 (3/4) ≤ 0 := by
  refine iSup_le fun θ => iSup_le fun lam => iSup_le fun h => ?_
  exact_mod_cast dual_le h

lemma hpay : IsPayment d0 m0 := by
  refine ⟨by simp [m0_apply], ?_, ?_, ?_, ?_⟩
  · intro x hx
    have : ¬ 1 ≤ x := by change x < 1/2 at hx; linarith
    simp [m0_apply, this]
  · intro x y hx hy
    have hx' : 1 ≤ x := by simpa [d0] using hx
    have hy' : 1 ≤ y := by simpa [d0] using hy
    simp [m0_apply, hx', hy']
  · intro x _
    rw [m0_apply]; split_ifs <;> norm_num
  · intro x hx
    rw [mem_int] at hx
    unfold allocation
    have hsub : interval d0 ∩ Ioc 0 x ⊆ Ioc 0 1 := by
      intro t ht
      rw [mem_inter_iff, mem_int] at ht
      exact ⟨by linarith [ht.1.1], ht.1.2⟩
    have hbd : ∀ t ∈ interval d0 ∩ Ioc 0 x, ENNReal.ofReal (1 / t) ≤ 2 := by
      intro t ht
      rw [mem_inter_iff, mem_int] at ht
      have : 1 / t ≤ 2 := by
        rw [div_le_iff₀ (by linarith [ht.1.1])]; linarith [ht.1.1]
      calc ENNReal.ofReal (1 / t) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
        _ = 2 := by simp
    have hmeas : MeasurableSet (interval d0 ∩ Ioc 0 x) := by
      have : interval d0 = Icc (1/2) 1 := by ext t; rw [mem_int]; rfl
      rw [this]; exact measurableSet_Icc.inter measurableSet_Ioc
    calc ∫⁻ t in interval d0 ∩ Ioc 0 x, ENNReal.ofReal (1 / t) ∂m0.measure
        ≤ ∫⁻ t in interval d0 ∩ Ioc 0 x, 2 ∂m0.measure :=
          setLIntegral_mono measurable_const hbd
      _ = 2 * m0.measure (interval d0 ∩ Ioc 0 x) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      _ ≤ 2 * m0.measure (Ioc 0 1) := by gcongr
      _ ≤ 1 := by
          rw [StieltjesFunction.measure_Ioc, m0_apply, m0_apply]
          norm_num
          rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          rw [ENNReal.ofReal_le_one]; norm_num

lemma hcons : Consistent d0 := by
  refine ⟨Measure.dirac 1, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [Measure.dirac_apply]
    norm_num [mem_int]
  · intro i
    refine ⟨integrable_dirac (by simp), ?_⟩
    rw [integral_dirac]
    simp [d0]
  · simp [cdf, Measure.dirac_apply, d0]
    norm_num

end WMS107eq34

open WangMinimaxRegret.Reformulation in
theorem solution : ¬ (∀ (d : Data) (hc : Consistent d) (m : StieltjesFunction ℝ)
    (hm : IsPayment d m) (p : ℝ) (hp : p ∈ interval d),
    ((homogenizedLP d m p).value : EReal) = dualValue d m p ∧
    (∀ v : ℝ, ((homogenizedLP d m p).value : EReal) = (v : EReal) →
      ∃ lam : Fin d.K → ℝ, DualFeasible d m p v lam)) := by
  intro h
  have h1 := (h WMS107eq34.d0 WMS107eq34.hcons WMS107eq34.m0 WMS107eq34.hpay (3/4)
    ((WMS107eq34.mem_int _).2 (by norm_num))).1
  have h2 := h1 ▸ WMS107eq34.dual_nonpos
  have h3 := WMS107eq34.value_ge
  have h4 : (homogenizedLP WMS107eq34.d0 WMS107eq34.m0 (3/4)).value = 0 :=
    nonpos_iff_eq_zero.1 (by exact_mod_cast h2)
  rw [h4] at h3
  simp at h3
