-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_5_31_instance_restricted_bayes_risk
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:47:51.943574+00:00
-- url     : https://prove2.me/submissions/5648a3e8-6ab1-4e12-85f7-bfa946cfb1d4

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace SVMCex35ae

open SupportVectorMachines.Classification

/-- ℓ²(ℕ). -/
abbrev HH : Type := lp (fun _ : ℕ => ℝ) 2

noncomputable def toFunL : HH →ₗ[ℝ] (ℕ → ℝ) where
  toFun f := ⇑f
  map_add' f g := lp.coeFn_add f g
  map_smul' c f := lp.coeFn_smul c f

noncomputable def kk (n m : ℕ) : ℝ := (lp.single 2 n (1:ℝ) : HH) m

theorem rkhs : IsRKHSOfKernel HH toFunL kk := by
  refine ⟨?_, ⟨fun n => lp.single 2 n (1:ℝ), fun x x' => rfl, ?_⟩, fun x => measurable_from_nat⟩
  · intro f g h
    exact lp.ext h
  · intro f x
    rw [lp.inner_single_right]
    simp [toFunL]

theorem dense (μ : Measure ℕ) : DenseInL1 HH toFunL μ := by
  intro g hg ε hε
  let t : ℕ → ℕ → ℝ := fun N n => if n < N then g n else 0
  have mem : ∀ N, Memℓp (t N) 2 := by
    intro N
    refine (memℓp_zero ?_).of_exponent_ge (by simp)
    refine (Set.finite_Iio N).subset ?_
    intro n hn
    by_contra hc
    simp only [Set.mem_Iio] at hc
    simp [t, hc] at hn
  have lim : Tendsto (fun N => ∫ x, |t N x - g x| ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => |g x|)
      (F := fun N x => |t N x - g x|) (f := fun _ => (0:ℝ))
      (fun N => measurable_from_nat.aestronglyMeasurable) hg.abs
      (fun N => ae_of_all _ (fun x => by
        by_cases hx : x < N
        · simp [t, hx]
        · simp [t, hx]))
      (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop x] with N hN
        simp [t, hN]))
    simpa using h
  obtain ⟨N, hN⟩ := (lim.eventually (gt_mem_nhds hε)).exists
  refine ⟨⟨t N, mem N⟩, ?_, hN⟩
  refine hg.abs.mono' measurable_from_nat.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  show ‖t N x‖ ≤ |g x|
  by_cases hx : x < N
  · simp [t, hx]
  · simp [t, hx]

noncomputable def PX : Measure ℕ :=
  Measure.sum (fun n => ENNReal.ofReal (1 / 2 / 2 ^ n) • Measure.dirac n)

instance : IsProbabilityMeasure PX :=
  HasSum.isProbabilityMeasure_sum_dirac (fun n => by positivity) (hasSum_geometric_two' 1)

theorem PX_singleton (n : ℕ) : PX {n} = ENNReal.ofReal (1 / 2 / 2 ^ n) := by
  rw [PX, Measure.sum_smul_dirac_singleton]

noncomputable def PP : Measure (ℕ × ℝ) :=
  (2⁻¹ : ENNReal) • (PX.map (fun n => (n, (1:ℝ))) + PX.map (fun n => (n, (-1:ℝ))))

instance : IsProbabilityMeasure PP := by
  constructor
  have h1 : PX.map (fun n => (n, (1:ℝ))) Set.univ = 1 := by
    rw [Measure.map_apply measurable_from_nat MeasurableSet.univ]; simp
  have h2 : PX.map (fun n => (n, (-1:ℝ))) Set.univ = 1 := by
    rw [Measure.map_apply measurable_from_nat MeasurableSet.univ]; simp
  simp only [PP, Measure.smul_apply, Measure.add_apply, h1, h2, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem lint_PP (G : ℕ × ℝ → ENNReal) (hG : Measurable G) :
    ∫⁻ p, G p ∂PP = 2⁻¹ * (∫⁻ n, G (n, 1) ∂PX + ∫⁻ n, G (n, -1) ∂PX) := by
  simp only [PP, lintegral_smul_measure, lintegral_add_measure, smul_eq_mul]
  rw [lintegral_map hG measurable_from_nat, lintegral_map hG measurable_from_nat]

theorem risk_eq (g : ℕ → ℝ) :
    risk hingeLoss PP g =
      (2⁻¹ * (∫⁻ n, ENNReal.ofReal (max 0 (1 - g n)) ∂PX +
        ∫⁻ n, ENNReal.ofReal (max 0 (1 + g n)) ∂PX)).toReal := by
  have hm : Measurable (fun p : ℕ × ℝ => max 0 (1 - p.2 * g p.1)) := by
    have : Measurable (fun p : ℕ × ℝ => g p.1) := measurable_from_nat.comp measurable_fst
    fun_prop
  unfold risk hingeLoss
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun p : ℕ × ℝ => max 0 (1 - p.2 * g p.1))
    (ae_of_all _ (fun p => le_max_left _ _)) hm.aestronglyMeasurable]
  rw [lint_PP (fun p => ENNReal.ofReal (max 0 (1 - p.2 * g p.1))) (ENNReal.measurable_ofReal.comp hm)]
  congr 3
  · simp
  · congr 1; funext n; congr 1; ring_nf

theorem risk_nonneg (f : ℕ → ℝ) : 0 ≤ risk hingeLoss PP f := by
  rw [risk_eq]; exact ENNReal.toReal_nonneg

theorem risk_H (h : HH) : 1 ≤ risk hingeLoss PP (toFunL h) := by
  rw [risk_eq]
  set f : ℕ → ℝ := toFunL h
  have hb : ∀ n, |f n| ≤ ‖h‖ := fun n => by
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) h n
    simpa [f, toFunL, Real.norm_eq_abs] using this
  have hsum : ∫⁻ n, ENNReal.ofReal (max 0 (1 - f n)) ∂PX +
      ∫⁻ n, ENNReal.ofReal (max 0 (1 + f n)) ∂PX =
      ∫⁻ n, (ENNReal.ofReal (max 0 (1 - f n)) + ENNReal.ofReal (max 0 (1 + f n))) ∂PX := by
    exact (lintegral_add_left measurable_from_nat _).symm
  rw [hsum]
  have hlow : (2 : ENNReal) ≤
      ∫⁻ n, (ENNReal.ofReal (max 0 (1 - f n)) + ENNReal.ofReal (max 0 (1 + f n))) ∂PX := by
    calc (2 : ENNReal) = ∫⁻ _n, (2 : ENNReal) ∂PX := by simp
      _ ≤ _ := by
        apply lintegral_mono
        intro n
        dsimp only
        rw [← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
        apply ENNReal.ofReal_le_ofReal
        have := le_max_right 0 (1 - f n)
        have := le_max_right 0 (1 + f n)
        linarith
  have hup : ∫⁻ n, (ENNReal.ofReal (max 0 (1 - f n)) + ENNReal.ofReal (max 0 (1 + f n))) ∂PX
      ≤ ∫⁻ _n, ENNReal.ofReal (2 + 2 * ‖h‖) ∂PX := by
    apply lintegral_mono
    intro n
    dsimp only
    rw [← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    apply ENNReal.ofReal_le_ofReal
    have := hb n
    have h1 : max 0 (1 - f n) ≤ 1 + ‖h‖ := max_le (by positivity) (by
      have := neg_abs_le (f n); linarith)
    have h2 : max 0 (1 + f n) ≤ 1 + ‖h‖ := max_le (by positivity) (by
      have := le_abs_self (f n); linarith)
    linarith
  have hfin : 2⁻¹ * ∫⁻ n, (ENNReal.ofReal (max 0 (1 - f n)) +
      ENNReal.ofReal (max 0 (1 + f n))) ∂PX ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top ?_ hup)
    simp
  have h1 : (1 : ENNReal) ≤ 2⁻¹ * ∫⁻ n, (ENNReal.ofReal (max 0 (1 - f n)) +
      ENNReal.ofReal (max 0 (1 + f n))) ∂PX := by
    calc (1 : ENNReal) = 2⁻¹ * 2 := (ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
      _ ≤ _ := by gcongr
  have := ENNReal.toReal_mono hfin h1
  simpa using this

noncomputable def badF (n : ℕ) : ℝ := 2 * 2 ^ n

theorem risk_bad : risk hingeLoss PP badF = 0 := by
  rw [risk_eq]
  apply ENNReal.toReal_eq_zero_iff _ |>.mpr
  right
  have hinf : ∫⁻ n, ENNReal.ofReal (max 0 (1 + badF n)) ∂PX = ⊤ := by
    rw [lintegral_countable']
    apply eq_top_mono _ (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (one_ne_zero))
    apply ENNReal.tsum_le_tsum
    intro n
    rw [PX_singleton, ← ENNReal.ofReal_mul (le_max_left _ _)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hp : (0:ℝ) < 2 ^ n := by positivity
    have : max 0 (1 + badF n) ≥ 2 * 2 ^ n := le_max_of_le_right (by unfold badF; linarith)
    calc (1:ℝ) = (2 * 2 ^ n) * (1 / 2 / 2 ^ n) := by field_simp
      _ ≤ max 0 (1 + badF n) * (1 / 2 / 2 ^ n) := by
        apply mul_le_mul_of_nonneg_right this (by positivity)
  rw [hinf]
  simp

theorem bayes_le : bayesRisk hingeLoss PP ≤ 0 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨f, -, rfl⟩
    exact risk_nonneg f
  · exact ⟨badF, measurable_from_nat, risk_bad⟩

theorem restricted_ge : 1 ≤ restrictedBayesRisk HH toFunL hingeLoss PP := by
  unfold restrictedBayesRisk
  refine le_csInf ⟨risk hingeLoss PP (toFunL 0), 0, rfl⟩ ?_
  rintro r ⟨h, rfl⟩
  exact risk_H h

end SVMCex35ae

open MeasureTheory in
open SupportVectorMachines.Classification in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hDense : DenseInL1 H toFun (P.map Prod.fst)),
    restrictedBayesRisk H toFun hingeLoss P = bayesRisk hingeLoss P) := by
  intro h
  have e := h SVMCex35ae.HH SVMCex35ae.toFunL SVMCex35ae.kk SVMCex35ae.rkhs SVMCex35ae.PP
    (SVMCex35ae.dense _)
  have h1 := SVMCex35ae.restricted_ge
  have h2 := SVMCex35ae.bayes_le
  linarith
