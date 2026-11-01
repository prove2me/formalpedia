-- Prove2me | solution 1 for PartialLostSales.ACOI.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:12:22.006987+00:00
-- url     : https://prove2.me/submissions/744ddc8b-ff91-4cc5-86db-d0ce629233fd

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace PLSLemma4Aux
open PartialLostSales.ACOI

/-- The one-period cost identity for the coupled processes. -/
lemma cost_identity (P : Params) (y a dd d : ℝ) (hd : 0 ≤ d) :
    stageCost P y a dd + P.hplus * (max (y + d + a - dd) 0 - max (y + a - dd) 0) =
      stageCost P (y + d) a dd +
        P.hminus * (d - (max (y + d + a - dd) 0 - max (y + a - dd) 0)) := by
  unfold stageCost
  have e1 : max (dd - y - a) 0 = max (y + a - dd) 0 - (y + a - dd) := by
    rcases le_total (y + a - dd) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have e2 : max (dd - (y + d) - a) 0 = max (y + d + a - dd) 0 - (y + d + a - dd) := by
    rcases le_total (y + d + a - dd) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have e3 : y + d + a - dd = (y + d) + a - dd := by ring
  rw [e1, e2, ← e3]
  ring

lemma measurable_inv {Ω : Type*} [MeasurableSpace Ω] (x : ℝ) (ζ D : ℕ → Ω → ℝ)
    (hζ : ∀ t, Measurable (ζ t)) (hD : ∀ t, Measurable (D t)) :
    ∀ t, Measurable (inv x ζ D t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact ((ih.add (hζ t)).sub (hD t)).max measurable_const

lemma inv_nonneg {Ω : Type*} (x : ℝ) (hx : 0 ≤ x) (ζ D : ℕ → Ω → ℝ) :
    ∀ t ω, 0 ≤ inv x ζ D t ω := by
  intro t ω
  cases t with
  | zero => exact hx
  | succ t => exact le_max_right _ _

end PLSLemma4Aux

open PartialLostSales.ACOI PLSLemma4Aux in
theorem solution (P : Params) (hP : Standing P) :
    ∃ C : ℝ, 0 < C ∧ ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, ∃ h' : ℝ, P.hminus < h' ∧
      ∀ α ∈ Set.Ico αstar 1, ∀ x x' : ℝ, 0 ≤ x → x ≤ x' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ D ζ : ℕ → Ω → ℝ,
        (∀ t, Measurable (D t)) → iIndepFun D μ → (∀ t, μ.map (D t) = P.demand) →
        (∀ t, Measurable (ζ t)) → (∀ t ω, ζ t ω ∈ Set.Icc (0 : ℝ) P.K) →
        Vζ P μ α x' ζ D ≠ ⊤ →
        Vζ P μ α x ζ D + ENNReal.ofReal (if C ≤ x' - x then h' * (x' - x) else 0) ≤
            Vζ P μ α x' ζ D + ENNReal.ofReal (P.hminus * (x' - x)) ∧
          P.hminus * (x' - x) - (if C ≤ x' - x then h' * (x' - x) else 0) ≤
            P.hminus * C := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  set m := ∫ s, s ∂P.demand with hm
  set h' := P.hminus + 1 with hh'
  set T0 : ℕ := ⌈4 * h' / P.hplus⌉₊ + 1 with hT0def
  have hT0pos : (0:ℝ) < T0 := by positivity
  have hT0 : 4 * h' / P.hplus ≤ T0 := (Nat.le_ceil _).trans (by rw [hT0def]; push_cast; linarith)
  set αs : ℝ := (1/2 : ℝ) ^ ((T0 : ℝ)⁻¹) with hαsdef
  have hαs_pow : αs ^ T0 = 1/2 := by
    rw [hαsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      inv_mul_cancel₀ hT0pos.ne', Real.rpow_one]
  have hαs0 : 0 < αs := by positivity
  have hαs1 : αs < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine ⟨2 * T0 * m, by positivity, αs, ⟨hαs0, hαs1⟩, h', by linarith, ?_⟩
  intro α hα x x' hx hxx' Ω _ μ hμ D ζ hD _ hlaw hζ hζr _
  have hα0 : 0 ≤ α := hαs0.le.trans hα.1
  have hα1 : α ≤ 1 := hα.2.le
  set d0 := x' - x with hd0def
  have hd0 : 0 ≤ d0 := by rw [hd0def]; linarith
  set X := inv x ζ D with hXdef
  set X' := inv x' ζ D with hX'def
  set d : ℕ → Ω → ℝ := fun t ω => X' t ω - X t ω with hddef
  have hX'eq : ∀ t ω, X' t ω = X t ω + d t ω := fun t ω => by simp only [hddef]; ring
  have hdsucc : ∀ t ω, d (t + 1) ω =
      max (X t ω + d t ω + ζ t ω - D t ω) 0 - max (X t ω + ζ t ω - D t ω) 0 := by
    intro t ω
    simp only [hddef]
    rw [show X' (t + 1) ω = max (X' t ω + ζ t ω - D t ω) 0 from rfl,
      show X (t + 1) ω = max (X t ω + ζ t ω - D t ω) 0 from rfl,
      show X t ω + (X' t ω - X t ω) + ζ t ω - D t ω = X' t ω + ζ t ω - D t ω by ring]
  have hd0eq : ∀ ω, d 0 ω = d0 := fun ω => rfl
  have hdnn : ∀ t ω, 0 ≤ d t ω := by
    intro t
    induction t with
    | zero => intro ω; rw [hd0eq]; exact hd0
    | succ t ih =>
      intro ω
      rw [hdsucc]
      have := ih ω
      exact sub_nonneg.2 (max_le_max (by linarith) le_rfl)
  have hdmono : ∀ t ω, d (t + 1) ω ≤ d t ω := by
    intro t ω
    rw [hdsucc]
    have := hdnn t ω
    rcases le_total (X t ω + ζ t ω - D t ω) 0 with h | h
    · rw [max_eq_right h]
      rcases le_total (X t ω + d t ω + ζ t ω - D t ω) 0 with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
  have hcost : ∀ t ω, stageCost P (X t ω) (ζ t ω) (D t ω) + P.hplus * d (t + 1) ω =
      stageCost P (X' t ω) (ζ t ω) (D t ω) + P.hminus * (d t ω - d (t + 1) ω) := by
    intro t ω
    rw [hdsucc, hX'eq]
    exact cost_identity P (X t ω) (ζ t ω) (D t ω) (d t ω) (hdnn t ω)
  have hXm : ∀ t, Measurable (X t) := measurable_inv x ζ D hζ hD
  have hX'm : ∀ t, Measurable (X' t) := measurable_inv x' ζ D hζ hD
  have hdm : ∀ t, Measurable (d t) := fun t => (hX'm t).sub (hXm t)
  have hsc_nn : ∀ y a dd, 0 ≤ stageCost P y a dd := fun y a dd => by
    unfold stageCost; positivity
  -- the extra holding cost term
  let B : Ω → ℝ≥0∞ := fun ω => ∑' t, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω)
  have hBm : Measurable B :=
    Measurable.ennreal_tsum fun t => measurable_const.mul
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (hdm (t + 1))))
  -- pathwise comparison
  have hpath : ∀ ω, (∑' t, ENNReal.ofReal (α ^ t) *
        ENNReal.ofReal (stageCost P (X t ω) (ζ t ω) (D t ω))) + B ω ≤
      (∑' t, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (stageCost P (X' t ω) (ζ t ω) (D t ω)))
        + ENNReal.ofReal (P.hminus * d0) := by
    intro ω
    have hterm : ∀ t, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (stageCost P (X t ω) (ζ t ω) (D t ω))
        + ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω) =
        ENNReal.ofReal (α ^ t) * ENNReal.ofReal (stageCost P (X' t ω) (ζ t ω) (D t ω))
        + ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω)) := by
      intro t
      rw [← mul_add, ← mul_add, ← ENNReal.ofReal_add (hsc_nn _ _ _)
        (mul_nonneg hhp.le (hdnn _ _)), ← ENNReal.ofReal_add (hsc_nn _ _ _)
        (mul_nonneg hhm.le (sub_nonneg.2 (hdmono _ _))), hcost]
    have htel : (∑' t, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω)))
        ≤ ENNReal.ofReal (P.hminus * d0) := by
      refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
      calc ∑ t ∈ Finset.range N, ENNReal.ofReal (α ^ t) *
            ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω))
          ≤ ∑ t ∈ Finset.range N, ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω)) := by
            refine Finset.sum_le_sum fun t _ => ?_
            calc _ ≤ 1 * ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω)) := by
                  gcongr
                  exact ENNReal.ofReal_le_one.2 (pow_le_one₀ hα0 hα1)
              _ = _ := one_mul _
        _ = ENNReal.ofReal (∑ t ∈ Finset.range N, P.hminus * (d t ω - d (t + 1) ω)) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro t _
            exact mul_nonneg hhm.le (sub_nonneg.2 (hdmono _ _))
        _ ≤ ENNReal.ofReal (P.hminus * d0) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.mul_sum, Finset.sum_range_sub' (fun t => d t ω), hd0eq]
            have := hdnn N ω
            nlinarith
    calc _ = ∑' t, (ENNReal.ofReal (α ^ t) * ENNReal.ofReal (stageCost P (X t ω) (ζ t ω) (D t ω))
          + ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω)) :=
            (ENNReal.tsum_add).symm
      _ = ∑' t, (ENNReal.ofReal (α ^ t) * ENNReal.ofReal (stageCost P (X' t ω) (ζ t ω) (D t ω))
          + ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hminus * (d t ω - d (t + 1) ω))) := by
            simp_rw [hterm]
      _ = _ := ENNReal.tsum_add
      _ ≤ _ := add_le_add le_rfl htel
  have hint_ineq : Vζ P μ α x ζ D + ∫⁻ ω, B ω ∂μ ≤
      Vζ P μ α x' ζ D + ENNReal.ofReal (P.hminus * d0) := by
    unfold Vζ
    rw [← lintegral_add_right _ hBm]
    calc _ ≤ ∫⁻ ω, ((∑' t, ENNReal.ofReal (α ^ t) *
          ENNReal.ofReal (stageCost P (X' t ω) (ζ t ω) (D t ω)))
          + ENNReal.ofReal (P.hminus * d0)) ∂μ := lintegral_mono hpath
      _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
          mul_one]
  -- demands are nonnegative almost surely
  have hDnn : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ D t ω := by
    rw [ae_all_iff]
    intro t
    have h0 : μ (D t ⁻¹' Iio 0) = 0 := by
      rw [← Measure.map_apply (hD t) measurableSet_Iio, hlaw t]; exact hneg
    rw [ae_iff]
    simp only [not_le]
    exact h0
  -- the gap shrinks at most by the demand
  have hstep : ∀ ω, (∀ t, 0 ≤ D t ω) → ∀ t, d t ω - D t ω ≤ d (t + 1) ω := by
    intro ω hω t
    rw [hdsucc]
    have h1 := inv_nonneg x hx ζ D t ω
    have h2 := (hζr t ω).1
    have h3 := hω t
    have h4 := hdnn t ω
    rcases le_total (X t ω + ζ t ω - D t ω) 0 with h | h
    · rw [max_eq_right h]
      have := le_max_left (X t ω + d t ω + ζ t ω - D t ω) 0
      have hXt : 0 ≤ X t ω := h1
      linarith
    · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
  have hgap : ∀ ω, (∀ t, 0 ≤ D t ω) → ∀ t,
      d0 - ∑ s ∈ Finset.range (t + 1), D s ω ≤ d (t + 1) ω := by
    intro ω hω t
    induction t with
    | zero => simpa [hd0eq] using hstep ω hω 0
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have := hstep ω hω (t + 1)
      linarith
  -- mean of each demand
  have hmeanD : ∀ s, ∫⁻ ω, ENNReal.ofReal (D s ω) ∂μ = ENNReal.ofReal m := by
    intro s
    rw [show (∫⁻ ω, ENNReal.ofReal (D s ω) ∂μ) = ∫⁻ y, ENNReal.ofReal y ∂(μ.map (D s)) from
      (lintegral_map ENNReal.measurable_ofReal (hD s)).symm, hlaw s, hm]
    refine (ofReal_integral_eq_lintegral_ofReal (f := fun y => y) hint ?_).symm
    · have : ∀ᵐ y ∂P.demand, y ∉ Iio (0:ℝ) := measure_eq_zero_iff_ae_notMem.1 hneg
      filter_upwards [this] with y hy
      simpa using hy
  have hEd : ∀ t : ℕ, ENNReal.ofReal (d0 - ((t : ℝ) + 1) * m) ≤ ∫⁻ ω, ENNReal.ofReal (d (t + 1) ω) ∂μ := by
    intro t
    have hm0 : 0 ≤ m := hmean.le
    have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal d0 ≤ ENNReal.ofReal (d (t + 1) ω) +
        ∑ s ∈ Finset.range (t + 1), ENNReal.ofReal (D s ω) := by
      filter_upwards [hDnn] with ω hω
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hω s)]
      refine le_trans ?_ ENNReal.ofReal_add_le
      apply ENNReal.ofReal_le_ofReal
      have := hgap ω hω t
      linarith
    have hint2 : ENNReal.ofReal d0 ≤ ∫⁻ ω, ENNReal.ofReal (d (t + 1) ω) ∂μ +
        ((t : ℝ≥0∞) + 1) * ENNReal.ofReal m := by
      calc ENNReal.ofReal d0 = ∫⁻ _ω, ENNReal.ofReal d0 ∂μ := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ ω, (ENNReal.ofReal (d (t + 1) ω) +
            ∑ s ∈ Finset.range (t + 1), ENNReal.ofReal (D s ω)) ∂μ := lintegral_mono_ae hpt
        _ = ∫⁻ ω, ENNReal.ofReal (d (t + 1) ω) ∂μ +
            ∑ s ∈ Finset.range (t + 1), ∫⁻ ω, ENNReal.ofReal (D s ω) ∂μ := by
            rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (d (t + 1) ω))
                (ENNReal.measurable_ofReal.comp (hdm _)),
              lintegral_finset_sum (f := fun s ω => ENNReal.ofReal (D s ω)) _
                (fun s _ => ENNReal.measurable_ofReal.comp (hD s))]
        _ = _ := by
            simp_rw [hmeanD]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    rw [ENNReal.ofReal_sub _ (by positivity), tsub_le_iff_right]
    convert hint2 using 2
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  have hB_lb : 2 * T0 * m ≤ d0 → ENNReal.ofReal (h' * d0) ≤ ∫⁻ ω, B ω ∂μ := by
    intro hC
    have hαT : ∀ t, t < T0 → (1/2 : ℝ) ≤ α ^ t := fun t ht =>
      calc (1/2:ℝ) = αs ^ T0 := hαs_pow.symm
        _ ≤ α ^ T0 := pow_le_pow_left₀ hαs0.le hα.1 T0
        _ ≤ α ^ t := pow_le_pow_of_le_one hα0 hα1 ht.le
    have hterm : ∀ t, t < T0 → ENNReal.ofReal (P.hplus * d0 / 4) ≤
        ∫⁻ ω, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω) ∂μ := by
      intro t ht
      rw [lintegral_const_mul (f := fun ω => ENNReal.ofReal (P.hplus * d (t + 1) ω)) _
        (ENNReal.measurable_ofReal.comp (measurable_const.mul (hdm _)))]
      have h1 : ENNReal.ofReal (d0 / 2) ≤ ∫⁻ ω, ENNReal.ofReal (d (t + 1) ω) ∂μ := by
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hEd t)
        have : ((t:ℝ) + 1) ≤ T0 := by exact_mod_cast ht
        nlinarith [hmean]
      have h2 : ∫⁻ ω, ENNReal.ofReal (P.hplus * d (t + 1) ω) ∂μ =
          ENNReal.ofReal P.hplus * ∫⁻ ω, ENNReal.ofReal (d (t + 1) ω) ∂μ := by
        simp_rw [ENNReal.ofReal_mul hhp.le]
        rw [lintegral_const_mul (f := fun ω => ENNReal.ofReal (d (t + 1) ω)) _
          (ENNReal.measurable_ofReal.comp (hdm _))]
      rw [h2]
      calc ENNReal.ofReal (P.hplus * d0 / 4) =
            ENNReal.ofReal (1/2) * (ENNReal.ofReal P.hplus * ENNReal.ofReal (d0/2)) := by
            rw [← ENNReal.ofReal_mul hhp.le, ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
        _ ≤ _ := by
            gcongr
            exact hαT t ht
    calc ENNReal.ofReal (h' * d0) ≤ ∑ t ∈ Finset.range T0, ENNReal.ofReal (P.hplus * d0 / 4) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have : 4 * h' ≤ T0 * P.hplus := by rwa [div_le_iff₀ hhp] at hT0
          nlinarith
      _ ≤ ∑ t ∈ Finset.range T0,
            ∫⁻ ω, ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω) ∂μ :=
          Finset.sum_le_sum fun t ht => hterm t (Finset.mem_range.1 ht)
      _ = ∫⁻ ω, ∑ t ∈ Finset.range T0,
            ENNReal.ofReal (α ^ t) * ENNReal.ofReal (P.hplus * d (t + 1) ω) ∂μ :=
          (lintegral_finset_sum _ (fun t _ => measurable_const.mul
            (ENNReal.measurable_ofReal.comp (measurable_const.mul (hdm (t + 1)))))).symm
      _ ≤ ∫⁻ ω, B ω ∂μ := lintegral_mono fun ω => ENNReal.sum_le_tsum _
  refine ⟨?_, ?_⟩
  · split_ifs with hC
    · calc _ ≤ Vζ P μ α x ζ D + ∫⁻ ω, B ω ∂μ := add_le_add le_rfl (hB_lb hC)
        _ ≤ _ := hint_ineq
    · rw [ENNReal.ofReal_zero, add_zero]
      exact le_trans le_self_add hint_ineq
  · have hm0 : 0 ≤ m := hmean.le
    split_ifs with hC
    · have : 0 ≤ P.hminus * (2 * T0 * m) := by positivity
      nlinarith
    · push_neg at hC
      nlinarith

