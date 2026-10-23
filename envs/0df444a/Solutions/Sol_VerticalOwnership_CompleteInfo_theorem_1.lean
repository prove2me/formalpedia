-- Prove2me | solution 1 for VerticalOwnership.CompleteInfo.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T05:27:55.311114+00:00
-- url     : https://prove2.me/submissions/6845dac4-c75e-4be1-aa7c-9d0813d55ab2

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace PB74f28c8

open VerticalOwnership.CompleteInfo

/-- The cdf of an atomless probability measure is continuous. -/
theorem cdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : ∀ x, μ {x} = 0) :
    Continuous (fun x => cdf μ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hm := (cdf μ).mono
  have hsing : (cdf μ).measure {x} = ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) :=
    StieltjesFunction.measure_singleton _ x
  rw [measure_cdf, h0 x] at hsing
  have h1 : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.1 hsing.symm
  have h2 : Function.leftLim (cdf μ) x ≤ cdf μ x := Monotone.leftLim_le hm le_rfl
  have hl : Function.leftLim (cdf μ) x = cdf μ x := le_antisymm h2 (by linarith)
  have hL : ContinuousWithinAt (cdf μ) (Iio x) x :=
    (Monotone.continuousWithinAt_Iio_iff_leftLim_eq hm).2 hl
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨continuousWithinAt_Iio_iff_Iic.1 hL, (cdf μ).right_continuous x⟩

lemma swap_ind (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a q : ℝ) (k : ℝ → ℝ) (hk : Measurable k)
    (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ u, |g u| ≤ C) :
    ∫ x, (∫ u in Ioc a q, (if x ≤ k u then g u else 0)) ∂ρ
      = ∫ u in Ioc a q, ρ.real (Iic (k u)) * g u := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ k p.2} :=
    measurableSet_le measurable_fst (hk.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (x u : ℝ) => if x ≤ k u then g u else 0)
      (ρ.prod (volume.restrict (Ioc a q))) := by
    have : (Function.uncurry fun (x u : ℝ) => if x ≤ k u then g u else 0)
        = {p : ℝ × ℝ | p.1 ≤ k p.2}.indicator (fun p => g p.2) := by
      funext p; simp [Function.uncurry, Set.indicator]
    rw [this]
    refine Integrable.indicator ?_ hS
    refine Integrable.mono' (integrable_const C) (hg.comp measurable_snd).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC p.2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have : (fun x => if x ≤ k u then g u else 0) = (Iic (k u)).indicator (fun _ => g u) := by
    funext x; simp [Set.indicator]
  simp only
  rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul]

lemma pos_part_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (hae : ∀ᵐ x ∂μ, a ≤ x)
    (y : ℝ) : ∫ x, max (y - x) 0 ∂μ = ∫ u in Ioc a y, cdf μ u := by
  have h1 := swap_ind μ a y id measurable_id (fun _ => 1) measurable_const 1 (by simp)
  simp only [id, mul_one] at h1
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => cdf_eq_real μ u), ← h1]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  have : (fun u : ℝ => if x ≤ u then (1:ℝ) else 0) = (Ici x).indicator 1 := by
    funext u; simp [Set.indicator]
  rw [this, integral_indicator_one measurableSet_Ici, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  have hsub1 : Ioc x y ⊆ Ici x ∩ Ioc a y := fun u hu =>
    ⟨le_of_lt hu.1, lt_of_le_of_lt hx hu.1, hu.2⟩
  have hsub2 : Ici x ∩ Ioc a y ⊆ Icc x y := fun u hu => ⟨hu.1, hu.2.2⟩
  have e1 := measure_mono (μ := volume) hsub1
  have e2 := measure_mono (μ := volume) hsub2
  rw [Real.volume_Ioc] at e1
  rw [Real.volume_Icc] at e2
  rw [le_antisymm e2 e1, ENNReal.toReal_ofReal']

/-- `Φ(y) = ∫_{ε̲}^{y} F`. -/
noncomputable def Phi (M : Model) (y : ℝ) : ℝ := ∫ x in M.εlo..y, cdf M.P x

lemma cdf_cont (M : Model) (hM : M.Standing) : Continuous (fun x => cdf M.P x) := by
  haveI := hM.prob
  exact cdf_continuous M.P (fun x => hM.density Real.volume_singleton)

lemma ae_ge (M : Model) (hM : M.Standing) : ∀ᵐ x ∂M.P, M.εlo ≤ x := by
  haveI := hM.prob
  have h0 : M.P (Iic M.εlo) = 0 := by
    have h := hM.cdf_εlo
    rw [cdf_eq_real] at h
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h
  rw [ae_iff]
  have : {x : ℝ | ¬ M.εlo ≤ x} = Iio M.εlo := by ext; simp
  rw [this]
  exact measure_mono_null Iio_subset_Iic_self h0

lemma cdf_zero (M : Model) (hM : M.Standing) (x : ℝ) (hx : x ≤ M.εlo) : cdf M.P x = 0 :=
  le_antisymm (((cdf M.P).mono hx).trans_eq hM.cdf_εlo) (cdf_nonneg M.P x)

lemma Phi_zero (M : Model) (hM : M.Standing) (y : ℝ) (hy : y ≤ M.εlo) : Phi M y = 0 := by
  unfold Phi
  have h : EqOn (fun x => cdf M.P x) (fun _ => (0:ℝ)) (uIcc M.εlo y) := by
    intro x hx
    rw [mem_uIcc] at hx
    exact cdf_zero M hM x (by rcases hx with h | h <;> linarith [h.1, h.2])
  rw [intervalIntegral.integral_congr h]
  simp

lemma Epos (M : Model) (hM : M.Standing) (y : ℝ) : ∫ x, max (y - x) 0 ∂M.P = Phi M y := by
  haveI := hM.prob
  rcases le_or_gt M.εlo y with hy | hy
  · rw [pos_part_cdf M.P M.εlo (ae_ge M hM) y, Phi, intervalIntegral.integral_of_le hy]
  · rw [Phi_zero M hM y hy.le]
    have : (fun x => max (y - x) 0) =ᵐ[M.P] fun _ => (0:ℝ) := by
      filter_upwards [ae_ge M hM] with x hx
      exact max_eq_right (by linarith)
    rw [integral_congr_ae this, integral_zero]

lemma Phi_nonneg (M : Model) (hM : M.Standing) (y : ℝ) : 0 ≤ Phi M y := by
  rw [← Epos M hM y]
  exact integral_nonneg (fun x => le_max_right _ _)

lemma Phi_sub (M : Model) (a b : ℝ) : Phi M b - Phi M a = ∫ x in a..b, cdf M.P x :=
  intervalIntegral.integral_interval_sub_left ((cdf M.P).mono.intervalIntegrable)
    ((cdf M.P).mono.intervalIntegrable)

lemma int_maxsub (M : Model) (hM : M.Standing) (y : ℝ) :
    Integrable (fun x => max (y - x) 0) M.P := by
  haveI := hM.prob
  refine Integrable.mono' ((integrable_const |y|).add hM.integrable.norm)
    ((continuous_const.sub continuous_id).max continuous_const).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs, id, Pi.add_apply]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self y, neg_le_abs x]) (by positivity)

lemma int_lin (M : Model) (hM : M.Standing) (a b c y1 y2 : ℝ) :
    ∫ ε, (a - b * max (y1 - ε) 0 - c * max (y2 - ε) 0) ∂M.P
      = a - b * Phi M y1 - c * Phi M y2 := by
  haveI := hM.prob
  have i1 := int_maxsub M hM y1
  have i2 := int_maxsub M hM y2
  have j1 : Integrable (fun ε : ℝ => b * max (y1 - ε) 0) M.P := i1.const_mul b
  have j2 : Integrable (fun ε : ℝ => c * max (y2 - ε) 0) M.P := i2.const_mul c
  have j0 : Integrable (fun ε : ℝ => a - b * max (y1 - ε) 0) M.P := (integrable_const a).sub j1
  rw [integral_sub j0 j2, integral_sub (integrable_const a) j1, integral_const, integral_const_mul,
    integral_const_mul, Epos M hM, Epos M hM]
  simp

lemma vr_formula (M : Model) (hM : M.Standing) (β μ q K : ℝ) (hqK : q ≤ K) :
    M.vr β μ q K = (M.r - M.w + β * M.w) * (K - Phi M (K - μ)) - β * M.c * K
      - M.w * (1 - β) * Phi M (q - μ) := by
  have hmin : ∀ ε : ℝ, min (μ + ε) K = K - max (K - μ - ε) 0 := fun ε => by
    simp only [min_def, max_def]; split_ifs <;> linarith
  have hmm : ∀ ε : ℝ, min K (max (μ + ε) q) = K - max (K - μ - ε) 0 + max (q - μ - ε) 0 :=
    fun ε => by simp only [min_def, max_def]; split_ifs <;> linarith
  have h1 : M.πr μ q K
      = (M.r - M.w) * K - (M.r - M.w) * Phi M (K - μ) - M.w * Phi M (q - μ) := by
    unfold Model.πr
    simp_rw [hmin]
    rw [← int_lin M hM]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
    dsimp only
    ring
  have h2 : M.πs μ q K
      = (M.w * K - M.c * K) - M.w * Phi M (K - μ) - (-M.w) * Phi M (q - μ) := by
    unfold Model.πs
    simp_rw [hmm]
    rw [← int_lin M hM]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
    dsimp only
    ring
  unfold Model.vr
  rw [h1, h2]
  ring

lemma quant (M : Model) (hM : M.Standing) (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    M.εlo < M.Finv z ∧ cdf M.P (M.Finv z) = z ∧ (∀ x, x < M.Finv z → cdf M.P x < z) ∧
      (∀ x, M.Finv z < x → z < cdf M.P x) := by
  haveI := hM.prob
  have hcont := cdf_cont M hM
  set S : Set ℝ := {x | z ≤ cdf M.P x} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop M.P).eventually (lt_mem_nhds hz1)).exists
    exact ⟨x, le_of_lt hx⟩
  have hlb : ∀ x ∈ S, M.εlo ≤ x := by
    intro x hx
    by_contra h
    push_neg at h
    have := cdf_zero M hM x h.le
    have hx' : z ≤ cdf M.P x := hx
    linarith
  have hbdd : BddBelow S := ⟨M.εlo, hlb⟩
  have hclosed : IsClosed S := isClosed_le continuous_const hcont
  have hFinv : M.Finv z = sInf S := rfl
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  have hmem' : z ≤ cdf M.P (sInf S) := hmem
  have hge : M.εlo ≤ sInf S := le_csInf hne hlb
  have hlt : ∀ x, x < sInf S → cdf M.P x < z := by
    intro x hx
    by_contra h
    push_neg at h
    exact absurd (csInf_le hbdd h) (not_le.2 hx)
  have hgt0 : M.εlo < sInf S := by
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hM.cdf_εlo] at hmem'
      linarith
  have heq : cdf M.P (sInf S) = z := by
    have hzI : z ∈ Icc (cdf M.P M.εlo) (cdf M.P (sInf S)) :=
      ⟨by rw [hM.cdf_εlo]; exact hz0.le, hmem'⟩
    obtain ⟨x, hx, hxz⟩ := intermediate_value_Icc hge hcont.continuousOn hzI
    have hxS : z ≤ cdf M.P x := le_of_eq hxz.symm
    have : sInf S ≤ x := csInf_le hbdd hxS
    have hx' : x = sInf S := le_antisymm hx.2 this
    rw [← hx']
    exact hxz
  rw [hFinv]
  refine ⟨hgt0, heq, hlt, ?_⟩
  intro x hx
  have := hM.strictMono_support (sInf S) x hgt0.le hx (by rw [heq]; exact hz1)
  rw [heq] at this
  exact this

lemma Finv_mono (M : Model) (hM : M.Standing) {z1 z2 : ℝ} (h1 : 0 < z1) (h2 : z2 < 1)
    (h12 : z1 ≤ z2) : M.Finv z1 ≤ M.Finv z2 := by
  by_contra h
  push_neg at h
  have q1 := quant M hM z1 h1 (by linarith)
  have q2 := quant M hM z2 (by linarith) h2
  have := q1.2.2.1 _ h
  linarith [q2.2.1]

lemma key_strict (M : Model) (hM : M.Standing) (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (y : ℝ)
    (hy : y ≠ M.Finv z) : z * y - Phi M y < z * M.Finv z - Phi M (M.Finv z) := by
  obtain ⟨_, _, hlt, hgt⟩ := quant M hM z hz0 hz1
  have hcont := cdf_cont M hM
  rcases lt_or_gt_of_ne hy with h | h
  · have hpos : 0 < ∫ x in y..M.Finv z, (z - cdf M.P x) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        ((continuous_const.sub hcont).intervalIntegrable _ _)
        (fun x hx => sub_pos.2 (hlt x hx.2)) h
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, ← Phi_sub M] at hpos
    nlinarith
  · have hpos : 0 < ∫ x in M.Finv z..y, (cdf M.P x - z) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        ((hcont.sub continuous_const).intervalIntegrable _ _)
        (fun x hx => sub_pos.2 (hgt x hx.1)) h
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, ← Phi_sub M] at hpos
    nlinarith

lemma key_le (M : Model) (hM : M.Standing) (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (y : ℝ) :
    z * y - Phi M y ≤ z * M.Finv z - Phi M (M.Finv z) := by
  by_cases hy : y = M.Finv z
  · rw [hy]
  · exact (key_strict M hM z hz0 hz1 y hy).le

lemma zs_bounds (M : Model) (hM : M.Standing) : 0 < M.zs ∧ M.zs < 1 := by
  have hw : 0 < M.w := by linarith [hM.c_pos, hM.c_lt_w]
  unfold Model.zs
  constructor
  · have : M.c / M.w < 1 := (div_lt_one hw).2 hM.c_lt_w
    linarith
  · have : 0 < M.c / M.w := div_pos hM.c_pos hw
    linarith

lemma zr_bounds (M : Model) (hM : M.Standing) : 0 < M.zr ∧ M.zr < 1 := by
  have hw : 0 < M.w := by linarith [hM.c_pos, hM.c_lt_w]
  have hr : 0 < M.r := by linarith [hM.w_lt_r]
  unfold Model.zr
  constructor
  · have : M.w / M.r < 1 := (div_lt_one hr).2 hM.w_lt_r
    linarith
  · have : 0 < M.w / M.r := div_pos hw hr
    linarith

lemma zrβ_bounds (M : Model) (hM : M.Standing) (β : ℝ) (hβ : β ∈ Icc (0:ℝ) 1) :
    0 < M.zrβ β ∧ M.zrβ β < 1 := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  have hb := hβ.1
  have hb1 := hβ.2
  unfold Model.zrβ
  have hu : 0 < 1 - M.zr := by linarith
  have hv0 : 0 < 1 - β * M.zs := by nlinarith
  have hv1 : 1 - β * M.zs ≤ 1 := by nlinarith
  constructor <;> nlinarith [mul_pos hu hv0, mul_le_mul_of_nonneg_left hv1 hu.le]

lemma zrβ_sub (M : Model) (β1 β2 : ℝ) :
    M.zrβ β2 - M.zrβ β1 = (β2 - β1) * M.zs * (1 - M.zr) := by
  unfold Model.zrβ; ring

lemma r_zrβ (M : Model) (hM : M.Standing) (β : ℝ) :
    M.r * M.zrβ β = M.r - M.w + β * (M.w - M.c) := by
  have hw : M.w ≠ 0 := by linarith [hM.c_pos, hM.c_lt_w]
  have hr : M.r ≠ 0 := by linarith [hM.c_pos, hM.c_lt_w, hM.w_lt_r]
  unfold Model.zrβ Model.zr Model.zs
  field_simp
  ring

lemma r_a (M : Model) (hM : M.Standing) (β : ℝ) :
    M.r * (M.zr + β * (1 - M.zr)) = M.r - M.w + β * M.w := by
  have hr : M.r ≠ 0 := by linarith [hM.c_pos, hM.c_lt_w, hM.w_lt_r]
  unfold Model.zr
  field_simp
  ring

lemma G9_eq (M : Model) (β : ℝ) : M.G9 β = M.zrβ β * M.Finv (M.zrβ β) - Phi M (M.Finv (M.zrβ β))
    - M.zrβ β * M.Finv M.zs + (M.zr + β * (1 - M.zr)) * Phi M (M.Finv M.zs) := by
  unfold Model.G9 Phi
  ring

lemma G9_neg (M : Model) (hM : M.Standing) (β : ℝ) (hβ : β ∈ Icc (0:ℝ) 1)
    (h : M.Finv (M.zrβ β) < M.Finv M.zs) : M.G9 β < 0 := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  obtain ⟨_, hFs, _, _⟩ := quant M hM M.zs hs0 hs1
  have hdiff : Phi M (M.Finv M.zs) - Phi M (M.Finv (M.zrβ β))
      ≤ M.zs * (M.Finv M.zs - M.Finv (M.zrβ β)) := by
    rw [Phi_sub]
    have := intervalIntegral.integral_mono_on (g := fun _ : ℝ => M.zs) h.le
      ((cdf M.P).mono.intervalIntegrable) (intervalIntegrable_const (μ := volume))
      (fun x hx => ((cdf M.P).mono hx.2).trans_eq hFs)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hΦ := Phi_nonneg M hM (M.Finv (M.zrβ β))
  have e : M.zrβ β - (M.zr + β * (1 - M.zr)) * M.zs = M.zr * (1 - M.zs) := by
    unfold Model.zrβ; ring
  have e' : M.zrβ β * (M.Finv M.zs - M.Finv (M.zrβ β))
      = (M.zr + β * (1 - M.zr)) * M.zs * (M.Finv M.zs - M.Finv (M.zrβ β))
        + M.zr * (1 - M.zs) * (M.Finv M.zs - M.Finv (M.zrβ β)) := by
    linear_combination (M.Finv M.zs - M.Finv (M.zrβ β)) * e
  have ha0 : 0 ≤ M.zr + β * (1 - M.zr) := by nlinarith [hβ.1]
  have ha1 : 0 ≤ 1 - (M.zr + β * (1 - M.zr)) := by nlinarith [hβ.2]
  rw [G9_eq]
  nlinarith [mul_le_mul_of_nonneg_left hdiff ha0, mul_nonneg ha1 hΦ,
    mul_pos (mul_pos hr0 (sub_pos.2 hs1)) (sub_pos.2 h)]

/-- A Lipschitz constant for `G9` on `[0,1]` (one-sided). -/
noncomputable def Lc (M : Model) : ℝ :=
  M.zs * (1 - M.zr) * (M.Finv (M.zrβ 1) - M.Finv M.zs) + (1 - M.zr) * Phi M (M.Finv M.zs) + 1

lemma zrβ_le_one_val (M : Model) (hM : M.Standing) (β : ℝ) (hβ : β ∈ Icc (0:ℝ) 1) :
    M.zrβ β ≤ M.zrβ 1 := by
  obtain ⟨hs0, _⟩ := zs_bounds M hM
  obtain ⟨_, hr1⟩ := zr_bounds M hM
  have := zrβ_sub M β 1
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hβ.2) hs0.le) (sub_nonneg.2 hr1.le)]

lemma Lc_pos (M : Model) (hM : M.Standing) : 0 < Lc M := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  obtain ⟨hzT0, hzT1⟩ := zrβ_bounds M hM 1 ⟨zero_le_one, le_rfl⟩
  have hle : M.zs ≤ M.zrβ 1 := by
    have : M.zrβ 1 - M.zs = M.zr * (1 - M.zs) := by unfold Model.zrβ; ring
    nlinarith [mul_pos hr0 (sub_pos.2 hs1)]
  have hmono := Finv_mono M hM hs0 hzT1 hle
  have hΦ := Phi_nonneg M hM (M.Finv M.zs)
  unfold Lc
  nlinarith [mul_nonneg (mul_nonneg hs0.le (sub_nonneg.2 hr1.le)) (sub_nonneg.2 hmono),
    mul_nonneg (sub_nonneg.2 hr1.le) hΦ]

lemma G9_lipU (M : Model) (hM : M.Standing) (β1 β2 : ℝ) (h1 : β1 ∈ Icc (0:ℝ) 1)
    (h2 : β2 ∈ Icc (0:ℝ) 1) (h12 : β1 ≤ β2) : M.G9 β2 ≤ M.G9 β1 + Lc M * (β2 - β1) := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  obtain ⟨hz10, hz11⟩ := zrβ_bounds M hM β1 h1
  obtain ⟨hz20, hz21⟩ := zrβ_bounds M hM β2 h2
  obtain ⟨hzT0, hzT1⟩ := zrβ_bounds M hM 1 ⟨zero_le_one, le_rfl⟩
  have hk := key_le M hM (M.zrβ β1) hz10 hz11 (M.Finv (M.zrβ β2))
  have hd := zrβ_sub M β1 β2
  have hd2 : M.zrβ β2 * M.Finv (M.zrβ β2) = M.zrβ β1 * M.Finv (M.zrβ β2)
      + (β2 - β1) * M.zs * (1 - M.zr) * M.Finv (M.zrβ β2) := by
    linear_combination M.Finv (M.zrβ β2) * hd
  have hds : M.zrβ β2 * M.Finv M.zs = M.zrβ β1 * M.Finv M.zs
      + (β2 - β1) * M.zs * (1 - M.zr) * M.Finv M.zs := by
    linear_combination M.Finv M.zs * hd
  have hT : M.Finv (M.zrβ β2) ≤ M.Finv (M.zrβ 1) :=
    Finv_mono M hM hz20 hzT1 (zrβ_le_one_val M hM β2 h2)
  have hΦ := Phi_nonneg M hM (M.Finv M.zs)
  rw [G9_eq, G9_eq]
  unfold Lc
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 h12) hs0.le)
    (sub_nonneg.2 hr1.le)) (sub_nonneg.2 hT), sub_nonneg.2 h12]

lemma G9_mono (M : Model) (hM : M.Standing) (β1 β2 : ℝ) (h1 : β1 ∈ Icc (0:ℝ) 1)
    (h2 : β2 ∈ Icc (0:ℝ) 1) (h12 : β1 ≤ β2) (hpos : 0 ≤ M.G9 β1) : M.G9 β1 ≤ M.G9 β2 := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  obtain ⟨hz20, hz21⟩ := zrβ_bounds M hM β2 h2
  have hy1 : M.Finv M.zs ≤ M.Finv (M.zrβ β1) := by
    by_contra h
    push_neg at h
    linarith [G9_neg M hM β1 h1 h]
  have hk := key_le M hM (M.zrβ β2) hz20 hz21 (M.Finv (M.zrβ β1))
  have hd := zrβ_sub M β1 β2
  have hd1 : M.zrβ β2 * M.Finv (M.zrβ β1) = M.zrβ β1 * M.Finv (M.zrβ β1)
      + (β2 - β1) * M.zs * (1 - M.zr) * M.Finv (M.zrβ β1) := by
    linear_combination M.Finv (M.zrβ β1) * hd
  have hds : M.zrβ β2 * M.Finv M.zs = M.zrβ β1 * M.Finv M.zs
      + (β2 - β1) * M.zs * (1 - M.zr) * M.Finv M.zs := by
    linear_combination M.Finv M.zs * hd
  have hΦ := Phi_nonneg M hM (M.Finv M.zs)
  rw [G9_eq, G9_eq]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 h12) hs0.le)
    (sub_nonneg.2 hr1.le)) (sub_nonneg.2 hy1),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hr1.le)) hΦ]

lemma G9_one_pos (M : Model) (hM : M.Standing) : 0 < M.G9 1 := by
  obtain ⟨hs0, hs1⟩ := zs_bounds M hM
  obtain ⟨hr0, hr1⟩ := zr_bounds M hM
  obtain ⟨hzT0, hzT1⟩ := zrβ_bounds M hM 1 ⟨zero_le_one, le_rfl⟩
  have hgap : M.zrβ 1 - M.zs = M.zr * (1 - M.zs) := by unfold Model.zrβ; ring
  obtain ⟨_, hFs, _, _⟩ := quant M hM M.zs hs0 hs1
  obtain ⟨_, hFT, _, _⟩ := quant M hM (M.zrβ 1) hzT0 hzT1
  have hne : M.Finv M.zs ≠ M.Finv (M.zrβ 1) := by
    intro h
    have : M.zs = M.zrβ 1 := by
      calc M.zs = cdf M.P (M.Finv M.zs) := hFs.symm
        _ = cdf M.P (M.Finv (M.zrβ 1)) := by rw [h]
        _ = M.zrβ 1 := hFT
    nlinarith [mul_pos hr0 (sub_pos.2 hs1)]
  have hk := key_strict M hM (M.zrβ 1) hzT0 hzT1 (M.Finv M.zs) hne
  rw [G9_eq]
  nlinarith

lemma threshold (M : Model) (hM : M.Standing) :
    ∃ βlow : ℝ, IsLeast {β : ℝ | β ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ M.G9 β} βlow ∧ βlow < 1 ∧
      ∀ β ∈ Icc (0:ℝ) 1, (β < βlow → M.G9 β < 0) ∧ (βlow ≤ β → 0 ≤ M.G9 β) := by
  set S := {β : ℝ | β ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ M.G9 β} with hS
  have hone : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hG1 := G9_one_pos M hM
  have h1S : (1:ℝ) ∈ S := ⟨hone, hG1.le⟩
  have hbdd : BddBelow S := ⟨0, fun b hb => hb.1.1⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  have hL := Lc_pos M hM
  have hb0 : 0 ≤ sInf S := le_csInf hne (fun x hx => hx.1.1)
  have hb1 : sInf S ≤ 1 := csInf_le hbdd h1S
  have hbI : sInf S ∈ Icc (0:ℝ) 1 := ⟨hb0, hb1⟩
  have hGb : 0 ≤ M.G9 (sInf S) := by
    by_contra hneg
    push_neg at hneg
    have hq : 0 < (-M.G9 (sInf S)) / Lc M := div_pos (neg_pos.2 hneg) hL
    have hlt : sInf S < sInf S + (-M.G9 (sInf S)) / Lc M := by linarith
    obtain ⟨β, hβS, hβlt⟩ := exists_lt_of_csInf_lt hne hlt
    have hbβ : sInf S ≤ β := csInf_le hbdd hβS
    have hlip := G9_lipU M hM (sInf S) β hbI hβS.1 hbβ
    have h3 : (β - sInf S) * Lc M < -M.G9 (sInf S) := (lt_div_iff₀ hL).1 (by linarith)
    have h4 : 0 ≤ M.G9 β := hβS.2
    nlinarith
  refine ⟨sInf S, ⟨⟨hbI, hGb⟩, fun x hx => csInf_le hbdd hx⟩, ?_, ?_⟩
  · have hq : 0 < M.G9 1 / Lc M := div_pos hG1 hL
    have hβ'1 : max 0 (1 - M.G9 1 / Lc M) < 1 := max_lt zero_lt_one (by linarith)
    have hβ'I : max 0 (1 - M.G9 1 / Lc M) ∈ Icc (0:ℝ) 1 := ⟨le_max_left _ _, hβ'1.le⟩
    have hlip := G9_lipU M hM _ 1 hβ'I hone hβ'1.le
    have h2 : 1 - max 0 (1 - M.G9 1 / Lc M) ≤ M.G9 1 / Lc M := by
      have := le_max_right 0 (1 - M.G9 1 / Lc M)
      linarith
    have h3 := (le_div_iff₀ hL).1 h2
    have hβ'S : max 0 (1 - M.G9 1 / Lc M) ∈ S := ⟨hβ'I, by nlinarith⟩
    exact lt_of_le_of_lt (csInf_le hbdd hβ'S) hβ'1
  · intro β hβ
    constructor
    · intro hlt
      by_contra h
      push_neg at h
      exact absurd (csInf_le hbdd ⟨hβ, h⟩) (not_le.2 hlt)
    · intro hle
      exact le_trans hGb (G9_mono M hM (sInf S) β hbI hβ hle hGb)

end PB74f28c8

open MeasureTheory ProbabilityTheory VerticalOwnership.CompleteInfo in
theorem solution (M : Model) (hM : M.Standing) :
    ∃ βlow : ℝ, IsLeast {β : ℝ | β ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ M.G9 β} βlow ∧ βlow < 1 ∧
      ∀ μ ∈ ({M.μL, M.μH} : Set ℝ), ∀ β ∈ Set.Icc (0 : ℝ) 1,
        (∃ qs : ℝ, 0 ≤ qs ∧ IsMaxOn (fun q => M.vr β μ q q) (Set.Ici 0) qs) ∧
        ∀ qs : ℝ, 0 ≤ qs → IsMaxOn (fun q => M.vr β μ q q) (Set.Ici 0) qs →
          (M.qCI β μ qs, M.KCI μ (M.qCI β μ qs)) =
              (if β < βlow then ((0 : ℝ), μ + M.Finv M.zs)
               else (μ + M.Finv (M.zrβ β), μ + M.Finv (M.zrβ β))) ∧
            IsMaxOn (fun q => M.vr β μ q (M.KCI μ q)) (Set.Ici 0) (M.qCI β μ qs) := by
  haveI := hM.prob
  obtain ⟨βlow, hleast, hlt1, hsplit⟩ := PB74f28c8.threshold M hM
  refine ⟨βlow, hleast, hlt1, ?_⟩
  intro μ hμ β hβ
  have hμε : 0 ≤ μ + M.εlo := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with h | h
    · rw [h]; exact hM.demand_nonneg
    · rw [h]; linarith [hM.demand_nonneg, hM.μL_lt_μH]
  obtain ⟨hs0, hs1⟩ := PB74f28c8.zs_bounds M hM
  obtain ⟨hz0, hz1⟩ := PB74f28c8.zrβ_bounds M hM β hβ
  obtain ⟨hys_gt, _, _, _⟩ := PB74f28c8.quant M hM M.zs hs0 hs1
  obtain ⟨hyb_gt, _, _, _⟩ := PB74f28c8.quant M hM (M.zrβ β) hz0 hz1
  have hr : 0 < M.r := by linarith [hM.c_pos, hM.c_lt_w, hM.w_lt_r]
  have hw : 0 < M.w := by linarith [hM.c_pos, hM.c_lt_w]
  have hrz := PB74f28c8.r_zrβ M hM β
  have hra := PB74f28c8.r_a M hM β
  have hdiag : ∀ q, M.vr β μ q q = M.r * (M.zrβ β * q - PB74f28c8.Phi M (q - μ)) := by
    intro q
    rw [PB74f28c8.vr_formula M hM β μ q q le_rfl]
    linear_combination (-q) * hrz
  have hK0 : 0 ≤ μ + M.Finv M.zs := by linarith
  have hΦ0 : PB74f28c8.Phi M (0 - μ) = 0 := PB74f28c8.Phi_zero M hM _ (by linarith)
  have hA : M.vr β μ 0 (μ + M.Finv M.zs) = M.r * (M.zrβ β * (μ + M.Finv M.zs))
      - (M.r - M.w + β * M.w) * PB74f28c8.Phi M (M.Finv M.zs) := by
    rw [PB74f28c8.vr_formula M hM β μ 0 (μ + M.Finv M.zs) hK0, hΦ0,
      show μ + M.Finv M.zs - μ = M.Finv M.zs by ring]
    linear_combination (-(μ + M.Finv M.zs)) * hrz
  have hlow : ∀ q, q ≤ μ + M.Finv M.zs → M.vr β μ q (μ + M.Finv M.zs)
      = M.vr β μ 0 (μ + M.Finv M.zs) - M.w * (1 - β) * PB74f28c8.Phi M (q - μ) := by
    intro q hq
    rw [PB74f28c8.vr_formula M hM β μ q (μ + M.Finv M.zs) hq,
      PB74f28c8.vr_formula M hM β μ 0 (μ + M.Finv M.zs) hK0, hΦ0]
    ring
  have hG : M.vr β μ (μ + M.Finv (M.zrβ β)) (μ + M.Finv (M.zrβ β))
      - M.vr β μ 0 (μ + M.Finv M.zs) = M.r * M.G9 β := by
    rw [hdiag, hA, PB74f28c8.G9_eq, show μ + M.Finv (M.zrβ β) - μ = M.Finv (M.zrβ β) by ring]
    linear_combination (-PB74f28c8.Phi M (M.Finv M.zs)) * hra
  have hq0 : 0 ≤ μ + M.Finv (M.zrβ β) := by linarith
  have hmaxle : ∀ q, M.vr β μ q q ≤ M.vr β μ (μ + M.Finv (M.zrβ β)) (μ + M.Finv (M.zrβ β)) := by
    intro q
    rw [hdiag, hdiag, show μ + M.Finv (M.zrβ β) - μ = M.Finv (M.zrβ β) by ring]
    have := PB74f28c8.key_le M hM (M.zrβ β) hz0 hz1 (q - μ)
    nlinarith [mul_le_mul_of_nonneg_left this hr.le]
  have hmaxlt : ∀ q, q ≠ μ + M.Finv (M.zrβ β) →
      M.vr β μ q q < M.vr β μ (μ + M.Finv (M.zrβ β)) (μ + M.Finv (M.zrβ β)) := by
    intro q hq
    rw [hdiag, hdiag, show μ + M.Finv (M.zrβ β) - μ = M.Finv (M.zrβ β) by ring]
    have hne : q - μ ≠ M.Finv (M.zrβ β) := by
      intro h; apply hq; linarith
    have := PB74f28c8.key_strict M hM (M.zrβ β) hz0 hz1 (q - μ) hne
    nlinarith [mul_lt_mul_of_pos_left this hr]
  constructor
  · exact ⟨μ + M.Finv (M.zrβ β), hq0, isMaxOn_iff.2 (fun q _ => hmaxle q)⟩
  · intro qs hqs hmax
    have hqs_eq : qs = μ + M.Finv (M.zrβ β) := by
      by_contra hne
      have h1 := hmaxlt qs hne
      have h2 := isMaxOn_iff.1 hmax (μ + M.Finv (M.zrβ β)) (Set.mem_Ici.2 hq0)
      linarith
    subst hqs_eq
    by_cases hβl : β < βlow
    · have hGn := (hsplit β hβ).1 hβl
      have hrG := mul_neg_of_pos_of_neg hr hGn
      have hqCI : M.qCI β μ (μ + M.Finv (M.zrβ β)) = 0 := by
        unfold Model.qCI
        rw [if_pos]
        linarith
      have hKCI0 : M.KCI μ 0 = μ + M.Finv M.zs := by
        unfold Model.KCI
        rw [if_pos hK0]
      rw [hqCI, hKCI0, if_pos hβl]
      refine ⟨rfl, ?_⟩
      rw [isMaxOn_iff]
      intro q hq
      show M.vr β μ q (M.KCI μ q) ≤ M.vr β μ 0 (M.KCI μ 0)
      rw [hKCI0]
      unfold Model.KCI
      split_ifs with hqK
      · rw [hlow q hqK]
        have := PB74f28c8.Phi_nonneg M hM (q - μ)
        nlinarith [mul_nonneg (mul_nonneg hw.le (sub_nonneg.2 hβ.2)) this]
      · have := hmaxle q
        linarith
    · have hGp := (hsplit β hβ).2 (not_lt.1 hβl)
      have hrG := mul_nonneg hr.le hGp
      have hyb_ge : M.Finv M.zs ≤ M.Finv (M.zrβ β) := by
        by_contra h
        push_neg at h
        linarith [PB74f28c8.G9_neg M hM β hβ h]
      have hqCI : M.qCI β μ (μ + M.Finv (M.zrβ β)) = μ + M.Finv (M.zrβ β) := by
        unfold Model.qCI
        rw [if_neg]
        exact not_lt.2 (by linarith)
      have hKq : M.KCI μ (μ + M.Finv (M.zrβ β)) = μ + M.Finv (M.zrβ β) := by
        unfold Model.KCI
        split_ifs with h
        · linarith
        · rfl
      rw [hqCI, hKq, if_neg hβl]
      refine ⟨rfl, ?_⟩
      rw [isMaxOn_iff]
      intro q hq
      show M.vr β μ q (M.KCI μ q)
        ≤ M.vr β μ (μ + M.Finv (M.zrβ β)) (M.KCI μ (μ + M.Finv (M.zrβ β)))
      rw [hKq]
      unfold Model.KCI
      split_ifs with hqK
      · rw [hlow q hqK]
        have := PB74f28c8.Phi_nonneg M hM (q - μ)
        nlinarith [mul_nonneg (mul_nonneg hw.le (sub_nonneg.2 hβ.2)) this]
      · exact hmaxle q
