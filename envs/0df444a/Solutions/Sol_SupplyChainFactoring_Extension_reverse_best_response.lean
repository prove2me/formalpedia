-- Prove2me | solution 1 for SupplyChainFactoring.Extension.reverse_best_response
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:06:53.895777+00:00
-- url     : https://prove2.me/submissions/96a1c300-ce7b-48be-bba8-c2494c328aaf

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

open MeasureTheory ProbabilityTheory Set Filter Topology

lemma aux_rbr_noatom (M : Model) (x : ℝ) : M.μ {x} = 0 := by
  have hac : M.μ ≪ volume := by
    rw [M.density]; exact withDensity_absolutelyContinuous _ _
  exact hac (Real.volume_singleton)

lemma aux_rbr_cont (M : Model) : Continuous M.Fbar := by
  have := M.isProb
  have hc : Continuous (cdf M.μ) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · rw [(monotone_cdf M.μ).continuousWithinAt_Iio_iff_leftLim_eq]
      have h1 := (cdf M.μ).measure_singleton x
      rw [measure_cdf, aux_rbr_noatom] at h1
      have h2 := (monotone_cdf M.μ).leftLim_le (le_refl x)
      have h3 : cdf M.μ x - Function.leftLim (cdf M.μ) x ≤ 0 := ENNReal.ofReal_eq_zero.1 h1.symm
      linarith
    · exact ((cdf M.μ).right_continuous x).mono Ioi_subset_Ici_self
  unfold Model.Fbar
  exact continuous_const.sub hc

lemma aux_rbr_anti (M : Model) : Antitone M.Fbar := by
  intro a b hab
  unfold Model.Fbar
  have := monotone_cdf M.μ hab
  linarith

lemma aux_rbr_nonneg (M : Model) (x : ℝ) : 0 ≤ M.Fbar x := by
  unfold Model.Fbar
  have := cdf_le_one M.μ x
  linarith

lemma aux_rbr_le_one (M : Model) (x : ℝ) : M.Fbar x ≤ 1 := by
  unfold Model.Fbar
  have := cdf_nonneg M.μ x
  linarith

lemma aux_rbr_zero (M : Model) : M.Fbar 0 = 1 := by
  have := M.isProb
  have hIio : M.μ (Iio 0) = 0 := by
    rw [M.density, withDensity_apply _ measurableSet_Iio]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun x hx => by simp [M.f_zero_of_neg x hx])]
    simp
  have hIic : M.μ (Iic 0) = 0 := by
    rw [← Iio_union_right]
    apply le_antisymm _ (by simp)
    calc M.μ (Iio 0 ∪ {0}) ≤ M.μ (Iio 0) + M.μ {0} := measure_union_le _ _
      _ = 0 := by rw [hIio, aux_rbr_noatom]; simp
  unfold Model.Fbar
  rw [cdf_eq_real, measureReal_def, hIic]
  simp

lemma aux_rbr_lt_one (M : Model) {q : ℝ} (hq : 0 < q) : M.Fbar q < 1 := by
  have := M.isProb
  obtain ⟨r, hr0, hrZ⟩ := EReal.lt_iff_exists_real_btwn.1 M.Z_pos
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  set r' := min r q with hr'
  have hr'pos : 0 < r' := lt_min hr0' hq
  have hsub : Icc 0 r' ⊆ {x : ℝ | 0 ≤ x ∧ (x : EReal) ≤ M.Z} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have : x ≤ r := hx.2.trans (min_le_left _ _)
    exact (EReal.coe_le_coe_iff.2 this).trans hrZ.le
  obtain ⟨x0, hx0K, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hr'pos.le)
    (M.f_continuousOn.mono hsub)
  have hm : 0 < M.f x0 := M.f_pos x0 (hsub hx0K).1 (hsub hx0K).2
  have hpos : 0 < M.μ (Iic q) := by
    have h1 : M.μ (Icc 0 r') ≤ M.μ (Iic q) :=
      measure_mono (fun x hx => hx.2.trans (min_le_right _ _))
    refine lt_of_lt_of_le ?_ h1
    rw [M.density, withDensity_apply _ measurableSet_Icc]
    have h2 : ∫⁻ _ in Icc 0 r', ENNReal.ofReal (M.f x0) ∂volume ≤
        ∫⁻ x in Icc 0 r', ENNReal.ofReal (M.f x) ∂volume :=
      setLIntegral_mono' measurableSet_Icc (fun x hx => ENNReal.ofReal_le_ofReal (hmin hx))
    refine lt_of_lt_of_le ?_ h2
    rw [setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hm).ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hcdf : 0 < cdf M.μ q := by
    rw [cdf_eq_real, measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  unfold Model.Fbar
  linarith

lemma aux_rbr_ltZ (M : Model) {q : ℝ} (hq : 0 < M.Fbar q) : (q : EReal) < M.Z := by
  have := M.isProb
  by_contra h
  push_neg at h
  have hIoi : M.μ (Ioi q) = 0 := by
    rw [M.density, withDensity_apply _ measurableSet_Ioi]
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)
      (fun x hx => by
        have : M.Z < (x : EReal) := h.trans_lt (EReal.coe_lt_coe_iff.2 hx)
        simp [M.f_zero_of_gt x this])]
    simp
  have h1 : M.μ (Iic q) = 1 := by
    rw [← prob_compl_eq_zero_iff measurableSet_Iic, compl_Iic]
    exact hIoi
  have : M.Fbar q = 0 := by
    unfold Model.Fbar
    rw [cdf_eq_real, measureReal_def, h1]
    simp
  linarith

lemma aux_rbr_sub (M : Model) (a b : ℝ) : M.S b - M.S a = ∫ x in a..b, M.Fbar x := by
  unfold Model.S
  exact intervalIntegral.integral_interval_sub_left ((aux_rbr_cont M).intervalIntegrable _ _)
    ((aux_rbr_cont M).intervalIntegrable _ _)

lemma aux_rbr_S_zero (M : Model) : M.S 0 = 0 := by
  unfold Model.S; simp

lemma aux_rbr_S_bounds (M : Model) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ M.S q ∧ M.S q ≤ q := by
  constructor
  · unfold Model.S
    exact intervalIntegral.integral_nonneg hq (fun x _ => aux_rbr_nonneg M x)
  · unfold Model.S
    have := intervalIntegral.integral_mono_on (f := M.Fbar) (g := fun _ => (1 : ℝ)) (μ := volume) hq
      ((aux_rbr_cont M).intervalIntegrable _ _) intervalIntegrable_const
      (fun x _ => aux_rbr_le_one M x)
    simpa using this

/-- Sufficiency of the first-order condition. -/
lemma aux_rbr_suff (M : Model) {w c0 q0 : ℝ} (hc0 : 0 < c0) (hq0 : w * M.Fbar q0 = c0)
    (q' : ℝ) : w * M.S q' - c0 * q' ≤ w * M.S q0 - c0 * q0 := by
  have hw : 0 < w := by
    by_contra hw
    push_neg at hw
    have := mul_nonpos_of_nonpos_of_nonneg hw (aux_rbr_nonneg M q0)
    linarith
  have hint : ∀ a b : ℝ, IntervalIntegrable M.Fbar volume a b :=
    fun a b => (aux_rbr_cont M).intervalIntegrable a b
  rcases le_total q0 q' with h | h
  · have h1 : ∫ x in q0..q', M.Fbar x ≤ ∫ x in q0..q', M.Fbar q0 :=
      intervalIntegral.integral_mono_on h (hint _ _) intervalIntegrable_const
        (fun x hx => aux_rbr_anti M hx.1)
    rw [intervalIntegral.integral_const, ← aux_rbr_sub] at h1
    simp only [smul_eq_mul] at h1
    have := mul_le_mul_of_nonneg_left h1 hw.le
    nlinarith
  · have h1 : ∫ x in q'..q0, M.Fbar q0 ≤ ∫ x in q'..q0, M.Fbar x :=
      intervalIntegral.integral_mono_on h intervalIntegrable_const (hint _ _)
        (fun x hx => aux_rbr_anti M hx.2)
    rw [intervalIntegral.integral_const, ← aux_rbr_sub] at h1
    simp only [smul_eq_mul] at h1
    have := mul_le_mul_of_nonneg_left h1 hw.le
    nlinarith

/-- Necessity of the first-order condition at an interior maximizer. -/
lemma aux_rbr_nec (M : Model) {w c0 q : ℝ} (hq : 0 < q)
    (hmax : ∀ q' : ℝ, 0 ≤ q' → w * M.S q' - c0 * q' ≤ w * M.S q - c0 * q) :
    w * M.Fbar q = c0 := by
  have hloc : IsLocalMax (fun x => w * M.S x - c0 * x) q := by
    filter_upwards [Ioi_mem_nhds hq] with y hy using hmax y (le_of_lt hy)
  have hS : HasDerivAt M.S (M.Fbar q) q := by
    unfold Model.S
    exact ((aux_rbr_cont M).integral_hasStrictDerivAt 0 q).hasDerivAt
  have hd : HasDerivAt (fun x => w * M.S x - c0 * x) (w * M.Fbar q - c0 * 1) q :=
    (hS.const_mul w).sub ((hasDerivAt_id q).const_mul c0)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- If `c0 < w`, then `0` is not a maximizer. -/
lemma aux_rbr_notzero (M : Model) {w c0 : ℝ} (hc0 : 0 < c0) (hw : c0 < w) :
    ∃ q' : ℝ, 0 ≤ q' ∧ w * M.S 0 - c0 * 0 < w * M.S q' - c0 * q' := by
  have ht : Tendsto (fun x => w * M.Fbar x) (𝓝[>] 0) (𝓝 (w * M.Fbar 0)) :=
    (((aux_rbr_cont M).tendsto 0).const_mul w).mono_left nhdsWithin_le_nhds
  rw [aux_rbr_zero, mul_one] at ht
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), c0 < w * M.Fbar x := ht (Ioi_mem_nhds hw)
  obtain ⟨ε, hε1, hε2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos : (0 : ℝ) < ε := hε2
  refine ⟨ε, hεpos.le, ?_⟩
  have h1 : ∫ x in (0 : ℝ)..ε, M.Fbar ε ≤ ∫ x in (0 : ℝ)..ε, M.Fbar x :=
    intervalIntegral.integral_mono_on hεpos.le intervalIntegrable_const
      ((aux_rbr_cont M).intervalIntegrable _ _) (fun x hx => aux_rbr_anti M hx.2)
  rw [intervalIntegral.integral_const] at h1
  simp only [smul_eq_mul, sub_zero] at h1
  have hS : ε * M.Fbar ε ≤ M.S ε := h1
  have hwpos : 0 < w := hc0.trans hw
  rw [aux_rbr_S_zero]
  have := mul_le_mul_of_nonneg_left hS hwpos.le
  nlinarith

lemma aux_rbr_rho_lt (M : Model) {Cs : ℝ} (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) : M.ρ Cs < 1 := by
  have hC' : (M.Cmin + Cs) / 2 ∈ Set.Ioo M.Cmin M.Cmax := by
    constructor <;> linarith [hCs.1, hCs.2]
  have h1 : M.ρ Cs < M.ρ ((M.Cmin + Cs) / 2) :=
    M.ρ_strictAnti hC' hCs (by linarith [hCs.1])
  have h2 := (M.ρ_mem _ hC').2
  linarith

lemma aux_rbr_cR_pos (M : Model) (Cs Cr τ : ℝ) : 0 < M.cR Cs Cr τ := by
  unfold Model.cR
  exact mul_pos M.c_pos (Real.exp_pos _)

lemma aux_rbr_br_iff (M : Model) {Cs Cr w τ : ℝ} (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (q : ℝ) :
    M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔
      (0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' →
        w * M.S q' - M.cR Cs Cr τ * q' ≤ w * M.S q - M.cR Cs Cr τ * q) := by
  set K := (1 - M.ρ Cs) * (M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1))) with hKdef
  have hK : 0 < K := by
    have := aux_rbr_rho_lt M hCs
    refine mul_pos (by linarith) (mul_pos ?_ (Real.exp_pos _))
    unfold Model.ΛR; exact Real.exp_pos _
  have hA : M.ΛR Cr τ * Real.exp (-(M.lamS * M.t1)) * M.cR Cs Cr τ =
      M.c * Real.exp (M.η Cs * M.t1) := by
    unfold Model.ΛR Model.cR
    have : Real.exp (-(M.η Cr * (M.t2 + τ))) * Real.exp (-(M.lamS * M.t1)) *
        Real.exp ((M.η Cs + M.lamS) * M.t1 + M.η Cr * (M.t2 + τ)) =
        Real.exp (M.η Cs * M.t1) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    linear_combination M.c * this
  have key : ∀ x, M.supplierProfit (M.ΛR Cr τ) Cs w x =
      K * (w * M.S x - M.cR Cs Cr τ * x) := by
    intro x
    unfold Model.supplierProfit
    rw [hKdef]
    linear_combination ((1 - M.ρ Cs) * x) * hA
  unfold Model.IsBestResponse
  simp_rw [key]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun q' hq' => le_of_mul_le_mul_left (h q' hq') hK⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun q' hq' => mul_le_mul_of_nonneg_left (h q' hq') hK.le⟩

end SupplyChainFactoring.Extension

open SupplyChainFactoring.Extension

theorem solution (M : Model) {Cs Cr w τ : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) :
    (M.cR Cs Cr τ < w → ∀ q : ℝ,
      M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ (M.InSupport q ∧ w * M.Fbar q = M.cR Cs Cr τ)) ∧
    (w ≤ M.cR Cs Cr τ → ∀ q : ℝ, M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ q = 0) := by
  have hc0 := aux_rbr_cR_pos M Cs Cr τ
  constructor
  · intro hw q
    rw [aux_rbr_br_iff M hCs]
    constructor
    · rintro ⟨h0, hmax⟩
      rcases h0.lt_or_eq with hq | hq
      · have hfoc := aux_rbr_nec M hq hmax
        refine ⟨⟨hq, aux_rbr_ltZ M ?_⟩, hfoc⟩
        by_contra hF
        push_neg at hF
        have hw0 : 0 < w := hc0.trans hw
        have := mul_le_mul_of_nonneg_left hF hw0.le
        linarith
      · subst hq
        obtain ⟨q', hq', hlt⟩ := aux_rbr_notzero M hc0 hw
        exact absurd (hmax q' hq') (not_le.2 hlt)
    · rintro ⟨⟨hq, _⟩, hfoc⟩
      exact ⟨hq.le, fun q' _ => aux_rbr_suff M hc0 hfoc q'⟩
  · intro hw q
    rw [aux_rbr_br_iff M hCs]
    constructor
    · rintro ⟨h0, hmax⟩
      by_contra hne
      have hq : 0 < q := lt_of_le_of_ne h0 (Ne.symm hne)
      have hfoc := aux_rbr_nec M hq hmax
      have hw0 : 0 < w := by
        by_contra hw0
        push_neg at hw0
        have := mul_nonpos_of_nonpos_of_nonneg hw0 (aux_rbr_nonneg M q)
        linarith
      have hlt := aux_rbr_lt_one M hq
      have := mul_lt_mul_of_pos_left hlt hw0
      linarith
    · rintro rfl
      refine ⟨le_refl 0, fun q' hq' => ?_⟩
      rw [aux_rbr_S_zero]
      obtain ⟨hS0, hS1⟩ := aux_rbr_S_bounds M hq'
      rcases le_or_gt w 0 with hw0 | hw0
      · nlinarith
      · nlinarith
