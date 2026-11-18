-- Prove2me | solution 1 for OWMR.fifo_candidate_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:03.90421+00:00
-- url     : https://prove2.me/submissions/694cb654-74f1-427c-b2b5-763093eb4fba

import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewal_doubling
import Theorems.Thm_OWMR_mirror_bounds
import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_half_window_shift
import Theorems.Thm_OWMR_tail_mirror
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Proposition 1 of the paper (the two-candidate comparison), reduced to: finiteness of the renewal
measure (footnote to (9)), the renewal-reward identity (10) for (s,S) policies, the doubling bound
of Lemma 2, the mirror bound of Lemma 4, the half-window shift (Lemma 5), the tail-mirror
inequality (Lemma 6), and the regularity of `F_i` used in Lemma 3. Lemma 3 itself (the canonical
savings) and the candidate-cost formula (15) of Lemma 4 are derived below.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- Step 3 of the proof of Proposition 1, in normalized form: `X₁ = M(b)(𝓛_half - G)`,
`X₂ = M(b)(𝓛_full - G)`, `P = β b M(b)`, `k` the planning setup cost, `r = p/h`. -/
private lemma prop1_algebra (r k P X1 X2 : ℝ) (hr : 1 ≤ r) (hk : 0 ≤ k) (hP : 0 ≤ P)
    (h1 : 40 * r * X1 ≤ k * (4 * r - 5) + 10 * (3 * r + 1) * P)
    (h2 : 5 * r * X2 ≤ -(k * r) + 5 * (r + 1) * P) : min X2 X1 ≤ P := by
  have hr0 : 0 < r := by linarith
  rcases le_or_gt r (5 / 4) with hr5 | hr5
  · refine (min_le_right _ _).trans ?_
    have e1 : k * (4 * r - 5) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith)
    have e2 : 10 * (3 * r + 1) * P ≤ 40 * r * P := by
      nlinarith [mul_nonneg (sub_nonneg.2 hr) hP]
    have e3 : (40 * r) * X1 ≤ (40 * r) * P := by linarith
    exact le_of_mul_le_mul_left e3 (by linarith)
  · have hm2 : min X2 X1 ≤ X2 := min_le_left _ _
    have hm1 : min X2 X1 ≤ X1 := min_le_right _ _
    have a1 : (4 * r - 5) * (5 * r * min X2 X1) ≤ (4 * r - 5) * (5 * r * X2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 (by linarith)) (by linarith)
    have a2 : r * (40 * r * min X2 X1) ≤ r * (40 * r * X1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm1 (by linarith)) hr0.le
    have a3 : (4 * r - 5) * (5 * r * X2) ≤ (4 * r - 5) * (-(k * r) + 5 * (r + 1) * P) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have a4 : r * (40 * r * X1) ≤ r * (k * (4 * r - 5) + 10 * (3 * r + 1) * P) :=
      mul_le_mul_of_nonneg_left h1 hr0.le
    have a5 : 0 ≤ P * (2 * r ^ 2 - 6 * r + 5) :=
      mul_nonneg hP (by nlinarith [sq_nonneg (r - 3 / 2)])
    have key : (5 * r * (12 * r - 5)) * min X2 X1 ≤ (5 * r * (12 * r - 5)) * P := by
      linarith
    exact le_of_mul_le_mul_left key (mul_pos (by linarith) (by linarith))

/-- `U[0,w) ≥ 1` for `w > 0`: the zero partial sum `D^{(0)} = 0` lies in `[0,w)`. -/
private lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

/-- A continuous function is integrable on `[a, e)` against `U` when `a ≥ 0`. -/
private lemma intOn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {a e : ℝ} (ha : 0 ≤ a) :
    IntegrableOn φ (Set.Ico a e) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (ne_top_of_le_ne_top (renewalMeasure_Ico_lt_top ρ hρ e).ne
      (measure_mono (Set.Ico_subset_Ico_left ha))) hφ.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Set.Ico_subset_Icc_self hx)

private lemma bdd_of_cont {φ : ℝ → ℝ} (hφ : Continuous φ) (c e : ℝ) :
    ∃ C, ∀ y ∈ Set.Icc c e, φ y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

private lemma setIntegral_const_sub (μ : Measure ℝ) {s : Set ℝ} (hs : μ s ≠ ∞) (G : ℝ)
    {φ : ℝ → ℝ} (hφ : IntegrableOn φ s μ) :
    ∫ x in s, (G - φ x) ∂μ = G * (μ s).toReal - ∫ x in s, φ x ∂μ := by
  rw [integral_sub (integrableOn_const hs).integrable hφ.integrable, setIntegral_const, smul_eq_mul,
    measureReal_def, mul_comm]

/-- The mirror average is the zero-setup `(s,S)` cost of the reflected warehouse-rate loss. -/
private lemma mirrorAvg_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    mirrorAvg ρ h p s S a = ssAvgCost ρ (fun y => whLoss h p (a - y)) 0 s S := by
  unfold mirrorAvg ssAvgCost ssPeriodCost
  simp only [zero_mul, zero_add]

set_option maxHeartbeats 400000 in
/-- Proposition 1 for one retailer, stated for an abstract demand law `ρ` and cost `F`. -/
private lemma core (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF0 : ∀ y, 0 ≤ F y) (hFc : Continuous F) (hFconv : ConvexOn ℝ Set.univ F)
    (K h p : ℝ) (hK : 0 < K) (hh : 0 < h) (hhp : h ≤ p)
    (hFslope : ∀ y y', y ≤ y' → F y - p * (y' - y) ≤ F y')
    (sh Sh s' S' : ℝ) (hlt : sh < Sh)
    (hopt : ssAvgCost ρ F (5 * K / 3) sh Sh = ENNReal.ofReal (F sh))
    (hle : ∀ y ∈ Set.Icc sh Sh, F y ≤ F sh)
    (hhalf : IsBestHalfWindow ρ F sh Sh s' S') :
    min (ssAvgCost ρ F K sh Sh + mirrorCost ρ h p sh Sh)
        (ssAvgCost ρ F K s' S' + mirrorCost ρ h p s' S')
      ≤ ENNReal.ofReal (F sh) + ENNReal.ofReal (h * p / (h + p) * (Sh - sh) / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le hh hhp
  obtain ⟨hs'1, hs'2, hS'1, hwidth, hbest⟩ := hhalf
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (Sh - sh) / 2 := ⟨_, rfl⟩
  have hw : Sh - sh = 2 * b := by rw [hb]; ring
  have hb0 : 0 < b := by rw [hb]; linarith
  have hwb : S' - s' = b := by rw [hwidth, hb]
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = F sh := ⟨_, rfl⟩
  rw [← hG] at hopt hle ⊢
  have hG0 : 0 ≤ G := hG ▸ hF0 sh
  have hFm : Measurable F := hFc.measurable
  -- the renewal counts `M(b)` and `M(2b)`
  have hUb : renewalMeasure ρ (Set.Ico 0 b) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ b).ne
  have hUw : renewalMeasure ρ (Set.Ico 0 (2 * b)) ≠ ∞ :=
    (renewalMeasure_Ico_lt_top ρ hρ (2 * b)).ne
  obtain ⟨Mb, hMb⟩ : ∃ M : ℝ, M = (renewalMeasure ρ (Set.Ico 0 b)).toReal := ⟨_, rfl⟩
  obtain ⟨Mw, hMw⟩ : ∃ M : ℝ, M = (renewalMeasure ρ (Set.Ico 0 (2 * b))).toReal := ⟨_, rfl⟩
  have hMb1 : 1 ≤ Mb := by
    have := ENNReal.toReal_mono hUb (one_le_renewal ρ b hb0)
    simpa [hMb] using this
  have hMw1 : 1 ≤ Mw := by
    have := ENNReal.toReal_mono hUw (one_le_renewal ρ (2 * b) (by linarith))
    simpa [hMw] using this
  have hMb0 : 0 < Mb := by linarith
  have hMw0 : 0 < Mw := by linarith
  have hdouble : Mw ≤ 2 * Mb := by
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hUb)
      (renewal_doubling ρ b hb0.le)
    rw [ENNReal.toReal_mul] at h2
    simpa [hMb, hMw] using h2
  have hbd : ∀ {a c : ℝ}, sh ≤ a → c ≤ Sh → ∃ C, ∀ y ∈ Set.Icc a c, F y ≤ C :=
    fun ha hc => ⟨G, fun y hy => hle y ⟨ha.trans hy.1, hy.2.trans hc⟩⟩
  have hcF : ∀ c : ℝ, Continuous fun x => F (c - x) := fun c =>
    hFc.comp (continuous_const.sub continuous_id)
  have hIF : ∀ c a e : ℝ, 0 ≤ a → IntegrableOn (fun x => F (c - x)) (Set.Ico a e)
      (renewalMeasure ρ) := fun c a e ha => intOn ρ hρ (hcF c) ha
  -- the occupation identity (10) for the three windows (Lemma 4, candidate cost (15))
  have hB1 := ss_renewal_reward ρ hρ F hFm hF0 (5 * K / 3) sh Sh (by linarith) hlt
    (hbd le_rfl le_rfl)
  rw [hopt, hw, ← hMw] at hB1
  have hB2 := ss_renewal_reward ρ hρ F hFm hF0 K sh Sh hK.le hlt (hbd le_rfl le_rfl)
  rw [hw, ← hMw] at hB2
  have hB3 := ss_renewal_reward ρ hρ F hFm hF0 K s' S' hK.le hs'2 (hbd hs'1 hS'1)
  rw [hwb, ← hMb] at hB3
  -- Lemma 3: the canonical savings `g(x) = G - F(Ŝ - x)` integrate to `k = 5K/3`
  have hIf0 : 0 ≤ ∫ x in Set.Ico 0 (2 * b), F (Sh - x) ∂renewalMeasure ρ :=
    setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
  have hfull : 5 * K / 3 + ∫ x in Set.Ico 0 (2 * b), F (Sh - x) ∂renewalMeasure ρ = G * Mw := by
    rw [ENNReal.ofReal_eq_ofReal_iff hG0 (div_nonneg (by linarith) hMw0.le)] at hB1
    rw [hB1, div_mul_cancel₀ _ hMw0.ne']
  have hgfull : ∫ x in Set.Ico 0 (2 * b), (G - F (Sh - x)) ∂renewalMeasure ρ = 5 * K / 3 := by
    rw [setIntegral_const_sub _ hUw G (hIF Sh 0 (2 * b) le_rfl), ← hMw]
    linarith [hfull]
  have hgshift : ∀ υ : ℝ, ∫ x in Set.Ico 0 b, (G - F (Sh - (υ + x))) ∂renewalMeasure ρ
      = G * Mb - ∫ x in Set.Ico 0 b, F (Sh - υ - x) ∂renewalMeasure ρ := by
    intro υ
    simp only [sub_add_eq_sub_sub]
    rw [setIntegral_const_sub _ hUb G (hIF (Sh - υ) 0 b le_rfl), ← hMb]
  have hgc : ContinuousOn (fun x => G - F (Sh - x)) (Set.Icc 0 (2 * b)) :=
    (continuous_const.sub (hcF Sh)).continuousOn
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (2 * b), 0 ≤ G - F (Sh - x) := fun x hx => by
    have := hle (Sh - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    linarith
  have hgconc : ConcaveOn ℝ (Set.Icc 0 (2 * b)) (fun x => G - F (Sh - x)) := by
    refine ⟨convex_Icc 0 (2 * b), fun x _ y _ a c ha hc hac => ?_⟩
    have hcv := hFconv.2 (Set.mem_univ (Sh - x)) (Set.mem_univ (Sh - y)) ha hc hac
    simp only [smul_eq_mul] at hcv ⊢
    have e : a * (Sh - x) + c * (Sh - y) = Sh - (a * x + c * y) := by
      linear_combination Sh * hac
    rw [e] at hcv
    have e2 : a * G + c * G = G := by rw [← add_mul, hac, one_mul]
    linarith
  -- the best half window retains the most savings among the shifted half windows
  have hbestυ : ∀ υ ∈ Set.Icc (0 : ℝ) b, ∫ x in Set.Ico 0 b, F (S' - x) ∂renewalMeasure ρ
      ≤ ∫ x in Set.Ico 0 b, F (Sh - υ - x) ∂renewalMeasure ρ := by
    intro υ hυ
    have h1 := hbest (Sh - υ - b) (Sh - υ) (by linarith [hυ.2]) (by linarith) (by linarith [hυ.1])
      (by rw [hb]; ring)
    rw [ss_renewal_reward ρ hρ F hFm hF0 0 s' S' le_rfl hs'2 (hbd hs'1 hS'1),
      ss_renewal_reward ρ hρ F hFm hF0 0 (Sh - υ - b) (Sh - υ) le_rfl (by linarith)
        (hbd (by linarith [hυ.2]) (by linarith [hυ.1])), hwb,
      show Sh - υ - (Sh - υ - b) = b by ring, zero_add, zero_add, ← hMb] at h1
    rw [ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _) hMb0.le)] at h1
    exact (div_le_div_iff_of_pos_right hMb0).1 h1
  obtain ⟨Ψ', hΨ'⟩ : ∃ I : ℝ, I = ∫ x in Set.Ico 0 b, F (S' - x) ∂renewalMeasure ρ := ⟨_, rfl⟩
  have hΨ'0 : 0 ≤ Ψ' := hΨ' ▸ setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
  -- Lemma 5 (half-window shift): `k ≤ 2 Φ*`
  have hshift : 5 * K / 3 ≤ 2 * (G * Mb - Ψ') := by
    obtain ⟨υ, hυ, hsh⟩ := half_window_shift ρ hρ b hb0 (fun x => G - F (Sh - x)) hgc hg0 hgconc
    have h1 : ∫ x in Set.Ico 0 (2 * b), (G - F (Sh - x)) ∂renewalMeasure ρ
        ≤ 2 * ∫ x in Set.Ico 0 b, (G - F (Sh - (υ + x))) ∂renewalMeasure ρ := hsh
    rw [hgfull, hgshift υ] at h1
    have := hbestυ υ hυ
    rw [← hΨ'] at this
    linarith
  -- splitting the full-cycle savings at `b`: `k ≤ Φ* + p 𝒯_b`
  have hsplit : 5 * K / 3 ≤ (G * Mb - Ψ') + p * ∫ x in Set.Ico b (2 * b), (2 * b - x)
      ∂renewalMeasure ρ := by
    have hgint : ∀ a e : ℝ, 0 ≤ a → IntegrableOn (fun x => G - F (Sh - x)) (Set.Ico a e)
        (renewalMeasure ρ) := fun a e ha => intOn ρ hρ (continuous_const.sub (hcF Sh)) ha
    have hunion : ∫ x in Set.Ico 0 (2 * b), (G - F (Sh - x)) ∂renewalMeasure ρ
        = (∫ x in Set.Ico 0 b, (G - F (Sh - x)) ∂renewalMeasure ρ)
          + ∫ x in Set.Ico b (2 * b), (G - F (Sh - x)) ∂renewalMeasure ρ := by
      rw [← setIntegral_union Set.Ico_disjoint_Ico_same measurableSet_Ico (hgint 0 b le_rfl)
        (hgint b (2 * b) hb0.le), Set.Ico_union_Ico_eq_Ico hb0.le (by linarith)]
    have hfirst : ∫ x in Set.Ico 0 b, (G - F (Sh - x)) ∂renewalMeasure ρ ≤ G * Mb - Ψ' := by
      rw [setIntegral_const_sub _ hUb G (hIF Sh 0 b le_rfl), ← hMb, hΨ']
      have := hbestυ 0 ⟨le_rfl, hb0.le⟩
      simp only [sub_zero] at this
      linarith
    have htail : ∫ x in Set.Ico b (2 * b), (G - F (Sh - x)) ∂renewalMeasure ρ
        ≤ p * ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂renewalMeasure ρ := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hgint b (2 * b) hb0.le) (intOn ρ hρ (by fun_prop) hb0.le)
        measurableSet_Ico fun x hx => ?_
      have := hFslope sh (Sh - x) (by linarith [hx.2])
      have e : Sh - x - sh = 2 * b - x := by linarith
      rw [e] at this
      linarith
    linarith [hgfull]
  -- the mirror cost of the half window, as a lower bound for every fixed center (Lemma 4)
  have hφc : ∀ a : ℝ, Continuous fun y => whLoss h p (a - y) := fun a => by
    unfold whLoss; fun_prop
  have hφ0 : ∀ a y : ℝ, 0 ≤ whLoss h p (a - y) := fun a y =>
    add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp0.le (le_max_right _ _))
  have hmir : ∀ s S a : ℝ, s < S → mirrorAvg ρ h p s S a = ENNReal.ofReal
      ((∫ x in Set.Ico 0 (S - s), whLoss h p (a - (S - x)) ∂renewalMeasure ρ)
        / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal) := by
    intro s S a hsS
    rw [mirrorAvg_eq, ss_renewal_reward ρ hρ _ (hφc a).measurable (hφ0 a) 0 s S le_rfl hsS
      (bdd_of_cont (hφc a) s S), zero_add]
  have hmir_half : ∀ z : ℝ, mirrorCost ρ h p s' S' ≤ ENNReal.ofReal
      ((∫ x in Set.Ico 0 b, (p * max (z - x) 0 + h * max (x - z) 0) ∂renewalMeasure ρ) / Mb) := by
    intro z
    refine (iInf_le (fun a => mirrorAvg ρ h p s' S' a) (S' - z)).trans (le_of_eq ?_)
    rw [hmir s' S' (S' - z) hs'2, hwb, ← hMb]
    congr 2
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    simp only [whLoss]
    rw [show S' - z - (S' - x) = x - z by ring, show -(x - z) = z - x by ring]
    ring
  have hmir_fin : mirrorCost ρ h p s' S' ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmir_half 0)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (mirrorCost ρ h p s' S').toReal := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ ENNReal.toReal_nonneg
  have hBV : ∀ z : ℝ, B * Mb
      ≤ ∫ x in Set.Ico 0 b, (p * max (z - x) 0 + h * max (x - z) 0) ∂renewalMeasure ρ := by
    intro z
    have hV0 : 0 ≤ ∫ x in Set.Ico 0 b, (p * max (z - x) 0 + h * max (x - z) 0)
        ∂renewalMeasure ρ := setIntegral_nonneg measurableSet_Ico fun x _ =>
      add_nonneg (mul_nonneg hp0.le (le_max_right _ _)) (mul_nonneg hh.le (le_max_right _ _))
    have := ENNReal.toReal_le_of_le_ofReal (div_nonneg hV0 hMb0.le) (hmir_half z)
    rw [← hB] at this
    exact (le_div_iff₀ hMb0).1 this
  -- Lemma 6 (tail-mirror inequality)
  have htm := tail_mirror ρ hρ h p b hh hp0 hb0 B (by intro z; rw [← hMb]; exact hBV z)
  rw [← hMb] at htm
  -- Lemma 4 (mirror bound of the full window)
  have hmf : mirrorCost ρ h p sh Sh ≤ ENNReal.ofReal (h * b) := by
    have := (mirror_bounds ρ hρ h p sh Sh hh hp0 hlt).2
    rwa [hw, show h * (2 * b) / 2 = h * b by ring] at this
  -- names for the remaining real quantities
  obtain ⟨If, hIf⟩ : ∃ I : ℝ, I = ∫ x in Set.Ico 0 (2 * b), F (Sh - x) ∂renewalMeasure ρ :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ I : ℝ, I = ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂renewalMeasure ρ := ⟨_, rfl⟩
  rw [← hIf] at hfull hB2 hIf0
  rw [← hΨ'] at hB3
  rw [← hT] at hsplit htm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = p / h := ⟨_, rfl⟩
  rw [← hr] at htm
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hh]; linarith
  have hrh : r * h = p := by rw [hr, div_mul_cancel₀ _ hh.ne']
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = h * p / (h + p) * b * Mb := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hPr : (r + 1) * P = p * b * Mb := by
    rw [hP, hr]
    field_simp
    ring
  have htm' : p * T + 4 * r * Mb * B ≤ (3 * r + 1) * P := by rw [hP]; linarith [htm]
  -- the two candidate costs
  obtain ⟨Af, hAf⟩ : ∃ A : ℝ, A = (K + If) / Mw := ⟨_, rfl⟩
  obtain ⟨Ah, hAh⟩ : ∃ A : ℝ, A = (K + Ψ') / Mb := ⟨_, rfl⟩
  have hAfM : Af * Mw = K + If := by rw [hAf, div_mul_cancel₀ _ hMw0.ne']
  have hAhM : Ah * Mb = K + Ψ' := by rw [hAh, div_mul_cancel₀ _ hMb0.ne']
  have hAf0 : 0 ≤ Af := by rw [hAf]; exact div_nonneg (by linarith) hMw0.le
  have hAh0 : 0 ≤ Ah := by rw [hAh]; exact div_nonneg (by linarith) hMb0.le
  -- full-window bound (20), normalized
  have hX2 : Mb * (Af + h * b - G) ≤ -(K / 3) + h * b * Mb := by
    have e : (Af - G) * Mw = -(2 * K / 3) := by linear_combination hAfM + hfull
    have hneg : Af - G ≤ 0 := by
      by_contra hcon
      have := mul_pos (lt_of_not_ge hcon) hMw0
      linarith
    have := mul_nonpos_of_nonpos_of_nonneg hneg (by linarith : (0 : ℝ) ≤ 2 * Mb - Mw)
    linarith
  have h2 : 5 * r * (Mb * (Af + h * b - G)) ≤ -(5 * K / 3 * r) + 5 * (r + 1) * P := by
    have := mul_le_mul_of_nonneg_left hX2 (by linarith : (0 : ℝ) ≤ 5 * r)
    have e1 : r * (h * b * Mb) = p * b * Mb := by rw [← hrh]; ring
    linarith [hPr]
  -- half-window bound (19), normalized
  have hX1 : Mb * (Ah + B - G) = K - (G * Mb - Ψ') + Mb * B := by linarith [hAhM]
  have h1 : 40 * r * (Mb * (Ah + B - G)) ≤ 5 * K / 3 * (4 * r - 5) + 10 * (3 * r + 1) * P := by
    rw [hX1]
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * r - 1)
      (by linarith : (0 : ℝ) ≤ 2 * (G * Mb - Ψ') - 5 * K / 3)]
  have hmin := prop1_algebra r (5 * K / 3) P (Mb * (Ah + B - G)) (Mb * (Af + h * b - G)) hr1
    (by linarith) hP0 h1 h2
  have hβb : h * p / (h + p) * (Sh - sh) / 2 = h * p / (h + p) * b := by rw [hw]; ring
  have hβ0 : 0 ≤ h * p / (h + p) * b := by positivity
  rw [hβb]
  rcases min_le_iff.1 hmin with hc | hc
  · have hL : Af + h * b ≤ G + h * p / (h + p) * b := by
      have h3 : Mb * (Af + h * b - G) ≤ Mb * (h * p / (h + p) * b) := by rw [hP] at hc; linarith
      have := le_of_mul_le_mul_left h3 hMb0
      linarith
    calc min (ssAvgCost ρ F K sh Sh + mirrorCost ρ h p sh Sh)
          (ssAvgCost ρ F K s' S' + mirrorCost ρ h p s' S')
        ≤ ssAvgCost ρ F K sh Sh + mirrorCost ρ h p sh Sh := min_le_left _ _
      _ ≤ ENNReal.ofReal Af + ENNReal.ofReal (h * b) := by
          rw [hB2, ← hAf]
          exact add_le_add le_rfl hmf
      _ = ENNReal.ofReal (Af + h * b) := (ENNReal.ofReal_add hAf0 (by positivity)).symm
      _ ≤ ENNReal.ofReal (G + h * p / (h + p) * b) := ENNReal.ofReal_le_ofReal hL
      _ = ENNReal.ofReal G + ENNReal.ofReal (h * p / (h + p) * b) := ENNReal.ofReal_add hG0 hβ0
  · have hL : Ah + B ≤ G + h * p / (h + p) * b := by
      have h3 : Mb * (Ah + B - G) ≤ Mb * (h * p / (h + p) * b) := by rw [hP] at hc; linarith
      have := le_of_mul_le_mul_left h3 hMb0
      linarith
    calc min (ssAvgCost ρ F K sh Sh + mirrorCost ρ h p sh Sh)
          (ssAvgCost ρ F K s' S' + mirrorCost ρ h p s' S')
        ≤ ssAvgCost ρ F K s' S' + mirrorCost ρ h p s' S' := min_le_right _ _
      _ = ENNReal.ofReal Ah + ENNReal.ofReal B := by
          rw [hB3, ← hAh, hB, ENNReal.ofReal_toReal hmir_fin]
      _ = ENNReal.ofReal (Ah + B) := (ENNReal.ofReal_add hAh0 hB0).symm
      _ ≤ ENNReal.ofReal (G + h * p / (h + p) * b) := ENNReal.ofReal_le_ofReal hL
      _ = ENNReal.ofReal G + ENNReal.ofReal (h * p / (h + p) * b) := ENNReal.ofReal_add hG0 hβ0

theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (hH : N.h ≤ N.H i) (hp : N.h ≤ N.p) (hK : 0 < N.K i) (sh Sh s' S' : ℝ)
    (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) (5 * N.K i / 3) sh Sh)
    (hhalf : IsBestHalfWindow (N.marginal i) (N.F i) sh Sh s' S') :
    min (N.augCost i sh Sh) (N.augCost i s' S')
      ≤ N.J i (5 * N.K i / 3) + ENNReal.ofReal (N.h * N.p / (N.h + N.p) * (Sh - sh) / 2) := by
  have hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) := by
    rw [Network.marginal, lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  obtain ⟨hF0, hFconv, hFlip, hFslope⟩ := F_properties N hN i
  have hFc : Continuous (N.F i) := by
    have hL : LipschitzWith (Real.toNNReal (N.H i + N.p)) (N.F i) := by
      refine LipschitzWith.of_dist_le_mul fun y y' => ?_
      rw [Real.dist_eq, Real.dist_eq,
        Real.coe_toNNReal _ (by linarith [hN.H_pos i, hN.p_pos])]
      exact hFlip y y'
    exact hL.continuous
  obtain ⟨hlt, hopt, hGeq, -, hGle⟩ := hcan
  have hJ : N.J i (5 * N.K i / 3) = ENNReal.ofReal (N.F i sh) := hGeq.symm
  have hle : ∀ y ∈ Set.Icc sh Sh, N.F i y ≤ N.F i sh := fun y hy =>
    (ENNReal.ofReal_le_ofReal_iff (hF0 sh)).1 ((hGle y hy).trans_eq hGeq.symm)
  rw [hJ]
  exact core (N.marginal i) hρ (N.F i) hF0 hFc hFconv (N.K i) N.h N.p hK hN.h_pos hp hFslope
    sh Sh s' S' hlt (hopt.trans hGeq.symm) hle hhalf
