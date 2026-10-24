-- Prove2me | solution 1 for SuspensionContract.ControlBand.proposition_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:29:08.331245+00:00
-- url     : https://prove2.me/submissions/70746816-c6b9-416e-a037-185b902b723c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction
import Theorems.Thm_SuspensionContract_ControlBand_EC3_9_construction
import Theorems.Thm_SuspensionContract_ControlBand_EC3_10_case1_AI
import Theorems.Thm_SuspensionContract_ControlBand_lemma_EC_12
import Theorems.Thm_SuspensionContract_ControlBand_lemma_EC_13

open SuspensionContract.ControlBand

/-- Derivative of the suspension-state solution `V_c(w) = v̲ + w + c w^{r/ρ}` at `w > 0`. -/
theorem cb4_hasDerivAt_Vc (P : Params) (c w : ℝ) (hw : 0 < w) :
    HasDerivAt (P.Vc c) (1 + c * ((P.r / P.ρ) * w ^ (P.r / P.ρ - 1))) w := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (P.r / P.ρ)) ((P.r / P.ρ) * w ^ (P.r / P.ρ - 1)) w :=
    Real.hasDerivAt_rpow_const (Or.inl hw.ne')
  have h2 : HasDerivAt (fun x : ℝ => P.vlow + x + c * x ^ (P.r / P.ρ))
      (1 + c * ((P.r / P.ρ) * w ^ (P.r / P.ρ - 1))) w :=
    ((hasDerivAt_id' w).const_add P.vlow).add (h1.const_mul c)
  exact h2

/-- A function whose derivative within `ℝ₊` at `x > 0` is nonzero is differentiable at `x`,
and that derivative is the two-sided one. -/
theorem cb4_diff_of_d1_ne (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (h : d1 f x ≠ 0) :
    DifferentiableAt ℝ f x ∧ d1 f x = deriv f x := by
  have hmem : Set.Ici (0:ℝ) ∈ nhds x := Ici_mem_nhds hx
  have hdw : DifferentiableWithinAt ℝ f (Set.Ici 0) x := by
    by_contra hnd
    exact h (derivWithin_zero_of_not_differentiableWithinAt hnd)
  exact ⟨hdw.differentiableAt hmem, derivWithin_of_mem_nhds hmem⟩

theorem solution (P : Params) (hP : P.Standing) (h3 : P.Condition3) :
    ∃ c wB thHi thLo : ℝ, P.Prop6Params c wB thHi thLo ∧
      P.OptCond (P.VI46 c wB thLo) (P.V046 c wB thHi) := by
  obtain ⟨th, hcase, hψ, h6⟩ := EC3_9_construction P hP h3
  refine ⟨P.Cof th, P.wtil th, P.thetaBar th, th, h6, ?_⟩
  obtain ⟨hc, hlo, hlohi, hhiwB, hC1, hC2, h42, h43, h44, h45, h45b, hwchk⟩ := h6
  obtain ⟨⟨hμl, hμ⟩, ⟨hb, hbc⟩, hK, ⟨hr, hrρ⟩, hA1⟩ := id hP
  set c := P.Cof th with hcdef
  set wB := P.wtil th with hwBdef
  set hi := P.thetaBar th with hhidef
  have hρ : 0 < P.ρ := lt_of_lt_of_le hr hrρ
  have ha : P.r / P.ρ ≠ 0 := (div_pos hr hρ).ne'
  have hΔ : 0 < P.Δμ := by unfold Params.Δμ; linarith
  have hβ : 0 < P.β := div_pos hb hΔ
  have hwbar : 0 < P.wbar := by
    unfold Params.wbar; exact div_pos (mul_pos hβ (by linarith)) hρ
  have hdVc : ∀ x, 0 < x → deriv (P.Vc c) x = 1 + c * ((P.r / P.ρ) * x ^ (P.r / P.ρ - 1)) :=
    fun x hx => (cb4_hasDerivAt_Vc P c x hx).deriv
  have hdVcpos : ∀ x, 0 < x → 0 < deriv (P.Vc c) x := by
    intro x hx; rw [hdVc x hx]
    have : 0 < x ^ (P.r / P.ρ - 1) := Real.rpow_pos_of_pos hx _
    have : 0 < P.r / P.ρ := div_pos hr hρ
    positivity
  -- the suspension-state solution V_c has A∅ V_c = 0 on (0, ∞)
  have hVc0 : P.Vc c 0 = P.vlow := by
    simp [Params.Vc, Real.zero_rpow ha]
  have hA0 : ∀ w, 0 < w → w < hi → P.A0 (P.V046 c wB hi) w = 0 := by
    intro w hw hwhi
    have heq : P.V046 c wB hi =ᶠ[nhds w] P.Vc c := by
      filter_upwards [Iio_mem_nhds hwhi] with x hx
      simp [Params.V046, show x < hi from hx]
    have hd := cb4_hasDerivAt_Vc P c w hw
    have hdw : derivWithin (P.V046 c wB hi) (Set.Iic w) w
        = 1 + c * ((P.r / P.ρ) * w ^ (P.r / P.ρ - 1)) := by
      rw [Filter.EventuallyEq.derivWithin_eq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds]
      exact (hd.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Iic w)
    have hval : P.V046 c wB hi w = P.Vc c w := heq.eq_of_nhds
    simp only [Params.A0, hdw, hval, Params.Vc, Params.vlow]
    have hpow : w * w ^ (P.r / P.ρ - 1) = w ^ (P.r / P.ρ) := by
      rw [Real.rpow_sub_one hw.ne']; field_simp
    have : P.ρ * w * (1 + c * (P.r / P.ρ * w ^ (P.r / P.ρ - 1)))
        = P.ρ * w + P.r * c * w ^ (P.r / P.ρ) := by
      rw [← hpow]; field_simp
    rw [this]; field_simp; ring
  ------------------------------------------------------------------
  -- Case 1, (21) on the band [ϑ̲, ϑ̄): Φ = 𝒱_ŵ − V_c increases from 0 to K
  have hdiff : ∀ x, 0 < x → d1 (P.calV wB) x ≠ 0 →
      DifferentiableAt ℝ (P.calV wB) x ∧ d1 (P.calV wB) x = deriv (P.calV wB) x :=
    fun x hx h => cb4_diff_of_d1_ne _ x hx h
  have hhi0 : 0 < hi := by linarith
  have hwB0 : 0 < wB := by linarith
  have hinner : ∀ x ∈ Set.Ioo th hi, deriv (P.Vc c) x < d1 (P.calV wB) x := by
    intro x hx
    by_contra hle
    push_neg at hle
    have hmem : x ∈ {w | th < w ∧
        d1 (P.calV (P.wtil th)) w ≤ 1 + P.Cof th * (P.r / P.ρ) * w ^ (P.r / P.ρ - 1)} := by
      refine ⟨hx.1, ?_⟩
      have := hdVc x (by linarith [hx.1])
      rw [this] at hle; rw [← hwBdef, ← hcdef]; linarith
    have : hi ≤ x := csInf_le ⟨th, fun y hy => hy.1.le⟩ hmem
    linarith [hx.2]
  have hdiffAt : ∀ x ∈ Set.Icc th hi, DifferentiableAt ℝ (P.calV wB) x ∧
      d1 (P.calV wB) x = deriv (P.calV wB) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    apply hdiff x hx0
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [h43]; exact (hdVcpos _ hx0).ne'
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h', h45]; exact (hdVcpos _ hhi0).ne'
    · exact (lt_trans (hdVcpos x hx0) (hinner x ⟨h, h'⟩)).ne'
  set Φ : ℝ → ℝ := fun x => P.calV wB x - P.Vc c x with hΦ
  have hΦmono : StrictMonoOn Φ (Set.Icc th hi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc th hi)
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      exact ((hdiffAt x hx).1.sub (cb4_hasDerivAt_Vc P c x hx0).differentiableAt).continuousAt
        |>.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hdA := hdiffAt x ⟨hx.1.le, hx.2.le⟩
      have : deriv Φ x = deriv (P.calV wB) x - deriv (P.Vc c) x :=
        deriv_sub hdA.1 (cb4_hasDerivAt_Vc P c x hx0).differentiableAt
      rw [this, ← hdA.2]
      linarith [hinner x hx]
  have hΦth : Φ th = 0 := by simp [hΦ, h42]
  have hΦhi : Φ hi = P.K := by simp [hΦ, h44]
  ------------------------------------------------------------------
  -- Case 3: existence of the delay-ODE solution behind 𝒱_ŵ
  have hex : ∃ V, P.SolvesDDE wB V := by
    by_contra hne
    have hVt : P.Vt wB = fun _ => 0 := by unfold Params.Vt; rw [dif_neg hne]
    have hcal : P.calV wB = fun _ => 0 := by
      funext x; unfold Params.calV; rw [hVt]; simp [d1]
    have := h45b; rw [← h45, hcal] at this; simp [d1] at this; linarith
  have hV : P.SolvesDDE wB (P.Vt wB) := by
    unfold Params.Vt; rw [dif_pos hex]; exact Classical.choose_spec hex
  obtain ⟨hVc1, hODE, hVbd⟩ := hV
  have hcalbig : ∀ x, hi < x → P.calV wB x = P.Vt wB (min x wB) := by
    intro x hx; unfold Params.calV; rw [if_neg (by linarith)]
  have hVIbig : ∀ x, hi < x → P.VI46 c wB th x = P.Vt wB (min x wB) := by
    intro x hx; unfold Params.VI46; rw [if_neg (by linarith), hcalbig x hx]
  have hV0big : ∀ x, hi ≤ x → P.V046 c wB hi x = P.VI46 c wB th x - P.K := by
    intro x hx; unfold Params.V046 Params.VI46; rw [if_neg (by linarith), if_neg (by linarith)]
  set Vb := P.VbarFn wB with hVbdef
  have hVI_ge : ∀ x, wB ≤ x → P.VI46 c wB th x = Vb := by
    intro x hx; rw [hVIbig x (by linarith), min_eq_right hx]; exact hVbd wB le_rfl
  -- left derivative of V_I is the derivative of V_ŵ within [0, ŵ] at ŵ, and 0 beyond
  set D := derivWithin (P.Vt wB) (Set.Icc 0 wB) wB with hDdef
  have hODEw := hODE wB ⟨hwB0.le, le_rfl⟩
  rw [min_eq_right (by linarith : wB ≤ wB + P.β)] at hODEw
  have hVwB : P.Vt wB wB = Vb := hVbd wB le_rfl
  have hwBlt : wB < P.wbar := by
    rcases hcase with ⟨h1, -, -⟩ | ⟨h2, -, -⟩
    · have hw := hC1 h1
      have : P.what < P.wbar := by
        unfold Params.what
        by_cases hne : ({w | 0 ≤ w ∧ w < P.wbar ∧ P.calV w 0 = P.vlow} : Set ℝ).Nonempty
        · obtain ⟨x, hx⟩ := hne
          exact lt_of_le_of_lt (csInf_le ⟨0, fun y hy => hy.1⟩ hx) hx.2.1
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]; exact hwbar
      linarith
    · exact hC2 h2
  have hD0 : D = 0 := by
    have hr' : P.r * Vb = P.μ * P.R - P.c - (P.ρ - P.r) * wB := by
      rw [hVbdef]; unfold Params.VbarFn; field_simp
    rw [hVwB] at hODEw
    have : P.ρ * (P.wbar - wB) * D = 0 := by linarith
    have hne : P.ρ * (P.wbar - wB) ≠ 0 := mul_ne_zero hρ.ne' (by linarith)
    exact (mul_eq_zero.mp this).resolve_left hne
  have hLD : ∀ w, wB ≤ w → derivWithin (P.VI46 c wB th) (Set.Iic w) w = 0 := by
    intro w hw
    rcases eq_or_lt_of_le hw with h | h
    · subst h
      have heq : P.VI46 c wB th =ᶠ[nhdsWithin wB (Set.Iic wB)] P.Vt wB := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show hi < wB from hhiwB)),
          self_mem_nhdsWithin] with x hx hx'
        rw [hVIbig x hx, min_eq_left hx']
      rw [Filter.EventuallyEq.derivWithin_eq heq (by rw [hVIbig wB hhiwB, min_self])]
      rw [derivWithin_congr_set (show Set.Iic wB =ᶠ[nhds wB] Set.Icc 0 wB from ?_)]
      · exact hD0
      · filter_upwards [Ioi_mem_nhds hwB0] with x hx
        simp only [Set.mem_Iic, Set.mem_Icc, eq_iff_iff]
        exact ⟨fun h => ⟨hx.le, h⟩, fun h => h.2⟩
    · have heq : P.VI46 c wB th =ᶠ[nhds w] fun _ => Vb := by
        filter_upwards [Ioi_mem_nhds h] with x hx
        exact hVI_ge x hx.le
      rw [Filter.EventuallyEq.derivWithin_eq (heq.filter_mono nhdsWithin_le_nhds)
        heq.eq_of_nhds]
      simp
  have hLD0 : ∀ w, wB ≤ w → derivWithin (P.V046 c wB hi) (Set.Iic w) w = 0 := by
    intro w hw
    have heq : P.V046 c wB hi =ᶠ[nhds w] fun x => P.VI46 c wB th x - P.K := by
      filter_upwards [Ioi_mem_nhds (show hi < w by linarith)] with x hx
      exact hV0big x hx.le
    rw [Filter.EventuallyEq.derivWithin_eq (heq.filter_mono nhdsWithin_le_nhds)
      heq.eq_of_nhds, derivWithin_sub_const, hLD w hw]
  -- bound on K: r K ≤ RΔμ − c
  have hKb : P.r * P.K ≤ P.R * P.Δμ - P.c := by
    rcases hcase with ⟨h1, hK1, -⟩ | ⟨h2, hK2, -⟩
    · have hwh : 0 ≤ P.what := Real.sInf_nonneg fun x hx => hx.1
      have : P.Kbar1 ≤ P.VbarFn P.what - P.vlow := by
        unfold Params.Kbar1 at hK1 ⊢
        by_cases hne : ({K | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧
            ∃ θ m, P.TangentPair K θ m ∧ m < 1} : Set ℝ).Nonempty
        · obtain ⟨x, hx⟩ := hne
          exact le_trans (csInf_le ⟨0, fun y hy => hy.1.le⟩ hx) hx.2.1
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty] at hK1; linarith
      have h' : P.r * (P.VbarFn P.what - P.vlow)
          = P.R * P.Δμ - P.c - (P.ρ - P.r) * P.what := by
        unfold Params.VbarFn Params.vlow Params.Δμ; field_simp; ring
      nlinarith
    · obtain ⟨hμρ, hRh⟩ := h2
      unfold Params.Klow at hK2
      split_ifs at hK2 with hcnd
      · have ha' : 0 < P.ρ - P.r - P.μ := by linarith
        have hd' : 0 < P.ρ - P.r := by linarith
        have hμ0 : 0 < P.μ := by linarith
        have hX : (P.R * P.Δμ - P.c) * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r))
            - ((P.ρ - P.μ) / P.ρ) * P.β
            = (P.R - P.Rhat) * P.Δμ * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r)) := by
          unfold Params.Rhat Params.β
          field_simp
          ring
        rw [hX] at hK2
        have hX0 : 0 ≤ (P.R - P.Rhat) * P.Δμ * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r)) := by
          apply div_nonneg
          · exact mul_nonneg (mul_nonneg (by linarith) hΔ.le) ha'.le
          · positivity
        have hT : 0 ≤ (P.μ * P.ρ / (P.ρ - P.r - P.μ))
            * ((P.R - P.Rhat) * P.Δμ * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r)))
              ^ (1 - P.r / P.ρ) * P.wbar ^ (P.r / P.ρ) := by
          have := Real.rpow_nonneg hX0 (1 - P.r / P.ρ)
          have := Real.rpow_nonneg hwbar.le (P.r / P.ρ)
          have : 0 ≤ P.μ * P.ρ / (P.ρ - P.r - P.μ) := by positivity
          positivity
        have hβμ : 0 ≤ P.β * P.μ := by positivity
        have : P.r * P.K < P.r * ((1 / P.r) * (P.R * P.Δμ - P.c - P.β * P.μ
            - (P.μ * P.ρ / (P.ρ - P.r - P.μ))
              * ((P.R - P.Rhat) * P.Δμ * (P.ρ - P.r - P.μ) / (P.μ * (P.ρ - P.r)))
                ^ (1 - P.r / P.ρ) * P.wbar ^ (P.r / P.ρ))) :=
          mul_lt_mul_of_pos_left hK2 hr
        rw [← mul_assoc, mul_one_div_cancel hr.ne', one_mul] at this
        linarith
      · linarith
  have hcase3 : ∀ w, wB ≤ w →
      0 ≤ P.AI (P.VI46 c wB th) w ∧ 0 ≤ P.A0 (P.V046 c wB hi) w := by
    intro w hw
    have hr' : P.r * Vb = P.μ * P.R - P.c - (P.ρ - P.r) * wB := by
      rw [hVbdef]; unfold Params.VbarFn; field_simp
    constructor
    · unfold Params.AI
      rw [hLD w hw, hVI_ge w hw, hVI_ge (w + P.β) (by linarith)]
      have e : (P.μ + P.r) * Vb - P.μ * Vb + P.ρ * (P.wbar - w) * 0 - (P.μ * P.R - P.c)
          + (P.ρ - P.r) * w = (P.ρ - P.r) * (w - wB) := by linear_combination hr'
      rw [e]; exact mul_nonneg (by linarith) (by linarith)
    · unfold Params.A0
      rw [hLD0 w hw, hV0big w (by linarith), hVI_ge w hw]
      unfold Params.Δμ at hKb
      have e : P.r * (Vb - P.K) - P.ρ * w * 0 + (P.ρ - P.r) * w - P.R * P.μlow
          = (P.R * (P.μ - P.μlow) - P.c - P.r * P.K) + (P.ρ - P.r) * (w - wB) := by
        linear_combination hr'
      rw [e]
      have : 0 ≤ (P.ρ - P.r) * (w - wB) := mul_nonneg (by linarith) (by linarith)
      linarith
  ------------------------------------------------------------------
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    constructor
    · rcases lt_or_ge w th with h | h
      · exact lemma_EC_13 P hP th hcase hψ w ⟨hw, h⟩
      rcases lt_or_ge w wB with h' | h'
      · exact EC3_10_case1_AI P hP th hcase hψ w ⟨h, h'⟩
      · exact (hcase3 w h').1
    · rcases lt_or_ge w hi with h | h
      · exact (hA0 w hw h).symm.le
      rcases lt_or_ge w wB with h' | h'
      · exact lemma_EC_12 P hP th hcase hψ w ⟨h, h'⟩
      · exact (hcase3 w h').2
  · intro w hw
    rcases lt_or_ge w th with h | h
    · have h2 : w < hi := by linarith
      simp [Params.VI46, Params.V046, h, h2, hK.le]
    rcases lt_or_ge w hi with h' | h'
    · have e1 : P.VI46 c wB th w - P.V046 c wB hi w = Φ w := by
        simp [Params.VI46, Params.V046, hΦ, not_lt.mpr h, h']
      rw [e1]
      have hm := hΦmono.monotoneOn
      constructor
      · rw [← hΦth]; exact hm ⟨le_rfl, hlohi.le⟩ ⟨h, h'.le⟩ h
      · rw [← hΦhi]; exact hm ⟨h, h'.le⟩ ⟨hlohi.le, le_rfl⟩ h'.le
    · rw [hV0big w h']; simp [hK.le]
  · simp [Params.VI46, hlo, hVc0]
  · simp [Params.V046, show (0:ℝ) < hi by linarith, hVc0]
