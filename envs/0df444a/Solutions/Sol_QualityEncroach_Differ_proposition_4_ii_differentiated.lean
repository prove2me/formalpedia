-- Prove2me | solution 1 for QualityEncroach.Differ.proposition_4_ii_differentiated
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:25:59.078918+00:00
-- url     : https://prove2.me/submissions/ae1ca27d-ba8a-47de-b599-8f3c56ab3051

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

open QualityEncroach.Differ

/-!
Proof of `QualityEncroach.Differ.proposition_4_ii_differentiated`.

Outline:
1. For `0 < t ≤ 1`, the manufacturer's stage-3 best response is uniquely
   `max 0 (L k c u t qR)`.
2. Whenever `0 ≤ qR7` and `0 ≤ qM7` (for `0 < t ≤ 1`), `(qR7, qM7)` is the unique
   stage-2/stage-3 subgame equilibrium.
3. On an encroaching SPE path with `0 < t < 1` and `0 < qM`, we prove `0 < qR`,
   `qR = qR7`, `qM = qM7`, and `w = wH k c t u`, so `(σ.t, σ.u)` is an interior local
   maximizer of `PiH k c`.
4. Clearing the positive denominator `4 * u * (8 - 5 * t)` of `PiH`, the first-order
   condition in `t` yields `4 * c = k * u^2 * (12 * t - 5 * t^2 - 4)` and `2/5 ≤ t < 1`,
   under which `retailerPayoff σ.path = t^3 * (2 - t) * k^2 * u^3 / 8`.
5. Along the polynomial direction `(t(s), u(s)) = (t - (12*t - 5*t^2 - 4)*s, u + u*(6 - 5*t)*s)`,
   the 1D second-order optimality condition gives `P(t) * k * u ≤ 32 * (6 - 5 * t)`, where
   `P(t) = 384 - 640*t + 624*t^2 - 328*t^3 + 150*t^4 - 25*t^5`.
6. Lower-bounding `P(t) ≥ Q(t) := 320 - 395*t + 236*t^2` on `[2/5, 1]` yields:
   - `retailerPayoff σ.path < 1 / (108 * k)` directly via a Bernstein certificate;
   - `k * c < 2 / 15` via a two-square sum-of-squares certificate, which makes the uniform-quality
     deviation `(w', u', t') = (2/(9*k) - c/6, 1/(3*k), 1)` strictly profitable above `1 / (54 * k)`.
-/

private noncomputable def L_br (k c u t qR : ℝ) : ℝ :=
  (1 - t * qR - c / u - k * u) / 2

private noncomputable def qR7 (k c w u t : ℝ) : ℝ :=
  1 / (2 * (2 - t)) - w / (t * (2 - t) * u) + k * u / (2 * (2 - t)) + c / (2 * (2 - t) * u)

private noncomputable def qM7 (k c w u t : ℝ) : ℝ :=
  (4 - 3 * t) / (4 * (2 - t)) + w / (2 * (2 - t) * u) - (4 - t) * k * u / (4 * (2 - t))
    - (4 - t) * c / (4 * (2 - t) * u)

private noncomputable def wH (k c t u : ℝ) : ℝ :=
  t * u / 2 + k * t ^ 2 * (7 - 4 * t) * u ^ 2 / (2 * (8 - 5 * t)) - c * t ^ 2 / (2 * (8 - 5 * t))

private noncomputable def PiH (k c t u : ℝ) : ℝ :=
  (4 * k ^ 2 * u ^ 3 * t ^ 3 - (8 * k ^ 2 * u ^ 3 + 8 * k * c * u) * t ^ 2
      - (k ^ 2 * u ^ 3 + 2 * k * c * u + c ^ 2 / u) * t
      + 8 * k ^ 2 * u ^ 3 + 16 * k * c * u + 8 * c ^ 2 / u) / (4 * (8 - 5 * t))
    - (2 * k * u ^ 2 - u + 2 * c) / 4

private noncomputable def N_poly (k c t u : ℝ) : ℝ :=
  4 * k ^ 2 * u ^ 4 * t ^ 3 - 8 * k * u ^ 2 * (k * u ^ 2 + c) * t ^ 2
    + (8 - t) * (k * u ^ 2 + c) ^ 2 - u * (8 - 5 * t) * (2 * k * u ^ 2 - u + 2 * c)

private noncomputable def D_poly (t u : ℝ) : ℝ :=
  4 * u * (8 - 5 * t)

private lemma PiH_eq_div (k c t u : ℝ) (hu : u ≠ 0) (ht : 8 - 5 * t ≠ 0) :
    PiH k c t u = N_poly k c t u / D_poly t u := by
  set s := 8 - 5 * t with hs_def
  have hs : s ≠ 0 := ht
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hden : D_poly t u ≠ 0 := by
    unfold D_poly; exact mul_ne_zero (mul_ne_zero h4 hu) ht
  rw [eq_div_iff hden]
  unfold PiH N_poly D_poly
  rw [← hs_def]
  field_simp [hu, hs]
  rw [hs_def]
  ring

private lemma L_br_qR7 (k c w u t : ℝ) (hu : u ≠ 0) (ht0 : t ≠ 0) (ht2 : 2 - t ≠ 0) :
    L_br k c u t (qR7 k c w u t) = qM7 k c w u t := by
  unfold L_br qR7 qM7
  field_simp
  ring

/-! ### Stage 3 and Stage 2 uniqueness for `0 < t ≤ 1` -/

private lemma stage3_unique {k c : ℝ} {σ : Profile} (hσ : IsSPE k c (Set.Ioi 0) σ)
    (w : ℝ) {u t qR : ℝ} (hu : 0 < u) (ht0 : 0 < t) (ht1 : t ≤ 1) (hqR : 0 ≤ qR) :
    σ.direct w u t qR = max 0 (L_br k c u t qR) := by
  have h3 := hσ.1 w u t qR hu ht0 hqR
  set qM := σ.direct w u t qR
  set L := L_br k c u t qR
  set qM' := max 0 L
  have hqM_nonneg : 0 ≤ qM := h3.1
  have hqM'_nonneg : 0 ≤ qM' := le_max_left 0 L
  have hle : mfrPayoff k c ⟨w, u, t, qR, qM'⟩ ≤ mfrPayoff k c ⟨w, u, t, qR, qM⟩ := h3.2 qM' hqM'_nonneg
  have hdiff :
      mfrPayoff k c ⟨w, u, t, qR, qM'⟩ - mfrPayoff k c ⟨w, u, t, qR, qM⟩ =
        u * (qM' - qM) * (2 * L - qM' - qM) := by
    simp only [mfrPayoff, priceM, ht1, ↓reduceIte, L, L_br]
    field_simp [hu.ne']
    ring
  have hnonpos : u * (qM' - qM) * (2 * L - qM' - qM) ≤ 0 := by linarith
  by_cases hL : 0 ≤ L
  · have hqM'_eq : qM' = L := max_eq_right hL
    rw [hqM'_eq] at hnonpos ⊢
    have hsq : u * (L - qM) ^ 2 ≤ 0 := by
      have : u * (L - qM) * (2 * L - L - qM) = u * (L - qM) ^ 2 := by ring
      linarith
    have hsq0 : (L - qM) ^ 2 ≤ 0 := by nlinarith
    nlinarith [sq_nonneg (L - qM)]
  · push Not at hL
    have hqM'_eq : qM' = 0 := max_eq_left hL.le
    rw [hqM'_eq] at hnonpos ⊢
    have hprod : u * qM * (qM - 2 * L) ≤ 0 := by linarith
    by_contra hne
    have hpos : 0 < qM := lt_of_le_of_ne hqM_nonneg (Ne.symm hne)
    have hpos_prod : 0 < u * qM * (qM - 2 * L) := mul_pos (mul_pos hu hpos) (by linarith)
    linarith

private lemma retailerPayoff_le_quad {k c : ℝ} {σ : Profile} (hσ : IsSPE k c (Set.Ioi 0) σ)
    (w : ℝ) {u t qR : ℝ} (hu : 0 < u) (ht0 : 0 < t) (ht1 : t ≤ 1) (hqR : 0 ≤ qR) :
    retailerPayoff (σ.outcomeAtDirect w u t qR) ≤
      (t * u * (1 - L_br k c u t qR - qR) - w) * qR := by
  have hdir := stage3_unique hσ w hu ht0 ht1 hqR
  simp only [Profile.outcomeAtDirect, retailerPayoff, priceR, ht1, ↓reduceIte, hdir]
  have hmax : L_br k c u t qR ≤ max 0 (L_br k c u t qR) := le_max_right 0 _
  have htu : 0 < t * u := mul_pos ht0 hu
  have h1 : t * u * (1 - max 0 (L_br k c u t qR) - qR) - w ≤
      t * u * (1 - L_br k c u t qR - qR) - w := by nlinarith
  exact mul_le_mul_of_nonneg_right h1 hqR

private lemma quad_identity (k c w u t qR : ℝ) (hu : u ≠ 0) (ht0 : t ≠ 0) (ht2 : 2 - t ≠ 0) :
    (t * u * (1 - L_br k c u t (qR7 k c w u t) - qR7 k c w u t) - w) * qR7 k c w u t -
      (t * u * (1 - L_br k c u t qR - qR) - w) * qR =
      t * (2 - t) * u / 2 * (qR - qR7 k c w u t) ^ 2 := by
  unfold L_br qR7
  field_simp
  ring

private lemma stage2_unique {k c : ℝ} {σ : Profile} (hσ : IsSPE k c (Set.Ioi 0) σ)
    {w u t : ℝ} (hu : 0 < u) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hqR7 : 0 ≤ qR7 k c w u t) (hqM7 : 0 ≤ qM7 k c w u t) :
    σ.order w u t = qR7 k c w u t ∧
      σ.direct w u t (σ.order w u t) = qM7 k c w u t := by
  have h2 := hσ.2.1 w u t hu (Set.mem_Ioi.mpr ht0)
  have ht2 : 0 < 2 - t := by linarith
  have hL7 : L_br k c u t (qR7 k c w u t) = qM7 k c w u t :=
    L_br_qR7 k c w u t hu.ne' ht0.ne' ht2.ne'
  have hdir7 : σ.direct w u t (qR7 k c w u t) = qM7 k c w u t := by
    rw [stage3_unique hσ w hu ht0 ht1 hqR7, hL7, max_eq_right hqM7]
  have hval7 :
      retailerPayoff (σ.outcomeAtDirect w u t (qR7 k c w u t)) =
        (t * u * (1 - L_br k c u t (qR7 k c w u t) - qR7 k c w u t) - w) * qR7 k c w u t := by
    simp only [Profile.outcomeAtDirect, retailerPayoff, priceR, ht1, ↓reduceIte, hdir7, hL7]
  have hopt : retailerPayoff (σ.outcomeAtDirect w u t (qR7 k c w u t)) ≤
      retailerPayoff (σ.outcomeAtOrder w u t) := h2.2 (qR7 k c w u t) hqR7
  have hub : retailerPayoff (σ.outcomeAtOrder w u t) ≤
      (t * u * (1 - L_br k c u t (σ.order w u t) - σ.order w u t) - w) * σ.order w u t :=
    retailerPayoff_le_quad hσ w hu ht0 ht1 h2.1
  have hquad := quad_identity k c w u t (σ.order w u t) hu.ne' ht0.ne' ht2.ne'
  have hcoeff : 0 < t * (2 - t) * u / 2 := by positivity
  have hsq : t * (2 - t) * u / 2 * (σ.order w u t - qR7 k c w u t) ^ 2 ≤ 0 := by
    linarith [hval7, hopt, hub, hquad]
  have hsq0 : (σ.order w u t - qR7 k c w u t) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hsq hcoeff
  have hord : σ.order w u t = qR7 k c w u t := by
    have : σ.order w u t - qR7 k c w u t = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hsq0 (sq_nonneg _))
    linarith
  exact ⟨hord, by rw [hord, hdir7]⟩

/-! ### Equilibrium path characterization for `0 < t < 1` and `0 < qM` -/

private lemma mfrPayoff_subgame_quad (k c w u t : ℝ)
    (hu : u ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≤ 1) (ht2 : 2 - t ≠ 0) (ht8 : 8 - 5 * t ≠ 0) :
    mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩ =
      PiH k c t u - (8 - 5 * t) / (4 * t * (2 - t) ^ 2 * u) * (w - wH k c t u) ^ 2 := by
  rw [PiH_eq_div k c t u hu ht8, ← sub_eq_zero]
  set s := 8 - 5 * t with hs_def
  have hs : s ≠ 0 := ht8
  simp only [mfrPayoff, priceM, ht1, ↓reduceIte]
  unfold qR7 qM7 N_poly D_poly wH
  rw [← hs_def]
  field_simp [hu, ht0, ht2, hs]
  rw [hs_def]
  ring

private lemma qR7_at_wH (k c t u : ℝ) (hu : u ≠ 0) (ht0 : t ≠ 0) (ht2 : 2 - t ≠ 0) (ht8 : 8 - 5 * t ≠ 0) :
    qR7 k c (wH k c t u) u t = 2 * (k * u ^ 2 * (1 - t) + c) / ((8 - 5 * t) * u) := by
  rw [← sub_eq_zero]
  set s := 8 - 5 * t with hs_def
  have hs : s ≠ 0 := ht8
  unfold qR7 wH
  rw [← hs_def]
  field_simp [hu, ht0, ht2, hs]
  rw [hs_def]
  ring

private lemma path_eq_wH {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) {σ : Profile}
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) (ht : σ.t < 1) :
    σ.w = wH k c σ.t σ.u ∧
      σ.path.qR = qR7 k c (wH k c σ.t σ.u) σ.u σ.t ∧
      σ.path.qM = qM7 k c (wH k c σ.t σ.u) σ.u σ.t ∧
      0 < qR7 k c (wH k c σ.t σ.u) σ.u σ.t ∧
      0 < qM7 k c (wH k c σ.t σ.u) σ.u σ.t := by
  set w := σ.w
  set u := σ.u
  set t := σ.t
  set qR := σ.order w u t
  have hu : 0 < u := hσ.2.2.1
  have ht0 : 0 < t := hσ.2.2.2.1
  have ht1 : t ≤ 1 := ht.le
  have ht2 : 0 < 2 - t := by linarith
  have ht8 : 0 < 8 - 5 * t := by linarith
  have h2 := hσ.2.1 w u t hu ht0
  have hqR_nonneg : 0 ≤ qR := h2.1
  have hdir_path : σ.path.qM = max 0 (L_br k c u t qR) :=
    stage3_unique hσ w hu ht0 ht1 hqR_nonneg
  have hL_pos : 0 < L_br k c u t qR := by
    by_contra hle
    push Not at hle
    rw [hdir_path, max_eq_left hle] at henc
    exact lt_irrefl 0 henc
  have hqM_eq_L : σ.path.qM = L_br k c u t qR := by
    rw [hdir_path, max_eq_right hL_pos.le]
  -- First show `qR ≠ 0`
  have hqR_pos : 0 < qR := by
    by_contra hle
    have hqR0 : qR = 0 := le_antisymm (not_lt.mp hle) hqR_nonneg
    have hL0 : 0 < L_br k c u t 0 := by rwa [hqR0] at hL_pos
    set w0 := t * (u + c + k * u ^ 2) / 2
    have hqR7_w0 : qR7 k c w0 u t = 0 := by
      unfold qR7 w0; field_simp [hu.ne', ht0.ne', ht2.ne']; ring
    have hqM7_w0 : qM7 k c w0 u t = L_br k c u t 0 := by
      rw [← L_br_qR7 k c w0 u t hu.ne' ht0.ne' ht2.ne', hqR7_w0]
    have hqR7_wH_pos : 0 < qR7 k c (wH k c t u) u t := by
      rw [qR7_at_wH k c t u hu.ne' ht0.ne' ht2.ne' ht8.ne']
      have hnum : 0 < k * u ^ 2 * (1 - t) + c := by nlinarith [mul_pos hk (sq_pos_of_pos hu)]
      positivity
    have hqR7_lin : ∀ w', qR7 k c w' u t = (w0 - w') / (t * (2 - t) * u) := by
      intro w'; unfold qR7 w0; field_simp [hu.ne', ht0.ne', ht2.ne']; ring
    have hwH_lt_w0 : wH k c t u < w0 := by
      have h1 := hqR7_lin (wH k c t u)
      have hden : 0 < t * (2 - t) * u := by positivity
      rw [h1, div_pos_iff_of_pos_right hden] at hqR7_wH_pos
      linarith
    set δ := min ((w0 - wH k c t u) / 2) ((2 - t) * u * L_br k c u t 0)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by positivity)
    set w' := w0 - δ
    have hw'_gt_wH : wH k c t u < w' := by
      have : δ ≤ (w0 - wH k c t u) / 2 := min_le_left _ _
      linarith
    have hqR7_w'_pos : 0 ≤ qR7 k c w' u t := by
      rw [hqR7_lin w']
      have : w0 - w' = δ := by ring
      rw [this]
      positivity
    have hqM7_w'_eq : qM7 k c w' u t = L_br k c u t 0 - δ / (2 * (2 - t) * u) := by
      rw [← hqM7_w0]; unfold qM7 w'; field_simp [hu.ne', ht2.ne']; ring
    have hqM7_w'_nonneg : 0 ≤ qM7 k c w' u t := by
      rw [hqM7_w'_eq]
      have hδ2 : δ ≤ (2 - t) * u * L_br k c u t 0 := min_le_right _ _
      have hden : 0 < 2 * (2 - t) * u := by positivity
      rw [sub_nonneg, div_le_iff₀ hden]
      linarith
    have hsub := stage2_unique hσ hu ht0 ht1 hqR7_w'_pos hqM7_w'_nonneg
    have hpay_w' : mfrPayoff k c (σ.outcomeAtOrder w' u t) =
        mfrPayoff k c ⟨w', u, t, qR7 k c w' u t, qM7 k c w' u t⟩ := by
      simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect]
      rw [hsub.2, hsub.1]
    have hpay_path : mfrPayoff k c σ.path =
        mfrPayoff k c ⟨w0, u, t, qR7 k c w0 u t, qM7 k c w0 u t⟩ := by
      have h1 : σ.path = ⟨w, u, t, 0, L_br k c u t 0⟩ := by
        have hqM0 : σ.path.qM = L_br k c u t 0 := by rwa [hqR0] at hqM_eq_L
        change (⟨w, u, t, qR, σ.path.qM⟩ : Outcome) = _
        rw [hqR0, hqM0]
      rw [h1, hqR7_w0, hqM7_w0]
      simp [mfrPayoff]
    have hquad_w' := mfrPayoff_subgame_quad k c w' u t hu.ne' ht0.ne' ht1 ht2.ne' ht8.ne'
    have hquad_w0 := mfrPayoff_subgame_quad k c w0 u t hu.ne' ht0.ne' ht1 ht2.ne' ht8.ne'
    have hcoeff : 0 < (8 - 5 * t) / (4 * t * (2 - t) ^ 2 * u) := by positivity
    have hsq_lt : (w' - wH k c t u) ^ 2 < (w0 - wH k c t u) ^ 2 := by
      nlinarith
    have hstrict : mfrPayoff k c σ.path < mfrPayoff k c (σ.outcomeAtOrder w' u t) := by
      rw [hpay_w', hpay_path, hquad_w', hquad_w0]
      have := mul_lt_mul_of_pos_left hsq_lt hcoeff
      linarith
    exact not_le_of_gt hstrict (hσ.2.2.2.2 w' u t hu (Set.mem_Ioi.mpr ht0))
  -- Second show `qR = qR7 k c w u t`
  have hqR_eq : qR = qR7 k c w u t := by
    by_contra hne
    set d := qR7 k c w u t - qR
    have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hq_abs : 0 < |d| := abs_pos.mpr hd_ne
    set δ := min (1 / 2) (min (qR / (2 * |d|)) (L_br k c u t qR / (t * |d|)))
    have hδ_pos : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
    have hδ_le_qR : δ ≤ qR / (2 * |d|) := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_le_L : δ ≤ L_br k c u t qR / (t * |d|) := le_trans (min_le_right _ _) (min_le_right _ _)
    set q' := qR + δ * d
    have hq'_nonneg : 0 ≤ q' := by
      have h1 : |δ * d| ≤ qR / 2 := by
        rw [abs_mul, abs_of_pos hδ_pos]
        have h2 : δ * (2 * |d|) ≤ qR := (le_div_iff₀ (by positivity)).mp hδ_le_qR
        linarith
      linarith [(abs_le.mp h1).1]
    have hL'_nonneg : 0 ≤ L_br k c u t q' := by
      have hdiffL : L_br k c u t q' = L_br k c u t qR - t * (δ * d) / 2 := by
        unfold L_br q'; ring
      rw [hdiffL]
      have h1 : t * |δ * d| ≤ L_br k c u t qR := by
        rw [abs_mul, abs_of_pos hδ_pos]
        have h2 : δ * (t * |d|) ≤ L_br k c u t qR := (le_div_iff₀ (by positivity)).mp hδ_le_L
        linarith
      have h2 : t * (δ * d) ≤ t * |δ * d| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
      linarith
    have hdir' : σ.direct w u t q' = L_br k c u t q' := by
      rw [stage3_unique hσ w hu ht0 ht1 hq'_nonneg, max_eq_right hL'_nonneg]
    have hval' : retailerPayoff (σ.outcomeAtDirect w u t q') =
        (t * u * (1 - L_br k c u t q' - q') - w) * q' := by
      simp only [Profile.outcomeAtDirect, retailerPayoff, priceR, ht1, ↓reduceIte, hdir']
    have hval : retailerPayoff (σ.outcomeAtOrder w u t) =
        (t * u * (1 - L_br k c u t qR - qR) - w) * qR := by
      simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff, priceR, ht1,
        ↓reduceIte]
      have : σ.direct w u t qR = L_br k c u t qR := hqM_eq_L
      rw [this]
    have hq_id1 := quad_identity k c w u t qR hu.ne' ht0.ne' ht2.ne'
    have hq_id2 := quad_identity k c w u t q' hu.ne' ht0.ne' ht2.ne'
    have hdiff_q : (q' - qR7 k c w u t) ^ 2 = (1 - δ) ^ 2 * d ^ 2 := by
      have : q' - qR7 k c w u t = -(1 - δ) * d := by unfold q' d; ring
      rw [this]; ring
    have hdiff_r : (qR - qR7 k c w u t) ^ 2 = d ^ 2 := by
      have : qR - qR7 k c w u t = -d := by unfold d; ring
      rw [this]; ring
    have hcoeff : 0 < t * (2 - t) * u / 2 := by positivity
    have h1m : (1 - δ) ^ 2 < 1 := by
      have h1 : 1 - (1 - δ) ^ 2 = δ * (2 - δ) := by ring
      have h2 : 0 < δ * (2 - δ) := mul_pos hδ_pos (by linarith)
      linarith
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd_ne
    have hstrict : retailerPayoff (σ.outcomeAtOrder w u t) <
        retailerPayoff (σ.outcomeAtDirect w u t q') := by
      rw [hval, hval']
      have hmul1 : (1 - δ) ^ 2 * d ^ 2 < 1 * d ^ 2 := mul_lt_mul_of_pos_right h1m hd2
      have hmul2 : t * (2 - t) * u / 2 * (q' - qR7 k c w u t) ^ 2 <
          t * (2 - t) * u / 2 * (qR - qR7 k c w u t) ^ 2 := by
        rw [hdiff_q, hdiff_r]
        exact mul_lt_mul_of_pos_left (by linarith) hcoeff
      linarith
    exact not_le_of_gt hstrict (h2.2 q' hq'_nonneg)
  -- Third show `w = wH k c t u`
  have hqM_eq : σ.path.qM = qM7 k c w u t := by
    rw [hqM_eq_L, hqR_eq, L_br_qR7 k c w u t hu.ne' ht0.ne' ht2.ne']
  have hqR7_pos : 0 < qR7 k c w u t := by rwa [← hqR_eq]
  have hqM7_pos : 0 < qM7 k c w u t := by rwa [← hqM_eq]
  have hw_eq : w = wH k c t u := by
    by_contra hne
    set dw := wH k c t u - w
    have hdw_ne : dw ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hdw_abs : 0 < |dw| := abs_pos.mpr hdw_ne
    set δ := min (1 / 2)
      (min (qR7 k c w u t * (t * (2 - t) * u) / (2 * |dw|))
           (qM7 k c w u t * (2 * (2 - t) * u) / (2 * |dw|)))
    have hδ_pos : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
    have hδ_le_R : δ ≤ qR7 k c w u t * (t * (2 - t) * u) / (2 * |dw|) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_le_M : δ ≤ qM7 k c w u t * (2 * (2 - t) * u) / (2 * |dw|) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    set w' := w + δ * dw
    have hqR'_nonneg : 0 ≤ qR7 k c w' u t := by
      have hdiff : qR7 k c w' u t = qR7 k c w u t - δ * dw / (t * (2 - t) * u) := by
        unfold qR7 w'; field_simp [hu.ne', ht0.ne', ht2.ne']; ring
      rw [hdiff]
      have h1 : δ * |dw| ≤ qR7 k c w u t * (t * (2 - t) * u) / 2 := by
        have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * |dw|)).mp hδ_le_R
        linarith
      have h2 : δ * dw ≤ δ * |dw| := mul_le_mul_of_nonneg_left (le_abs_self _) hδ_pos.le
      have hden : 0 < t * (2 - t) * u := by positivity
      have hpos : 0 < qR7 k c w u t * (t * (2 - t) * u) := mul_pos hqR7_pos hden
      rw [sub_nonneg, div_le_iff₀ hden]
      linarith
    have hqM'_nonneg : 0 ≤ qM7 k c w' u t := by
      have hdiff : qM7 k c w' u t = qM7 k c w u t + δ * dw / (2 * (2 - t) * u) := by
        unfold qM7 w'; field_simp [hu.ne', ht2.ne']; ring
      rw [hdiff]
      have h1 : δ * |dw| ≤ qM7 k c w u t * (2 * (2 - t) * u) / 2 := by
        have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * |dw|)).mp hδ_le_M
        linarith
      have h2 : -(δ * |dw|) ≤ δ * dw := by
        have hneg := mul_le_mul_of_nonneg_left (neg_abs_le dw) hδ_pos.le
        linarith
      have hden : 0 < 2 * (2 - t) * u := by positivity
      have hpos : 0 < qM7 k c w u t * (2 * (2 - t) * u) := mul_pos hqM7_pos hden
      have h3 : -(qM7 k c w u t * (2 * (2 - t) * u)) ≤ δ * dw := by linarith
      have h4 : -qM7 k c w u t ≤ δ * dw / (2 * (2 - t) * u) := by
        rw [le_div_iff₀ hden]; linarith
      linarith
    have hsub := stage2_unique hσ hu ht0 ht1 hqR'_nonneg hqM'_nonneg
    have hpay' : mfrPayoff k c (σ.outcomeAtOrder w' u t) =
        mfrPayoff k c ⟨w', u, t, qR7 k c w' u t, qM7 k c w' u t⟩ := by
      simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect]
      rw [hsub.2, hsub.1]
    have hpay : mfrPayoff k c σ.path =
        mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩ := by
      show mfrPayoff k c (⟨w, u, t, qR, σ.path.qM⟩ : Outcome) = _
      rw [hqR_eq, hqM_eq]
    have hq1 := mfrPayoff_subgame_quad k c w' u t hu.ne' ht0.ne' ht1 ht2.ne' ht8.ne'
    have hq2 := mfrPayoff_subgame_quad k c w u t hu.ne' ht0.ne' ht1 ht2.ne' ht8.ne'
    have hcoeff : 0 < (8 - 5 * t) / (4 * t * (2 - t) ^ 2 * u) := by positivity
    have hsq1 : (w' - wH k c t u) ^ 2 = (1 - δ) ^ 2 * dw ^ 2 := by
      have : w' - wH k c t u = -(1 - δ) * dw := by unfold w' dw; ring
      rw [this]; ring
    have hsq2 : (w - wH k c t u) ^ 2 = dw ^ 2 := by
      have : w - wH k c t u = -dw := by unfold dw; ring
      rw [this]; ring
    have hstrict : mfrPayoff k c σ.path < mfrPayoff k c (σ.outcomeAtOrder w' u t) := by
      rw [hpay', hpay, hq1, hq2, hsq1, hsq2]
      have h1m : (1 - δ) ^ 2 < 1 := by
        have h1 : 1 - (1 - δ) ^ 2 = δ * (2 - δ) := by ring
        have h2 : 0 < δ * (2 - δ) := mul_pos hδ_pos (by linarith)
        linarith
      have hdw2 : 0 < dw ^ 2 := sq_pos_of_ne_zero hdw_ne
      have hmul1 : (1 - δ) ^ 2 * dw ^ 2 < 1 * dw ^ 2 := mul_lt_mul_of_pos_right h1m hdw2
      have hmul2 : (8 - 5 * t) / (4 * t * (2 - t) ^ 2 * u) * ((1 - δ) ^ 2 * dw ^ 2) <
          (8 - 5 * t) / (4 * t * (2 - t) ^ 2 * u) * dw ^ 2 :=
        mul_lt_mul_of_pos_left (by linarith) hcoeff
      linarith
    exact not_le_of_gt hstrict (hσ.2.2.2.2 w' u t hu (Set.mem_Ioi.mpr ht0))
  refine ⟨hw_eq, ?_, ?_, ?_, ?_⟩
  · show qR = _; rwa [← hw_eq]
  · rwa [← hw_eq]
  · rwa [← hw_eq]
  · rwa [← hw_eq]

/-! ### Local optimality of `PiH` and 1D second-order necessary condition -/

private lemma second_deriv_nonpos_of_isLocalMax {f f' : ℝ → ℝ} {x₀ L : ℝ}
    (hmax : IsLocalMax f x₀)
    (hf : ∀ᶠ x in nhds x₀, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' L x₀) :
    f' x₀ = 0 ∧ L ≤ 0 := by
  have hzero : f' x₀ = 0 := hmax.hasDerivAt_eq_zero hf.self_of_nhds
  refine ⟨hzero, ?_⟩
  by_contra hgt
  push Not at hgt
  have hslope : Filter.Tendsto (slope f' x₀) (nhdsWithin x₀ {x₀}ᶜ) (nhds L) :=
    hasDerivAt_iff_tendsto_slope.mp hf'
  have hev_slope : ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, 0 < slope f' x₀ x :=
    hslope.eventually (Ioi_mem_nhds hgt)
  rw [eventually_nhdsWithin_iff] at hev_slope
  have hall : ∀ᶠ x in nhds x₀,
      (f x ≤ f x₀) ∧ HasDerivAt f (f' x) x ∧ (x ≠ x₀ → 0 < slope f' x₀ x) :=
    hmax.and (hf.and hev_slope)
  rcases Metric.eventually_nhds_iff.mp hall with ⟨ε, hε, hball⟩
  set δ := ε / 2 with hδε
  have hδ : 0 < δ := half_pos hε
  have hcont : ContinuousOn f (Set.Icc x₀ (x₀ + δ)) := by
    intro x hx
    have hdist : dist x x₀ < ε := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2, hδε]
    exact (hball hdist).2.1.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo x₀ (x₀ + δ), HasDerivAt f (f' x) x := by
    intro x hx
    have hdist : dist x x₀ < ε := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2, hδε]
    exact (hball hdist).2.1
  rcases exists_hasDerivAt_eq_slope f f' (by linarith : x₀ < x₀ + δ) hcont hderiv with
    ⟨ξ, hξ, hξ_eq⟩
  have hdist_end : dist (x₀ + δ) x₀ < ε := by
    rw [Real.dist_eq, show x₀ + δ - x₀ = δ by ring, abs_of_pos hδ]
    linarith [hδε]
  have hf_end : f (x₀ + δ) ≤ f x₀ := (hball hdist_end).1
  have hξ_nonpos : f' ξ ≤ 0 := by
    rw [hξ_eq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hdist_ξ : dist ξ x₀ < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hξ.1])]
    linarith [hξ.2, hδε]
  have hξ_slope : 0 < slope f' x₀ ξ := (hball hdist_ξ).2.2 (ne_of_gt hξ.1)
  rw [slope_def_field, hzero, sub_zero] at hξ_slope
  have hξ_pos : 0 < f' ξ := by
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hξ.1)).mp hξ_slope
    exact this
  linarith

private lemma local_max_slice {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) {σ : Profile}
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) (ht : σ.t < 1)
    (a v : ℝ) :
    IsLocalMax (fun s =>
      N_poly k c (σ.t + a * s) (σ.u + v * s) * D_poly σ.t σ.u -
        N_poly k c σ.t σ.u * D_poly (σ.t + a * s) (σ.u + v * s)) 0 := by
  have hpath := path_eq_wH hk hc hσ henc ht
  set t := σ.t
  set u := σ.u
  have hu : 0 < u := hσ.2.2.1
  have ht0 : 0 < t := hσ.2.2.2.1
  have ht2 : 0 < 2 - t := by linarith
  have ht8 : 0 < 8 - 5 * t := by linarith
  have hD0 : 0 < D_poly t u := by unfold D_poly; positivity
  let ft : ℝ → ℝ := fun s => t + a * s
  let fu : ℝ → ℝ := fun s => u + v * s
  have hct : ContinuousAt ft 0 := by fun_prop
  have hcu : ContinuousAt fu 0 := by fun_prop
  have hev_u : ∀ᶠ s in nhds (0 : ℝ), 0 < fu s :=
    hcu.eventually (Ioi_mem_nhds (by simpa [fu] using hu))
  have hev_t0 : ∀ᶠ s in nhds (0 : ℝ), 0 < ft s :=
    hct.eventually (Ioi_mem_nhds (by simpa [ft] using ht0))
  have hev_t1 : ∀ᶠ s in nhds (0 : ℝ), ft s < 1 :=
    hct.eventually (Iio_mem_nhds (by simpa [ft] using ht))
  have hcwH : ContinuousAt (fun s => wH k c (ft s) (fu s)) 0 := by
    unfold wH
    have h8 : 2 * (8 - 5 * ft 0) ≠ 0 := by simp [ft]; linarith
    fun_prop (disch := assumption)
  have hcqR : ContinuousAt (fun s => qR7 k c (wH k c (ft s) (fu s)) (fu s) (ft s)) 0 := by
    unfold qR7
    have h1 : 2 * (2 - ft 0) ≠ 0 := by simp only [ft, mul_zero, add_zero]; linarith
    have h2 : ft 0 * (2 - ft 0) * fu 0 ≠ 0 := by simp only [ft, fu, mul_zero, add_zero]; positivity
    have h3 : 2 * (2 - ft 0) * fu 0 ≠ 0 := by simp only [ft, fu, mul_zero, add_zero]; positivity
    fun_prop (disch := assumption)
  have hcqM : ContinuousAt (fun s => qM7 k c (wH k c (ft s) (fu s)) (fu s) (ft s)) 0 := by
    unfold qM7
    have h1 : 4 * (2 - ft 0) ≠ 0 := by simp only [ft, mul_zero, add_zero]; linarith
    have h2 : 2 * (2 - ft 0) * fu 0 ≠ 0 := by simp only [ft, fu, mul_zero, add_zero]; positivity
    have h3 : 4 * (2 - ft 0) * fu 0 ≠ 0 := by simp only [ft, fu, mul_zero, add_zero]; positivity
    fun_prop (disch := assumption)
  have hev_qR : ∀ᶠ s in nhds (0 : ℝ), 0 < qR7 k c (wH k c (ft s) (fu s)) (fu s) (ft s) :=
    hcqR.eventually (Ioi_mem_nhds (by simpa [ft, fu] using hpath.2.2.2.1))
  have hev_qM : ∀ᶠ s in nhds (0 : ℝ), 0 < qM7 k c (wH k c (ft s) (fu s)) (fu s) (ft s) :=
    hcqM.eventually (Ioi_mem_nhds (by simpa [ft, fu] using hpath.2.2.2.2))
  have hall := hev_u.and (hev_t0.and (hev_t1.and (hev_qR.and hev_qM)))
  filter_upwards [hall] with s hs
  rcases hs with ⟨hus, hts0, hts1, hqRs, hqMs⟩
  have hsub := stage2_unique hσ hus hts0 hts1.le hqRs.le hqMs.le
  have hts2 : 0 < 2 - ft s := by linarith
  have hts8 : 0 < 8 - 5 * ft s := by linarith
  have hDs : 0 < D_poly (ft s) (fu s) := by unfold D_poly; positivity
  have hpay_s : mfrPayoff k c (σ.outcomeAtOrder (wH k c (ft s) (fu s)) (fu s) (ft s)) =
      PiH k c (ft s) (fu s) := by
    have h1 : σ.outcomeAtOrder (wH k c (ft s) (fu s)) (fu s) (ft s) =
        ⟨wH k c (ft s) (fu s), fu s, ft s,
          qR7 k c (wH k c (ft s) (fu s)) (fu s) (ft s),
          qM7 k c (wH k c (ft s) (fu s)) (fu s) (ft s)⟩ := by
      simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect]
      rw [hsub.2, hsub.1]
    rw [h1, mfrPayoff_subgame_quad k c (wH k c (ft s) (fu s)) (fu s) (ft s)
      hus.ne' hts0.ne' hts1.le hts2.ne' hts8.ne']
    ring
  have hpay_0 : mfrPayoff k c σ.path = PiH k c t u := by
    have h1 : σ.path = ⟨wH k c t u, u, t,
        qR7 k c (wH k c t u) u t, qM7 k c (wH k c t u) u t⟩ := by
      show (⟨σ.w, u, t, σ.path.qR, σ.path.qM⟩ : Outcome) = _
      rw [hpath.1, hpath.2.1, hpath.2.2.1]
    rw [h1, mfrPayoff_subgame_quad k c (wH k c t u) u t hu.ne' ht0.ne' ht.le ht2.ne' ht8.ne']
    ring
  have hle_Pi : PiH k c (ft s) (fu s) ≤ PiH k c t u := by
    rw [← hpay_s, ← hpay_0]
    exact hσ.2.2.2.2 (wH k c (ft s) (fu s)) (fu s) (ft s) hus (Set.mem_Ioi.mpr hts0)
  rw [PiH_eq_div k c (ft s) (fu s) hus.ne' hts8.ne',
      PiH_eq_div k c t u hu.ne' ht8.ne'] at hle_Pi
  have hmul : N_poly k c (ft s) (fu s) * D_poly t u ≤
      N_poly k c t u * D_poly (ft s) (fu s) :=
    (div_le_div_iff₀ hDs hD0).mp hle_Pi
  simp only [mul_zero, add_zero, sub_self]
  linarith

/-! ### Explicit derivatives of the polynomial slice `P_slice` -/

private noncomputable def N_slice_d1 (k c t u a v s : ℝ) : ℝ :=
  let T := t + a * s
  let U := u + v * s
  let W := k * U ^ 2 + c
  let Wp := 2 * k * U * v
  let Z := 2 * k * U ^ 2 - U + 2 * c
  let Zp := (4 * k * U - 1) * v
  4 * k ^ 2 * (4 * U ^ 3 * v * T ^ 3 + 3 * U ^ 4 * T ^ 2 * a)
    - 8 * k * (2 * U * v * W * T ^ 2 + U ^ 2 * Wp * T ^ 2 + U ^ 2 * W * 2 * T * a)
    + (-a * W ^ 2 + (8 - T) * 2 * W * Wp)
    - (v * (8 - 5 * T) * Z + U * (-5 * a) * Z + U * (8 - 5 * T) * Zp)

private noncomputable def N_slice_d2_zero (k c t u a v : ℝ) : ℝ :=
  let W := k * u ^ 2 + c
  let Wp := 2 * k * u * v
  let Wpp := 2 * k * v ^ 2
  let Z := 2 * k * u ^ 2 - u + 2 * c
  let Zp := (4 * k * u - 1) * v
  let Zpp := 4 * k * v ^ 2
  4 * k ^ 2 * (12 * u ^ 2 * v ^ 2 * t ^ 3 + 24 * u ^ 3 * v * t ^ 2 * a + 6 * u ^ 4 * t * a ^ 2)
    - 8 * k * (2 * v ^ 2 * W * t ^ 2 + 4 * u * v * Wp * t ^ 2 + 8 * u * v * W * t * a
      + u ^ 2 * Wpp * t ^ 2 + 4 * u ^ 2 * Wp * t * a + 2 * u ^ 2 * W * a ^ 2)
    + (-4 * a * W * Wp + 2 * (8 - t) * (Wp ^ 2 + W * Wpp))
    - (2 * v * (-5 * a) * Z + 2 * v * (8 - 5 * t) * Zp + 2 * u * (-5 * a) * Zp
      + u * (8 - 5 * t) * Zpp)

private lemma hasDerivAt_fun_mul {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y * g y) (f' * g x + f x * g') x :=
  hf.mul hg

private lemma hasDerivAt_fun_add {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x :=
  hf.add hg

private lemma hasDerivAt_fun_sub {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - g y) (f' - g') x :=
  hf.sub hg

private lemma hasDerivAt_fun_pow {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => f y ^ n) (n * f x ^ (n - 1) * f') x :=
  hf.pow n

private lemma hasDerivAt_N_slice (k c t u a v s : ℝ) :
    HasDerivAt (fun x => N_poly k c (t + a * x) (u + v * x)) (N_slice_d1 k c t u a v s) s := by
  have hT : HasDerivAt (fun x => t + a * x) a s := by
    simpa using ((hasDerivAt_id s).const_mul a).const_add t
  have hU : HasDerivAt (fun x => u + v * x) v s := by
    simpa using ((hasDerivAt_id s).const_mul v).const_add u
  have hU2 : HasDerivAt (fun x => (u + v * x) ^ 2) (2 * (u + v * s) * v) s :=
    (hasDerivAt_fun_pow hU 2).congr_deriv (by norm_num)
  have hU4 : HasDerivAt (fun x => (u + v * x) ^ 4) (4 * (u + v * s) ^ 3 * v) s :=
    (hasDerivAt_fun_pow hU 4).congr_deriv (by norm_num)
  have hT2 : HasDerivAt (fun x => (t + a * x) ^ 2) (2 * (t + a * s) * a) s :=
    (hasDerivAt_fun_pow hT 2).congr_deriv (by norm_num)
  have hT3 : HasDerivAt (fun x => (t + a * x) ^ 3) (3 * (t + a * s) ^ 2 * a) s :=
    (hasDerivAt_fun_pow hT 3).congr_deriv (by norm_num)
  have hW : HasDerivAt (fun x => k * (u + v * x) ^ 2 + c) (2 * k * (u + v * s) * v) s :=
    ((hU2.const_mul k).add_const c).congr_deriv (by ring)
  have hW2 : HasDerivAt (fun x => (k * (u + v * x) ^ 2 + c) ^ 2)
      (2 * (k * (u + v * s) ^ 2 + c) * (2 * k * (u + v * s) * v)) s :=
    (hasDerivAt_fun_pow hW 2).congr_deriv (by norm_num)
  have h8mT : HasDerivAt (fun x => 8 - (t + a * x)) (-a) s :=
    hT.const_sub 8
  have h8m5T : HasDerivAt (fun x => 8 - 5 * (t + a * x)) (-5 * a) s :=
    ((hT.const_mul 5).const_sub 8).congr_deriv (by ring)
  have hZ : HasDerivAt (fun x => 2 * k * (u + v * x) ^ 2 - (u + v * x) + 2 * c)
      ((4 * k * (u + v * s) - 1) * v) s :=
    ((hasDerivAt_fun_sub (hU2.const_mul (2 * k)) hU).add_const (2 * c)).congr_deriv (by ring)
  have hN1 := hasDerivAt_fun_mul (hU4.const_mul (4 * k ^ 2)) hT3
  have hN2 := hasDerivAt_fun_mul (hasDerivAt_fun_mul (hU2.const_mul (8 * k)) hW) hT2
  have hN3 := hasDerivAt_fun_mul h8mT hW2
  have hN4 := hasDerivAt_fun_mul (hasDerivAt_fun_mul hU h8m5T) hZ
  have hN := hasDerivAt_fun_sub (hasDerivAt_fun_add (hasDerivAt_fun_sub hN1 hN2) hN3) hN4
  refine (hN.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [N_poly]
  · simp only [N_slice_d1]; ring

private lemma hasDerivAt_N_slice_d1 (k c t u a v : ℝ) :
    HasDerivAt (N_slice_d1 k c t u a v) (N_slice_d2_zero k c t u a v) 0 := by
  have hT : HasDerivAt (fun x => t + a * x) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add t
  have hU : HasDerivAt (fun x => u + v * x) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul v).const_add u
  have hU2 : HasDerivAt (fun x => (u + v * x) ^ 2) (2 * u * v) 0 :=
    (hasDerivAt_fun_pow hU 2).congr_deriv (by norm_num)
  have hU3 : HasDerivAt (fun x => (u + v * x) ^ 3) (3 * u ^ 2 * v) 0 :=
    (hasDerivAt_fun_pow hU 3).congr_deriv (by norm_num)
  have hU4 : HasDerivAt (fun x => (u + v * x) ^ 4) (4 * u ^ 3 * v) 0 :=
    (hasDerivAt_fun_pow hU 4).congr_deriv (by norm_num)
  have hT2 : HasDerivAt (fun x => (t + a * x) ^ 2) (2 * t * a) 0 :=
    (hasDerivAt_fun_pow hT 2).congr_deriv (by norm_num)
  have hT3 : HasDerivAt (fun x => (t + a * x) ^ 3) (3 * t ^ 2 * a) 0 :=
    (hasDerivAt_fun_pow hT 3).congr_deriv (by norm_num)
  have hW : HasDerivAt (fun x => k * (u + v * x) ^ 2 + c) (2 * k * u * v) 0 :=
    ((hU2.const_mul k).add_const c).congr_deriv (by ring)
  have hWp : HasDerivAt (fun x => 2 * k * (u + v * x) * v) (2 * k * v ^ 2) 0 :=
    ((hU.const_mul (2 * k)).mul_const v).congr_deriv (by ring)
  have hW2 : HasDerivAt (fun x => (k * (u + v * x) ^ 2 + c) ^ 2)
      (2 * (k * u ^ 2 + c) * (2 * k * u * v)) 0 :=
    (hasDerivAt_fun_pow hW 2).congr_deriv (by norm_num)
  have h8mT : HasDerivAt (fun x => 8 - (t + a * x)) (-a) 0 :=
    hT.const_sub 8
  have h8m5T : HasDerivAt (fun x => 8 - 5 * (t + a * x)) (-5 * a) 0 :=
    ((hT.const_mul 5).const_sub 8).congr_deriv (by ring)
  have hZ : HasDerivAt (fun x => 2 * k * (u + v * x) ^ 2 - (u + v * x) + 2 * c)
      ((4 * k * u - 1) * v) 0 :=
    ((hasDerivAt_fun_sub (hU2.const_mul (2 * k)) hU).add_const (2 * c)).congr_deriv (by ring)
  have hZp : HasDerivAt (fun x => (4 * k * (u + v * x) - 1) * v) (4 * k * v ^ 2) 0 :=
    (((hU.const_mul (4 * k)).sub_const 1).mul_const v).congr_deriv (by ring)
  have h1a := hasDerivAt_fun_mul ((hU3.const_mul 4).mul_const v) hT3
  have h1b := (hasDerivAt_fun_mul (hU4.const_mul 3) hT2).mul_const a
  have h1 := (hasDerivAt_fun_add h1a h1b).const_mul (4 * k ^ 2)
  have h2a := hasDerivAt_fun_mul (hasDerivAt_fun_mul ((hU.const_mul 2).mul_const v) hW) hT2
  have h2b := hasDerivAt_fun_mul (hasDerivAt_fun_mul hU2 hWp) hT2
  have h2c := (hasDerivAt_fun_mul ((hasDerivAt_fun_mul hU2 hW).mul_const 2) hT).mul_const a
  have h2 := (hasDerivAt_fun_add (hasDerivAt_fun_add h2a h2b) h2c).const_mul (8 * k)
  have h3a := hW2.const_mul (-a)
  have h3b := hasDerivAt_fun_mul (hasDerivAt_fun_mul (h8mT.mul_const 2) hW) hWp
  have h3 := hasDerivAt_fun_add h3a h3b
  have h4a := hasDerivAt_fun_mul (h8m5T.const_mul v) hZ
  have h4b := hasDerivAt_fun_mul (hU.mul_const (-5 * a)) hZ
  have h4c := hasDerivAt_fun_mul (hasDerivAt_fun_mul hU h8m5T) hZp
  have h4 := hasDerivAt_fun_add (hasDerivAt_fun_add h4a h4b) h4c
  have hall := hasDerivAt_fun_sub (hasDerivAt_fun_add (hasDerivAt_fun_sub h1 h2) h3) h4
  refine (hall.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [N_slice_d1]
  · simp only [N_slice_d2_zero]; ring

private lemma slice_deriv_conditions {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) {σ : Profile}
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) (ht : σ.t < 1)
    (a v : ℝ) :
    N_slice_d1 k c σ.t σ.u a v 0 * D_poly σ.t σ.u -
        N_poly k c σ.t σ.u * (4 * (v * (8 - 5 * σ.t) - 5 * a * σ.u)) = 0 ∧
      N_slice_d2_zero k c σ.t σ.u a v * D_poly σ.t σ.u -
        N_poly k c σ.t σ.u * (-40 * a * v) ≤ 0 := by
  set t := σ.t
  set u := σ.u
  set D0 := D_poly t u
  set N0 := N_poly k c t u
  have hmax := local_max_slice hk hc hσ henc ht a v
  let P' : ℝ → ℝ := fun s =>
    N_slice_d1 k c t u a v s * D0 -
      N0 * (4 * (v * (8 - 5 * (t + a * s)) - 5 * a * (u + v * s)))
  have hP1 : ∀ s, HasDerivAt
      (fun x => N_poly k c (t + a * x) (u + v * x) * D0 -
        N0 * D_poly (t + a * x) (u + v * x))
      (P' s) s := by
    intro s
    have hD : HasDerivAt (fun x => D_poly (t + a * x) (u + v * x))
        (4 * (v * (8 - 5 * (t + a * s)) - 5 * a * (u + v * s))) s := by
      have hT : HasDerivAt (fun x => t + a * x) a s := by
        simpa using ((hasDerivAt_id s).const_mul a).const_add t
      have hU : HasDerivAt (fun x => u + v * x) v s := by
        simpa using ((hasDerivAt_id s).const_mul v).const_add u
      have h8 : HasDerivAt (fun x => 8 - 5 * (t + a * x)) (-5 * a) s := by
        have h := (hT.const_mul 5).const_sub 8
        rwa [show -(5 * a) = -5 * a by ring] at h
      have hmul := (hU.const_mul 4).mul h8
      have hfun : ((fun y => 4 * (u + v * y)) * fun x => 8 - 5 * (t + a * x)) =
          fun x => D_poly (t + a * x) (u + v * x) := by
        ext x; simp only [Pi.mul_apply, D_poly]
      have hder : 4 * v * (8 - 5 * (t + a * s)) + 4 * (u + v * s) * (-5 * a) =
          4 * (v * (8 - 5 * (t + a * s)) - 5 * a * (u + v * s)) := by ring
      rwa [hfun, hder] at hmul
    exact ((hasDerivAt_N_slice k c t u a v s).mul_const D0).sub (hD.const_mul N0)
  have hP2 : HasDerivAt P'
      (N_slice_d2_zero k c t u a v * D0 - N0 * (-40 * a * v)) 0 := by
    have hD2 : HasDerivAt
        (fun x => 4 * (v * (8 - 5 * (t + a * x)) - 5 * a * (u + v * x)))
        (-40 * a * v) 0 := by
      have hT : HasDerivAt (fun x => t + a * x) a 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add t
      have hU : HasDerivAt (fun x => u + v * x) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul v).const_add u
      have h8 : HasDerivAt (fun x => 8 - 5 * (t + a * x)) (-5 * a) 0 := by
        have h := (hT.const_mul 5).const_sub 8
        rwa [show -(5 * a) = -5 * a by ring] at h
      have hcomb := ((h8.const_mul v).sub (hU.const_mul (5 * a))).const_mul 4
      have hfun : (fun y => 4 * ((fun y => v * (8 - 5 * (t + a * y))) -
          fun y => 5 * a * (u + v * y)) y) =
          fun x => 4 * (v * (8 - 5 * (t + a * x)) - 5 * a * (u + v * x)) := by
        ext x; simp only [Pi.sub_apply]
      have hder : 4 * (v * (-5 * a) - 5 * a * v) = -40 * a * v := by ring
      rwa [hfun, hder] at hcomb
    exact ((hasDerivAt_N_slice_d1 k c t u a v).mul_const D0).sub (hD2.const_mul N0)
  have hcond := second_deriv_nonpos_of_isLocalMax hmax (Filter.Eventually.of_forall hP1) hP2
  simpa [P', D0, N0, mul_zero, add_zero] using hcond

/-! ### Polynomial inequalities on `[2/5, 1)` -/

private def P_poly (t : ℝ) : ℝ :=
  384 - 640 * t + 624 * t ^ 2 - 328 * t ^ 3 + 150 * t ^ 4 - 25 * t ^ 5

private def Q_poly (t : ℝ) : ℝ :=
  320 - 395 * t + 236 * t ^ 2

private lemma Q_poly_pos (t : ℝ) : 0 < Q_poly t := by
  have h : Q_poly t = 236 * (t - 395 / 472) ^ 2 + 146055 / 944 := by
    unfold Q_poly; ring
  rw [h]
  positivity

private lemma Q_poly_le_P_poly {t : ℝ} (ht_lo : 2 / 5 ≤ t) (ht_hi : t < 1) :
    Q_poly t < P_poly t := by
  set s := (5 * t - 2) / 3
  set r := 5 * (1 - t) / 3
  have hs : 0 ≤ s := by unfold s; linarith
  have hr : 0 < r := by unfold r; linarith
  have hdiff : P_poly t - Q_poly t =
      1334 / 125 * r ^ 5 + 2407 / 125 * r ^ 4 * s + 1796 / 125 * r ^ 3 * s ^ 2 +
      166 / 25 * r ^ 2 * s ^ 3 + 34 / 5 * r * s ^ 4 + 4 * s ^ 5 := by
    unfold P_poly Q_poly s r; ring
  have hpos : 0 < P_poly t - Q_poly t := by rw [hdiff]; positivity
  linarith

private lemma mfr_poly_ineq (t : ℝ) :
    1920 * (12 * t - 5 * t ^ 2 - 4) * (6 - 5 * t) ^ 2 < Q_poly t ^ 2 := by
  have h : Q_poly t ^ 2 - 1920 * (12 * t - 5 * t ^ 2 - 4) * (6 - 5 * t) ^ 2 =
      295696 * (t ^ 2 - 167305 / 73924 * t + 21 / 20) ^ 2 +
      8457169552 / 92405 * (t - 276568165 / 367703024) ^ 2 +
      438782952227 / 399677200 := by
    unfold Q_poly; ring
  have hpos : 0 < Q_poly t ^ 2 - 1920 * (12 * t - 5 * t ^ 2 - 4) * (6 - 5 * t) ^ 2 := by
    rw [h]; positivity
  linarith

private lemma retailer_poly_ineq {t : ℝ} (ht_lo : 2 / 5 ≤ t) (ht_hi : t < 1) :
    442368 * t ^ 3 * (2 - t) * (6 - 5 * t) ^ 3 < Q_poly t ^ 3 := by
  set s := (5 * t - 2) / 3
  set r := 5 * (1 - t) / 3
  have hs : 0 ≤ s := by unfold s; linarith
  have hr : 0 < r := by unfold r; linarith
  have h : Q_poly t ^ 3 - 442368 * t ^ 3 * (2 - t) * (6 - 5 * t) ^ 3 =
      79252056584 / 15625 * r ^ 7 + 238411146044 / 15625 * r ^ 6 * s +
      36616183662 / 3125 * r ^ 5 * s ^ 2 + 2726724253 / 625 * r ^ 4 * s ^ 3 +
      3199887908 / 125 * r ^ 3 * s ^ 4 + 182808822 / 5 * r ^ 2 * s ^ 5 +
      19073270 * r * s ^ 6 + 3730913 * s ^ 7 := by
    unfold Q_poly s r; ring
  have hpos : 0 < Q_poly t ^ 3 - 442368 * t ^ 3 * (2 - t) * (6 - 5 * t) ^ 3 := by
    rw [h]; positivity
  linarith

private lemma foc_alg_id (k c t u : ℝ) :
    N_slice_d1 k c t u 1 0 0 * D_poly t u -
        N_poly k c t u * (4 * (0 * (8 - 5 * t) - 5 * 1 * u)) =
      32 * u * (k * u ^ 2 * (1 - t) + c) * (4 * c + k * u ^ 2 * (5 * t ^ 2 - 12 * t + 4)) := by
  unfold N_slice_d1 N_poly D_poly; ring

private lemma soc_alg_id (k t u : ℝ) :
    let c := k * u ^ 2 * (12 * t - 5 * t ^ 2 - 4) / 4
    let a := -(12 * t - 5 * t ^ 2 - 4)
    let v := u * (6 - 5 * t)
    D_poly t u * (N_slice_d2_zero k c t u a v * D_poly t u - N_poly k c t u * (-40 * a * v)) -
        2 * (4 * (v * (8 - 5 * t) - 5 * a * u)) *
          (N_slice_d1 k c t u a v 0 * D_poly t u -
            N_poly k c t u * (4 * (v * (8 - 5 * t) - 5 * a * u))) =
      2 * k * u ^ 5 * (8 - 5 * t) ^ 3 * (6 - 5 * t) * (P_poly t * (k * u) - 32 * (6 - 5 * t)) := by
  dsimp only
  unfold N_slice_d2_zero N_slice_d1 N_poly D_poly P_poly
  ring

/-! ### Main theorem -/

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) (ht : σ.t < 1) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by
  set t := σ.t
  set u := σ.u
  have hu : 0 < u := hσ.2.2.1
  have ht0 : 0 < t := hσ.2.2.2.1
  have ht2 : 0 < 2 - t := by linarith
  have ht6 : 0 < 6 - 5 * t := by linarith
  have ht8 : 0 < 8 - 5 * t := by linarith
  have hpath := path_eq_wH hk hc hσ henc ht
  -- Step 1: First-order condition in `t` (`a = 1, v = 0`)
  have hfoc_raw := (slice_deriv_conditions hk hc hσ henc ht 1 0).1
  rw [foc_alg_id k c t u] at hfoc_raw
  have hfac1 : 0 < 32 * u * (k * u ^ 2 * (1 - t) + c) := by
    have : 0 < k * u ^ 2 * (1 - t) + c := by nlinarith [mul_pos hk (sq_pos_of_pos hu)]
    positivity
  have hc_rel : 4 * c + k * u ^ 2 * (5 * t ^ 2 - 12 * t + 4) = 0 := by
    rcases mul_eq_zero.mp hfoc_raw with h | h
    · linarith
    · exact h
  have hc_eq : c = k * u ^ 2 * (12 * t - 5 * t ^ 2 - 4) / 4 := by linarith
  have hquad_t : 0 ≤ 12 * t - 5 * t ^ 2 - 4 := by
    have hku2 : 0 < k * u ^ 2 := mul_pos hk (sq_pos_of_pos hu)
    nlinarith
  have ht_lo : 2 / 5 ≤ t := by
    have : (5 * t - 2) * (2 - t) = 12 * t - 5 * t ^ 2 - 4 := by ring
    nlinarith
  -- Step 2: Second-order condition along `(a, v) = (-(12*t - 5*t^2 - 4), u * (6 - 5*t))`
  set a := -(12 * t - 5 * t ^ 2 - 4)
  set v := u * (6 - 5 * t)
  have hsoc := slice_deriv_conditions hk hc hσ henc ht a v
  have hD0_pos : 0 < D_poly t u := by unfold D_poly; positivity
  have hsoc_comb :
      D_poly t u * (N_slice_d2_zero k c t u a v * D_poly t u - N_poly k c t u * (-40 * a * v)) -
        2 * (4 * (v * (8 - 5 * t) - 5 * a * u)) *
          (N_slice_d1 k c t u a v 0 * D_poly t u -
            N_poly k c t u * (4 * (v * (8 - 5 * t) - 5 * a * u))) ≤ 0 := by
    rw [hsoc.1, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hD0_pos.le hsoc.2
  have hsoc_id :
      D_poly t u * (N_slice_d2_zero k c t u a v * D_poly t u - N_poly k c t u * (-40 * a * v)) -
        2 * (4 * (v * (8 - 5 * t) - 5 * a * u)) *
          (N_slice_d1 k c t u a v 0 * D_poly t u -
            N_poly k c t u * (4 * (v * (8 - 5 * t) - 5 * a * u))) =
        2 * k * u ^ 5 * (8 - 5 * t) ^ 3 * (6 - 5 * t) * (P_poly t * (k * u) - 32 * (6 - 5 * t)) := by
    rw [hc_eq]
    exact soc_alg_id k t u
  rw [hsoc_id] at hsoc_comb
  have hsoc_coeff : 0 < 2 * k * u ^ 5 * (8 - 5 * t) ^ 3 * (6 - 5 * t) := by positivity
  have hPku : P_poly t * (k * u) ≤ 32 * (6 - 5 * t) := by
    by_contra hgt
    push Not at hgt
    have : 0 < 2 * k * u ^ 5 * (8 - 5 * t) ^ 3 * (6 - 5 * t) *
        (P_poly t * (k * u) - 32 * (6 - 5 * t)) := mul_pos hsoc_coeff (by linarith)
    linarith
  have hQ_pos : 0 < Q_poly t := Q_poly_pos t
  have hQ_lt_P : Q_poly t < P_poly t := Q_poly_le_P_poly ht_lo ht
  have hQku : Q_poly t * (k * u) ≤ 32 * (6 - 5 * t) := by
    have : Q_poly t * (k * u) ≤ P_poly t * (k * u) :=
      mul_le_mul_of_nonneg_right hQ_lt_P.le (mul_pos hk hu).le
    linarith
  -- Step 3: Manufacturer's inequality `1 / (54 * k) < mfrPayoff k c σ.path`
  have hkc_lt : k * c < 2 / 15 := by
    have h1 : Q_poly t ^ 2 * (k * u) ^ 2 ≤ (32 * (6 - 5 * t)) ^ 2 := by
      have hpos1 : 0 ≤ Q_poly t * (k * u) := mul_nonneg hQ_pos.le (mul_pos hk hu).le
      simpa [mul_pow] using pow_le_pow_left₀ hpos1 hQku 2
    have h2 : Q_poly t ^ 2 * (4 * (k * c)) =
        (12 * t - 5 * t ^ 2 - 4) * (Q_poly t ^ 2 * (k * u) ^ 2) := by
      rw [hc_eq]; ring
    have h3 : Q_poly t ^ 2 * (4 * (k * c)) ≤
        (12 * t - 5 * t ^ 2 - 4) * (32 * (6 - 5 * t)) ^ 2 := by
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hquad_t
    have h4 := mfr_poly_ineq t
    have h4b : 15 * ((12 * t - 5 * t ^ 2 - 4) * (32 * (6 - 5 * t)) ^ 2) =
        8 * (1920 * (12 * t - 5 * t ^ 2 - 4) * (6 - 5 * t) ^ 2) := by ring
    have h5 : Q_poly t ^ 2 * (60 * (k * c)) < Q_poly t ^ 2 * 8 := by linarith
    have h6 : 60 * (k * c) < 8 := lt_of_mul_lt_mul_left h5 (sq_pos_of_pos hQ_pos).le
    linarith
  have hmfr : 1 / (54 * k) < mfrPayoff k c σ.path := by
    set u1 := 1 / (3 * k)
    set w1 := 2 / (9 * k) - c / 6
    have hu1 : 0 < u1 := by unfold u1; positivity
    have hqR1 : qR7 k c w1 u1 1 = 2 * k * c := by
      unfold qR7 w1 u1; field_simp [hk.ne']; ring
    have hqM1 : qM7 k c w1 u1 1 = 1 / 3 - 5 * k * c / 2 := by
      unfold qM7 w1 u1; field_simp [hk.ne']; ring
    have hqR1_nn : 0 ≤ qR7 k c w1 u1 1 := by rw [hqR1]; positivity
    have hqM1_nn : 0 ≤ qM7 k c w1 u1 1 := by rw [hqM1]; linarith
    have hsub1 := stage2_unique hσ hu1 zero_lt_one le_rfl hqR1_nn hqM1_nn
    have hdev : mfrPayoff k c (σ.outcomeAtOrder w1 u1 1) ≤ mfrPayoff k c σ.path :=
      hσ.2.2.2.2 w1 u1 1 hu1 (Set.mem_Ioi.mpr zero_lt_one)
    have hval1 : mfrPayoff k c (σ.outcomeAtOrder w1 u1 1) =
        1 / (54 * k) + (7 / 4 * (k * c - 2 / 21) ^ 2 + 1 / 378) / k := by
      simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect]
      rw [hsub1.2, hsub1.1, hqR1, hqM1]
      simp only [mfrPayoff, priceM, le_rfl, ↓reduceIte, u1, w1]
      field_simp [hk.ne']
      ring
    have hpos_extra : 0 < (7 / 4 * (k * c - 2 / 21) ^ 2 + 1 / 378) / k := by positivity
    linarith
  -- Step 4: Retailer's inequality `retailerPayoff σ.path < 1 / (108 * k)`
  have hret : retailerPayoff σ.path < 1 / (108 * k) := by
    have hret_eq : retailerPayoff σ.path = t ^ 3 * (2 - t) * k ^ 2 * u ^ 3 / 8 := by
      have hp : σ.path = ⟨wH k c t u, u, t,
          qR7 k c (wH k c t u) u t, qM7 k c (wH k c t u) u t⟩ := by
        show (⟨σ.w, u, t, σ.path.qR, σ.path.qM⟩ : Outcome) = _
        rw [hpath.1, hpath.2.1, hpath.2.2.1]
      rw [hp]
      simp only [retailerPayoff, priceR, ht.le, ↓reduceIte]
      set s := 8 - 5 * t with hs_def
      have hs : s ≠ 0 := ht8.ne'
      unfold qR7 qM7 wH
      rw [hc_eq, ← hs_def]
      field_simp [hk.ne', hu.ne', ht0.ne', ht2.ne', hs]
      rw [hs_def]
      ring
    rw [hret_eq]
    have hku3 : Q_poly t ^ 3 * (k * u) ^ 3 ≤ (32 * (6 - 5 * t)) ^ 3 := by
      have hpos1 : 0 ≤ Q_poly t * (k * u) := mul_nonneg hQ_pos.le (mul_pos hk hu).le
      have hpos2 : 0 ≤ 32 * (6 - 5 * t) := by positivity
      have h3 := pow_le_pow_left₀ hpos1 hQku 3
      simpa [mul_pow] using h3
    have hret_ineq := retailer_poly_ineq ht_lo ht
    have hcoeff_nn : 0 ≤ t ^ 3 * (2 - t) := by positivity
    have h1 : t ^ 3 * (2 - t) * (Q_poly t ^ 3 * (k * u) ^ 3) ≤
        t ^ 3 * (2 - t) * (32 * (6 - 5 * t)) ^ 3 :=
      mul_le_mul_of_nonneg_left hku3 hcoeff_nn
    have h2 : 27 * (t ^ 3 * (2 - t) * (32 * (6 - 5 * t)) ^ 3) =
        2 * (442368 * t ^ 3 * (2 - t) * (6 - 5 * t) ^ 3) := by ring
    have h3 : 27 * (t ^ 3 * (2 - t) * (Q_poly t ^ 3 * (k * u) ^ 3)) < 2 * Q_poly t ^ 3 := by
      linarith
    have hQ3 : 0 < Q_poly t ^ 3 := pow_pos hQ_pos 3
    have h4 : 27 * (t ^ 3 * (2 - t) * (k * u) ^ 3) < 2 := by
      have h3' : Q_poly t ^ 3 * (27 * (t ^ 3 * (2 - t) * (k * u) ^ 3)) < Q_poly t ^ 3 * 2 := by
        linarith
      exact lt_of_mul_lt_mul_left h3' hQ3.le
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 8) (by positivity : 0 < 108 * k)]
    have h5 : t ^ 3 * (2 - t) * k ^ 2 * u ^ 3 * (108 * k) =
        4 * (27 * (t ^ 3 * (2 - t) * (k * u) ^ 3)) := by ring
    linarith
  exact ⟨hmfr, hret⟩
