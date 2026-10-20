-- Prove2me | solution 1 for PlatformQualReg.ExclSubsid.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:12:09.613292+00:00
-- url     : https://prove2.me/submissions/084c10ee-46a2-431e-9102-c93c3dcd3605

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid.P4Aux

open PlatformQualReg.ExclSubsid

lemma one_sided {g c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε : ℝ, 0 < ε → ε < δ → ε * g ≤ c * ε ^ 2) : g ≤ 0 := by
  by_contra hg
  have hg : 0 < g := lt_of_not_ge hg
  have hc : 0 ≤ |c| := abs_nonneg c
  set ε := min (δ / 2) (g / (2 * (|c| + 1))) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hε1 : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε2 : ε ≤ g / (2 * (|c| + 1)) := min_le_right _ _
  have h1 := h ε hε0 hε1
  have h2 : c * ε ^ 2 ≤ |c| * ε ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have h3 : ε * (2 * (|c| + 1)) ≤ g := by
    rwa [le_div_iff₀ (by positivity)] at hε2
  nlinarith [mul_le_mul_of_nonneg_left h3 hε0.le, mul_pos hε0 hg]

lemma two_sided {g c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε : ℝ, |ε| < δ → ε * g ≤ c * ε ^ 2) : g = 0 := by
  have h1 : g ≤ 0 := one_sided hδ (fun ε h0 h1 => h ε (by rw [abs_of_pos h0]; exact h1))
  have h2 : -g ≤ 0 := one_sided hδ (fun ε h0 h1 => by
    have := h (-ε) (by rw [abs_neg, abs_of_pos h0]; exact h1)
    have e1 : (-ε) * g = ε * (-g) := by ring
    have e2 : c * (-ε) ^ 2 = c * ε ^ 2 := by ring
    linarith)
  linarith

lemma two_sided_ev {g c : ℝ} (h : ∀ᶠ ε in nhds (0:ℝ), ε * g ≤ c * ε ^ 2) : g = 0 := by
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  exact two_sided hδ (fun ε he => hh (by simpa [Real.dist_eq] using he))

lemma one_sided_ev {g c : ℝ} (h : ∀ᶠ ε in nhds (0:ℝ), 0 < ε → ε * g ≤ c * ε ^ 2) :
    g ≤ 0 := by
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  exact one_sided hδ (fun ε h0 h1 => hh (by
    rw [Real.dist_eq, sub_zero, abs_of_pos h0]; exact h1) h0)

lemma ev_pos {a : ℝ} (k : ℝ) (ha : 0 < a) : ∀ᶠ ε in nhds (0:ℝ), 0 ≤ a + k * ε := by
  have hc : Continuous (fun ε : ℝ => a + k * ε) := by fun_prop
  have := (hc.tendsto 0).eventually (eventually_ge_nhds (show (0:ℝ) < a + k * 0 by simpa using ha))
  exact this

/-- Reduced exclusion profit. -/
noncomputable def FE (P : Params) (m n : ℝ) : ℝ :=
  P.w * m + xi1 P * m * n - P.thc * m ^ 2 - (P.thd + P.lam * P.b) / P.lam * n ^ 2

/-- Reduced subsidization profit. -/
noncomputable def GS (P : Params) (m n γ : ℝ) : ℝ :=
  P.w * m + xi P * m * n - P.thc * m ^ 2 - (P.thd + P.b) * n ^ 2 +
    P.β * P.qh * rho P * m ^ 2 + P.β * P.qh * t P * m * γ - rho P * m * γ - t P * γ ^ 2

lemma profitE_outE (P : Params) (m n : ℝ) : profitE P (outE P m n) = FE P m n := by
  simp only [profitE, outE, FE, xi1]; ring

lemma consE_outE (P : Params) (hP : P.Standing) (m n : ℝ) : ConsistentE P (outE P m n) := by
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP
  have hK : P.thd + P.lam * P.b ≠ 0 := by positivity
  constructor
  · simp only [outE]; field_simp; ring
  · simp only [outE]; field_simp; ring

lemma E_eq (P : Params) (hP : P.Standing) (x : OutcomeE) (hx : ConsistentE P x) :
    x = outE P x.m x.n := by
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP
  have hK : P.thd + P.lam * P.b ≠ 0 := by positivity
  obtain ⟨pd, pc, m, n⟩ := x
  obtain ⟨h1, h2⟩ := hx
  simp only at h1 h2
  simp only [outE, OutcomeE.mk.injEq, and_true]
  constructor
  · rw [eq_div_iff hK] at h1
    field_simp
    linarith
  · rw [eq_div_iff hc.ne'] at h2
    linarith

lemma nh_outS (P : Params) (hP : P.Standing) (m n γ : ℝ) :
    nh P (outS P m n γ) = P.lam * n + rho P * m + t P * γ := by
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP
  simp only [nh, outS, rho, t, abar]; field_simp; ring

lemma nl_outS (P : Params) (hP : P.Standing) (m n γ : ℝ) :
    nl P (outS P m n γ) = (1 - P.lam) * n - rho P * m - t P * γ := by
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP
  simp only [nl, outS, rho, t, abar]; field_simp; ring

lemma consS_outS (P : Params) (hP : P.Standing) (m n γ : ℝ) : ConsistentS P (outS P m n γ) := by
  have hc := hP.2.2.2.1
  constructor
  · rw [nl_outS P hP, nh_outS P hP]; simp only [outS]; ring
  · rw [nh_outS P hP]; simp only [outS]; field_simp; ring

lemma profitS_outS (P : Params) (hP : P.Standing) (m n γ : ℝ) :
    profitS P (outS P m n γ) = GS P m n γ := by
  simp only [profitS]
  rw [nh_outS P hP]
  simp only [outS, GS, xi]; ring

lemma S_eq (P : Params) (hP : P.Standing) (x : OutcomeS) (hx : ConsistentS P x) :
    x = outS P x.m x.n x.γ := by
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP
  obtain ⟨pd, pc, γ, m, n⟩ := x
  obtain ⟨h1, h2⟩ := hx
  simp only [nl, nh] at h1 h2
  have hpd : pd = abar P * m + P.lam * γ - (P.thd + P.b) * n := by
    simp only [abar]
    field_simp at h1
    linarith
  have hnh : P.lam * (P.adh * m - P.b * n + γ - pd) / P.thd =
      P.lam * n + rho P * m + t P * γ := by
    rw [hpd]; simp only [rho, t, abar]; field_simp; ring
  rw [hnh, eq_div_iff hc.ne'] at h2
  simp only [outS, OutcomeS.mk.injEq, and_true]
  exact ⟨hpd, by linarith⟩

lemma feasS_outS (P : Params) (hP : P.Standing) (m n γ : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hγ : 0 ≤ γ) (hl : 0 ≤ (1 - P.lam) * n - rho P * m - t P * γ)
    (hh : 0 ≤ P.lam * n + rho P * m + t P * γ) : FeasibleS P (outS P m n γ) := by
  refine ⟨consS_outS P hP m n γ, hm, hn, hγ, ?_, ?_⟩
  · rw [nl_outS P hP]; exact hl
  · rw [nh_outS P hP]; exact hh

end PlatformQualReg.ExclSubsid.P4Aux

open PlatformQualReg.ExclSubsid PlatformQualReg.ExclSubsid.P4Aux in
theorem solution (P : Params) (hP : P.Standing)
    (hcS : ConcaveS P) (hsub : P.adh - P.adl ≤ P.β * P.qh)
    (x : OutcomeS) (hx : IsOptS P x)
    (hint : 0 < x.m ∧ 0 < nl P x ∧ 0 < nh P x) :
    x.γ = optGammaS P ∧ x.m = optMS P ∧ x.n = optNS P ∧
    profitS P x = optProfitS P := by
  have hP' := hP
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP'
  have h1L : 0 < 1 - P.lam := by linarith
  obtain ⟨hmS, hnlS, hnhS⟩ := hint
  have hSeq := S_eq P hP x hx.1.1
  have hpS : profitS P x = GS P x.m x.n x.γ := by rw [← profitS_outS P hP, ← hSeq]
  have hnlS' : nl P x = (1 - P.lam) * x.n - rho P * x.m - t P * x.γ := by
    rw [← nl_outS P hP, ← hSeq]
  have hnhS' : nh P x = P.lam * x.n + rho P * x.m + t P * x.γ := by
    rw [← nh_outS P hP, ← hSeq]
  have hNL : 0 < (1 - P.lam) * x.n - rho P * x.m - t P * x.γ := hnlS' ▸ hnlS
  have hNH : 0 < P.lam * x.n + rho P * x.m + t P * x.γ := hnhS' ▸ hnhS
  have hNpos : 0 < x.n := by linarith
  have hΓ : 0 ≤ x.γ := hx.1.2.2.2.1
  have hoptS : ∀ m' n' γ', 0 ≤ m' → 0 ≤ n' → 0 ≤ γ' →
      0 ≤ (1 - P.lam) * n' - rho P * m' - t P * γ' →
      0 ≤ P.lam * n' + rho P * m' + t P * γ' → GS P m' n' γ' ≤ GS P x.m x.n x.γ := by
    intro m' n' γ' h1 h2 h3 h4 h5
    have := hx.2 (outS P m' n' γ') (feasS_outS P hP m' n' γ' h1 h2 h3 h4 h5)
    rwa [profitS_outS P hP, hpS] at this
  have S1 : P.w + xi P * x.n - 2 * P.thc * x.m + 2 * (P.β * P.qh) * rho P * x.m +
      (P.β * P.qh) * t P * x.γ - rho P * x.γ = 0 := by
    apply two_sided_ev (c := P.thc - P.β * P.qh * rho P)
    filter_upwards [ev_pos 1 hmS, ev_pos (-rho P) hNL, ev_pos (rho P) hNH] with ε h1 h2 h3
    have := hoptS (x.m + ε) x.n x.γ (by linarith) hNpos.le hΓ (by linarith) (by linarith)
    have e : GS P (x.m + ε) x.n x.γ - GS P x.m x.n x.γ =
        ε * (P.w + xi P * x.n - 2 * P.thc * x.m + 2 * (P.β * P.qh) * rho P * x.m +
          (P.β * P.qh) * t P * x.γ - rho P * x.γ) -
          (P.thc - P.β * P.qh * rho P) * ε ^ 2 := by unfold GS; ring
    linarith
  have S2 : xi P * x.m - 2 * (P.thd + P.b) * x.n = 0 := by
    apply two_sided_ev (c := P.thd + P.b)
    filter_upwards [ev_pos 1 hNpos, ev_pos (1 - P.lam) hNL, ev_pos P.lam hNH] with ε h1 h2 h3
    have := hoptS x.m (x.n + ε) x.γ hmS.le (by linarith) hΓ (by linarith) (by linarith)
    have e : GS P x.m (x.n + ε) x.γ - GS P x.m x.n x.γ =
        ε * (xi P * x.m - 2 * (P.thd + P.b) * x.n) - (P.thd + P.b) * ε ^ 2 := by
      unfold GS; ring
    linarith
  have S3 : (P.β * P.qh) * t P * x.m - rho P * x.m - 2 * t P * x.γ ≤ 0 := by
    apply one_sided_ev (c := t P)
    filter_upwards [ev_pos (-t P) hNL, ev_pos (t P) hNH] with ε h2 h3 h0
    have := hoptS x.m x.n (x.γ + ε) hmS.le hNpos.le (by linarith) (by linarith) (by linarith)
    have e : GS P x.m x.n (x.γ + ε) - GS P x.m x.n x.γ =
        ε * ((P.β * P.qh) * t P * x.m - rho P * x.m - 2 * t P * x.γ) - t P * ε ^ 2 := by
      unfold GS; ring
    linarith
  have hρ : rho P = t P * (P.adh - P.adl) := by unfold rho t; ring
  have hTpos : 0 < t P := by unfold t; exact div_pos (mul_pos hl h1L) hd
  -- the subsidy first-order condition holds with equality
  have Sγ : (P.β * P.qh) * t P * x.m - rho P * x.m - 2 * t P * x.γ = 0 := by
    rcases hΓ.lt_or_eq with hpos | hzero
    · apply two_sided_ev (c := t P)
      filter_upwards [ev_pos 1 hpos, ev_pos (-t P) hNL, ev_pos (t P) hNH] with ε h1 h2 h3
      have := hoptS x.m x.n (x.γ + ε) hmS.le hNpos.le (by linarith) (by linarith)
        (by linarith)
      have e : GS P x.m x.n (x.γ + ε) - GS P x.m x.n x.γ =
          ε * ((P.β * P.qh) * t P * x.m - rho P * x.m - 2 * t P * x.γ) - t P * ε ^ 2 := by
        unfold GS; ring
      linarith
    · rw [← hzero, hρ] at S3 ⊢
      have h0 : t P * x.m * (P.β * P.qh - (P.adh - P.adl)) ≤ 0 := by linarith
      have h1 : 0 ≤ t P * x.m * (P.β * P.qh - (P.adh - P.adl)) :=
        mul_nonneg (mul_nonneg hTpos.le hmS.le) (by linarith)
      linarith
  -- profit at the stationary point (Euler identity)
  have hval : GS P x.m x.n x.γ = P.w * x.m / 2 := by
    have e : GS P x.m x.n x.γ - P.w * x.m / 2 =
        (x.m * (P.w + xi P * x.n - 2 * P.thc * x.m + 2 * (P.β * P.qh) * rho P * x.m +
          (P.β * P.qh) * t P * x.γ - rho P * x.γ) +
         x.n * (xi P * x.m - 2 * (P.thd + P.b) * x.n) +
         x.γ * ((P.β * P.qh) * t P * x.m - rho P * x.m - 2 * t P * x.γ)) / 2 := by
      unfold GS; ring
    rw [S1, S2, Sγ] at e; linarith
  -- solve the linear first-order system
  have hp : 0 < P.thd + P.b := by positivity
  have hT : t P * P.thd = P.lam * (1 - P.lam) := by unfold t; field_simp
  have htau : tau P = t P * (P.thd + P.b) * (P.β * P.qh + (P.adh - P.adl)) ^ 2 := by
    unfold tau t; field_simp; ring
  have hγ2 : 2 * x.γ = (P.β * P.qh - (P.adh - P.adl)) * x.m := by
    rw [hρ] at Sγ
    have : t P * (2 * x.γ) = t P * ((P.β * P.qh - (P.adh - P.adl)) * x.m) := by linarith
    exact mul_left_cancel₀ hTpos.ne' this
  have hkey : x.m * denomS P = 2 * (P.thd + P.b) * P.w := by
    unfold denomS; rw [htau]
    rw [hρ] at S1
    have hN2 : 2 * (P.thd + P.b) * x.n = xi P * x.m := by linarith
    linear_combination (-2 * (P.thd + P.b)) * S1 + (xi P) * hN2 +
      ((P.thd + P.b) * t P * (P.β * P.qh - (P.adh - P.adl))) * hγ2
  have hden : 0 < denomS P := by
    have : 0 < x.m * denomS P := by rw [hkey]; positivity
    exact pos_of_mul_pos_right this hmS.le
  have hM : x.m = optMS P := by
    unfold optMS; rw [eq_div_iff hden.ne']; exact hkey
  refine ⟨?_, hM, ?_, ?_⟩
  · unfold optGammaS; rw [eq_div_iff hden.ne']
    have : 2 * x.γ * denomS P = (P.β * P.qh - (P.adh - P.adl)) * (x.m * denomS P) := by
      rw [hγ2]; ring
    rw [hkey] at this; linarith
  · unfold optNS; rw [eq_div_iff hden.ne']
    have : 2 * (P.thd + P.b) * x.n * denomS P = xi P * (x.m * denomS P) := by
      rw [show 2 * (P.thd + P.b) * x.n = xi P * x.m by linarith]; ring
    rw [hkey] at this
    have := mul_left_cancel₀ (show (2 * (P.thd + P.b)) ≠ 0 by positivity)
      (show 2 * (P.thd + P.b) * (x.n * denomS P) = 2 * (P.thd + P.b) * (xi P * P.w) by
        linarith)
    exact this
  · rw [hpS, hval, hM]; unfold optMS optProfitS; field_simp
