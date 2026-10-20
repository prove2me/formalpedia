-- Prove2me | solution 1 for PlatformQualReg.ExclSubsid.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:04:27.48999+00:00
-- url     : https://prove2.me/submissions/2b4226d6-8f43-4463-9a70-b7bf726b4ae1

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

lemma algebra (a c L B D ξ ξ1 T w thc m n M N Γ : ℝ) (ha : 0 < a) (hc : 0 < c) (hL : 0 < L)
    (hL1 : L < 1) (hBD : D ≤ B) (hT : T * a = L * (1 - L)) (hTpos : 0 < T) (hw : 0 < w)
    (hξ1 : ξ1 = ξ + (1 - L) * (D + B)) (hm : 0 < m) (hn : 0 < n) (hM : 0 < M) (hN : 0 < N)
    (E1 : w + ξ1 * n - 2 * thc * m = 0) (E2 : ξ1 * m - 2 * ((a + L * c) / L) * n = 0)
    (S1 : w + ξ * N - 2 * thc * M + 2 * B * (T * D) * M + B * T * Γ - (T * D) * Γ = 0)
    (S2 : ξ * M - 2 * (a + c) * N = 0) (S3 : B * T * M - (T * D) * M - 2 * T * Γ ≤ 0)
    (NL : 0 < (1 - L) * N - (T * D) * M - T * Γ) :
    0 ≤ a * n / L - D * m ∧ m < M ∧ n < N := by
  subst hξ1
  have hK : 0 < a + L * c := by positivity
  have h1L : 0 < 1 - L := by linarith
  have E2' : 2 * (a + L * c) * n = L * (ξ + (1 - L) * (D + B)) * m := by
    field_simp at E2; linarith
  have hS3' : (B - D) * M ≤ 2 * Γ := by
    have : T * ((B - D) * M) ≤ T * (2 * Γ) := by linarith
    exact le_of_mul_le_mul_left this hTpos
  have hA0 : T * M * (D + B) < 2 * (1 - L) * N := by linarith
  have hA : 0 < a * ξ - L * (D + B) * (a + c) := by
    have e : (1 - L) * M * (a * ξ - L * (D + B) * (a + c)) =
        a * (a + c) * (2 * (1 - L) * N - T * M * (D + B)) := by
      linear_combination (1 - L) * a * S2 + M * (D + B) * (a + c) * hT
    have : 0 < (1 - L) * M * (a * ξ - L * (D + B) * (a + c)) := by
      rw [e]; exact mul_pos (by positivity) (by linarith)
    exact pos_of_mul_pos_right this (mul_nonneg h1L.le hM.le)
  refine ⟨?_, ?_⟩
  · have hx : 0 < a * (ξ + (1 - L) * (D + B)) - 2 * (a + L * c) * D := by
      nlinarith [hA, mul_nonneg (sub_nonneg.2 hBD) hK.le]
    have e2 : 2 * (a + L * c) * (a * n - L * D * m) =
        L * m * (a * (ξ + (1 - L) * (D + B)) - 2 * (a + L * c) * D) := by
      linear_combination a * E2'
    have h3 : 0 ≤ 2 * (a + L * c) * (a * n - L * D * m) := by
      rw [e2]; exact mul_nonneg (mul_nonneg hL.le hm.le) hx.le
    have h4 : 0 ≤ a * n - L * D * m := (mul_nonneg_iff_of_pos_left (by positivity)).1 h3
    have e5 : a * n / L - D * m = (a * n - L * D * m) / L := by field_simp
    rw [e5]; exact div_nonneg h4 hL.le
  have hn' : n = L * (ξ + (1 - L) * (D + B)) * m / (2 * (a + L * c)) := by
    field_simp; linarith [E2']
  have hN' : N = ξ * M / (2 * (a + c)) := by
    field_simp; linarith [S2]
  set brE := 2 * thc - L * (ξ + (1 - L) * (D + B)) ^ 2 / (2 * (a + L * c)) with hbrE
  set brS := 2 * thc - ξ ^ 2 / (2 * (a + c)) - T * (D + B) ^ 2 / 2 with hbrS
  have hwE : w = m * brE := by
    have : w = 2 * thc * m - (ξ + (1 - L) * (D + B)) * n := by linarith
    rw [this, hn', hbrE]; field_simp
  have hq : 0 ≤ T * (B - D) * (2 * Γ - (B - D) * M) :=
    mul_nonneg (mul_nonneg hTpos.le (sub_nonneg.2 hBD)) (by linarith)
  have hwS : w ≤ M * brS := by
    have h0 : w = 2 * thc * M - ξ * N - 2 * B * (T * D) * M - B * T * Γ + T * D * Γ := by
      linarith
    have key : M * brS - w = T * (B - D) * (2 * Γ - (B - D) * M) / 2 := by
      rw [h0, hN', hbrS]; field_simp; ring
    linarith
  have hT' : T = L * (1 - L) / a := by field_simp; linarith
  have hdiff : brE - brS = (1 - L) * (a * ξ - L * (D + B) * (a + c)) ^ 2 /
      (2 * (a + c) * a * (a + L * c)) := by
    rw [hbrE, hbrS, hT']; field_simp; ring
  have hpos : 0 < brE - brS := by
    rw [hdiff]; exact div_pos (mul_pos h1L (pow_pos hA 2)) (by positivity)
  have hbrEpos : 0 < brE := pos_of_mul_pos_right (hwE ▸ hw) hm.le
  have hmM : m < M := by
    by_contra h
    have h' : M ≤ m := le_of_not_gt h
    have := mul_le_mul_of_nonneg_right h' hbrEpos.le
    have := mul_lt_mul_of_pos_left (show brS < brE by linarith) hM
    linarith
  refine ⟨hmM, ?_⟩
  have hξ1pos : 0 < ξ + (1 - L) * (D + B) := by
    have h0 : 0 < (L * m) * (ξ + (1 - L) * (D + B)) := by
      have : 0 < 2 * (a + L * c) * n := by positivity
      linarith
    exact (pos_iff_pos_of_mul_pos h0).1 (by positivity)
  have e3 : 2 * (a + c) * (a + L * c) * (N - n) =
      (1 - L) * (a * ξ - L * (D + B) * (a + c)) * M +
        (a + c) * L * (ξ + (1 - L) * (D + B)) * (M - m) := by
    linear_combination (-(a + L * c)) * S2 - (a + c) * E2'
  have h5 : 0 < 2 * (a + c) * (a + L * c) * (N - n) := by
    rw [e3]
    have := mul_pos (mul_pos h1L hA) hM
    have := mul_pos (mul_pos (mul_pos (by positivity : (0:ℝ) < a + c) hL) hξ1pos)
      (show 0 < M - m by linarith)
    linarith
  have := (mul_pos_iff_of_pos_left (by positivity)).1 h5
  linarith

end PlatformQualReg.ExclSubsid.P4Aux

open PlatformQualReg.ExclSubsid PlatformQualReg.ExclSubsid.P4Aux in
theorem solution (P : Params) (hP : P.Standing)
    (hcE : ConcaveE P) (hcS : ConcaveS P)
    (hsub : P.adh - P.adl ≤ P.β * P.qh)
    (xE : OutcomeE) (hxE : IsOptE P xE) (hintE : 0 < xE.m ∧ 0 < xE.n)
    (xS : OutcomeS) (hxS : IsOptS P xS)
    (hintS : 0 < xS.m ∧ 0 < nl P xS ∧ 0 < nh P xS) :
    profitE P xE ≤ profitS P xS ∧
    (∃ y : OutcomeS, FeasibleS P y ∧ nl P y = 0 ∧ nh P y = xE.n ∧
      y.m = xE.m ∧ y.n = xE.n ∧ profitS P y = profitE P xE) ∧
    avgQualityS P xS ≤ P.qh ∧
    xE.m < xS.m ∧ xE.n < xS.n := by
  have hP' := hP
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP'
  have h1L : 0 < 1 - P.lam := by linarith
  obtain ⟨hmE, hnE⟩ := hintE
  obtain ⟨hmS, hnlS, hnhS⟩ := hintS
  -- exclusion side
  have hEeq := E_eq P hP xE hxE.1.1
  have hpE : profitE P xE = FE P xE.m xE.n := by rw [← profitE_outE, ← hEeq]
  have hoptE : ∀ m' n', 0 ≤ m' → 0 ≤ n' → FE P m' n' ≤ FE P xE.m xE.n := by
    intro m' n' h1 h2
    have := hxE.2 (outE P m' n') ⟨consE_outE P hP m' n', h1, h2⟩
    rwa [profitE_outE, hpE] at this
  have E1 : P.w + xi1 P * xE.n - 2 * P.thc * xE.m = 0 := by
    apply two_sided_ev (c := P.thc)
    filter_upwards [ev_pos 1 hmE] with ε hε
    have := hoptE (xE.m + ε) xE.n (by linarith) hnE.le
    have e : FE P (xE.m + ε) xE.n - FE P xE.m xE.n =
        ε * (P.w + xi1 P * xE.n - 2 * P.thc * xE.m) - P.thc * ε ^ 2 := by unfold FE; ring
    linarith
  have E2 : xi1 P * xE.m - 2 * ((P.thd + P.lam * P.b) / P.lam) * xE.n = 0 := by
    apply two_sided_ev (c := (P.thd + P.lam * P.b) / P.lam)
    filter_upwards [ev_pos 1 hnE] with ε hε
    have := hoptE xE.m (xE.n + ε) hmE.le (by linarith)
    have e : FE P xE.m (xE.n + ε) - FE P xE.m xE.n =
        ε * (xi1 P * xE.m - 2 * ((P.thd + P.lam * P.b) / P.lam) * xE.n) -
          (P.thd + P.lam * P.b) / P.lam * ε ^ 2 := by unfold FE; ring
    linarith
  -- subsidization side
  have hSeq := S_eq P hP xS hxS.1.1
  have hpS : profitS P xS = GS P xS.m xS.n xS.γ := by rw [← profitS_outS P hP, ← hSeq]
  have hnlS' : nl P xS = (1 - P.lam) * xS.n - rho P * xS.m - t P * xS.γ := by
    rw [← nl_outS P hP, ← hSeq]
  have hnhS' : nh P xS = P.lam * xS.n + rho P * xS.m + t P * xS.γ := by
    rw [← nh_outS P hP, ← hSeq]
  have hNL : 0 < (1 - P.lam) * xS.n - rho P * xS.m - t P * xS.γ := hnlS' ▸ hnlS
  have hNH : 0 < P.lam * xS.n + rho P * xS.m + t P * xS.γ := hnhS' ▸ hnhS
  have hNpos : 0 < xS.n := by linarith
  have hΓ : 0 ≤ xS.γ := hxS.1.2.2.2.1
  have hoptS : ∀ m' n' γ', 0 ≤ m' → 0 ≤ n' → 0 ≤ γ' →
      0 ≤ (1 - P.lam) * n' - rho P * m' - t P * γ' →
      0 ≤ P.lam * n' + rho P * m' + t P * γ' → GS P m' n' γ' ≤ GS P xS.m xS.n xS.γ := by
    intro m' n' γ' h1 h2 h3 h4 h5
    have := hxS.2 (outS P m' n' γ') (feasS_outS P hP m' n' γ' h1 h2 h3 h4 h5)
    rwa [profitS_outS P hP, hpS] at this
  have S1 : P.w + xi P * xS.n - 2 * P.thc * xS.m + 2 * (P.β * P.qh) * rho P * xS.m +
      (P.β * P.qh) * t P * xS.γ - rho P * xS.γ = 0 := by
    apply two_sided_ev (c := P.thc - P.β * P.qh * rho P)
    filter_upwards [ev_pos 1 hmS, ev_pos (-rho P) hNL, ev_pos (rho P) hNH] with ε h1 h2 h3
    have := hoptS (xS.m + ε) xS.n xS.γ (by linarith) hNpos.le hΓ (by linarith) (by linarith)
    have e : GS P (xS.m + ε) xS.n xS.γ - GS P xS.m xS.n xS.γ =
        ε * (P.w + xi P * xS.n - 2 * P.thc * xS.m + 2 * (P.β * P.qh) * rho P * xS.m +
          (P.β * P.qh) * t P * xS.γ - rho P * xS.γ) -
          (P.thc - P.β * P.qh * rho P) * ε ^ 2 := by unfold GS; ring
    linarith
  have S2 : xi P * xS.m - 2 * (P.thd + P.b) * xS.n = 0 := by
    apply two_sided_ev (c := P.thd + P.b)
    filter_upwards [ev_pos 1 hNpos, ev_pos (1 - P.lam) hNL, ev_pos P.lam hNH] with ε h1 h2 h3
    have := hoptS xS.m (xS.n + ε) xS.γ hmS.le (by linarith) hΓ (by linarith) (by linarith)
    have e : GS P xS.m (xS.n + ε) xS.γ - GS P xS.m xS.n xS.γ =
        ε * (xi P * xS.m - 2 * (P.thd + P.b) * xS.n) - (P.thd + P.b) * ε ^ 2 := by
      unfold GS; ring
    linarith
  have S3 : (P.β * P.qh) * t P * xS.m - rho P * xS.m - 2 * t P * xS.γ ≤ 0 := by
    apply one_sided_ev (c := t P)
    filter_upwards [ev_pos (-t P) hNL, ev_pos (t P) hNH] with ε h2 h3 h0
    have := hoptS xS.m xS.n (xS.γ + ε) hmS.le hNpos.le (by linarith) (by linarith) (by linarith)
    have e : GS P xS.m xS.n (xS.γ + ε) - GS P xS.m xS.n xS.γ =
        ε * ((P.β * P.qh) * t P * xS.m - rho P * xS.m - 2 * t P * xS.γ) - t P * ε ^ 2 := by
      unfold GS; ring
    linarith
  have hρ : rho P = t P * (P.adh - P.adl) := by unfold rho t; ring
  have hT : t P * P.thd = P.lam * (1 - P.lam) := by unfold t; field_simp
  have hTpos : 0 < t P := by unfold t; exact div_pos (mul_pos hl h1L) hd
  have hξ1 : xi1 P = xi P + (1 - P.lam) * ((P.adh - P.adl) + P.β * P.qh) := by
    unfold xi1 xi abar; ring
  rw [hρ] at S1 S3 hNL
  obtain ⟨hγE, hmlt, hnlt⟩ := algebra P.thd P.b P.lam (P.β * P.qh) (P.adh - P.adl) (xi P)
    (xi1 P) (t P) P.w P.thc xE.m xE.n xS.m xS.n xS.γ hd hb hl hl1 hsub hT hTpos hw hξ1
    hmE hnE hmS hNpos E1 E2 S1 S2 S3 hNL
  -- replication
  have hpd : xE.pd = P.adh * xE.m - xE.n * (P.thd + P.lam * P.b) / P.lam := by
    have := congrArg OutcomeE.pd hEeq; simpa [outE] using this
  set y : OutcomeS := ⟨P.adl * xE.m - P.b * xE.n, xE.pc,
    P.thd * xE.n / P.lam - (P.adh - P.adl) * xE.m, xE.m, xE.n⟩ with hy
  have hnl : nl P y = 0 := by simp only [hy, nl]; ring
  have hnh : nh P y = xE.n := by simp only [hy, nh]; field_simp; ring
  have hyF : FeasibleS P y := by
    refine ⟨⟨?_, ?_⟩, hmE.le, hnE.le, hγE, hnl.ge, hnh ▸ hnE.le⟩
    · rw [hnl, hnh]; simp [hy]
    · rw [hnh]; simpa [hy] using hxE.1.1.2
  have hyP : profitS P y = profitE P xE := by
    simp only [profitS, profitE, hnh]
    rw [hpd]; simp only [hy]; field_simp; ring
  refine ⟨?_, ⟨y, hyF, hnl, hnh, rfl, rfl, hyP⟩, ?_, hmlt, hnlt⟩
  · rw [← hyP]; exact hxS.2 y hyF
  · have hn := hxS.1.1.1
    rw [avgQualityS, div_le_iff₀ hNpos]
    nlinarith [mul_pos hnlS hq]
