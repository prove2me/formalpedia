-- Prove2me | solution 1 for PlatformQualReg.ExclSubsid.exclusion_special_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:07:45.992973+00:00
-- url     : https://prove2.me/submissions/0748d165-2805-45d9-ace6-fcd4d6d0794b

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
    (x : OutcomeE) (hx : FeasibleE P x)
    (hγ : 0 ≤ P.thd * x.n / P.lam - (P.adh - P.adl) * x.m) :
    let y : OutcomeS :=
      ⟨P.adl * x.m - P.b * x.n, x.pc,
        P.thd * x.n / P.lam - (P.adh - P.adl) * x.m, x.m, x.n⟩
    FeasibleS P y ∧ nl P y = 0 ∧ nh P y = x.n ∧
    profitS P y = profitE P x := by
  intro y
  have hP' := hP
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP'
  have hEeq := E_eq P hP x hx.1
  have hpd : x.pd = P.adh * x.m - x.n * (P.thd + P.lam * P.b) / P.lam := by
    have := congrArg OutcomeE.pd hEeq; simpa [outE] using this
  have hnl : nl P y = 0 := by simp only [y, nl]; ring
  have hnh : nh P y = x.n := by simp only [y, nh]; field_simp; ring
  refine ⟨⟨⟨?_, ?_⟩, hx.2.1, hx.2.2, hγ, hnl.ge, hnh ▸ hx.2.2⟩, hnl, hnh, ?_⟩
  · rw [hnl, hnh]; simp [y]
  · rw [hnh]; simpa [y] using hx.1.2
  · simp only [profitS, profitE, hnh]
    rw [hpd]; simp only [y]; field_simp; ring
