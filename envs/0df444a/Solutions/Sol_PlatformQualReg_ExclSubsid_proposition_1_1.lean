-- Prove2me | solution 1 for PlatformQualReg.ExclSubsid.proposition_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:10:07.902491+00:00
-- url     : https://prove2.me/submissions/df92014a-bb0a-409c-ae92-557537beb587

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
    (hcE : ConcaveE P) (hxi : 0 < xi1 P) :
    IsOptE P (outE P (optME P) (optNE P)) ∧
    (∀ x : OutcomeE, IsOptE P x → x.m = optME P ∧ x.n = optNE P) ∧
    profitE P (outE P (optME P) (optNE P)) = optProfitE P := by
  have hP' := hP
  obtain ⟨hl, hl1, hq, hc, hd, hadl, hb, hβ, hw⟩ := hP'
  have hK : 0 < P.thd + P.lam * P.b := by positivity
  -- positive definiteness of the quadratic part, from strict concavity
  have hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) →
      0 < P.thc * u ^ 2 - xi1 P * u * v + (P.thd + P.lam * P.b) / P.lam * v ^ 2 := by
    intro u v huv
    have hne : ((-u, -v) : ℝ × ℝ) ≠ (u, v) := by
      intro h
      apply huv
      simp only [Prod.mk.injEq] at h ⊢
      constructor <;> linarith [h.1, h.2]
    have := hcE.2 (Set.mem_univ _) (Set.mem_univ _) hne (by norm_num : (0:ℝ) < 1 / 2)
      (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
    rw [profitE_outE, profitE_outE, profitE_outE] at this
    have e : FE P (1 / 2 * -u + 1 / 2 * u) (1 / 2 * -v + 1 / 2 * v) -
        (1 / 2 * FE P (-u) (-v) + 1 / 2 * FE P u v) =
        P.thc * u ^ 2 - xi1 P * u * v + (P.thd + P.lam * P.b) / P.lam * v ^ 2 := by
      unfold FE; ring
    linarith
  have hQ0 : ∀ u v : ℝ,
      0 ≤ P.thc * u ^ 2 - xi1 P * u * v + (P.thd + P.lam * P.b) / P.lam * v ^ 2 := by
    intro u v
    by_cases h : (u, v) = (0, 0)
    · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; ring_nf; rfl
    · exact (hQ u v h).le
  have hden : 0 < denomE P := by
    have := hQ (xi1 P) (2 * P.thc) (by
      intro h; simp only [Prod.mk.injEq] at h; linarith [h.2])
    have e : P.thc * xi1 P ^ 2 - xi1 P * xi1 P * (2 * P.thc) +
        (P.thd + P.lam * P.b) / P.lam * (2 * P.thc) ^ 2 = P.thc / P.lam * denomE P := by
      unfold denomE; field_simp; ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_left (div_pos hc hl)).1 this
  have hmo : 0 < optME P := by unfold optME; positivity
  have hno : 0 < optNE P := by unfold optNE; positivity
  -- value gap is the quadratic form of the displacement
  have hg1 : P.w + xi1 P * optNE P - 2 * P.thc * optME P = 0 := by
    have hd0 : denomE P ≠ 0 := hden.ne'
    unfold optME optNE
    field_simp
    unfold denomE; ring
  have hg2 : xi1 P * optME P - 2 * ((P.thd + P.lam * P.b) / P.lam) * optNE P = 0 := by
    have hd0 : denomE P ≠ 0 := hden.ne'
    unfold optME optNE
    field_simp
    ring
  have hgap : ∀ m n : ℝ, FE P (optME P) (optNE P) - FE P m n =
      P.thc * (m - optME P) ^ 2 - xi1 P * (m - optME P) * (n - optNE P) +
        (P.thd + P.lam * P.b) / P.lam * (n - optNE P) ^ 2 := by
    intro m n
    have e : FE P (optME P) (optNE P) - FE P m n =
        P.thc * (m - optME P) ^ 2 - xi1 P * (m - optME P) * (n - optNE P) +
        (P.thd + P.lam * P.b) / P.lam * (n - optNE P) ^ 2 -
        (P.w + xi1 P * optNE P - 2 * P.thc * optME P) * (m - optME P) -
        (xi1 P * optME P - 2 * ((P.thd + P.lam * P.b) / P.lam) * optNE P) * (n - optNE P) := by
      unfold FE; ring
    rw [e, hg1, hg2]; ring
  have hopt : IsOptE P (outE P (optME P) (optNE P)) := by
    refine ⟨⟨consE_outE P hP _ _, hmo.le, hno.le⟩, fun y hy => ?_⟩
    have hpy : profitE P y = FE P y.m y.n := by rw [← profitE_outE, ← E_eq P hP y hy.1]
    rw [hpy, profitE_outE]
    have := hgap y.m y.n
    have := hQ0 (y.m - optME P) (y.n - optNE P)
    linarith
  refine ⟨hopt, fun x hx => ?_, ?_⟩
  · have hpx : profitE P x = FE P x.m x.n := by rw [← profitE_outE, ← E_eq P hP x hx.1.1]
    have h1 := hx.2 _ hopt.1
    rw [hpx, profitE_outE] at h1
    have h2 := hgap x.m x.n
    by_contra hne
    have hne' : (x.m - optME P, x.n - optNE P) ≠ (0, 0) := by
      intro h; apply hne; simp only [Prod.mk.injEq] at h; constructor <;> linarith [h.1, h.2]
    have := hQ _ _ hne'
    linarith
  · rw [profitE_outE]
    have e : FE P (optME P) (optNE P) = P.w * optME P / 2 +
        ((P.w + xi1 P * optNE P - 2 * P.thc * optME P) * optME P +
          (xi1 P * optME P - 2 * ((P.thd + P.lam * P.b) / P.lam) * optNE P) * optNE P) / 2 := by
      unfold FE; ring
    rw [e, hg1, hg2]
    have hd0 : denomE P ≠ 0 := hden.ne'
    unfold optME optProfitE
    field_simp
    ring
