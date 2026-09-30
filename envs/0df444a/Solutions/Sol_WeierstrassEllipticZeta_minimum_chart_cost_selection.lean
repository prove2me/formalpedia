-- Prove2me | solution 1 for WeierstrassEllipticZeta.minimum_chart_cost_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T19:03:53.355888+00:00
-- url     : https://prove2.me/submissions/fb10a293-7a7b-4e65-8139-dd9618f0653b

import Definitions.Def_WeierstrassEllipticZeta_MinimumChartCost
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology Pointwise Classical
namespace WeierstrassEllipticZeta

private lemma sigma_second_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv D.sigma) z =
      (weierstrassZeta L z ^ 2 - L.weierstrassP z) * D.sigma z := by
  have heq : deriv D.sigma =ᶠ[𝓝 z] fun w ↦ weierstrassZeta L w * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (D.hasDerivAt w hw).deriv
  have h := ((hζ z hz).mul (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

private lemma sigma_third_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv (deriv D.sigma)) z =
      (weierstrassZeta L z ^ 3 - 3 * weierstrassZeta L z * L.weierstrassP z -
        L.derivWeierstrassP z) * D.sigma z := by
  have heq : deriv (deriv D.sigma) =ᶠ[𝓝 z]
      fun w ↦ (weierstrassZeta L w ^ 2 - L.weierstrassP w) * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact sigma_second_deriv L D hζ w hw
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have h := ((((hζ z hz).pow 2).sub hp).mul
    (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

private lemma normalized_origin_chart
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    S 2 0 = -2 := by
  let J : ℂ → ℂ := fun z => -2 * deriv D.sigma z ^ 3 +
    3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z -
    D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z
  have hJ : AnalyticOnNhd ℂ J Set.univ := by
    intro z _
    have h0 := D.entire.analyticAt z
    have h1 := h0.deriv
    have h2 := h1.deriv
    have h3 := h2.deriv
    exact (((analyticAt_const.mul (h1.pow 3)).add
      (((analyticAt_const.mul h0).mul h1).mul h2))).sub ((h0.pow 2).mul h3)
  have hSJ : S 2 = J := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS 2) hJ (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    rw [hS_value z hz 2]
    have h1 := (D.hasDerivAt z hz).deriv
    have h2 := sigma_second_deriv L D (hasDerivAt_weierstrassZeta L) z hz
    have h3 := sigma_third_deriv L D (hasDerivAt_weierstrassZeta L) z hz
    simp [J, h1, h2, h3]
    ring
  simp [hSJ, J, D.zero, D.deriv_zero.deriv]

private lemma mem_validChartPoints (S : Fin 5 → ℂ → ℂ) (X : Finset ℂ)
    (p : Fin 2 × ℂ) :
    p ∈ validChartPoints S X ↔
      p.2 ∈ X + X + X ∧ S (extensionChartDenominator p.1) p.2 ≠ 0 := by
  simp [validChartPoints]

private lemma minimumChartCost_le (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (X : Finset ℂ)
    (p : Fin 2 × ℂ) (hp : p ∈ validChartPoints S X) :
    minimumChartCost L S Q N T X ≤ cappedChartCost L S Q N T p.1 p.2 := by
  rw [minimumChartCost, dif_pos ⟨p, hp⟩]
  exact Finset.inf'_le _ hp

private lemma minimumChartCost_attained (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (X : Finset ℂ)
    (h : (validChartPoints S X).Nonempty) :
    ∃ p ∈ validChartPoints S X,
      cappedChartCost L S Q N T p.1 p.2 = minimumChartCost L S Q N T X := by
  obtain ⟨p, hp, hmin⟩ := (validChartPoints S X).exists_min_image
    (fun p => cappedChartCost L S Q N T p.1 p.2) h
  refine ⟨p, hp, le_antisymm ?_ (minimumChartCost_le L S Q N T X p hp)⟩
  rw [minimumChartCost, dif_pos h]
  exact Finset.le_inf' _ _ hmin


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    S 2 0 = -2 ∧ ∀ (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (X : Finset ℂ),
      0 ∈ X →
      (validChartPoints S X).Nonempty ∧
      (validChartPoints S X).card ≤ 2 * (X + X + X).card ∧
      1 ≤ minimumChartCost L S Q N T X ∧
      minimumChartCost L S Q N T X ≤ cappedChartCost L S Q N T 1 0 ∧
      (∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
        S (extensionChartDenominator c) z ≠ 0 ∧
        cappedChartCost L S Q N T c z = minimumChartCost L S Q N T X) ∧
      (∀ (W : ℕ) (R : ℝ),
        (∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
          S (extensionChartDenominator c) z ≠ 0 ∧
          ((W * cappedChartCost L S Q N T c z : ℕ) : ℝ) ≤ R) ↔
        ((W * minimumChartCost L S Q N T X : ℕ) : ℝ) ≤ R) := by
  have horigin := normalized_origin_chart L D S hS hS_value
  refine ⟨horigin, ?_⟩
  intro Q N T X h0
  have h00 : (0 : ℂ) ∈ X + X := by simpa using Finset.add_mem_add h0 h0
  have h000 : (0 : ℂ) ∈ X + X + X := by simpa using Finset.add_mem_add h00 h0
  have hden : S (extensionChartDenominator 1) 0 ≠ 0 := by
    simp [extensionChartDenominator, horigin]
  have hp0 : ((1 : Fin 2), (0 : ℂ)) ∈ validChartPoints S X :=
    (mem_validChartPoints S X _).mpr ⟨h000, hden⟩
  have hnonempty : (validChartPoints S X).Nonempty := ⟨_, hp0⟩
  obtain ⟨p, hp, heq⟩ := minimumChartCost_attained L S Q N T X hnonempty
  have hpvalid := (mem_validChartPoints S X p).mp hp
  have hatt : ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
      S (extensionChartDenominator c) z ≠ 0 ∧
      cappedChartCost L S Q N T c z = minimumChartCost L S Q N T X :=
    ⟨p.1, p.2, hpvalid.1, hpvalid.2, heq⟩
  have hupper := minimumChartCost_le L S Q N T X (1, 0) hp0
  refine ⟨hnonempty, ?_, ?_, hupper, hatt, ?_⟩
  · calc
      (validChartPoints S X).card ≤ ((Finset.univ : Finset (Fin 2)) ×ˢ
          (X + X + X)).card :=
        Finset.card_filter_le _ _
      _ = 2 * (X + X + X).card := by simp
  · rw [← heq]
    exact le_max_left _ _
  · intro W R
    constructor
    · rintro ⟨c, z, hz, hd, hb⟩
      have hle := minimumChartCost_le L S Q N T X (c, z)
        ((mem_validChartPoints S X _).mpr ⟨hz, hd⟩)
      have hw : ((W * minimumChartCost L S Q N T X : ℕ) : ℝ) ≤
          ((W * cappedChartCost L S Q N T c z : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left W hle
      exact hw.trans hb
    · intro hb
      refine ⟨p.1, p.2, hpvalid.1, hpvalid.2, ?_⟩
      rw [heq]
      exact hb
