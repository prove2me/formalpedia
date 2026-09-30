-- Prove2me | solution 2 for WeierstrassEllipticZeta.finite_set_projective_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T03:12:37.468779+00:00
-- url     : https://prove2.me/submissions/4f52e41b-d8ea-4c9e-b969-373b9db78e89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_minimum_weight_budget_scalar_obstruction
import Theorems.Thm_WeierstrassEllipticZeta_fibre_optimizer_section_cost_bound
import Theorems.Thm_WeierstrassEllipticZeta_fibre_present_minimum_anchor_weight
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_fibre_anchor_wp_spectrum_bound
import Theorems.Thm_WeierstrassEllipticZeta_finite_fibre_anchor_enumeration
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_uniform_jet_cap
import Theorems.Thm_WeierstrassEllipticZeta_closed_parallelepiped_wp_root_count_sharp_boundary
import Theorems.Thm_WeierstrassEllipticZeta_closed_parallelepiped_wp_root_count
import Theorems.Thm_WeierstrassEllipticZeta_minimum_chart_cost_contact_lower_bound
import Mathlib.Tactic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

open scoped Classical

private lemma scalar_bridge_compact_region (L : PeriodPair) :
    IsCompact {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} ∧
      (0 : ℂ) ∈ {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} := by
  refine ⟨L.basis.parallelepiped.isCompact.inter_right
    (isClosed_le continuous_norm continuous_const), ?_⟩
  constructor
  · change (0 : ℂ) ∈ _root_.parallelepiped L.basis
    rw [mem_parallelepiped_iff]
    exact ⟨0, by simp, by simp⟩
  · simpa using add_nonneg (norm_nonneg L.ω₁) (norm_nonneg L.ω₂)

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∃ K : Submodule ℤ ℂ, ∃ a b : ℕ,
          ((a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ L.lattice)) ∧ b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by
  classical
  obtain ⟨η, hη, _⟩ := elliptic_extension_group_geometry L
  obtain ⟨B, _, _, hBfull⟩ := elliptic_chart_uniform_jet_cap L
  have hB : ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      ∀ (c : Fin 2) (t : ℕ), extensionChartJetIdeal L Q c t =
        extensionChartJetIdeal L Q c (min t (B (m + 2 * n))) := by
    intro m n Q hQ c t
    exact (hBfull m n Q hQ c t).1
  obtain ⟨C, hC, hbound⟩ := fibre_optimizer_section_cost_bound L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨10 * C, by positivity, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  have hregion := scalar_bridge_compact_region L
  obtain ⟨Z, hZ⟩ := (finite_fibre_anchor_enumeration L.lattice η X S hS Q m n hQ hne
    {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖}
    hregion.1 hregion.2).1
  obtain ⟨H, hH, hdeg, hcard, hroots⟩ := fibre_anchor_wp_spectrum_bound
    L D S hS hS_value hS_ne Q m n hn hQ hne
  have hp0 := (closed_parallelepiped_wp_root_count L Z
    (fun z hz => ((hZ z).mp hz).1.1) H hH
    (fun z hz hnz => hroots z hnz ((hZ z).mp hz).2)).1
  have hc0 := closed_parallelepiped_wp_root_count_sharp_boundary L Z
    (fun z hz => ((hZ z).mp hz).1.1) H hH
    (fun z hz hnz => hroots z hnz ((hZ z).mp hz).2)
  have hp : (L.lattice.mkQ '' (Z : Set ℂ)).ncard ≤ 8 * n + 1 := by omega
  have hc : Z.card ≤ 16 * n + 4 := by omega
  have hbudget := hbound m n U hm hn hU X h0 Q hQ hne hhigh H hH hdeg hcard hroots Z hZ hp hc
  have hs := fibre_present_minimum_anchor_weight L.lattice η X S Q m n
    {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z
  have hw : minimumAnchorWeight L.lattice η X S Q m n
      {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z =
      (if X.card ≤ (m + 1) * (X.image L.lattice.mkQ).card then X.card
       else if Z.Nonempty then (m + 1) * (X.image L.lattice.mkQ).card
       else minimumAnchorWeight L.lattice η X S Q m n
         {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z) := by
    split_ifs with hpoint hfibre
    · exact hs.2.1 hpoint
    · rw [hs.2.2 hfibre, Nat.min_eq_right (by omega)]
    · rfl
  rw [← hw] at hbudget
  have hcontact := (minimum_chart_cost_contact_lower_bound L D S hS hS_value hS_ne
    Q n (B (m + 2 * n)) U X h0 (fun d hd => (hQ d hd).2) hne
    (hB m n Q hQ) (fun z hz c hc => hhigh z hz (extensionChartDenominator c) hc)).2.2
  rcases minimum_weight_budget_scalar_obstruction L η X S Q m n U
    (minimumChartCost L S Q (B (m + 2 * n)) U X)
    {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z C
    hm hn hC.le hcontact hbudget with hpoint | hperiod
  · refine ⟨⊥, 1, 2, Or.inl ⟨rfl, rfl⟩, le_rfl, ?_⟩
    have hinj : Function.Injective (⊥ : Submodule ℤ ℂ).mkQ := by
      intro x y hxy
      have h := (Submodule.Quotient.eq (⊥ : Submodule ℤ ℂ)).mp hxy
      exact sub_eq_zero.mp (by simpa using h)
    simpa only [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, pow_one] using hpoint
  · refine ⟨L.lattice, 0, 2, Or.inr ⟨rfl, le_rfl⟩, le_rfl, ?_⟩
    have hq : (L.lattice.mkQ '' (X : Set ℂ)).ncard = (X.image L.lattice.mkQ).card := by
      rw [← Finset.coe_image, Set.ncard_coe_finset]
    simp only [hq, pow_zero, mul_one]
    exact hperiod.trans (by nlinarith [sq_nonneg (n : ℝ)])

