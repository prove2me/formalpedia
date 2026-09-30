-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_locus_stabilizer_construction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T06:08:45.396984+00:00
-- url     : https://prove2.me/submissions/926ebc7e-42c4-4aa3-a4c8-2bb3de7d2399

import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
import Theorems.Thm_WeierstrassEllipticZeta_translated_subgroup_polynomial_constraint
import Theorems.Thm_WeierstrassEllipticZeta_linear_analytic_subgroup_degree_profile
import Mathlib.Tactic.NormNum

noncomputable section
open MvPolynomial WeierstrassEllipticZeta TranscendenceTheory
open scoped Classical

namespace WeierstrassEllipticZeta

private lemma directions_maximal (W : Set (Fin 3 → ℂ)) (U : Submodule ℂ (Fin 3 → ℂ)) :
    U ≤ linearTranslationDirections W ↔ ∀ w ∈ W, ∀ v ∈ U, w + v ∈ W := by
  constructor
  · intro h w hw v hv
    have hh := h hv
    change ∀ t : ℂ, ∀ w ∈ W, w + t • v ∈ W at hh
    simpa using hh 1 w hw
  · intro h v hv
    change ∀ t : ℂ, ∀ w ∈ W, w + t • v ∈ W
    intro t w hw
    exact h w hw (t • v) (U.smul_mem t hv)

private lemma translation_image_mem (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (W : Set (Fin 3 → ℂ)) (g : GraphExtensionGroup Λ η) :
    g ∈ linearTranslationImage Λ η W ↔ ∃ v ∈ linearTranslationDirections W,
      g = (v 0, (extensionPeriodGraph Λ η).mkQ (v 1, v 2)) := by
  change (∃ v, v ∈ linearTranslationDirections W ∧ extensionCoveringMap Λ η v = g) ↔ _
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, h.symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, h.symm⟩


end WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (W : Set (Fin 3 → ℂ)) (hW : W.Nonempty)
    (hWQ : ∀ w ∈ W,
      eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
        S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) :
    let V := linearTranslationDirections W
    let H := linearTranslationImage L.lattice η W
    (∀ g, g ∈ H ↔ ∃ v ∈ V,
      g = (v 0, (extensionPeriodGraph L.lattice η).mkQ (v 1, v 2))) ∧
    (∀ U : Submodule ℂ (Fin 3 → ℂ), U ≤ V ↔ ∀ w ∈ W, ∀ v ∈ U, w + v ∈ W) ∧
    ∃ r ∈ W,
      (∀ v ∈ V,
        eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1), S 2 (r 1 + v 1),
          S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
          S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0) ∧
      H ≠ ⊤ ∧ ∃ a : ℕ,
        (∀ m : ℝ, m ^ a = if (∀ v ∈ V, v 0 = 0) then m else 1) ∧
        ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
          (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) := by
  classical
  let V := linearTranslationDirections W
  let H := linearTranslationImage L.lattice η W
  have hH := translation_image_mem L.lattice η W
  obtain ⟨r, hr⟩ := hW
  have hvanish (v : Fin 3 → ℂ) (hv : v ∈ V) :
      eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1), S 2 (r 1 + v 1),
        S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
        S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0 := by
    have hrv : r + v ∈ W := by
      change ∀ t : ℂ, ∀ w ∈ W, w + t • v ∈ W at hv
      simpa using hv 1 r hr
    simpa only [Pi.add_apply] using hWQ (r + v) hrv
  obtain ⟨P, hproper, hP⟩ := translated_subgroup_polynomial_constraint L D S
    hS hS_value hS_ne Q n hQ hne V r hvanish
  obtain ⟨a, ha, hprofile⟩ := linear_analytic_subgroup_degree_profile L η V H hH
    P hproper hP
  have hHproper : H ≠ ⊤ := by
    intro htop
    have hg : extensionCurve L.lattice η (L.ω₁ / 2) ∈ H := by simp [htop]
    rcases hprofile with ⟨_, hker⟩ | ⟨_, hker⟩
    · have hh := hker hg
      change L.ω₁ / 2 = 0 at hh
      exact (div_ne_zero (L.indep.ne_zero (0 : Fin 2)) (by norm_num : (2 : ℂ) ≠ 0)) hh
    · have hh := hker hg
      change L.lattice.mkQ (L.ω₁ / 2) = 0 at hh
      exact L.ω₁_div_two_notMem_lattice ((Submodule.Quotient.mk_eq_zero _).mp hh)
  exact ⟨hH, directions_maximal W, r, hr, hvanish, hHproper, a, ha, hprofile⟩
