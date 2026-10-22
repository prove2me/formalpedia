-- Prove2me | solution 1 for SmartPTO.Fisher.prop3_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:22:12.040552+00:00
-- url     : https://prove2.me/submissions/260cda28-aba0-465f-ad9e-0e0144286752

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting
set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory
open SmartPTO.Fisher

theorem gg_xi_le {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hScpt : IsCompact S)
    (u w : EuclideanSpace ℝ (Fin d)) (hw : w ∈ S) : ⟪u, w⟫_ℝ ≤ xi S u := by
  have hb : BddAbove ((fun w => ⟪u, w⟫_ℝ) '' S) :=
    (hScpt.image (continuous_const.inner continuous_id)).bddAbove
  exact le_csSup hb ⟨w, hw, rfl⟩

theorem gg_xi_le_of {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSne : S.Nonempty)
    (u : EuclideanSpace ℝ (Fin d)) (b : ℝ) (h : ∀ w ∈ S, ⟪u, w⟫_ℝ ≤ b) : xi S u ≤ b := by
  apply csSup_le (hSne.image _)
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun chat => spoPlusLoss S wstar chat c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [spoPlusLoss, smul_eq_mul]
  have hx : xi S (c - (2 : ℝ) • (a • x + b • y)) ≤
      a * xi S (c - (2 : ℝ) • x) + b * xi S (c - (2 : ℝ) • y) := by
    apply gg_xi_le_of S hSne
    intro w hwS
    have e : c - (2 : ℝ) • (a • x + b • y) =
        a • (c - (2 : ℝ) • x) + b • (c - (2 : ℝ) • y) := by
      have : c = a • c + b • c := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      simp only [smul_sub, smul_add, smul_smul]
      module
    rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h1 := gg_xi_le S hScpt (c - (2 : ℝ) • x) w hwS
    have h2 := gg_xi_le S hScpt (c - (2 : ℝ) • y) w hwS
    nlinarith
  have hl : ⟪a • x + b • y, wstar c⟫_ℝ = a * ⟪x, wstar c⟫_ℝ + b * ⟪y, wstar c⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hz : zstar S c = a * zstar S c + b * zstar S c := by
    rw [← add_mul, hab, one_mul]
  rw [hl]
  nlinarith
