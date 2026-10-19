-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/e9cceb73-791a-472e-92c8-4da9c8def41c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdan_generator_sum_contraction

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ‖unitaryFinsetMarkov π S x‖ ≤
      kazhdanMarkovContractionFactor P S * ‖x‖ := by
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hsum := kazhdan_generator_sum_contraction
    P π S hone hsub x horth
  calc
    ‖unitaryFinsetMarkov π S x‖ =
        (S.card : ℝ)⁻¹ * ‖∑ g ∈ S, π g x‖ := by
      simp [unitaryFinsetMarkov, norm_smul, norm_inv]
    _ ≤ (S.card : ℝ)⁻¹ *
        (((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = (1 - P.kazhdanConstant ^ 2 /
        (4 * (S.card : ℝ))) * ‖x‖ := by
      field_simp
    _ ≤ kazhdanMarkovContractionFactor P S * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact le_max_right 0 _
end SoficGroups.KunThomInvariantOrthogonal
