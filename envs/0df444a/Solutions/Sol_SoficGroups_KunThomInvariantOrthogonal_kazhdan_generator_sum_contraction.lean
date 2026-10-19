-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_sum_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/54e56752-4117-401c-b395-247e39ac6ff5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_norm_add_le_two_sub_sq_div_four
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_norm_finset_sum_le_pair_add
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdan_generator_displacement_of_orthogonal_invariants

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
    ‖∑ g ∈ S, π g x‖ ≤
      ((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨g, hg, hgap⟩ :=
    kazhdan_generator_displacement_of_orthogonal_invariants
      P π x hx horth
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hupper : ‖π g x - x‖ ≤ 2 * ‖x‖ := by
    calc
      ‖π g x - x‖ ≤ ‖π g x‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖x‖ := by rw [(π g).norm_map]; ring
  have hκtwo : P.kazhdanConstant ≤ 2 :=
    le_of_mul_le_mul_right (hgap.trans hupper) hnormpos
  have hgone : g ≠ 1 := by
    intro h
    subst g
    have hpos : 0 < P.kazhdanConstant * ‖x‖ :=
      mul_pos P.positive hnormpos
    have hbad : P.kazhdanConstant * ‖x‖ ≤ 0 := by
      simpa using hgap
    exact not_le_of_gt hpos hbad
  have hpair :
      ‖x + π g x‖ ≤
        (2 - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
    apply norm_add_le_two_sub_sq_div_four x (π g x)
      P.kazhdanConstant P.positive.le hκtwo
      ((π g).norm_map x)
    rw [norm_sub_rev]
    exact hgap
  have hsum := norm_finset_sum_le_pair_add
    S (fun a : G => π a x) 1 g hone (hsub hg) (Ne.symm hgone)
    ‖x‖ (fun a _ => (π a).norm_map x)
  calc
    ‖∑ a ∈ S, π a x‖ ≤
        ‖π 1 x + π g x‖ + ((S.card : ℝ) - 2) * ‖x‖ := hsum
    _ = ‖x + π g x‖ + ((S.card : ℝ) - 2) * ‖x‖ := by
      simp
    _ ≤ (2 - P.kazhdanConstant ^ 2 / 4) * ‖x‖ +
        ((S.card : ℝ) - 2) * ‖x‖ :=
      add_le_add hpair (le_refl _)
    _ = ((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
      ring
end SoficGroups.KunThomInvariantOrthogonal
