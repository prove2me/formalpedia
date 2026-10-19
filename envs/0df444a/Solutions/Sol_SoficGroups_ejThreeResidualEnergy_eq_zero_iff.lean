-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/713b4cdc-fa31-4bf3-91b0-7ce6b429bccd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (x : H) :
    ejThreeResidualEnergy V x = 0 ↔
      ∀ i : Fin 3, ejResidualProjection (V i) x = 0 := by
  constructor
  · intro h i
    have h₀ : 0 ≤ ‖ejResidualProjection (V 0) x‖ ^ 2 :=
      sq_nonneg _
    have h₁ : 0 ≤ ‖ejResidualProjection (V 1) x‖ ^ 2 :=
      sq_nonneg _
    have h₂ : 0 ≤ ‖ejResidualProjection (V 2) x‖ ^ 2 :=
      sq_nonneg _
    unfold ejThreeResidualEnergy at h
    fin_cases i
    · change ejResidualProjection (V 0) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 0) x)]
    · change ejResidualProjection (V 1) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 1) x)]
    · change ejResidualProjection (V 2) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 2) x)]
  · intro h
    unfold ejThreeResidualEnergy
    simp [h 0, h 1, h 2]
end SoficGroups
