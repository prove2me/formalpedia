-- Prove2me | solution 1 for SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/edc70f66-9a8c-4548-a37e-0f18d2811430

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_diagonalRadius_tendsto_atTop
import Theorems.Thm_SoficGroups_diagonalRadius_error_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (e : ℕ → ℕ → ℝ) (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto (fun n => e n (r n)) atTop (𝓝 0) :=
  ⟨diagonalRadius e, diagonalRadius_tendsto_atTop e he,
    diagonalRadius_error_tendsto_zero e hnonneg he⟩
end SoficGroups
