-- Prove2me | solution 1 for PhosphorylationSharpness.reconstruct_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:00.130125+00:00
-- url     : https://prove2.me/submissions/b487e473-b6d8-4339-8f45-0c187339dad2

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Theorems.Thm_PhosphorylationSharpness_equilibrium_of_currents

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (u s f : ℝ) :
    Equilibrium (realize t B D) (reconstruct t B D u s f) := by
  apply equilibrium_of_currents
  · intro i
    dsimp [kinaseNet, realize, reconstruct]
    rw [pow_succ]
    field_simp [ne_of_gt (ht i.castSucc), ne_of_gt (hB i)]
    ring
  · intro i
    dsimp [phosphataseNet, realize, reconstruct]
    field_simp [ne_of_gt (ht i.succ)]
    ring
  · intro i
    dsimp [realize, reconstruct]
    field_simp [ne_of_gt (hB i)]
end PhosphorylationSharpness
