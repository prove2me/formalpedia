-- Prove2me | solution 1 for PermanentRollout.exists_source_block_slicedGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/5c0ef156-884b-40a6-b969-75412841ca78

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_source_parameter_slicedGradient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (P : MvPolynomial (Fin (blockVariables n d)) ℂ)
    (hP : P.IsHomogeneous d)
    (hcritical : criticalLocusDimension P ≤
      ((blockCount n d *
        (powerSumParameter d + blockColumns n d * (d - 2)) : ℕ) :
          WithBot ℕ∞)) :
    ∃ (W : (Fin (sliceRank n d) → ℂ) →ₗ[ℂ]
          (Fin (blockVariables n d) → ℂ))
      (A : (Fin (blockVariables n d) → ℂ) →ₗ[ℂ]
          (Fin (sliceRank n d) → ℂ)),
      Function.Injective W ∧
      (∀ i : Fin (sliceRank n d),
        (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1)) ∧
      (∀ u : Fin (sliceRank n d) → ℂ,
        (∀ i : Fin (sliceRank n d),
          MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
            u = 0) := by
  exact exists_source_parameter_slicedGradient
    hd hn hscale (by rfl) P hP hcritical
end PermanentRollout
