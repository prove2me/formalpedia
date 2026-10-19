-- Prove2me | solution 1 for PermanentRollout.exists_source_parameter_slicedGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/e9065a30-db56-4075-9033-f976dadab91e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_slicedGradient_of_criticalLocus_codimension
import Theorems.Thm_PermanentRollout_eight_le_blockVariables
import Theorems.Thm_PermanentRollout_twice_criticalDimension_lt_blockVariables
import Theorems.Thm_PermanentRollout_sliceRank_lt_blockVariables
import Theorems.Thm_PermanentRollout_sliceRank_le_codimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d dimension : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤
      blockWidth d * blockColumns n d)
    (hdimension : dimension ≤ blockCount n d *
      (powerSumParameter d + blockColumns n d * (d - 2)))
    (P : MvPolynomial (Fin (blockVariables n d)) ℂ)
    (hP : P.IsHomogeneous d)
    (hcritical : criticalLocusDimension P ≤
      (dimension : WithBot ℕ∞)) :
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
  have hhalf := twice_criticalDimension_lt_blockVariables
    hd hn hscale hdimension
  have hk := sliceRank_le_codimension hd hn hscale hdimension
  have hm := sliceRank_lt_blockVariables
    (eight_le_blockVariables hd hn)
  have hsub :
      blockVariables n d - (blockVariables n d - dimension) = dimension := by
    omega
  have hcodimension :
      criticalLocusDimension P ≤
        ((blockVariables n d -
          (blockVariables n d - dimension) : ℕ) : WithBot ℕ∞) := by
    simpa [hsub] using hcritical
  exact exists_slicedGradient_of_criticalLocus_codimension
    P (by omega) hP hk hm hcodimension
end PermanentRollout
