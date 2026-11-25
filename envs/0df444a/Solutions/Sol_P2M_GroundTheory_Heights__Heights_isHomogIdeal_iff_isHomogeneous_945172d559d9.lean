-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_945172d559d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:39.94121+00:00
-- url     : https://prove2.me/submissions/7d484382-03a7-44ea-8cd5-48632d67cf87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  constructor
  · intro h i r hr
    have := decomposition.decompose'_apply (σ := Fin n) (R := ℂ) r i
    change (decomposition.decompose' r i : MvPolynomial (Fin n) ℂ) ∈ I
    rw [this]
    exact h r hr i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d
end GroundTheory.Heights₂.Heights
