-- Prove2me | solution 1 for ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:04:35.16018+00:00
-- url     : https://prove2.me/submissions/c34dc4a2-e774-4c81-9a04-5c2093aa5294

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (x : Fin d → A) (hxp : ∀ j, x j ^ p = 0)
    {P : MvPolynomial (Fin d) R}
    (hP : P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p)) :
    aeval x P = 0 := by
  have hle : Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p) ≤
      RingHom.ker (aeval (R := R) x) := by
    rw [Ideal.span_le, Set.range_subset_iff]
    intro j
    simp [RingHom.mem_ker, hxp j]
  exact hle hP
end ReciprocityTheory.PGsh
