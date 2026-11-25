-- Prove2me | solution 1 for PI.SqPair.LCP.sg_hf_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:55.698055+00:00
-- url     : https://prove2.me/submissions/20966b4d-052f-4336-8938-4f2ce0480c9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]
namespace PI.SqPair.LCP
theorem _root_.solution {A : Matrix ι ι R} (hA : Aᴴ = A) (x y : ι → R) :
    star (hf A x y) = hf A y x := by
  conv_rhs => rw [← hA]
  simp only [hf, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, conjTranspose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.SqPair.LCP
