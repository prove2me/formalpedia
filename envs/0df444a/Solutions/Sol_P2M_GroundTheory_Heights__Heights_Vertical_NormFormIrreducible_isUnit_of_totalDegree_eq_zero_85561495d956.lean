-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:22.025992+00:00
-- url     : https://prove2.me/submissions/d5780193-cc05-4989-a957-4202a2542f80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution {p : MvPolynomial (Fin n) K} (hp : p ≠ 0)
    (hd : p.totalDegree = 0) : IsUnit p := by
  rw [totalDegree_eq_zero_iff_eq_C] at hd
  rw [hd] at hp ⊢
  exact (Ne.isUnit fun h => hp (by rw [h, C_0])).map C
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
