-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_totalDegree_embForm_le_1f6bcbe4888f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:30.245459+00:00
-- url     : https://prove2.me/submissions/273f7b68-d7a0-44c1-b9ce-840bf8fa962e

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
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution (σ : L →ₐ[E] K) (x : Fin n → L) : (embForm σ x).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X, totalDegree_C]
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
