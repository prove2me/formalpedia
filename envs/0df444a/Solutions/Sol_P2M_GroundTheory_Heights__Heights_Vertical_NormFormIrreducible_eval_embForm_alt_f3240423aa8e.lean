-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:46.69687+00:00
-- url     : https://prove2.me/submissions/89050102-c546-4840-9414-2304b7cf7ce0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e

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
theorem _root_.solution (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) :
    eval (fun j => algebraMap E K (t j)) (embForm σ x) = 1 := by
  rw [eval_embForm, ← map_one σ, ← ht, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, AlgHom.commutes]
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
