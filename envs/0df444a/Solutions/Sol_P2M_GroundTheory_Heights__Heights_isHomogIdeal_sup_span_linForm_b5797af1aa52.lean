-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:35.170611+00:00
-- url     : https://prove2.me/submissions/18619ff3-3a5b-46a5-97a9-ed861dfe621a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I)
    (u : Fin n → R) : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨1, ?_⟩
  rw [mem_homogeneousSubmodule]
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
end GroundTheory.Heights₂.Heights
