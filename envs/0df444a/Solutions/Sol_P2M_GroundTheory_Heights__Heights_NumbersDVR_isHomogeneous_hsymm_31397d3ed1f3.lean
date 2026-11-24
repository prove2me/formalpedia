-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_hsymm_31397d3ed1f3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:14.395491+00:00
-- url     : https://prove2.me/submissions/b34ddad2-b295-49b8-a1de-f66b8b1a1174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (N a : ℕ) : (hsymm (Fin N) ℤ a).IsHomogeneous a := by
  have h : ∀ t : Multiset (Fin N),
      ((t.map X).prod : MvPolynomial (Fin N) ℤ).IsHomogeneous (Multiset.card t) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (Fin N) ℤ
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact (isHomogeneous_X ℤ b).mul ih
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  simpa [s.2] using h s.1
end GroundTheory.Heights₂.Heights.NumbersDVR
