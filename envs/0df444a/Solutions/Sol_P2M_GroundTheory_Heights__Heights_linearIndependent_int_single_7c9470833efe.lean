-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:41.341682+00:00
-- url     : https://prove2.me/submissions/6a6af689-351b-4ec7-897d-e463f846b0d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel

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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m : ℕ) :
    LinearIndependent ℤ (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) := by
  have h : LinearIndependent ℚ (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) := by
    have e : (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) = ⇑(Pi.basisFun ℚ (Fin m)) := by
      funext j
      exact (Pi.basisFun_apply _ _ j).symm
    rw [e]
    exact (Pi.basisFun ℚ (Fin m)).linearIndependent
  exact h.restrict_scalars' ℤ
end GroundTheory.Heights₂.Heights
