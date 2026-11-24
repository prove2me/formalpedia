-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:09.360853+00:00
-- url     : https://prove2.me/submissions/afdcdcfc-99fe-41ee-a345-fbc010eeba5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection

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
open GroundTheory.Heights₂.Heights.FieldNumbers
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    relDim I = (n : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  show ((((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) = _
  push_cast
  simp
  rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
