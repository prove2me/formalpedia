-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_map_injective_fc941090a98a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:24.877485+00:00
-- url     : https://prove2.me/submissions/1c834bc3-8ba2-4794-8c9c-00e14347ba2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution :
    Function.Injective (WithBot.map (fun d : ℕ∞ =>
      WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)) :=
  WithBot.map_injective (WithTop.map_injective fun a b h => by
    have h' : (a : ℤ) - Fintype.card K = (b : ℤ) - Fintype.card K := h
    omega)
end GroundTheory.Heights₂.Heights.FieldNumbers
