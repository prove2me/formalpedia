-- Prove2me | solution 1 for QEC.Locality.minimumSeparator_card_real_le_profilePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:32:11.788022+00:00
-- url     : https://prove2.me/submissions/6f61bfc5-daa7-4e22-b315-445f113d854b

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Theorems.Thm_QEC_Locality_minimumSeparator_card_le_ownProfile
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (vertices separator : Finset ι)
    (hvertices : 1 ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    (separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent := by
  have hmeasured := minimumSeparator_card_le_ownProfile G vertices separator hminimum
  exact (Nat.cast_le.2 hmeasured).trans
    (hProfile.2.2.2 vertices.card hvertices (Finset.card_le_univ vertices))
end QEC.Locality
