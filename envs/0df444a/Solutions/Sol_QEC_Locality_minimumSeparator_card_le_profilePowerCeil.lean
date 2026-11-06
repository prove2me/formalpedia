-- Prove2me | solution 1 for QEC.Locality.minimumSeparator_card_le_profilePowerCeil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:15:33.828269+00:00
-- url     : https://prove2.me/submissions/75dd32d4-1f2a-445c-8acc-6f50f2ebe313

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Theorems.Thm_QEC_Locality_minimumSeparator_card_real_le_profilePower
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
    separator.card ≤ Nat.ceil (beta * Real.rpow vertices.card exponent) := by
  have hreal := minimumSeparator_card_real_le_profilePower
    G beta exponent hProfile vertices separator hvertices hminimum
  exact_mod_cast hreal.trans (Nat.le_ceil (beta * Real.rpow vertices.card exponent))
end QEC.Locality
