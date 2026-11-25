-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_not_add_add_9b3ea79ea563
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:26.197274+00:00
-- url     : https://prove2.me/submissions/276d171b-814d-4756-a307-d434747d09ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityDivisorSupportClosed
theorem _root_.solution {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega
end RegularityDivisorSupportClosed
end GroundTheory.Heights₂.Heights.Inter
