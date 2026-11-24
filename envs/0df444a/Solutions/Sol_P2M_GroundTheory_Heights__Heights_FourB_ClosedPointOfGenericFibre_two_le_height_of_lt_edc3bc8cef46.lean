-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:24.807884+00:00
-- url     : https://prove2.me/submissions/ced38d4e-b705-4743-8fef-644babd3da99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
namespace GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {P M : Ideal R} [P.IsPrime]
    [M.IsPrime] (hP : P ≠ ⊥) (hPM : P < M) : 2 ≤ M.height := by
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (I := ⊥) (J := P) (bot_lt_iff_ne_bot.mpr hP)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hPM
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ P.height + 1 := by gcongr
    _ ≤ M.height := h2
end GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
