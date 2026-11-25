-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:18.76774+00:00
-- url     : https://prove2.me/submissions/da925a45-bff2-40b3-9a80-269232dd109e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (M : Submonoid ℤ) (hM : (0 : ℤ) ∉ M) (o : Type) [CommRing o]
    [Algebra ℤ o] [IsLocalization M o] (φ : o →+* ℚ) (a : o) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * φ a = z := by
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj M a
  have hs0 : (s : ℤ) ≠ 0 := fun h => hM (h ▸ s.2)
  have hφ : φ a * ((s : ℤ) : ℚ) = z := by
    have := congrArg φ hs
    simpa only [map_mul, eq_intCast (algebraMap ℤ o), map_intCast] using this
  refine ⟨(s : ℤ).natAbs, Int.natAbs_pos.2 hs0, (Int.sign (s : ℤ)) * z, ?_⟩
  have hab : (((s : ℤ).natAbs : ℕ) : ℤ) = Int.sign (s : ℤ) * (s : ℤ) := by
    rw [Int.sign_mul_self]
  rw [show (((s : ℤ).natAbs : ℕ) : ℚ) = ((((s : ℤ).natAbs : ℕ) : ℤ) : ℚ) from
    (Int.cast_natCast _).symm, hab, Int.cast_mul, Int.cast_mul, ← hφ]
  ring
end GroundTheory.Heights₂.Heights.Model
