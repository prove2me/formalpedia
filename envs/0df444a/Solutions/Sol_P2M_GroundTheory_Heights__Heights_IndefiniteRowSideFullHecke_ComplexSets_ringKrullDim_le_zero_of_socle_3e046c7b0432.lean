-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_zero_of_socle_3e046c7b0432
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:26.832313+00:00
-- url     : https://prove2.me/submissions/c64536f6-6a76-434a-82e5-221e55ff2f6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {L : Type*} [CommRing L] [IsLocalRing L] (hS : SerreSAt L 2)
    {z : L} (hz : z ≠ 0) (hk : ∀ m ∈ maximalIdeal L, m * z = 0) : ringKrullDim L ≤ 0 := by
  obtain ⟨rs, hm, hreg, hlen⟩ := hS
  have := weaklyRegular_eq_nil_of_socle hz (fun m hm => by rw [smul_eq_mul]; exact hk m hm) hm hreg
  subst this
  simp only [List.length_nil, Nat.cast_zero] at hlen
  exact (min_le_iff.mp hlen).resolve_left (by decide)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
