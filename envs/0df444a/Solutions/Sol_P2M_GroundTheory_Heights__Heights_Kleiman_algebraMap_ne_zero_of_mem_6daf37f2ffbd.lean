-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:33.716309+00:00
-- url     : https://prove2.me/submissions/63fa9ff4-39be-478e-a214-985c38f1547c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (F : Type u) [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] [IsFractionRing S F] {t : S} (ht : t ∈ nonZeroDivisors S) : algebraMap S Ω t ≠ 0 := by
  have : Nontrivial S := (algebraMap S F).domain_nontrivial
  rw [IsScalarTower.algebraMap_apply S F Ω]
  exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht)
end GroundTheory.Heights₂.Heights.Kleiman
