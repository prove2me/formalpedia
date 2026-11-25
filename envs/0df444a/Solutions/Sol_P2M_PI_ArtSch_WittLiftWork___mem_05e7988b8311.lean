-- Prove2me | solution 1 for P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:42.67955+00:00
-- url     : https://prove2.me/submissions/13944e48-62f8-45b4-9602-cc001aa46909

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
variable [CharP k p]
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution {n : ℕ} {z : WittVector p k} (hz : z ∈ I n) : δ z ∈ I n := by
  show WittVector.map (frobenius k p) z - z ∈ I n
  have h1 : WittVector.map (frobenius k p) z ∈ I n := by
    refine mem_I.2 fun i hi => ?_
    rw [WittVector.map_coeff, mem_I.1 hz i hi, map_zero]
  exact Ideal.sub_mem _ h1 hz
end PI.ArtSch.WittLiftWork
