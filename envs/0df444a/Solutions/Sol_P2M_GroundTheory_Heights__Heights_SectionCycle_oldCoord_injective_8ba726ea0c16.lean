-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:16:08.336574+00:00
-- url     : https://prove2.me/submissions/b0e56cae-9dcb-4d16-8f3e-748e1745dacd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution : Function.Injective D.oldCoord := by
  intro v w h
  have h1 : v.1 = w.1 := Option.some_injective _ (congrArg Sigma.fst h)
  exact Sigma.ext h1 (Sigma.mk.inj_iff.mp h).2
end GroundTheory.Heights₂.Heights.SectionCycle
