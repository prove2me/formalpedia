-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongMono_proof_2074aa19ca6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:04.99451+00:00
-- url     : https://prove2.me/submissions/c2afc849-13d8-40e2-a62e-2c1a4dce62fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongMono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongMono_chartDens_annulus_nonneg_f01f4e959af3

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open RegLelongMono
namespace GroundTheory.Heights₂.Heights
namespace RegLelongMono
theorem _root_.solution (hA : RegLelongAnnulus.Statement) (hL : RegLogDensNonneg.Statement) :
    RegLelongMono.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have heq := hA n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg hL u hε x hr y
  have hrs0 : 0 ≤ r ^ (2 * d) * s ^ (2 * d) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith
end RegLelongMono
end GroundTheory.Heights₂.Heights
