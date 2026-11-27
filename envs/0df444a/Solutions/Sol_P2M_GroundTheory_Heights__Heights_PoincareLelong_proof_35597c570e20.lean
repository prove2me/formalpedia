-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PoincareLelong_proof_35597c570e20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:34.581627+00:00
-- url     : https://prove2.me/submissions/1f21354e-a1fc-4127-b644-d39080205a50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPoincareLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


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
namespace GroundTheory.Heights₂.Heights
namespace PoincareLelong
theorem _root_.solution (hStokes : StokesOnVariety.Statement)
    (hReg : LelongRegularise.Statement) (hLim : LelongLimit.Statement) :
    PoincareLelong.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ), varInt J (d + 1) f (vecCons (logReg u ε) φ) =
      varInt J (d + 1) (logReg u ε) (vecCons f φ) := fun ε hε =>
    hStokes n d J f (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hf)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hfc)
  exact tendsto_nhds_unique (hReg n d J u f φ hJ hdim hu hf hfc hφ)
    ((hLim n d J u f φ hJ hdim hu hf hfc hφ).congr' (eventually_nhdsWithin_of_forall hS))
end PoincareLelong
end GroundTheory.Heights₂.Heights
