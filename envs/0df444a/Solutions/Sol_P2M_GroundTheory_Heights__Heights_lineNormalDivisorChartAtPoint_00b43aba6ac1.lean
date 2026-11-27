-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAtPoint_00b43aba6ac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:25.575985+00:00
-- url     : https://prove2.me/submissions/837750f9-56de-4888-8df3-d5a9fe0c0df4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorChartGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_const_mem_zeroSetIn_lineDiagonal_f0d6d4f27065
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc


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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    NormalDivisorChartAtPoint IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel (fun _ => (1 : ℂ)) 0 0 :=
  lineNormalDivisorChartAt 0 (IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal 0) rfl
end GroundTheory.Heights₂.Heights
