-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_const_mem_zeroSetIn_lineDiagonal_f0d6d4f27065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:30.351388+00:00
-- url     : https://prove2.me/submissions/9c2a2746-5467-478c-8f71-288b0bd26344

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (c : ℂ) :
    (fun _ => c : Fin 1 ⊕ Fin 1 → ℂ) ∈ zeroSetIn lineDiagonalIdeal :=
  fun q hq => eval_const_of_lineDiagonalMap_eq_zero c q hq
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
