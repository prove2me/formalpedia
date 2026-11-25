-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_linPoly_83828813051c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:39.233552+00:00
-- url     : https://prove2.me/submissions/f9e9725c-b80f-4f70-9598-0978d3ac8696

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PZeroSetOpenMass

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
open MvPolynomial MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
