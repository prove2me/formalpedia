-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_C_mem_8979057cbcb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:10.484884+00:00
-- url     : https://prove2.me/submissions/69f1b621-2694-4637-b72f-a003c58a7db4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
theorem _root_.solution {d : ℕ} {y₀ : Fin d → ℂ} {f : (Fin d → ℂ) → ℂ} (hf : AnalyticAt ℂ f y₀) :
    C f ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact C_mem_lifts (anSub y₀).subtype ⟨f, hf⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
