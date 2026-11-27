-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isOfDegree_iff_3652ab92fe78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:11.720283+00:00
-- url     : https://prove2.me/submissions/03b0b929-6b66-4e36-80e9-eee1edf80069

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_mkF_11dd0b252176

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (a : ι → ℤ) (x : P.FunField) :
    P.IsOfDegree a x ↔ IsHomogOfDeg P a (funFieldEquiv P x) := by
  constructor
  · rintro ⟨f, g, df, dg, hf, hg, hd, hgP, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hgP, hd, ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
  · rintro ⟨f, g, df, dg, hf, hg, hgP, hd, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hd, hgP, (funFieldEquiv P).injective ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
