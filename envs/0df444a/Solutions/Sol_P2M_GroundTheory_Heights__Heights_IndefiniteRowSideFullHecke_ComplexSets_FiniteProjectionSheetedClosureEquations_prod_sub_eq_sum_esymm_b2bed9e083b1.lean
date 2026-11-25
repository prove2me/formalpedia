-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:33.29782+00:00
-- url     : https://prove2.me/submissions/31222670-23b4-4a55-90d1-b5ce42b3b285

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetedClosureEquations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionSheetedClosureEquations

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteProjectionSheetedClosureEquations
theorem _root_.solution (m : Multiset ℂ) (a : ℂ) :
    (m.map fun x => a - x).prod =
      ∑ j ∈ Finset.range (Multiset.card m + 1), (-1) ^ j * m.esymm j * a ^ (Multiset.card m - j) := by
  have key := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at key
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end FiniteProjectionSheetedClosureEquations
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
