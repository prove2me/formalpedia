-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_differentiable_polyEval_73aee85ab726
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:21.928798+00:00
-- url     : https://prove2.me/submissions/dbb4537c-5637-4531-91a5-eaa627b593b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRootSumHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalUniversalDenominator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_differentiable_eval_9e225807b9fc
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow


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
open MvPolynomial Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalUniversalDenominator
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalUniversalDenominator
theorem _root_.solution {d : ℕ} (P : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => (P.map (eval p.1)).eval p.2) := by
  have he : (fun p : (Fin d → ℂ) × ℂ => (P.map (eval p.1)).eval p.2) =
      fun p => ∑ i ∈ Finset.range (P.natDegree + 1), eval p.1 (P.coeff i) * p.2 ^ i := by
    funext p
    rw [Polynomial.eval_eq_sum_range' (n := P.natDegree + 1)
      (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
    simp only [Polynomial.coeff_map]
  rw [he]
  refine Differentiable.fun_sum fun i _ => ?_
  have h1 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => eval p.1 (P.coeff i)) :=
    (differentiable_eval (P.coeff i)).comp differentiable_fst
  have h2 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => p.2 ^ i) := differentiable_snd.pow i
  exact h1.mul h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalUniversalDenominator
