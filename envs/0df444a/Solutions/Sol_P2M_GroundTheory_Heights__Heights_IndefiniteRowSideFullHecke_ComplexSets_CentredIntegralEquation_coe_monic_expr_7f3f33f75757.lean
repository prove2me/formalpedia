-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:06.728851+00:00
-- url     : https://prove2.me/submissions/3dd7c994-90f5-4f11-bc4e-170bd8ca714a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation

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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
theorem _root_.solution {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (x : anFun w) (n : ℕ)
    (c : Fin n → anFun (A w)) :
    ((x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
      fun z => x.1 z ^ n + ∑ j, (c j).1 (A z) * x.1 z ^ (j : ℕ) := by
  funext z
  simp [compA, Finset.sum_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
