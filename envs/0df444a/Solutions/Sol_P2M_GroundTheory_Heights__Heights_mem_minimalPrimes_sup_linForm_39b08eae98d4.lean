-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:22.321941+00:00
-- url     : https://prove2.me/submissions/c33dbf0e-60d9-45e6-9ae7-d4f180f71262

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlueOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} (hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
  have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
  refine ⟨hWm.1.1, fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
  have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using this
end GroundTheory.Heights₂.Heights
