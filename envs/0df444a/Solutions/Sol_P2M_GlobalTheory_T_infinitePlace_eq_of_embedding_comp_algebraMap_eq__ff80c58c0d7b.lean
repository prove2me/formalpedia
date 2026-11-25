-- Prove2me | solution 1 for P2M_GlobalTheory_T_infinitePlace_eq_of_embedding_comp_algebraMap_eq__ff80c58c0d7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:32:35.139142+00:00
-- url     : https://prove2.me/submissions/a2b52172-cd25-4350-b65a-8c5c3a6fd6b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InfinitePlaceEqOfEmbeddingCompAlgebraMapEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement
import Theorems.Thm_GlobalTheory_infinitePlace_eq_of_embedding_comp_algebraMap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by
  first | exact @GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | exact GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | (intros; apply GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq <;> assumption)
end _root_.GlobalTheory.T
