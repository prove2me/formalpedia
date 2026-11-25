-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_proof_66674c159269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:46.298538+00:00
-- url     : https://prove2.me/submissions/e27f5283-fee1-48b9-963f-3ec49335420f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_Y_8f10abd9d489
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_orth_2b820cb671e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_continuous_torusHom_715533cbf2dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by
  intro x₀ w₀ hp
  refine ⟨torusHom h1 h2 hp, continuous_torusHom h1 h2 hp, fun a w => ?_⟩
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  refine ⟨torusMat_mulVec_X hXX hYX _ _, ?_, fun z hX hY => torusMat_mulVec_orth _ _ z hX hY⟩
  change torusMat _ _ _ _ _ *ᵥ _ = _
  rw [torusMat_mulVec_Y hYY hXY, Units.val_inv_eq_inv_val, map_inv₀]
end GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
