-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjTranspose_mulVec_colMat_515e18b64e61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:28.681861+00:00
-- url     : https://prove2.me/submissions/53b91b7a-62bb-49fa-8d70-620146e7fd31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
