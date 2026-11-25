-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:11.47493+00:00
-- url     : https://prove2.me/submissions/65de112c-f757-4628-bf9b-67deb9017490

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subIncl_injective_254710e4ea21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subProj_surjective_f26808b3cafa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_subExact_03efe69f570c

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable (F : Submodule (𝓞 K) E.carrier)
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution : E.rank F = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) :=
  finrank_eq_add_of_exact (X.subIncl_injective F) (X.subProj_surjective F) (X.subExact F)
end GroundTheory.Heights₂.Heights.HermitianExtension
