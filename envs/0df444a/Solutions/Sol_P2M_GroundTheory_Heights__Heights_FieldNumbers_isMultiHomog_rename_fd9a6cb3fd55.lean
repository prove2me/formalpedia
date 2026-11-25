-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:52.051445+00:00
-- url     : https://prove2.me/submissions/d50fe36e-fd0a-41a8-8ab7-bf13eea19952

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {a : MRing (fun k => ι' (j k)) F} {c : K → ℕ} (ha : IsMultiHomog a c) :
    IsMultiHomog (rename (blockIncl j ι') a) (Function.extend j c 0) := by
  classical
  have ha' : IsWeightedHomogeneous (blockWeight (fun k => ι' (j k))) a c := ha
  show IsWeightedHomogeneous _ _ _
  intro d' hd'
  have hmem : d' ∈ (rename (blockIncl j ι') a).support := mem_support_iff.mpr hd'
  rw [support_rename_of_injective (blockIncl_injective j ι')] at hmem
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmem
  rw [weight_blockIncl, ha' (mem_support_iff.mp hd)]
end GroundTheory.Heights₂.Heights.FieldNumbers
