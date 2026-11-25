-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:24.194304+00:00
-- url     : https://prove2.me/submissions/48c9ebe0-a9ef-49c4-b959-e368c4eb77aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc
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
theorem _root_.solution (a : MRing (fun k => ι' (j k)) F) (b : K → ℕ) :
    rename (blockIncl j ι') (weightedHomogeneousComponent (blockWeight (fun k => ι' (j k))) b a) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0)
        (rename (blockIncl j ι') a) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain (blockIncl j ι') d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain _ (blockIncl_injective j ι'),
      coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_weightedHomogeneousComponent,
      weight_blockIncl]
    by_cases hw : Finsupp.weight (blockWeight (fun k => ι' (j k))) d = b
    · rw [if_pos hw, if_pos (by rw [hw])]
    · rw [if_neg hw, if_neg (fun h => hw ((extend_inj j).mp h))]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ d' (fun u hu => absurd hu (hd u)),
      coeff_rename_eq_zero _ a d' (fun u hu => absurd hu (hd u))]
    simp
end GroundTheory.Heights₂.Heights.FieldNumbers
