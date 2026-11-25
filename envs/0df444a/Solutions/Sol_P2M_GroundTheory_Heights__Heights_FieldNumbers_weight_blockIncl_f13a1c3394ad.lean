-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:12.572976+00:00
-- url     : https://prove2.me/submissions/b7de5d43-e147-4534-8bc1-d3d48d590ebe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_not_5b15fa7008a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (d : (Σ k, ι' (j k)) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain (blockIncl j ι') d) =
      Function.extend j (Finsupp.weight (blockWeight (fun k => ι' (j k))) d) 0 := by
  rw [weight_mapDomain]
  funext k'
  rw [weight_apply_eval]
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [extend_apply_self, weight_apply_eval]
    have e : (fun v => (blockWeight ι' ∘ blockIncl j ι') v (j k)) =
        fun v => blockWeight (fun k => ι' (j k)) v k := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) (j k) = (Pi.single v.1 1 : K → ℕ) k
      simp only [Pi.single_apply, j.injective.eq_iff]
    rw [e]
  · rw [extend_apply_not j _ k' h]
    have h0 : (fun v => (blockWeight ι' ∘ blockIncl j ι') v k') = 0 := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) k' = 0
      rw [Pi.single_apply, if_neg (fun hv => h ⟨v.1, hv.symm⟩)]
    rw [h0]
    simp [Finsupp.weight_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers
