-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_intNum_map_rename_03f66fcd6074
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:20.021519+00:00
-- url     : https://prove2.me/submissions/8ba18e4d-1097-4a62-be89-dd46ff59b386

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_mixedDiff_precomp_c1f3f1b7faf4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]
include hφ
namespace GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
theorem _root_.solution (I : Ideal (MRing ι₁ F)) {n : ℕ} (bs : Fin n → K₂ → ℤ) :
    intNum F (I.map (renameEquiv F φ)) bs = intNum F I (fun i => bs i ∘ e) := by
  unfold intNum
  have h : hilbFn (I.map (renameEquiv F φ)) = fun m => hilbFn I (m ∘ e) :=
    funext (hilbFn_map_rename e φ hφ I)
  rw [h, mixedDiff_precomp, eventualValue_precomp]
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
