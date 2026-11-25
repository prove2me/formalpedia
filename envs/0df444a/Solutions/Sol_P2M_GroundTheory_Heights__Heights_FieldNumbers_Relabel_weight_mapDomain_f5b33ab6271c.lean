-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:02.1882+00:00
-- url     : https://prove2.me/submissions/fb242bea-525b-4a09-8b5c-9d04c446b40b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



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
theorem _root_.solution (d : (Σ k, ι₁ k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι₂) (Finsupp.mapDomain φ d) =
      Finsupp.weight (blockWeight ι₁) d ∘ e.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
    rfl
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hφ, Pi.smul_apply, Function.comp_apply, Pi.single_apply,
      Equiv.symm_apply_eq]
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
