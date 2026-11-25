-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:49.108075+00:00
-- url     : https://prove2.me/submissions/b9cbc6b5-1db7-4a61-a307-7291cd5bc2b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_chartProd_ne_zero_728a4ef52d77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_mul_of_isMultiHomog_db1b22d71340

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (hV : IsMultiHomogIdeal V) {f : MRing ι F} (hf : f ∈ V) :
    dehom V i f = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  have h1 := dehom_mul_of_isMultiHomog i hi
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) (n := b) (φ := f))
  rw [(cls_eq_zero_iff V _).2 (hV f hf b)] at h1
  exact (mul_eq_zero.mp h1).resolve_right (chartProd_ne_zero i hi b)
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
