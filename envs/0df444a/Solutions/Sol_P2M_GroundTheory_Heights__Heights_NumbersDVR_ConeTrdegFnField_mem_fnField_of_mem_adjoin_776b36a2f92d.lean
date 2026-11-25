-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:07.800411+00:00
-- url     : https://prove2.me/submissions/26b6b2ca-9f7e-49b9-9980-a2a8d42d6863

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ConeTrdegFnField
theorem _root_.solution (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz
end ConeTrdegFnField
end GroundTheory.Heights₂.Heights.NumbersDVR
