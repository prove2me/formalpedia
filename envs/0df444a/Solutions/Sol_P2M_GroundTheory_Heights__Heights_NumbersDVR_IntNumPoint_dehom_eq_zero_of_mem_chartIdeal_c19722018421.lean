-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_chartIdeal_c19722018421
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:52.06638+00:00
-- url     : https://prove2.me/submissions/0bdeb715-cd3f-48da-8adf-260047438114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_chartUnitIdeal_e888f0795333
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3

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
theorem _root_.solution (hV : IsMultiHomogIdeal V) {f : MRing ι F}
    (hf : f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) : dehom V i f = 0 := by
  have : ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i ≤ RingHom.ker (dehom V i) :=
    sup_le (fun g hg => dehom_eq_zero_of_mem i hi hV hg) (fun g hg => dehom_chartUnitIdeal i hi hg)
  exact this hf
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
