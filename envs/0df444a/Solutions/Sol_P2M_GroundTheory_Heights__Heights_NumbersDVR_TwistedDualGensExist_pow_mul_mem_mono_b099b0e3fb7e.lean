-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:37.976083+00:00
-- url     : https://prove2.me/submissions/1182c72c-c08a-464f-b23d-dc63a03d8a31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution {x : τ → Ω} {c c' : τ} {z : Ω} {n n' : ℕ}
    (h : (x c / x c') ^ n * z ∈ chartRing O x c') (hn : n ≤ n') :
    (x c / x c') ^ n' * z ∈ chartRing O x c' := by
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  exact mul_mem (pow_mem (div_mem_chartRing x c' c) _) h
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
