-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:28.502006+00:00
-- url     : https://prove2.me/submissions/e2b2634c-7977-4d8a-b2a8-637c744b4859

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (Y : AddSubgroup E) {u : Ω} (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (k : ℕ) :
    ∀ e ∈ Y, (u⁻¹) ^ k • e ∈ Y := by
  induction k with
  | zero => intro e he; simpa using he
  | succ k ih => intro e he; rw [pow_succ, mul_smul]; exact ih _ (hYu e he)
end GroundTheory.Heights₂.Heights.Model
