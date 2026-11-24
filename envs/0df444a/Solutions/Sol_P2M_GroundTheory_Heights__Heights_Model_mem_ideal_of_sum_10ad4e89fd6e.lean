-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.270798+00:00
-- url     : https://prove2.me/submissions/1c8b8391-c680-4ebd-95a9-8ad2c1a8d550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame

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
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A : Subalgebra ℤ Ω} (Q : Ideal A) {k : ℕ} (a y : Fin k → Ω)
    (ha : ∀ l, a l ∈ A) (hy : ∀ l, y l ∈ A) (hyQ : ∀ l, (⟨y l, hy l⟩ : A) ∈ Q) {z : Ω}
    (hz : z ∈ A) (hsum : ∑ l, a l * y l = z) : (⟨z, hz⟩ : A) ∈ Q := by
  have : (⟨z, hz⟩ : A) = ∑ l, (⟨a l, ha l⟩ : A) * ⟨y l, hy l⟩ := Subtype.ext (by simp [← hsum])
  rw [this]
  exact Q.sum_mem fun l _ => Q.mul_mem_left _ (hyQ l)
end GroundTheory.Heights₂.Heights.Model
