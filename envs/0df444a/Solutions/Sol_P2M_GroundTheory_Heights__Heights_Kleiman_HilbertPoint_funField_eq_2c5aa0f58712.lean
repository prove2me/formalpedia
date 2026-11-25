-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:10:17.359674+00:00
-- url     : https://prove2.me/submissions/8216b37e-7285-46cb-9ff3-0dcd7cbd415c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hj : y j ≠ 0) (hF : IsField (affRing k y j)) :
    funField (k := k) y = (affRing k y j).toIntermediateField' hF := by
  have haff : ∀ l, aff y j l ∈ (affRing k y j).toIntermediateField' hF := fun l =>
    show aff y j l ∈ affRing k y j from ⟨X l, by simp⟩
  apply le_antisymm
  · rw [funField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, l, hi, rfl⟩
    have : y l / y i = aff y j l * (aff y j i)⁻¹ := by
      simp only [aff]; field_simp
    rw [this]
    exact mul_mem (haff l) (inv_mem (haff i))
  · intro z hz
    change z ∈ affRing k y j at hz
    rw [affRing, ← Algebra.adjoin_range_eq_range_aeval] at hz
    refine Algebra.adjoin_le (S := (funField (k := k) y).toSubalgebra) ?_ hz
    rintro _ ⟨l, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨j, l, hj, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
