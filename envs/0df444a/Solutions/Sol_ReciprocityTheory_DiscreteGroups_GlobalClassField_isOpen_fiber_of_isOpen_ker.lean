-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_fiber_of_isOpen_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:49.213092+00:00
-- url     : https://prove2.me/submissions/e532c1eb-fdcb-40d1-b6f4-498752407571

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLimB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ResCompat_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ResCompat_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    (φ : A →* B) (h : IsOpen (φ.ker : Set A)) (b : B) : IsOpen {a | φ a = b} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have ha' : φ a = b := ha
  have hO : IsOpen ((fun y : A => a⁻¹ * y) ⁻¹' (φ.ker : Set A)) := h.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · show a⁻¹ * a ∈ φ.ker
    rw [inv_mul_cancel]; exact one_mem _
  · intro y hy
    have hy' : φ (a⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm.trans ha'
end ReciprocityTheory.DiscreteGroups.GlobalClassField
