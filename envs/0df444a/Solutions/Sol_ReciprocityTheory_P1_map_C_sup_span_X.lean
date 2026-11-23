-- Prove2me | solution 1 for ReciprocityTheory.P1.map_C_sup_span_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.595294+00:00
-- url     : https://prove2.me/submissions/5f367868-d120-4a7f-9058-2219f4785c53

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PowerSeries IsLocalRing
noncomputable section
open ReciprocityTheory ReciprocityTheory.P1
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace ReciprocityTheory.P1
theorem _root_.solution :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · simp [Ideal.span_singleton_le_iff_mem]
  · intro f hf
    rw [f.eq_X_mul_shift_add_const]
    exact add_mem
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
end ReciprocityTheory.P1
