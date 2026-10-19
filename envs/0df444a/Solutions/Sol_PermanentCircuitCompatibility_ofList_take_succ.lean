-- Prove2me | solution 1 for PermanentCircuitCompatibility.ofList_take_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/9270fb60-67ee-44a0-9c40-9ef91097763c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentCircuitCompatibility
namespace PermanentCircuitCompatibility
theorem _root_.solution {R : Type*} [CommRing R]
    {k : ℕ} (G : Fin k → R) (j : ℕ) (hj : j < k) :
    Ideal.ofList ((List.ofFn G).take j) ⊔
        Ideal.span ({G ⟨j, hj⟩} : Set R) =
      Ideal.ofList ((List.ofFn G).take (j + 1)) := by
  rw [List.take_succ_eq_append_getElem
    (show j < (List.ofFn G).length by
      simpa only [List.length_ofFn] using hj)]
  rw [Ideal.ofList_append, Ideal.ofList_singleton]
  simp only [List.getElem_ofFn]
end PermanentCircuitCompatibility
