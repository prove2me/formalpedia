-- Prove2me | solution 1 for Supermodularity.Lattices.inter_increasing_of_forall_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T06:34:35.101655+00:00
-- url     : https://prove2.me/submissions/3ad107d6-f4f6-48e3-872b-7481b82d4789

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

set_option autoImplicit false

open Supermodularity.Lattices in
theorem solution {X T A : Type*} [Lattice X] [PartialOrder T]
    (S : A → T → Set X)
    (hinc : ∀ α : A, ∀ ⦃t t' : T⦄, t ≤ t' → InducedSetOrder (S α t) (S α t'))
    (hne : ∀ t : T, (⋂ α, S α t).Nonempty) :
    ∀ ⦃t t' : T⦄, t ≤ t' → InducedSetOrder (⋂ α, S α t) (⋂ α, S α t') := by
  intro t t' htt' a ha b hb
  rw [Set.mem_iInter] at ha hb
  refine ⟨Set.mem_iInter.2 fun α => ?_, Set.mem_iInter.2 fun α => ?_⟩
  · exact (hinc α htt' (ha α) (hb α)).1
  · exact (hinc α htt' (ha α) (hb α)).2
