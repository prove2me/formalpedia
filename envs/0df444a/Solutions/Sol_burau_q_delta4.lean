-- Prove2me | solution 1 for burau_q_delta4
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:33:53.020679+00:00
-- url     : https://prove2.me/submissions/571aa8bd-1a66-4b85-8ca8-489bfa8a63ec

import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

/-- `Δ⁴ = (σ₀σ₁)⁶` is trivial in `Q = B₃/⟨⟨Δ⁴⟩⟩`. -/
theorem solution : ((BurauNC.Delta4 : BurauNC.B3) : BurauNC.Q) = 1 :=
  (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure ({BurauNC.Delta4} : Set BurauNC.B3))
      BurauNC.Delta4).mpr
    (Subgroup.subset_normalClosure (by simp))
