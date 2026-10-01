-- Prove2me | solution 2 for burau_q_delta4
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:46:32.645832+00:00
-- url     : https://prove2.me/submissions/a86e2c1b-fa86-45fd-9d1b-f8144c7fea67

import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

/-- `Δ⁴ = (σ₀σ₁)⁶` is trivial in `Q = B₃/⟨⟨Δ⁴⟩⟩`. -/
theorem solution : ((BurauNC.Delta4 : BurauNC.B3) : BurauNC.Q) = 1 :=
  (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure ({BurauNC.Delta4} : Set BurauNC.B3))
      BurauNC.Delta4).mpr
    (Subgroup.subset_normalClosure (by simp))
