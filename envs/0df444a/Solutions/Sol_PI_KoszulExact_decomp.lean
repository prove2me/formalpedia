-- Prove2me | solution 1 for PI.KoszulExact.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:39.766895+00:00
-- url     : https://prove2.me/submissions/95027bbd-9016-4238-8a83-370641b6fa20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
import Theorems.Thm_PI_KoszulExact_Dc_zero
import Theorems.Thm_PI_KoszulExact_Dc_add
import Theorems.Thm_PI_KoszulExact_Dc_smul
import Theorems.Thm_PI_KoszulExact_eb_mul_swap
import Theorems.Thm_PI_KoszulExact_eb_mul_self
import Theorems.Thm_PI_KoszulExact_eb_mem_Li
import Theorems.Thm_PI_KoszulExact_one_mem_pow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KoszulExact
theorem _root_.solution (i : Fin D) : ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)),
    x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b := by
  intro j
  induction j with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    show Dc R i 1 0 x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      by_cases hki : (k : ℕ) < i
      · exact ⟨eb R k, by rw [pow_one]; exact eb_mem_Li k _ hki, 0, Submodule.zero_mem _, by simp⟩
      · have : k = i := Fin.ext (by omega)
        subst this
        exact ⟨0, Submodule.zero_mem _, 1, one_mem_pow_zero _, by simp⟩
    | zero => exact Dc_zero i 1 0
    | add x y _ _ hx hy => exact Dc_add i 1 0 x y hx hy
    | smul r x _ hx => exact Dc_smul i 1 0 r x hx
  | succ j ih =>
    intro x hx
    rw [pow_succ'] at hx
    show Dc R i (j + 2) (j + 1) x
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      obtain ⟨a2, ha2, b2, hb2, rfl⟩ := ih n hn
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, hk, rfl⟩ := hy
        have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
        by_cases hki : (k : ℕ) < i
        · refine ⟨eb R k * a2, ?_, -(eb R k * b2), ?_, ?_⟩
          · rw [pow_succ']
            exact Submodule.mul_mem_mul (eb_mem_Li k _ hki) ha2
          · rw [pow_succ']
            exact Submodule.neg_mem _ (Submodule.mul_mem_mul (eb_mem_Li k _ hki) hb2)
          · rw [mul_add, ← mul_assoc, eb_mul_swap, neg_mul, mul_assoc, mul_neg]
        · have : k = i := Fin.ext (by omega)
          subst this
          refine ⟨0, Submodule.zero_mem _, a2, ha2, ?_⟩
          rw [mul_add, ← mul_assoc, eb_mul_self, zero_mul, add_zero, zero_add]
      | zero => rw [zero_mul]; exact Dc_zero i _ _
      | add x y _ _ hx hy => rw [add_mul]; exact Dc_add i _ _ _ _ hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Dc_smul i _ _ r _ hx
    · intro x y hx hy
      exact Dc_add i _ _ x y hx hy
end PI.KoszulExact
