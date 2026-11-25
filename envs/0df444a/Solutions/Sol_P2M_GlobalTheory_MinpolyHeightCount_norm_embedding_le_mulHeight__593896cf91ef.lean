-- Prove2me | solution 1 for P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:24.51009+00:00
-- url     : https://prove2.me/submissions/1e0b7f8d-d628-457e-8e64-e0f7f3c4b789

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution (φ : K →+* ℂ) (c : K) : ‖φ c‖ ≤ Height.mulHeight₁ c := by
  classical
  set w := InfinitePlace.mk φ
  have hw : w c = ‖φ c‖ := InfinitePlace.apply φ c
  rw [← hw, NumberField.mulHeight₁_eq]
  have h1 : ∀ v : InfinitePlace K, 1 ≤ max (v c) 1 ^ v.mult :=
    fun v => one_le_pow₀ (le_max_right _ _)
  calc w c ≤ max (w c) 1 := le_max_left _ _
    _ ≤ max (w c) 1 ^ w.mult := le_self_pow₀ (le_max_right _ _) w.mult_ne_zero
    _ ≤ ∏ v : InfinitePlace K, max (v c) 1 ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod fun v _ => h1 v)
    _ ≤ _ := le_mul_of_one_le_right (Finset.prod_nonneg fun v _ => by positivity)
        (one_le_finprod fun _ => le_max_right _ _)
end GlobalTheory.MinpolyHeightCount
