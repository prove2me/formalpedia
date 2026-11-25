-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yhb3.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:42.235913+00:00
-- url     : https://prove2.me/submissions/0fb52b0d-a69c-469d-acbe-6f8943018f87

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace SupNormSqLeSumNormSq
private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)
end SupNormSqLeSumNormSq
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhb3
theorem _root_.solution :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
end UpperTheory.Reformulated.B.Yhb3
