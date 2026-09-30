-- Prove2me | solution 1 for VirialTheorem.momentOfInertia_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:08:24.038127+00:00
-- url     : https://prove2.me/submissions/e4b22c11-011f-43bd-8fd4-5714bfcc7cd5

import Definitions.Def_virial_theorem_defs

set_option autoImplicit false
open VirialTheorem

theorem solution {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space) (t : ℝ)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t) :
    HasDerivAt (momentOfInertia m r) (2 * virialG m r v t) t := by
  change HasDerivAt (fun s => ∑ k, m k * ‖r k s‖ ^ 2) _ t
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => ((hr k).norm_sq).const_mul (m k))
  convert hsum using 1 <;> try rfl
  dsimp [virialG]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_left, real_inner_comm (v k t) (r k t)]
  ring



