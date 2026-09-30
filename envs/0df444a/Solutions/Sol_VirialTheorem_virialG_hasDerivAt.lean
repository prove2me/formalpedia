-- Prove2me | solution 1 for VirialTheorem.virialG_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:06:46.388848+00:00
-- url     : https://prove2.me/submissions/566a08d7-5f68-4f76-8191-4fceae757057

import Definitions.Def_virial_theorem_defs

set_option autoImplicit false
open VirialTheorem

theorem solution {N : ℕ} (m : Fin N → ℝ) (r v F : Fin N → ℝ → Space) (t : ℝ)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k, HasDerivAt (fun s => m k • v k s) (F k t) t) :
    HasDerivAt (virialG m r v) (2 * kineticEnergy m v t + ∑ k, inner ℝ (F k t) (r k t)) t := by
  change HasDerivAt (fun s => ∑ k, inner ℝ (m k • v k s) (r k s)) _ t
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hp k).inner ℝ (hr k))
  simpa [virialG, kineticEnergy, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Finset.sum_add_distrib] using hsum

