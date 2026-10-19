-- Prove2me | solution 1 for SoficGroups.KunCombinedPrescribedRootSourceTolerance.eventually_scaled_tolerance_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/ed983ceb-7827-4c48-ba40-1b2ca0ae7059

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCombinedPrescribedRootSourceTolerance
open Filter Topology
namespace SoficGroups.KunCombinedPrescribedRootSourceTolerance
theorem _root_.solution
    (N t : ℕ → ℕ)
    (hN : ∀ n, 0 < N n)
    (ht : Tendsto (fun n => (t n : ℝ) / (N n : ℝ)) atTop (𝓝 0))
    (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell) :
    ∀ᶠ n in atTop, c * (t n : ℝ) < ell * (N n : ℝ) := by
  have hthreshold : 0 < ell / c := div_pos hell hc
  filter_upwards [ht.eventually (gt_mem_nhds hthreshold)] with n hn
  have hNreal : (0 : ℝ) < N n := by
    exact_mod_cast hN n
  have hratio : (t n : ℝ) < (ell / c) * (N n : ℝ) :=
    (div_lt_iff₀ hNreal).mp hn
  calc
    c * (t n : ℝ) < c * ((ell / c) * (N n : ℝ)) :=
      mul_lt_mul_of_pos_left hratio hc
    _ = ell * (N n : ℝ) := by
      field_simp
end SoficGroups.KunCombinedPrescribedRootSourceTolerance
