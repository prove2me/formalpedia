-- Prove2me | solution 1 for SoficGroups.large_cut_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/4079a50b-154e-4845-999f-82c4660b707c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {γ ell a d N b e q : ℝ}
    (hgap : ell < γ) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hdeleted : (γ - ell) * b ≤ a * N)
    (hsmall : 2 * a * (2 * (γ - ell) + d) ≤ (γ - ell) ^ 2)
    (hlarge : N / 2 - b < e)
    (hcut : γ * e - a * N - d * b ≤ q) :
    ell * e ≤ q := by
  have hδ : 0 < γ - ell := sub_pos.mpr hgap
  have hδd : 0 ≤ (γ - ell) + d := by linarith
  have hscaledDeleted := mul_le_mul_of_nonneg_left hdeleted hδd
  have hscaledSmall := mul_le_mul_of_nonneg_right hsmall hN
  have hscaledLarge := mul_lt_mul_of_pos_left hlarge hδ
  nlinarith
end SoficGroups
