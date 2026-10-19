-- Prove2me | solution 1 for SoficGroups.LocalMultiplicativeOn.map_inv_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/51b40c38-521c-4a30-90f4-b9c6eff073e8

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.LocalMultiplicativeOn
variable {G : Type u} {H : Type v} [Group G] [Group H]
namespace SoficGroups.LocalMultiplicativeOn
theorem _root_.solution {s : Finset G} {f : G → H}
    (h : LocalMultiplicativeOn s f) {x : G} (hx : x ∈ s) (hi : x⁻¹ ∈ s) :
    f x⁻¹ = (f x)⁻¹ := by
  have hm := h.map_mul x hx x⁻¹ hi
  rw [mul_inv_cancel, h.map_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm
end SoficGroups.LocalMultiplicativeOn
