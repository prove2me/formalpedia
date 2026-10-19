-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.sum_sub_finiteMean_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/a2ad2a11-c2ec-4ea7-b909-172a9acc4775

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.CheegerPoincare
open scoped BigOperators
namespace SoficGroups.CheegerPoincare
theorem _root_.solution {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (∑ x : V, (f x - finiteMean f)) = 0 := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, finiteMean]
  field_simp
  ring
end SoficGroups.CheegerPoincare
