-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/acb0e275-5255-48f2-afa8-5fcd249735f5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    (P : SoficGroups.KazhdanPair.{u, v} G)
    (S : Finset G) (hS : S.Nonempty) :
    kazhdanMarkovContractionFactor P S < 1 := by
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hpositive :
      0 < P.kazhdanConstant ^ 2 / (4 * (S.card : ℝ)) := by
    exact div_pos (sq_pos_of_pos P.positive)
      (mul_pos (by norm_num) hcard)
  unfold kazhdanMarkovContractionFactor
  exact max_lt (by norm_num) (by linarith)
end SoficGroups.KunThomInvariantOrthogonal
