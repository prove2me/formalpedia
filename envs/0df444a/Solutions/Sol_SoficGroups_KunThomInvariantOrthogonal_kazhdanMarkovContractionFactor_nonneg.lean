-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/04da3d83-2a05-41c7-ab9c-69d580aa0e6f

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
    (P : SoficGroups.KazhdanPair.{u, v} G) (S : Finset G) :
    0 ≤ kazhdanMarkovContractionFactor P S :=
  le_max_left _ _
end SoficGroups.KunThomInvariantOrthogonal
