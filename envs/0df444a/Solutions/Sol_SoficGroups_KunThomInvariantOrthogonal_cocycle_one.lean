-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.cocycle_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/fdf44ad0-c036-484e-9a86-494b547e0bf5

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
    (π : SoficGroups.UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h)) :
    b 1 = 0 := by
  have hcancel : b 1 + b 1 = b 1 + 0 := by
    simpa using (hb 1 1).symm
  exact add_left_cancel hcancel
end SoficGroups.KunThomInvariantOrthogonal
