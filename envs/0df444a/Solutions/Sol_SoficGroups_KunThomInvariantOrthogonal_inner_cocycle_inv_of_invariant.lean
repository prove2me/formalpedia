-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.inner_cocycle_inv_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/e8f7fdd2-412c-4a03-bcb5-41f04cf437ee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_cocycle_one

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
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (y : H) (hy : ∀ g : G, π g y = y) (g : G) :
    @inner ℂ H _ y (b g⁻¹) = -@inner ℂ H _ y (b g) := by
  have hysymm : (π g).symm y = y := by
    have hyinv := hy g⁻¹
    simpa [map_inv, LinearIsometryEquiv.inv_def] using hyinv
  have htransport :
      @inner ℂ H _ y (π g (b g⁻¹)) = @inner ℂ H _ y (b g⁻¹) := by
    calc
      @inner ℂ H _ y (π g (b g⁻¹)) =
          @inner ℂ H _ ((π g).symm y) (b g⁻¹) := by
            simpa using
              ((π g).symm.inner_map_map y (π g (b g⁻¹))).symm
      _ = @inner ℂ H _ y (b g⁻¹) := by rw [hysymm]
  have hsum : b g + π g (b g⁻¹) = 0 := by
    calc
      b g + π g (b g⁻¹) = b (g * g⁻¹) := (hb g g⁻¹).symm
      _ = b 1 := by rw [mul_inv_cancel]
      _ = 0 := cocycle_one π b hb
  have hinner :
      @inner ℂ H _ y (b g) + @inner ℂ H _ y (b g⁻¹) = 0 := by
    have h := congrArg (fun x : H => @inner ℂ H _ y x) hsum
    simpa [inner_add_right, htransport] using h
  apply (add_eq_zero_iff_eq_neg).mp
  simpa [add_comm] using hinner
end SoficGroups.KunThomInvariantOrthogonal
