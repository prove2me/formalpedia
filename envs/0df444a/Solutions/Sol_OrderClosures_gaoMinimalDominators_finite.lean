-- Prove2me | solution 1 for OrderClosures.gaoMinimalDominators_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:07.727705+00:00
-- url     : https://prove2.me/submissions/d74a554c-8247-4686-a34d-afc5f74c98a0

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_gaoMinimalDominators_pairwise
public import Theorems.Thm_OrderClosures_ordinalProjection_incomparable_iInf


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hbne : b ≠ 0) :
    (gaoMinimalDominators ξ γ b).Finite := by
  classical
  by_contra hinf
  have hMInf : (gaoMinimalDominators ξ γ b).Infinite := hinf
  have hglb := ordinalProjection_incomparable_iInf ξ
    (gaoMinimalDominators ξ γ b) hMInf
    (gaoMinimalDominators_pairwise ξ γ b)
  have hbLower : b ∈ lowerBounds
      (ordinalProjection ξ '' gaoMinimalDominators ξ γ b) := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact hμ.1.2
  have hb_le_zero : b ≤ 0 := hglb.2 hbLower
  exact hbne (le_antisymm hb_le_zero hb0)
end OrderClosures
