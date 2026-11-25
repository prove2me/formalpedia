-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.finite_minimalGenerator_eq_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:04:28.827719+00:00
-- url     : https://prove2.me/submissions/61c8a4ab-7ae9-473c-89d1-af3e2826ed22

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_bot
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iInf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_inf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_top
public import Theorems.Thm_PretorsionImageClosed_SetClosure_extremePoints_subset_of_closure_eq
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints
public import Theorems.Thm_PretorsionImageClosed_SetClosure_not_mem_closure_union_of_finite
attribute [local simp] PretorsionImageClosed.SetClosure.coe_bot
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iInf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_inf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_pointClosure
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_top



set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {B C : Set E} (hC : c.IsClosed C)
    (hB : c.IsMinimalGenerator B C) :
    B = c.extremePoints C := by
  apply Set.Subset.antisymm
  · intro b hbB
    rw [mem_extremePoints]
    have hbC : b ∈ C := hB.1 ▸ c.le_closure B hbB
    refine ⟨hbC, ?_⟩
    have hbK : b ∉ c (B \ {b}) := by
      intro hb
      apply hB.2 hbB
      apply Set.Subset.antisymm
      · exact c.closure_min
          (fun z hz ↦ hB.1 ▸ c.le_closure B (sdiff_subset hz)) hC
      · intro z hzC
        have hzClosureB : z ∈ c B := hB.1.symm ▸ hzC
        have hBsub : B ⊆ c (B \ {b}) := by
          intro w hwB
          by_cases hwb : w = b
          · subst w
            exact hb
          · exact c.le_closure (B \ {b}) ⟨hwB, by simpa using hwb⟩
        have hz := c.monotone hBsub hzClosureB
        simpa using hz
    let K : Set E := c (B \ {b})
    have hK : c.IsClosed K := c.isClosed_closure _
    have hBinsert : B ⊆ insert b K := by
      intro z hzB
      by_cases hzb : z = b
      · simp [hzb]
      · exact mem_insert_of_mem b
          (c.le_closure (B \ {b}) ⟨hzB, by simpa using hzb⟩)
    have hCavailable : C ⊆ c (insert b K) := by
      intro z hzC
      exact c.monotone hBinsert (hB.1.symm ▸ hzC)
    intro hb
    obtain ⟨Y, hYfin, hYC, hbY⟩ := hfin hb
    have hYb : b ∉ Y := by
      intro hb'
      exact (hYC hb').2 rfl
    have hnot : b ∉ c (K ∪ Y) :=
      not_mem_closure_union_of_finite hae hK hbK hYfin
        (fun z hz ↦ hCavailable (hYC hz).1) hYb
    exact hnot (c.monotone subset_union_right hbY)
  · exact extremePoints_subset_of_closure_eq hB.1
end PretorsionImageClosed.SetClosure
