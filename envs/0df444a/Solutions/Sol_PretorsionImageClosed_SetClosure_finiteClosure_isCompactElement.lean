-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.finiteClosure_isCompactElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:13:19.505579+00:00
-- url     : https://prove2.me/submissions/8c2aff7f-6a10-49f4-b961-077deb9d4e95

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_bot
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iInf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_inf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_top
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_le_iff
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
    (hfin : c.IsFinitary) {B : Set E} (hBfin : B.Finite) :
    IsCompactElement (c.toCloseds B) := by
  classical
  let s : Finset E := hBfin.toFinset
  have hclosure :
      c.toCloseds B = s.sup c.pointClosure := by
    apply le_antisymm
    · apply c.closure_min
      · intro x hxB
        have hxs : x ∈ s := by
          simpa [s] using hxB
        have hle : c.pointClosure x ≤ s.sup c.pointClosure :=
          Finset.le_sup (s := s) (f := c.pointClosure) hxs
        exact hle (c.le_closure ({x} : Set E) (mem_singleton x))
      · exact (s.sup c.pointClosure).2
    · apply Finset.sup_le
      intro x hxs
      rw [pointClosure_le_iff]
      apply c.le_closure B
      simpa [s] using hxs
  rw [hclosure]
  apply CompleteLattice.isCompactElement_finsetSup s
  intro x _
  exact pointClosure_isCompactElement hfin x
end PretorsionImageClosed.SetClosure
