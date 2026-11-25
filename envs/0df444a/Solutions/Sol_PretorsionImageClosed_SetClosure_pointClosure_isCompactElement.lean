-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.pointClosure_isCompactElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:04:15.306598+00:00
-- url     : https://prove2.me/submissions/50c0516d-8f9b-4ba6-8bb7-7a3134ae74d1

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
    (hfin : c.IsFinitary) (x : E) :
    IsCompactElement (c.pointClosure x) := by
  classical
  intro S b hSne hSdir hSb hxS
  have hxS' : c.pointClosure x ≤ sSup S := hSb.sSup_eq ▸ hxS
  have hxClosure : x ∈ c (⋃ C : S, (C.1 : Set E)) := by
    have hx : x ∈ ((sSup S : c.Closeds) : Set E) :=
      pointClosure_le_iff.1 hxS'
    simpa using hx
  obtain ⟨Y, hYfin, hYsub, hxY⟩ := hfin hxClosure
  have hcover : ∀ y : Y, ∃ C : S, y.1 ∈ (C.1 : Set E) := by
    intro y
    have hy := hYsub y.2
    simpa only [Set.mem_iUnion] using hy
  choose f hf using hcover
  let : Fintype Y := hYfin.fintype
  let T : Finset c.Closeds :=
    Finset.univ.image fun y : Y ↦ (f y).1
  have hTS : (T : Set c.Closeds) ⊆ S := by
    intro C hC
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hC
    exact (f y).2
  have hTbound : ∀ (U : Finset c.Closeds), (U : Set c.Closeds) ⊆ S → ∃ C ∈ S, U.sup id ≤ C := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨C₀, hC₀⟩ := hSne
      exact ⟨C₀, hC₀, bot_le⟩
    | @insert a T' _ ih =>
      intro hU
      have haS : a ∈ S := hU (Finset.mem_insert_self a T')
      have hT'S : (T' : Set c.Closeds) ⊆ S := fun z hz => hU (Finset.mem_insert_of_mem hz)
      obtain ⟨C', hC'S, hT'C'⟩ := ih hT'S
      obtain ⟨C, hCS, haC, hC'C⟩ := hSdir a haS C' hC'S
      exact ⟨C, hCS, by rw [Finset.sup_insert]; exact sup_le haC (hT'C'.trans hC'C)⟩
  obtain ⟨C, hCS, hTC⟩ := hTbound T hTS
  refine ⟨C, hCS, le_trans ?_ hTC⟩
  rw [pointClosure_le_iff]
  have hYsup : Y ⊆ ((T.sup id : c.Closeds) : Set E) := by
    intro y hyY
    let y' : Y := ⟨y, hyY⟩
    have hmem : (f y').1 ∈ T := by
      apply Finset.mem_image.mpr
      exact ⟨y', Finset.mem_univ _, rfl⟩
    have hle : (f y').1 ≤ T.sup id :=
      Finset.le_sup (s := T) (f := id) hmem
    exact hle (hf y')
  exact c.closure_min hYsup (T.sup id).2 hxY
end PretorsionImageClosed.SetClosure
