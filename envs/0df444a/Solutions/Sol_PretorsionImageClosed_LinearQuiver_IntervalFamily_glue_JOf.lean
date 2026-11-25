-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.IntervalFamily.glue_JOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:09:23.35186+00:00
-- url     : https://prove2.me/submissions/f04798bf-73dd-459f-ada0-ce6b3b443a00

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
namespace IntervalFamily
theorem _root_.solution (D : IntervalFamily (n + 1)) : D.restrict.glue (JOf D) = D := by
  ext p
  rw [mem_glue]
  constructor
  · rintro (⟨a, d, rfl, had⟩ | ⟨h2, h1⟩)
    · exact mem_restrict.1 had
    · rw [mem_JOf] at h1
      have : p = (p.1, Fin.last n) := Prod.ext rfl h2
      rw [this]
      exact h1
  · intro hp
    obtain ⟨p1, p2⟩ := p
    induction p2 using Fin.lastCases with
    | last => exact Or.inr ⟨rfl, mem_JOf.2 hp⟩
    | cast d =>
      have hle : p1 ≤ d.castSucc := D.le_of_mem _ hp
      induction p1 using Fin.lastCases with
      | last => exact absurd hle (not_le.2 (Fin.castSucc_lt_last d))
      | cast a => exact Or.inl ⟨a, d, rfl, mem_restrict.2 hp⟩
end IntervalFamily
end PretorsionImageClosed.LinearQuiver
