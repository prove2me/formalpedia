-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.crossedKernelAndImage
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:18:40.898985+00:00
-- url     : https://prove2.me/submissions/81eae455-a022-4252-bef1-38c97d9a7e5e

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P20
universe u v

theorem solution {C : Type u} {G : Type v} [Group C] [Group G]
    (boundary : C →* G) (action : G →* MulAut C) (h : CrossedModule boundary action) :
    (∀ a b : boundary.ker, a * b = b * a) ∧ boundary.range.Normal := by
  constructor
  · intro a b
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    have ha : boundary a.val = 1 := a.property
    have hp : b.val = a.val * b.val * a.val⁻¹ := by
      simpa only [ha, map_one, MulAut.one_apply] using h.2 a.val b.val
    have hm := congrArg (fun x : C => x * a.val) hp
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  · constructor
    intro y hy g
    rcases hy with ⟨c, rfl⟩
    exact ⟨action g c, h.1 g c⟩

#print axioms solution
