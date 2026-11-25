-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.adjoin_gL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:53.551801+00:00
-- url     : https://prove2.me/submissions/8050a282-58ef-430d-859c-7f52a07285ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Lx_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK

set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    adjoin (fnField (x ∘ e)) (Set.range (gL x e)) = ⊤ := by
  apply IntermediateField.map_injective (Lx x e).val
  have htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp, htop]
  exact (Lx_eq x e hx0).symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
