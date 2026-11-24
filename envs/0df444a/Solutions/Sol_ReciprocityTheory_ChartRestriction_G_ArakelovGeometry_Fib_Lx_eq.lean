-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Lx_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:48.94934+00:00
-- url     : https://prove2.me/submissions/51414559-436b-4458-8fd1-d36d68d1a4e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField

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
    Lx x e = adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · intro t ht
    have key : fnField x ≤
        (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro s ⟨i, j, rfl⟩
      have hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨i, rfl⟩
      have hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨j, rfl⟩
      have hq := div_mem hi hj
      have e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j := by
        by_cases hj0 : x j = 0
        · simp [hj0]
        · field_simp
      rw [e2] at hq
      exact hq
    exact key ht
  · rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
