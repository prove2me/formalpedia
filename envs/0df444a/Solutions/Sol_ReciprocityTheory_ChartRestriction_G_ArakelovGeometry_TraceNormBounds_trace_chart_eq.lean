-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.trace_chart_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:10.368831+00:00
-- url     : https://prove2.me/submissions/7bc85c1a-6d5b-4263-904d-bf8189d3391a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h0 : x (e 0) ≠ 0)
    (l : Fin (D + 1)) (hl : x (e l) ≠ 0) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : fnField (x ∘ e)) : Ω) =
    (x (e 0) / x (e l)) ^ n *
      ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) := by
  have hc : (x (e 0) / x (e l)) ^ n ∈ fnField (x ∘ e) := pow_mem (div_mem_fnField (x ∘ e) 0 l) n
  have heq : (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) =
      (⟨(x (e 0) / x (e l)) ^ n, hc⟩ : fnField (x ∘ e)) • ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ := by
    apply Subtype.ext
    show s / x (e l) ^ n = (x (e 0) / x (e l)) ^ n * (s / x (e 0) ^ n)
    rw [div_pow]
    field_simp
  rw [heq, LinearMap.map_smul, smul_eq_mul]
  rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
