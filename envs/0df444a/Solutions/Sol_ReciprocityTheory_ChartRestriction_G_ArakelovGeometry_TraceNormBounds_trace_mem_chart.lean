-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.trace_mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:27.408917+00:00
-- url     : https://prove2.me/submissions/ef8ee806-ced8-43d7-bece-c1b67243cfa5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_chartRing_closed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_chartRing_frac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_isIntegral
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
theorem _root_.solution [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ ∈ chartRing x e l := by
  have hi := sec_div_isIntegral x e h l n hs
  haveI := chartRing_frac x e h.free l
  haveI := chartRing_closed x e h.free l
  by_cases hfd : FiniteDimensional (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
  · haveI := hfd
    have ht := Algebra.isIntegral_trace (L := fnField (x ∘ e)) hi
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := fnField (x ∘ e))).1 ht
    rw [← hy]
    exact y.2
  · have hnb : ¬∃ s : Finset (IntermediateField.extendScalars (fnField_comp_le' x e)),
        Nonempty (Basis s (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))) := by
      rintro ⟨s, ⟨b⟩⟩
      first
        | exact hfd (FiniteDimensional.of_fintype_basis b)
        | exact hfd (Module.Finite.of_basis b)
    have h0 : Algebra.trace (fnField (x ∘ e))
        (IntermediateField.extendScalars (fnField_comp_le' x e)) = 0 := by
      first
        | exact Algebra.trace_eq_zero_of_not_exists_basis _ hnb
        | exact Algebra.trace_eq_zero_of_not_exists_basis hnb
    rw [h0, LinearMap.zero_apply]
    exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
