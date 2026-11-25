-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.trace_mem_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:24.92067+00:00
-- url     : https://prove2.me/submissions/792de0be-1927-4a0d-9266-a62b39c59da7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mem_sec_of_charts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_trace_chart_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_homog_of_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_trace_mem_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
private theorem coord_ne_zero_of_coordIdeal_eq_bot (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (i : Fin (D + 1)) :
    y i ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h0]
  rw [hfree, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero i hmem
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ)
    {s : Ω} (hs : s ∈ sec ℤ x n) :
    x (e 0) ^ n * ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) ∈ sec ℤ (x ∘ e) n := by
  have hne : ∀ j, x (e j) ≠ 0 := fun j => coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free j
  choose N0 hN0 using fun j => homog_of_chart x e j _ (trace_mem_chart x e h j n hs) (hne j)
  choose H hHh hHe using fun j => hN0 j (Finset.univ.sup N0 + n)
    (le_trans (Finset.le_sup (Finset.mem_univ j)) (Nat.le_add_right _ _))
  refine mem_sec_of_charts (x ∘ e) h.free _ n (Finset.univ.sup N0) H hHh (fun j => ?_)
  rw [← hHe j, trace_chart_eq x e (hne 0) j (hne j) n hs]
  simp only [Function.comp_apply]
  have hj := hne j
  rw [div_pow, pow_add]
  field_simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
