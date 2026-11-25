-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.brFib_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:43.491741+00:00
-- url     : https://prove2.me/submissions/6b801a7d-669d-4ba5-ae47-3af6877d720c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_notMemB_of_notMem_brBad
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_projection_zero_ne_of_notMem_bridgeBadSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_brW_mem_fibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_brW_injOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  refine Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)
  · intro x hx
    have h0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2
    have hq : brQ R Ψ x = y := hx.1
    rw [← hq]
    exact brW_mem_fibre R Ψ hP.1 hPh h0
  · intro x hx x' hx' h
    exact brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩
      ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h
end ReciprocityTheory.ChartRestriction.G.Geo
