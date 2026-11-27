-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isConeSetB_coneOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:34.788843+00:00
-- url     : https://prove2.me/submissions/c07f18eb-51d0-42f7-bd55-cc5ed99984e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) :
    IsConeSetB (coneOver U γ) := by
  intro c z hc
  constructor
  · rintro ⟨y, hy, c', hc', hz⟩
    refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
    rw [mul_smul, ← hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨y, hy, c', hc', rfl⟩
    exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
