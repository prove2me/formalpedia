-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_van_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:52.172737+00:00
-- url     : https://prove2.me/submissions/af2d1ae4-c419-4d41-adba-bf0e29f5cffa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (φ : R →+* MvPolynomial (Fin n) ℂ)
    (I : Ideal R) (w : Fin n → ℂ) :
    (∀ g ∈ I.map φ, eval w g = 0) ↔ ∀ g ∈ I, eval w (φ g) = 0 := by
  constructor
  · intro h g hg
    exact h _ (Ideal.mem_map_of_mem φ hg)
  · intro h g hg
    have hle : I.map φ ≤ RingHom.ker (eval w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact h x hx
    exact hle hg
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
