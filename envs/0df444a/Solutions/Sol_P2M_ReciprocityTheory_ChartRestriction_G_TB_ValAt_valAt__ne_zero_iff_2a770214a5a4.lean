-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__ne_zero_iff_2a770214a5a4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:48.01258+00:00
-- url     : https://prove2.me/submissions/1e104a0a-1dd1-4583-8ed2-0c3fdd4669a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp ℂ) :
    valAt' x U f ≠ 0 ↔ x p ∈ X.basicOpen f := by
  rw [valAt'_of _ _ h]
  have key : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  have e2 : (x.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (valAt x U h f) := by
    simp [valAt]
  change _ ↔ p ∈ x ⁻¹ᵁ X.basicOpen f
  rw [← key, e2, basicOpen_eq_of_affine]
  refine Iff.trans ?_ (PrimeSpectrum.mem_basicOpen (R := ℂ) (valAt x U h f) p).symm
  have hp := (p : PrimeSpectrum ℂ).isPrime
  have hb : (p : PrimeSpectrum ℂ).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hb, Submodule.mem_bot]
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
