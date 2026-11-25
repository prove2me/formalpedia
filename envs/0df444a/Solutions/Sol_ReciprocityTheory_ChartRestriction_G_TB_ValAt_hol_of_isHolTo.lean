-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ValAt.hol_of_isHolTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:49.44919+00:00
-- url     : https://prove2.me/submissions/9594a436-acce-4bf9-9718-27f257d58100

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
open NumberField
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution (F : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => F bz.2)) (U : X.Opens) (f : Γ(X, U)) :
    IsOpen {z | ⊤ ≤ F z ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (F z) U f) {z | ⊤ ≤ F z ⁻¹ᵁ U} := by
  have h1 := h U f
  have hc : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := continuous_const.prodMk continuous_id
  have hd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  constructor
  · have ho := h1.1.preimage hc
    convert ho using 1
    ext z
    exact ⟨fun hz => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩, fun hz => hz.2⟩
  · intro z hz
    have hw := h1.2 ((0 : Fin 0 → ℂ), z) ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hz⟩
    exact hw.comp z (hd z).differentiableWithinAt (fun w hw' => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hw'⟩)
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
