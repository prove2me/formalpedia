-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.psd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:38:36.833876+00:00
-- url     : https://prove2.me/submissions/9a1c2121-fee5-40b6-9c31-00bccd24b32f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_chiAt_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_posSemidef_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
theorem _root_.solution (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (F : Frame X.Ψ r → ℂ)
    (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (τ0 : X.Ψ) : (Matrix.of (χ τ0)).PosSemidef := by
  refine posSemidef_of (X := X) hχ τ0 (fun x hx => ?_)
  have ha : ∀ τ : X.Ψ, (fun i => conj (x i)) ≠ 0 := by
    intro τ h
    apply hx
    funext i
    have h1 := congrFun h i
    simpa using h1
  have h2 := chiAt_nonneg X u hu la χ F hF hZ C hC hx0 hF0 (fun _ i => conj (x i)) ha τ0
  simpa [Data.chiAt, mul_comm, mul_left_comm, mul_assoc] using h2
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
