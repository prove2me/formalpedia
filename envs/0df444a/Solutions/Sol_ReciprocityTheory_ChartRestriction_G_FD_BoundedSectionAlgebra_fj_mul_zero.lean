-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:31.025162+00:00
-- url     : https://prove2.me/submissions/0b3a7c0c-4640-431a-8fb8-373fef341968

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_mod_of_bdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_sign_of_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
theorem _root_.solution (h3d : ModerateCoefficientPositivity (E := E)) (h3e : CoefficientConvolution (E := E)) {la la' : Wt X.Ψ r}
    {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la' Q) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ)
    (hvan : ∀ ν' : X.Ψ → ℝ, (∀ τ, 0 ≤ ν' τ) → (∀ τ, 0 ≤ ν τ - ν' τ) → X.fj la ξ ν' P x = 0) :
    X.fj (la + la') ξ ν (P * Q) x = 0 := by
  have hs := h3e r X la la' P Q hP.1 hQ.1 (mod_of_bdd X hP) (mod_of_bdd X hQ) ξ hξ x hx ν
  have hz : (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x) = 0 := by
    funext ν'
    by_cases h1 : X.fj la ξ ν' P x = 0
    · simp [h1]
    by_cases h2 : X.fj la' ξ (ν - ν') Q x = 0
    · simp [h2]
    exfalso
    apply h1
    apply hvan ν' (sign_of_bdd X h3d hP hξ ν' hx h1)
    intro τ
    have h3 := sign_of_bdd X h3d hQ hξ (ν - ν') hx h2 τ
    simpa using h3
  rw [hz] at hs
  exact hs.unique hasSum_zero
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
