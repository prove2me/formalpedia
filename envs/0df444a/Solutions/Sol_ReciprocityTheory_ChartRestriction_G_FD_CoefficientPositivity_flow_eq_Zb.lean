-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.flow_eq_Zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:15.08881+00:00
-- url     : https://prove2.me/submissions/5c5ad296-2b37-42c6-adbc-702db48cac14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowV_uvec


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
theorem _root_.solution (X : Data E r) (u : Fin 2 → Fin r → E) (ξ : Fin r → E) (a : X.Ψ → Fin 2 → ℂ)
    (hemb : ∀ τ : X.Ψ, Data.emb τ.1 ξ = X.uvec u a τ) (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) y = X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) y := by
  have h1 : X.flow ξ (fun τ => (s τ : ℂ)) y = X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) y := by
    funext τ
    simp only [Data.flow, Data.flowV]
    congr 1
    rw [← hemb τ]
    ext i j
    simp [Data.flowMat, Data.flowMatV, Data.emb]
  rw [h1, X.flowV_uvec]
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
