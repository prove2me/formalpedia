-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.Bv_LZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:26.748309+00:00
-- url     : https://prove2.me/submissions/beb8c3f0-9f4f-4c3f-a5ad-3a282b198db7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_LZ_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)
variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
include hω
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (n : Fin (4 * Fintype.card X.Ψ) → ℤ) : Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum X g hω.1 n
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
