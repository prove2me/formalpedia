-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.la_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:39.704268+00:00
-- url     : https://prove2.me/submissions/eb5f3fde-7936-4930-a9c2-dc4a466483f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
theorem _root_.solution {T μ x : ℝ} (hT : 1 ≤ T) (hμ : 2 * μ ^ 2 ≤ T ^ 2) {p0 : ℕ} (hp0 : 1 ≤ p0)
    (hx : x ≤ T ^ 2 ∨ x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2)) : x ≤ (T ^ (2 * p0 - 1)) ^ 2 := by
  have he : (T ^ (2 * p0 - 1)) ^ 2 = T ^ (4 * (p0 - 1)) * T ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  have h1 : 1 ≤ T ^ (4 * (p0 - 1)) := one_le_pow₀ hT
  rcases hx with hx | hx
  · calc x ≤ T ^ 2 := hx
      _ = 1 * T ^ 2 := by ring
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr
  · calc x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2) := hx
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
