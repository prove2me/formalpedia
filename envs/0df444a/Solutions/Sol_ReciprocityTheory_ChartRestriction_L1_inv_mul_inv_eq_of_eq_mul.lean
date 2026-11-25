-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inv_mul_inv_eq_of_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:31.931288+00:00
-- url     : https://prove2.me/submissions/abdd8bfd-bcf0-458f-b76b-2c7855b67abf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
omit [IsUltrametricDist K] [CharZero K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring
end ReciprocityTheory.ChartRestriction.L1
