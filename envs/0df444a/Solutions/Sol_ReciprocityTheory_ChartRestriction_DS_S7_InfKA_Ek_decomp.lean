-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.Ek_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:35.623194+00:00
-- url     : https://prove2.me/submissions/6f84ca76-6081-4857-a88d-f168166b4d9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A P Q : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Ek T μ x φ A (P + Complex.I • Q) k = Ek T μ x φ A P k + Complex.I • Ek T μ x φ A Q k := by
  have h1 : toMK k⁻¹ * A * toMK k * (P + Complex.I • Q) - (P + Complex.I • Q) * (toMK k⁻¹ * A * toMK k) =
      (toMK k⁻¹ * A * toMK k * P - P * (toMK k⁻¹ * A * toMK k)) +
        Complex.I • (toMK k⁻¹ * A * toMK k * Q - Q * (toMK k⁻¹ * A * toMK k)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    abel
  simp only [Ek, h1, map_add, map_smul, smul_eq_mul]
  first
  | module
  | (simp only [smul_add, add_smul, smul_smul, mul_comm]; abel)
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
