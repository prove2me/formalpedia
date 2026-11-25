-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.lint_lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:40.312875+00:00
-- url     : https://prove2.me/submissions/cbac544b-9f81-4b65-9e4e-2accd0c91254

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {a : Mat k 0} (ha : a ∈ U0 k)
    {F : Mt k 0 → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, F (lmulM a x) ∂ν = ∫⁻ x, F x ∂ν := by
  have hm : Measurable (lmulM (k := k) (r := 0) a) := by
    have hc : Continuous (lmulM (k := k) (r := 0) a) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      show Continuous fun x : Mt k 0 => (a * Matrix.of x) i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact continuous_finset_sum _ fun l _ =>
        continuous_const.mul ((continuous_apply j).comp (continuous_apply l))
    exact hc.measurable
  rw [← lintegral_map hF hm, hν.left a ha]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
