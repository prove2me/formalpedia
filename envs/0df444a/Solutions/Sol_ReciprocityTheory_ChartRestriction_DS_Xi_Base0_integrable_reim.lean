-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_reim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:37.78746+00:00
-- url     : https://prove2.me/submissions/0c4f8a01-d7bc-4302-be9b-b33cc939370f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {p q : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q) :
    Integrable (fun z : ℂ => p z.re * q z.im) := by
  have h : Integrable (fun z : ℝ × ℝ => p z.1 * q z.2) (volume.prod volume) := by
    first
    | exact Integrable.mul_prod hp hq
    | exact Integrable.prod_mul hp hq
    | exact Integrable.prod_smul hp hq
  have e := Complex.volume_preserving_equiv_real_prod
  have h2 := (e.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).2 h
  first
  | exact h2
  | (convert h2 using 1; funext z; rfl)
  | (convert h2 using 1; funext z; simp [Complex.measurableEquivRealProd])
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
