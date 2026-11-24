-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.continuous_tW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:51.907276+00:00
-- url     : https://prove2.me/submissions/87631443-9a0c-4f7f-861c-11f14f4c9384

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι) : Continuous (tW q) := by
  show Continuous fun x : ι → ℂ => Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_if_const _ (fun _ => continuous_const)
      (fun _ => Complex.continuous_normSq.comp (continuous_apply i)))
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
