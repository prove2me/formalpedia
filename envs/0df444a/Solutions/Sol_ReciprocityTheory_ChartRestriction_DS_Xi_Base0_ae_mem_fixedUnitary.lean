-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.ae_mem_fixedUnitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:27.883205+00:00
-- url     : https://prove2.me/submissions/5c2cdb0d-42e1-4408-8654-5f32a80cd485

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
theorem _root_.solution {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ∀ᵐ x ∂ν, (Matrix.of x : Mat k 0) ∈ U0 k := by
  first
  | exact ae_iff.2 hν.conc
  | (rw [ae_iff]; convert hν.conc using 1)
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
