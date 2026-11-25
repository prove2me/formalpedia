-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:05.230841+00:00
-- url     : https://prove2.me/submissions/1b7710cb-8eeb-43c2-acee-bff70c1c74dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (c : ℂ) : 0 ≤ mw k r' c :=
  le_min (Real.rpow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (norm_nonneg _))
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
