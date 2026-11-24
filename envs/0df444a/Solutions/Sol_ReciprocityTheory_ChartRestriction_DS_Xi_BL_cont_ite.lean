-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.cont_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:20.734585+00:00
-- url     : https://prove2.me/submissions/87ffc7f2-64b4-4a28-b706-e3a04c2df4bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {p m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
