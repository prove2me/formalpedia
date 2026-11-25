-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.cont_linF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:50.8548+00:00
-- url     : https://prove2.me/submissions/09d93605-d0d8-4c7a-8066-929aa8641c29

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
theorem _root_.solution (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
