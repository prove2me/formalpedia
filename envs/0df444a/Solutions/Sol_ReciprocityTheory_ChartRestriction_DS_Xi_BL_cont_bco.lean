-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.cont_bco
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:24.982989+00:00
-- url     : https://prove2.me/submissions/31002646-6bbe-4de6-93ab-78f92ea914bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_cont_ite

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
theorem _root_.solution (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
