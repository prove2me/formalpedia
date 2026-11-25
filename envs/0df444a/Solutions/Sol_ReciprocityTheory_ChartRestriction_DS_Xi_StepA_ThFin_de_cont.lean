-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.de_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:59.499083+00:00
-- url     : https://prove2.me/submissions/e0fedf60-4824-4629-a1bd-25109059743a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_lsq_cont

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
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l := by
  unfold de
  refine Real.continuous_sqrt.comp (((lsq_cont l).mul ?_).add ?_)
  · unfold rhoSq
    exact ((lsq_cont _).add (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2)).add
      (continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2) continuous_const)
  · have h2 : Continuous fun x : Xp p m => ∑ j : Fin p, if (l : ℕ) ≤ (j : ℕ) then x.2.1 j * star (x.1 j) else 0 :=
      continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
          ((continuous_apply j).comp continuous_fst).star) continuous_const
    unfold bco
    fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
