-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.ga_yx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:31.635586+00:00
-- url     : https://prove2.me/submissions/ac4fb342-fe96-4e7b-875b-95876ed2f4d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_ga_nn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_ga_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_lev_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_lev_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_mv3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_heis_eq

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
theorem _root_.solution (hCL : HeisConjLev) (hInv : HeisInv) (k r' : ℕ) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (Yx k r' x) = Del k (1 + r') l (heis0 k r' (tm k r' x)) ^ 2 := by
  have hY : ∀ a, Yx k r' x a =
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := by
    intro a
    unfold Yx phi2 tm
    rw [hInv k r' x, heis_eq hCL k r' (-x.1) (-x.2), mv3 _ _ (lev_sq k r')]
  have hY' : Yx k r' x = fun a =>
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := funext hY
  have hU : (ιLev k 1 r' (Hpk k r'))ᴴ * ιLev k 1 r' (Hpk k r') = 1 := by rw [lev_conjT, lev_sq]
  rw [hY', ga_unit k (1 + r') l hU]
  unfold Del
  rw [Real.sq_sqrt (ga_nn _ _ _ _)]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
