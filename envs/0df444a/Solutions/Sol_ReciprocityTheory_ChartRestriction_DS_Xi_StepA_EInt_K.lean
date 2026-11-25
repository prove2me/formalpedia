-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.EInt_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:58.930424+00:00
-- url     : https://prove2.me/submissions/68d6b289-5e19-4e85-b35b-dabbe92b0dcd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_gN_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOne_levi_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (A : ℝ) (c : ℂ) {κ : Mat k r'} (hκ : κ ∈ Kset k r') (g : Mat k r') :
    EInt k r' A c (κ * g) = EInt k r' A c g := by
  unfold EInt
  refine lintegral_congr fun x => ?_
  have e : w0 k r' c * ιLev k 1 r' (κ * g) * heis0 k r' x =
      ιLev k 1 r' κ * (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
    rw [lev_mul, ← Matrix.mul_assoc (w0 k r' c), rankOne_levi_comm]; simp only [Matrix.mul_assoc]
  rw [e, gN_unitary k (1 + r') (lev_K k r' hκ).2]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
