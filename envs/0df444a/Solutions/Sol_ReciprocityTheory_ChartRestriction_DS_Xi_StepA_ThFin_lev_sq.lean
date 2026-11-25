-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.lev_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:53.99591+00:00
-- url     : https://prove2.me/submissions/c1bd2982-1fd9-4e81-b545-5482570a0a44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Hpk_mulVec_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mat_eq_of_mulVec


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
theorem _root_.solution (k r' : ℕ) : ιLev k 1 r' (Hpk k r') * ιLev k 1 r' (Hpk k r') = 1 := by
  apply mat_eq_of_mulVec
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have e : (fun j => (ιLev k 1 r' (Hpk k r') *ᵥ v) (levPos k 1 r' j)) =
      Hpk k r' *ᵥ fun j => v (levPos k 1 r' j) := by
    funext j
    rw [RankOneLeviIdentities.ιLev_mulVec, dif_pos ⟨Nat.le_add_left 1 j.val, by
      show j.val + 1 < 2 * r' + k + 1 + 1; omega⟩]
    congr 1
  ext p
  rw [RankOneLeviIdentities.ιLev_mulVec]
  split_ifs with h
  · rw [e, Hpk_mulVec_mulVec]
    exact congrArg v (Fin.ext (show p.val - 1 + 1 = p.val by omega))
  · rw [RankOneLeviIdentities.ιLev_mulVec, dif_neg h]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
