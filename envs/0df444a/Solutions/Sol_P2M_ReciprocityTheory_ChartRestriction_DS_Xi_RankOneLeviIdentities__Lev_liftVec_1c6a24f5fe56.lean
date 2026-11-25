-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_liftVec_1c6a24f5fe56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:38.972978+00:00
-- url     : https://prove2.me/submissions/928e4b5a-6410-4448-ae97-7610d6e5f5e9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_lev
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (g : Mat k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' z = liftVec k 1 r' (g *ᵥ z) := by
  ext p
  rw [ιLev_mulVec, liftVec_apply]
  split_ifs with h
  · have e : (fun j => liftVec k 1 r' z (levPos k 1 r' j)) = z := funext (liftVec_lev k r' z)
    rw [e, liftVec_apply, dif_pos h]
  · rw [liftVec_apply, dif_neg h]
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
