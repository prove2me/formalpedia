-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_fix_7b458090db62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:14.505922+00:00
-- url     : https://prove2.me/submissions/80a9f057-70e1-4433-8efd-36ea8c34c9c6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
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
theorem _root_.solution (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hu : ∀ q : Fin (2 * (1 + r') + k + 1), (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → u q = 0) :
    ιLev k 1 r' g *ᵥ u = u := by
  ext p
  rw [ιLev_mulVec]
  split_ifs with h
  · have : (fun j => u (levPos k 1 r' j)) = 0 := by
      ext j; apply hu; rw [levPos_val]; omega
    rw [this, mulVec_zero, hu p h]; rfl
  · rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
