-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_conjT__409f3ae7451d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:57.010115+00:00
-- url     : https://prove2.me/submissions/fb21a3d1-edf1-4d9f-8e5a-d86741f48de3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight

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
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [conjTranspose_apply, Hpk, Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
