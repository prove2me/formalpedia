-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.hermitian_dual_base_vector_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:30.621799+00:00
-- url     : https://prove2.me/submissions/d76fff88-f4b7-45c0-9a3e-3f14e873dad9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_goodRowsProjector_apply_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hermitianForm_mulVec_basisSum

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
theorem _root_.solution (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (es0 k r') v = star (v ⟨0, by omega⟩) := by
  unfold herm
  rw [hermitianForm_mulVec_basisSum]
  simp only [dotProduct, Pi.star_apply, goodRowsProjector_apply_eq_sum]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
  · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
