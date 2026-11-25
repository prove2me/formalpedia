-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:48.532093+00:00
-- url     : https://prove2.me/submissions/5e18ec62-8189-49e7-a266-dcef9dcb028e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hpk_conjT__409f3ae7451d

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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec q) v = star ((Hpk k r *ᵥ v) q) := by
  have hc : ∀ p, star (Hpk k r q p) = Hpk k r p q := fun p => by
    have := congrFun (congrFun (hpk_conjT' k r) p) q
    rwa [conjTranspose_apply] at this
  unfold herm bvec
  rw [mulVec_single_one]
  simp only [dotProduct, mulVec, star_sum, star_mul', hc, Pi.star_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
