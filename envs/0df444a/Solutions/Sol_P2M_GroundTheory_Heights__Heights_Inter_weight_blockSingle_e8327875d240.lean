-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_weight_blockSingle_e8327875d240
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:20.307429+00:00
-- url     : https://prove2.me/submissions/3377130b-11d5-4d76-a730-72be58ba223a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]
end GroundTheory.Heights₂.Heights.Inter
