-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:26.826342+00:00
-- url     : https://prove2.me/submissions/62d93bfa-de16-4d71-8bc5-4d9a94a2c584

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
end GroundTheory.Heights₂.Heights.FlagTypings
