-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_monoList_perm_282dba544287
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:18.329228+00:00
-- url     : https://prove2.me/submissions/933ef0f1-36de-48a5-ad65-5c5998ec20e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1

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
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution {N : ℕ} (cls : Fin N → K → ℤ) (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map cls).Perm (NumbersDVR.classList cls μ) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, coe_monoList, NumbersDVR.classList,
    Multiset.coe_toList]
end GroundTheory.Heights₂.Heights.FlagTypings
