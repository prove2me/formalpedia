-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:06.121436+00:00
-- url     : https://prove2.me/submissions/faff5ebd-a5a6-4bcc-b000-0d06d0778a60

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
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution {N : ℕ} (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ : List (Fin N)) : Multiset (Fin N)) = Finsupp.toMultiset μ := by
  ext a
  rw [Multiset.coe_count, Finsupp.count_toMultiset]
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.monoList, List.count_flatMap]
  rw [← Fin.sum_univ_def]
  simp [List.count_replicate]
end GroundTheory.Heights₂.Heights.FlagTypings
