-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_length_monoList_15dd32156d22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:16.35412+00:00
-- url     : https://prove2.me/submissions/bcde7464-bff6-4b84-9427-10fe1439c8c1

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
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution {N : ℕ} {Q : MvPolynomial (Fin N) ℤ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    {μ : Fin N →₀ ℕ} (hμ : μ ∈ Q.support) : (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length = d := by
  have h1 : (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length = Multiset.card (Finsupp.toMultiset μ) := by
    rw [← coe_monoList, Multiset.coe_card]
  have h2 := hQ (mem_support_iff.mp hμ)
  rw [h1, Finsupp.card_toMultiset, ← h2, Finsupp.weight_apply]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rfl
end GroundTheory.Heights₂.Heights.FlagTypings
