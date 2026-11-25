-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_single_add_perm_ed287dfb2f19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:27.861622+00:00
-- url     : https://prove2.me/submissions/da2428ea-1cc0-4478-99b4-0db4516b8dcb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ : Type*} (cls : σ → K → ℤ) (s : σ) (μ : σ →₀ ℕ) :
    (classList cls (Finsupp.single s 1 + μ)).Perm (cls s :: classList cls μ) := by
  rw [← Multiset.coe_eq_coe]
  unfold classList
  rw [Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList]
  simp [Finsupp.toMultiset_single]
end GroundTheory.Heights₂.Heights.NumbersDVR
