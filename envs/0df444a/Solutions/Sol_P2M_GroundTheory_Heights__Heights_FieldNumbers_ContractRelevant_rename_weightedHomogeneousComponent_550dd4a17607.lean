-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:23.153711+00:00
-- url     : https://prove2.me/submissions/552e7613-92ae-46e9-8d0c-d07368199846

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_extend_zero_inj_2eeca3831901
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_weight_mapDomain_f233384a8c53

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)
include hgj
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
theorem _root_.solution (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain g d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg,
      coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
