-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:45.953004+00:00
-- url     : https://prove2.me/submissions/d57a9551-feb8-4797-a18b-5972aa659619

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (A : HermLine n) {y : Cone n K} (hy : BlockNonzero y) :
    ∑ᶠ w : FinitePlace L, finiteTerm A w (fun k i ↦ algebraMap K L (y k i)) =
      finrank K L * ∑ᶠ v : FinitePlace K, finiteTerm A v y := by
  have hyL : ∀ k, (fun i ↦ algebraMap K L (y k i)) ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hy k)
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  unfold finiteTerm
  rw [finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hyL k),
    finsum_sum_mul _ _ fun k ↦ support_log_iSup_place_finite (hy k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finsum_log_iSup_algebraMap (hy k)]
  ring
end GroundTheory.Heights₂.Heights
