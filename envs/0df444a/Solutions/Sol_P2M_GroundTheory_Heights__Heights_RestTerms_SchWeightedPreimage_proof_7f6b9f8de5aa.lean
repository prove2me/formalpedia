-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchWeightedPreimage_proof_7f6b9f8de5aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:30.090995+00:00
-- url     : https://prove2.me/submissions/a8e3a209-d857-4cf4-b10e-f277a20b423b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchWeightedPreimage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchWeightedPreimage
theorem _root_.solution (h1 : SchPowerSumHomWeighted.Statement) :
    SchWeightedPreimage.Statement := by
  classical
  intro N k P hsym hhom
  obtain ⟨S₀, hS₀⟩ := Flag.exists_powerSumHom_eq hsym
  let w : Fin N → ℕ := fun i => (i : ℕ) + 1
  refine ⟨weightedHomogeneousComponent w k S₀, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous k S₀⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := w) S₀
  have hsum := sum_weightedHomogeneousComponent w S₀
  rw [finsum_eq_sum _ hfin] at hsum
  have hterm : ∀ m : ℕ, homogeneousComponent k (powerSumHom N (weightedHomogeneousComponent w m S₀))
      = if k = m then powerSumHom N (weightedHomogeneousComponent w m S₀) else 0 :=
    fun m => homogeneousComponent_of_mem
      (h1 N m _ (weightedHomogeneousComponent_isWeightedHomogeneous m S₀))
  have key : homogeneousComponent k (powerSumHom N S₀) =
      powerSumHom N (weightedHomogeneousComponent w k S₀) := by
    conv_lhs => rw [← hsum]
    rw [map_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have hk0 : weightedHomogeneousComponent w k S₀ = 0 := by
        by_contra hne
        exact hk (Set.Finite.mem_toFinset (hs := hfin) |>.mpr hne)
      rw [hk0, map_zero]
  rw [← key, hS₀, homogeneousComponent_eq_self hhom]
end SchWeightedPreimage
end GroundTheory.Heights₂.Heights.RestTerms
