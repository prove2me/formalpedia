-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:03.295117+00:00
-- url     : https://prove2.me/submissions/3f57848d-0381-4ca1-80f2-d969ecc6f749

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_isWeightedHomogeneous_sepBlock_9e2d0892eba8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) :
    coeffVec (offMonos n k₀ D) (atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  classical
  have hp' := finsum_weightedHomogeneousComponent (coordDeg n) p
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)] at hp'
  rw [← hp', map_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  have hqP : weightedHomogeneousComponent (coordDeg n) m p ∈ P.ideal := P.homogeneous p hp m
  have hqh := isWeightedHomogeneous_sepBlock k₀
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := coordDeg n) m p)
  by_cases hm : Function.update m k₀ 0 = offDeg k₀ D
  · exact Submodule.subset_span ⟨_, ⟨hqP, hm ▸ hqh⟩, rfl⟩
  · have h0 : coeffVec (offMonos n k₀ D) (atBlock k₀ w (weightedHomogeneousComponent (coordDeg n) m p))
        = 0 := by
      funext μ
      rw [coeffVec_apply, atBlock_apply, coeff_map]
      have hμ := mem_offMonos.mp μ.2
      rw [hqh.coeff_eq_zero μ.1 (by rw [hμ]; exact Ne.symm hm), map_zero]
      rfl
    rw [h0]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.BlockSurjectivity
