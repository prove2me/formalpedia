-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_mem_minimalPrimes_1a5a33e9bb16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:28.630523+00:00
-- url     : https://prove2.me/submissions/b76f2f6e-2946-4af3-8201-39cf93916f23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockDeg_component_mem_56f385ad8a51
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution [Fintype K] {I W : Ideal (MRing ι F)}
    (hI : IsMultiHomogIdeal I) (hW : W ∈ I.minimalPrimes) : IsMultiHomogIdeal W := by
  refine isMultiHomogIdeal_of_blockDeg fun k n r hr => ?_
  have hIk : I.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) :=
    (isHomogeneous_iff _ I).mpr fun n r hr => blockDeg_component_mem hI k n hr
  have hcore : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal.IsPrime :=
    hW.1.1.homogeneousCore
  have hle : I ≤ (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal :=
    hIk.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have heq : (W.homogeneousCore
      (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k))).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hW.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hWk : W.IsHomogeneous (weightedHomogeneousSubmodule F (blockDeg (ι := ι) k)) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  exact (isHomogeneous_iff _ W).mp hWk n r hr
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
