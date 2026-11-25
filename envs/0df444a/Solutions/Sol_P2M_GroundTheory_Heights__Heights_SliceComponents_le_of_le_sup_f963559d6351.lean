-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:24.59499+00:00
-- url     : https://prove2.me/submissions/9e08e590-2dca-428e-addf-0242b45f624c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_proof_95c60a838754
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalMultOrd_proof_21316c672e2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_proof_bf27ffa11a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_proof_d5922d801c8e


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceComponents
theorem _root_.solution {V W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (h : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := fun g hg => by
  rw [← sum_homogeneousComponent g]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof F n W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d g) (h (hV g hg d))
end GroundTheory.Heights₂.Heights.SliceComponents
