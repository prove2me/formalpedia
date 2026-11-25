-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartDim_le_of_homog_le_sup_94e75daff410
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:23.889312+00:00
-- url     : https://prove2.me/submissions/7bea00e2-813d-4f4d-a001-d4ff9f37010e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_proof_337a19539709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_proof_4e503d72b794
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_proof_17ca30ede7f1


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartDim
theorem _root_.solution {m : ℕ} {V W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (hle : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof ℂ m W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d f) (hle (hV f hf d))
end GroundTheory.Heights₂.Heights.GoodChartDim
