-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:55:54.246173+00:00
-- url     : https://prove2.me/submissions/276b5fc9-475a-42ec-b40a-4094ae7d88a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) := by
  classical
  rw [GroundTheory.Global.dedekindZetaReal, ENNReal.ofReal_tsum_of_nonneg
    (GroundTheory.Global.dedekindZetaTerm_nonneg K s) (ZetaSevenHalvesBounds.summable_dedekindZetaTerm K hs),
    ← ENNReal.tsum_fiberwise (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      Ideal.absNorm]
  refine tsum_congr fun n => ?_
  have hfin : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))).Finite :=
    Ideal.finite_setOfPred_absNorm_eq n
  have := hfin.fintype
  rw [tsum_congr (fun I : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))) => by
    rw [show Ideal.absNorm (I : Ideal (𝓞 K)) = n from I.2]), tsum_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, GroundTheory.Global.dedekindZetaTerm,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← Nat.card_eq_fintype_card]
  rfl
end GroundTheory.Heights₂.Theta.projectiveLineClassData
