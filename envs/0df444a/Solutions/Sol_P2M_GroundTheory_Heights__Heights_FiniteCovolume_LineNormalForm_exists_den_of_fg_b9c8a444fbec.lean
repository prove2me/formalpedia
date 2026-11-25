-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:17.074416+00:00
-- url     : https://prove2.me/submissions/cf524e6e-d85e-4a60-815c-e074c836ea3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
variable {E : Type*} [Field E] [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
theorem _root_.solution {J : AddSubgroup E} (hJ : J.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ j ∈ J, IsIntegral ℤ ((d : E) * j) := by
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨d, hd, hS⟩ := exists_common_multiple S (fun s n => IsIntegral ℤ ((n : E) * s))
    (fun _ _ _ h hab => isIntegral_mul_of_dvd h hab) (fun s _ => exists_nat_mul_isIntegral s)
  refine ⟨d, hd, fun j hj => ?_⟩
  induction hj using AddSubgroup.closure_induction with
  | mem x hx => exact hS x hx
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | neg x _ hx => rw [mul_neg]; exact hx.neg
end GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
