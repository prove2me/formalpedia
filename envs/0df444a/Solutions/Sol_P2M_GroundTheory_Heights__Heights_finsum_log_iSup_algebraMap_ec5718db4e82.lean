-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_log_iSup_algebraMap_ec5718db4e82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:23.533326+00:00
-- url     : https://prove2.me/submissions/8deebe0b-29e8-4619-8080-a2e927fd5f7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa

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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ i, w (algebraMap K L (y i))) =
      finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (y i)) := by
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finsum_log_eq_log_finprod (iSup_place_pos hyL) (hasFiniteMulSupport_iSup_place hyL),
    finsum_log_eq_log_finprod (iSup_place_pos hy) (hasFiniteMulSupport_iSup_place hy),
    finprod_iSup_algebraMap hy, Real.log_pow]
end GroundTheory.Heights₂.Heights
