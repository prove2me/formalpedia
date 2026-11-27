-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SegrePrime_proof_86273321f833
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:22.604794+00:00
-- url     : https://prove2.me/submissions/d5ab795d-ba22-4730-b422-c927a5832f59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegrePrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_weightedHomogeneousComponent_ddee863e2076
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace SegrePrime
theorem _root_.solution : SegrePrime.Statement := by
  intro F _ K _ _ _ ι _ q hq
  have := hq.isPrime
  refine ⟨segrePrime.isPrime F q, ?_, ?_⟩
  · intro g hg b
    rw [segrePrime, Ideal.mem_comap] at hg ⊢
    rw [segreMap_weightedHomogeneousComponent]
    exact hq.multiHomog _ hg _
  · intro u
    cases u
    choose i hi using hq.relevant
    refine ⟨i, ?_⟩
    rw [segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    exact hi k hk
end SegrePrime
end GroundTheory.Heights₂.Heights.HilbertSamuel
