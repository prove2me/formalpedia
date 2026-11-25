-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:06.097806+00:00
-- url     : https://prove2.me/submissions/9cb52db9-e99b-4681-975a-5007c5ebf547

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_not_mem_range_b45f5fd1c0af
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : conj F E ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_not_mem_range (F := F) (E := E)
  exact hx (mem_range_of_conj_eq (by rw [h]; rfl))
end GroundTheory.Heights₂.Theta
