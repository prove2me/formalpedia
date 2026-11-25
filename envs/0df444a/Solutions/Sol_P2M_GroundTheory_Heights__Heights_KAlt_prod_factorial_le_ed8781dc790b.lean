-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:36:52.079366+00:00
-- url     : https://prove2.me/submissions/5eb8b2a1-e710-4e28-9b73-5929d7401294

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_factorial_mul_le_79581543a245

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
open Finset
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    (∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ)) *
        ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) ≤
      (∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)) *
        ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_le_prod
  · intro a _; positivity
  · intro a _
    have := factorial_mul_le s (r - 1 - (a : ℕ)) (ν a)
    rw [show s + ν a + (r - 1 - (a : ℕ)) = s + (r - 1 - (a : ℕ)) + ν a by ring,
      show ν a + (r - 1 - (a : ℕ)) = (r - 1 - (a : ℕ)) + ν a by ring,
      mul_comm (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)]
    exact_mod_cast this
end GroundTheory.Heights₂.Heights.KAlt
