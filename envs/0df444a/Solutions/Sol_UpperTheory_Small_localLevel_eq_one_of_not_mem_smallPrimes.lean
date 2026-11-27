-- Prove2me | solution 1 for UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:56.615166+00:00
-- url     : https://prove2.me/submissions/5745a42e-e3c2-47fe-a1a7-55c99269b108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_UpperTheory_Small_ne_two
import Theorems.Thm_UpperTheory_Small_factorization_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
variable {H}
namespace UpperTheory.Small
theorem _root_.solution {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.l i ∉ H.small) : N.s0 i = 1 := by
  rw [N.restNLevelExponent_of_odd i (ne_two H h), factorization_eq_zero H h]; rfl
end UpperTheory.Small
