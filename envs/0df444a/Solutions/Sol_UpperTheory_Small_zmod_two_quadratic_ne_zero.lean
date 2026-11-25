-- Prove2me | solution 1 for UpperTheory.Small.zmod_two_quadratic_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:18.321512+00:00
-- url     : https://prove2.me/submissions/a7f2e5ce-a869-49b3-bcf5-0c91bfdca0e5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ZmodTwoQuadraticNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution : ∀ v : ZMod 2, v ^ 2 - v + 1 ≠ 0 := by decide
end UpperTheory.Small
