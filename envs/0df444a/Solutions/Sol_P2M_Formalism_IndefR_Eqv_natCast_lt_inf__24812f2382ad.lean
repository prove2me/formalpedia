-- Prove2me | solution 1 for P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:14.542797+00:00
-- url     : https://prove2.me/submissions/8df140d4-7877-4ff3-9101-07cbd9e88419

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m
end Formalism.IndefR.Eqv
