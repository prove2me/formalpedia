-- Prove2me | solution 1 for PI.SqPairW.conjTranspose_mem_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:37.741016+00:00
-- url     : https://prove2.me/submissions/42efce7f-155c-4a46-a02b-38a615a2f1ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Theorems.Thm_PI_SqPairW_conjTranspose_pres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L')
    (hL'' : IsSDG E N L'') {e : Matrix (Fin N) (Fin N) E} (he : e ∈ lam L' L'') :
    eᴴ ∈ lam L' L'' := ⟨conjTranspose_pres hL' he.1, conjTranspose_pres hL'' he.2⟩
end PI.SqPairW
