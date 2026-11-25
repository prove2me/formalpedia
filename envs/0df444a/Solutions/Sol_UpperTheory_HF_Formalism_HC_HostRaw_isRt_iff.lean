-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.isRt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:50.575575+00:00
-- url     : https://prove2.me/submissions/faaea8ed-6b00-4e70-ac0e-ebe06b780fcf

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
import Theorems.Thm_Formalism_HC_HostRaw_isMu_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace UpperTheory.HF.Formalism.HC.HostRaw
theorem _root_.solution (x : H.E) : H.IsRt x ↔ x ^ H.muW = 1 := H.isMu_iff x
end UpperTheory.HF.Formalism.HC.HostRaw
