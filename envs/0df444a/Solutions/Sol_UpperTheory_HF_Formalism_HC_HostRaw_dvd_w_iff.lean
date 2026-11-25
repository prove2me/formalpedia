-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.dvd_w_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:06:40.263172+00:00
-- url     : https://prove2.me/submissions/624ff2dd-e0ad-4755-948e-219a6608ced0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
import Theorems.Thm_Formalism_HC_HostRaw_w_pos


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
theorem _root_.solution {m : ℕ} (hm : 0 < m) : m ∣ H.w ↔ ∃ ζ : H.E, IsPrimitiveRoot ζ m := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, H.muGen_prim.pow H.w_pos (hk.trans (mul_comm _ _))⟩
  · rintro ⟨ζ, hζ⟩
    have : NeZero m := ⟨hm.ne'⟩
    exact NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hζ
end UpperTheory.HF.Formalism.HC.HostRaw
