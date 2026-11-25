-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.isMu_iff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:47.864805+00:00
-- url     : https://prove2.me/submissions/a4b5edb9-4e19-47bc-bcc2-dce668ca444f

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
theorem _root_.solution (x : H.E) : H.IsMu x ↔ ∃ k : ℕ, x = H.muGen ^ k := by
  rw [isMu_iff]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := H.muGen_prim.eq_pow_of_pow_eq_one h
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, H.muGen_prim.pow_eq_one, one_pow]
end UpperTheory.HF.Formalism.HC.HostRaw
