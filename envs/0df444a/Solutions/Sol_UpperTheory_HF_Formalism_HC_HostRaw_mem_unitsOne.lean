-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.mem_unitsOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:29:49.13391+00:00
-- url     : https://prove2.me/submissions/29a2f803-9896-49c6-b84d-9a2fcc4f7b0e

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace UpperTheory.HF.Formalism.HC.HostRaw
theorem _root_.solution {f : ℕ} (hf : f ∣ H.condN) (u : (ZMod H.condN)ˣ) :
    u ∈ H.unitsOne f ↔ (u : ZMod H.condN).val ≡ 1 [MOD f] := by
  rw [unitsOne, MonoidHom.mem_ker, ← Units.val_eq_one, ZMod.unitsMap_val, ZMod.cast_eq_val,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.gcd_eq_left hf]
end UpperTheory.HF.Formalism.HC.HostRaw
