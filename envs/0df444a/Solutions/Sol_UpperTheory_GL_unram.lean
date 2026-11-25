-- Prove2me | solution 1 for UpperTheory.GL.unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:13.694413+00:00
-- url     : https://prove2.me/submissions/44f7b85d-35da-4975-bb1c-c7d0ac47407d

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_Imports
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unramified_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) (p : ℕ) (hc : p.Coprime H.condN), p.Prime →
      (arith H).inertia p = ⊥ ∧ (arith H).frob p = (recH H (ZMod.unitOfCoprime p hc)).toAdd := by
  intro φ H p hc hp
  have hN : H.condN ≠ 0 := (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'
  have hnd : ¬ p ∣ H.condN := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h)
  obtain ⟨hloc, hfrob⟩ := Formalism.LFunctionChainParameters.LHost.unramified_spec H.condN p hN hp hnd
  constructor
  · show Subgroup.toAddSubgroup' (Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p)) = ⊥
    rw [hloc, Subgroup.map_bot]
    exact Subgroup.toAddSubgroup'.map_bot
  · show (recH H (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)).toAdd = _
    have he : Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p = ZMod.unitOfCoprime p hc :=
      Units.ext (by rw [hfrob, ZMod.coe_unitOfCoprime])
    rw [he]
end UpperTheory.GL
