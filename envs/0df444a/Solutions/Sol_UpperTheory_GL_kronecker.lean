-- Prove2me | solution 1 for UpperTheory.GL.kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:23.608329+00:00
-- url     : https://prove2.me/submissions/d79a5740-8e39-458e-ab7c-aef5ceebef87

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_kronecker
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_PsQ_psAt_eq
import Theorems.Thm_Formalism_HC_HostRaw_d_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_odd_of_coprime
import Theorems.Thm_Formalism_HC_HostRaw_psAt_of_coprime
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_Formalism_HC_jacobi_neg_recip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal
private theorem UpperTheory.GL.kron_sgn (s : ℤˣ) :
    (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 ↔ s = 1) ∧ (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 1 ↔ s = -1) := by
  revert s
  decide
private theorem UpperTheory.GL.kron_int (s : ℤˣ) (J : ℤ) (h : (s : ℤ) = J) :
    (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 ↔ J = 1) ∧ (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 1 ↔ J = -1) := by
  subst h
  rw [(UpperTheory.GL.kron_sgn s).1, (UpperTheory.GL.kron_sgn s).2, Units.ext_iff, Units.ext_iff]
  simp
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) (m : ℕ) (hm : m.Coprime H.condN),
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 0 ↔ jacobiSym (-(H.d : ℤ)) m = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 1 ↔ jacobiSym (-(H.d : ℤ)) m = -1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = -1) ∧
      (H.PsQ → ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ jacobiSym (-(H.q : ℤ)) m = 1) ∧
        ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ jacobiSym (-(H.q : ℤ)) m = -1)) ∧
      (recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.2 = φ.iotaInv (H.art (ZMod.unitOfCoprime m hm)).2 := by
  intro φ H m hm
  have hd : (((H.art (ZMod.unitOfCoprime m hm)).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) m := by
    rw [H.der.art_ch, jacobi_neg_recip H.d_mod_four (H.odd_of_coprime hm)]
    exact jacobi_congr ((H.val_unitOfCoprime hm).of_dvd H.d_dvd_condN)
  refine ⟨(UpperTheory.GL.kron_int _ _ hd).1, (UpperTheory.GL.kron_int _ _ hd).2, (UpperTheory.GL.kron_sgn _).1, (UpperTheory.GL.kron_sgn _).2,
    fun hP => UpperTheory.GL.kron_int _ _ ?_, rfl⟩
  rw [← H.psAt_of_coprime hm, hP.psAt_eq hm]
end UpperTheory.GL
