-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_exists_correctable_toQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:29.535938+00:00
-- url     : https://prove2.me/submissions/659d99ef-1eeb-40e4-a598-22ab7e1b766c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
import Theorems.Thm_QEC_Semantics_exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    ∃ hnoise : (scopedAmplitudeErrorFamily (ι := ι) t amp).Complete,
      ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.Correctable
          (Semantics.Qubit.QubitRegister ι)
          (Semantics.Qubit.QubitRegister ι)
          (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
          ((scopedAmplitudeErrorFamily (ι := ι) t amp).toQuantumChannel hnoise)
          recovery := by
  exact
    (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
      (C := binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (noise := scopedAmplitudeErrorFamily (ι := ι) t amp)).1
      (scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
        xCode zCode hdual hminX hminZ hbound amp hamp)
end QEC.Coding.PauliSymplectic
