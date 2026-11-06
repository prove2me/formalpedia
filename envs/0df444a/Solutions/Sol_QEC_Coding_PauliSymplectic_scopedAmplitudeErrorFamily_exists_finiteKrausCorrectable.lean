-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:54:10.134422+00:00
-- url     : https://prove2.me/submissions/99895be3-a90e-4a0c-82e1-49b2523c653e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_complete
import Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_sameSpaceKnillLaflammeCriterion
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_sameSpaceKnillLaflammeCriterion


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
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable
        {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}
        (Semantics.Qubit.QubitRegister ι)
        (Semantics.Qubit.QubitRegister ι)
        (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
        (scopedAmplitudeErrorFamily (ι := ι) t amp)
        recovery := by
  exact
    Semantics.FiniteKrausFamily.exists_recovery_of_sameSpaceKnillLaflammeCriterion
      (scopedAmplitudeErrorFamily (ι := ι) t amp)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (scopedAmplitudeErrorFamily_complete (ι := ι) amp hamp)
      (scopedAmplitudeErrorFamily_sameSpaceKnillLaflammeCriterion
        xCode zCode hdual hminX hminZ hbound amp)
end QEC.Coding.PauliSymplectic
