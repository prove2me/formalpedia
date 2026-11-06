-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_sameSpaceKnillLaflammeCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:52.09618+00:00
-- url     : https://prove2.me/submissions/0c82c573-9c71-4288-80df-d22b9aa32db2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_indexedKnillLaflammeConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar


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
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).sameSpaceKnillLaflammeCriterion
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual) := by
  exact
    ((Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
      (scopedAmplitudeErrorFamily (ι := ι) t amp)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)).2
        ⟨fun E F => star (amp E) * amp F *
            scopedErrorFamilyKLScalar (ι := ι) t E F,
          scopedAmplitudeErrorFamily_indexedKnillLaflammeConditionWithScalar
            xCode zCode hdual hminX hminZ hbound amp⟩)
end QEC.Coding.PauliSymplectic
