-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSParityChecks_exists_finiteKrausCorrectable_and_correctable_toQuantumChannel_of_componentwiseSyndromeInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:30.855486+00:00
-- url     : https://prove2.me/submissions/5806bd57-3fb4-4a44-8bc1-02f65a1e3068

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_CSS_Correctability
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctedBy_iff_correctable_toQuantumChannel
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_sameSpaceKnillLaflammeCriterion


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota),
      Semantics.FiniteKrausCorrectable alpha
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        (binaryPauliKrausFamily E amp) recovery ∧
      Semantics.Correctable
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        ((binaryPauliKrausFamily E amp).toQuantumChannel hcomplete) recovery := by
  obtain ⟨recovery, hcorrectable⟩ :=
    Semantics.FiniteKrausFamily.exists_recovery_of_sameSpaceKnillLaflammeCriterion
      (binaryPauliKrausFamily E amp)
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).code hcomplete
      (binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
        P Q horth tX tZ hP hQ E amp hbound)
  refine ⟨recovery, hcorrectable, ?_⟩
  exact
    ((binaryPauliKrausFamily E amp).correctedBy_iff_correctable_toQuantumChannel
      hcomplete (binaryCSSStabilizerCodeOfParityChecks P Q horth).code recovery).1 hcorrectable.2
end QEC.Coding.PauliSymplectic
