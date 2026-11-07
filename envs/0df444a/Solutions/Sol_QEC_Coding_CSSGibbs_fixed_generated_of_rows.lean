-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.fixed_generated_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:15.367468+00:00
-- url     : https://prove2.me/submissions/62ea4e5d-951d-4ded-a531-98e3f7c82928

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_one


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (x : Qubit.QubitRegister ι)
    (hx : ∀ j, toQubitOperator (binaryCSSParityCheckGenerators P Q j) x = x)
    (G : Binary ι) (hG : GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) G) :
    toQubitOperator G x = x := by
  induction hG with
  | one => rw [toQubitOperator_one]; rfl
  | generator j => exact hx j
  | @mul A B hA hB ihA ihB =>
      rw [toQubitOperator_binaryMul]
      change toQubitOperator A (toQubitOperator B x) = x
      rw [ihB, ihA]
  | @dagger A hA ih =>
      calc
        toQubitOperator (binaryDagger A) x =
            toQubitOperator (binaryDagger A) (toQubitOperator A x) := by rw [ih]
        _ = x := by
          change (toQubitOperator (binaryDagger A) * toQubitOperator A) x = x
          rw [← toQubitOperator_binaryMul, binaryMul_binaryDagger_left, toQubitOperator_one]
          rfl
end QEC.Coding.CSSGibbs
