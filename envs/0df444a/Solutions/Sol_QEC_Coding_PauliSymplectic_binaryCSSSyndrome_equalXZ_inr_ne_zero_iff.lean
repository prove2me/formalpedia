-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:08.456532+00:00
-- url     : https://prove2.me/submissions/1f0561d8-7bc4-461e-bbbb-591e0abdc8a2

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
      ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)
      (Sum.inr q)) ≠ 0 ↔ Q y ≠ 0 := by
  rw [binaryCSSSyndrome_equalXZ P Q horth phase y]
  rfl
end QEC.Coding.PauliSymplectic
