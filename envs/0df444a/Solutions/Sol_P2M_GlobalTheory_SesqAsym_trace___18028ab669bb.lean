-- Prove2me | solution 1 for P2M_GlobalTheory_SesqAsym_trace___18028ab669bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:40.277832+00:00
-- url     : https://prove2.me/submissions/19e5a3fe-8f0c-4cd1-930f-1a0f2e5e4612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGeneratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitSigmaEqMulHilbert90InvAlgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SesqAsym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.SesqAsym
namespace GlobalTheory.SesqAsym
theorem _root_.solution {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a
  rw [h, RingEquiv.apply_symm_apply]
end GlobalTheory.SesqAsym
