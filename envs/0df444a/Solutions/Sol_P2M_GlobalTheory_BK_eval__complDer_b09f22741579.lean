-- Prove2me | solution 1 for P2M_GlobalTheory_BK_eval__complDer_b09f22741579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:25.240786+00:00
-- url     : https://prove2.me/submissions/7eb99f21-65de-4f6f-955c-a2e2391852f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')
variable {ι s}
variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')
namespace GlobalTheory.BK
theorem _root_.solution {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n (complDer I D x) = Ideal.Quotient.mk _ (D r) :=
  evalₐ_complDerFun I D h
end GlobalTheory.BK
