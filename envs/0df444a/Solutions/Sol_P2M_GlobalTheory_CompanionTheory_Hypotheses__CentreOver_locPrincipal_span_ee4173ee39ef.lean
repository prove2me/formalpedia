-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_span_ee4173ee39ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:36.302179+00:00
-- url     : https://prove2.me/submissions/d66a544b-0dfe-49ec-8429-8a26ada52e62

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {A : Type} [CommRing A] {f : A} (hf : f ≠ 0) {p : Ideal A} (hp : p ≠ ⊤) :
    LocPrincipal (Ideal.span {f}) p :=
  ⟨1, f, fun h => hp ((Ideal.eq_top_iff_one p).2 h), Ideal.mem_span_singleton_self f, hf,
    fun g hg => ⟨0, by simpa using hg⟩⟩
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
