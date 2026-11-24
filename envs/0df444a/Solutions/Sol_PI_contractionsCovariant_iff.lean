-- Prove2me | solution 1 for PI.contractionsCovariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:04:39.798602+00:00
-- url     : https://prove2.me/submissions/ccaafb15-0a63-4555-b177-ca9091af223c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI
theorem _root_.solution : ContractionsCovariant ↔ QnCovDet ∧ QnCovHat ∧ QnCovHat2 := by
  unfold ContractionsCovariant QnCovDet QnCovHat QnCovHat2
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro A _ _ n E P Q hE hQP hPQ u
      exact (h A n E P Q hE hQP hPQ u 0 0 0 0).1
    · intro A _ _ n E P Q hE hQP hPQ u a β
      exact (h A n E P Q hE hQP hPQ u a 0 β 0).2.1
    · intro A _ _ n E P Q hE hQP hPQ u a a' β β'
      exact (h A n E P Q hE hQP hPQ u a a' β β').2.2
  · rintro ⟨h1, h2, h3⟩ A _ _ n E P Q hE hQP hPQ u a a' β β'
    exact ⟨h1 A n E P Q hE hQP hPQ u, h2 A n E P Q hE hQP hPQ u a β,
      h3 A n E P Q hE hQP hPQ u a a' β β'⟩
end PI
