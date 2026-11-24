-- Prove2me | solution 1 for P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:39.522749+00:00
-- url     : https://prove2.me/submissions/7092663f-a811-43e7-afe3-d1c3f6e44aab

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ R : Type*} [CommSemiring R] (v : σ) :
    (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} :=
  support_monomial_subset
end Formalism.GradedWeylDivisibility
