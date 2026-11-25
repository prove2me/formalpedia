-- Prove2me | solution 1 for P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:06.113816+00:00
-- url     : https://prove2.me/submissions/b0a91779-7100-4b90-b4ee-ab6cbaec2834

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
end PI.FockOneDegW.Diag
