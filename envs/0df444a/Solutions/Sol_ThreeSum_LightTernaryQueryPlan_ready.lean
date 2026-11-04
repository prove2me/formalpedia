-- Prove2me | solution 1 for ThreeSum.LightTernaryQueryPlan.ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:01.443304+00:00
-- url     : https://prove2.me/submissions/b0e904b4-576d-46ff-83ad-564e4b22501e

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryQueryPlan

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightTernaryNearPair
namespace ThreeSum.LightTernaryQueryPlan
theorem _root_.solution {lim : Limits} {N rows : ℕ} {c : Config} {μ : ℕ→ℤ}
    {Q : TritWord N} {bankWords nearWords : ℕ→TritWord N} {source : TritWord N→ℤ}
    (R : Resources lim rows c source)
    (hread : ∀ j<rows, μ (c.a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<c.nb, μ (c.bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (c.activeBase+i)=1)
    (hpowers : Powers μ c.powers (2*N))
    (hbankValues : ∀ j<c.nb, μ (c.bv+j)=binomialZeta source (bankWords j))
    (hbankSorted : ∀ j k, j<k → k<c.nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hbankPresent : ∀ W, rank W≤c.T → ∃ j<c.nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → c.T<rank W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<rank (nearWords j)) :
    Ready lim rows c μ Q bankWords nearWords source := by
  exact { R with
    hread := hread
    hbankRead := hbankRead
    hactiveRead := hactiveRead
    hpowers := hpowers
    hbankValues := hbankValues
    hbankSorted := hbankSorted
    hnearSorted := hnearSorted
    hbankPresent := hbankPresent
    hnearPresent := hnearPresent
    hnearRows := hnearRows }
end ThreeSum.LightTernaryQueryPlan
