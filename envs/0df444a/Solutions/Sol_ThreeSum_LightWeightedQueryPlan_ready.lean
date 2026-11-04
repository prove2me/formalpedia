-- Prove2me | solution 1 for ThreeSum.LightWeightedQueryPlan.ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:03.737201+00:00
-- url     : https://prove2.me/submissions/42d33243-0ed2-4666-90c8-4ccb49452d6a

import Definitions.Def_Submission_Weighted_WantedQuery
import Definitions.Def_Submission_Weighted_NearSetup
import Definitions.Def_Submission_Weighted_QueryPlan

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightWeightedNearPair
namespace ThreeSum.LightWeightedQueryPlan
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
    (hbankPresent : ∀ W, cacheCost W≤c.T → ∃ j<c.nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → c.T<cacheCost W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<cacheCost (nearWords j)) :
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
end ThreeSum.LightWeightedQueryPlan
