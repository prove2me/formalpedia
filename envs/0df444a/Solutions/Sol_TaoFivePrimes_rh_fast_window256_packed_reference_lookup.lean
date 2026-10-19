-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_packed_reference_lookup
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:08:20.879212+00:00
-- url     : https://prove2.me/submissions/40a5df06-b7a9-490e-bf99-1a2e1daf0e85

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_packed_reference_equality
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RHFastPackedReferenceLookupProof
lemma raw (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHFastWindow256CompactReference.raw k j=((RHHighGammaFourierTable.values k)[j]?).getD 0 := by
 have hm:=TaoFivePrimes.rh_fast_window256_packed_reference_equality
 have hr:=congrArg (fun xs:List (List Nat)=>(xs[k]?).getD []) hm
 have hr':(List.range 2048).map (RHFastWindow256CompactReference.raw k)=RHHighGammaFourierTable.values k := by
  simpa only [List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some,RHHighGammaFourierTable.values] using hr
 have h:=congrArg (fun xs:List Nat=>(xs[j]?).getD 0) hr'
 simpa only [List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some] using h
lemma signed (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHFastWindow256CompactReference.signed k j=RHHighZetaCorrelation.signed (RHHighGammaFourierTable.values k) j := by
 simp only [RHFastWindow256CompactReference.signed,RHFastWindow256CompactReference.sample,
  RHHighZetaCorrelation.signed,RHHighZetaCorrelation.sample,raw k j hk hj]
end RHFastPackedReferenceLookupProof

theorem solution (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHFastWindow256CompactReference.signed k j=RHHighZetaCorrelation.signed (RHHighGammaFourierTable.values k) j :=
 RHFastPackedReferenceLookupProof.signed k j hk hj
#print axioms solution
