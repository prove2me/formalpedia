-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_packed_reference_lookup
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:51:48.132237+00:00
-- url     : https://prove2.me/submissions/fe9b28a2-0f4a-4633-96c8-9c60eb89e420

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_packed_reference_equality
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RHBatch01New256RHFastPackedReferenceLookupProof
lemma raw (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHBatch01New256CompactReference.raw k j=((RHBatch01GammaFourierTable.values k)[j]?).getD 0 := by
 have hm:=TaoFivePrimes.rh_batch01_new256_packed_reference_equality
 have hr:=congrArg (fun xs:List (List Nat)=>(xs[k]?).getD []) hm
 have hr':(List.range 2048).map (RHBatch01New256CompactReference.raw k)=RHBatch01GammaFourierTable.values k := by
  simpa only [List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some,RHBatch01GammaFourierTable.values] using hr
 have h:=congrArg (fun xs:List Nat=>(xs[j]?).getD 0) hr'
 simpa only [List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some] using h
lemma signed (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHBatch01New256CompactReference.signed k j=RHBatch01ZetaCorrelation.signed (RHBatch01GammaFourierTable.values k) j := by
 simp only [RHBatch01New256CompactReference.signed,RHBatch01New256CompactReference.sample,
  RHBatch01ZetaCorrelation.signed,RHBatch01ZetaCorrelation.sample,raw k j hk hj]
end RHBatch01New256RHFastPackedReferenceLookupProof

theorem solution (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHBatch01New256CompactReference.signed k j=RHBatch01ZetaCorrelation.signed (RHBatch01GammaFourierTable.values k) j :=
 RHBatch01New256RHFastPackedReferenceLookupProof.signed k j hk hj
#print axioms solution
