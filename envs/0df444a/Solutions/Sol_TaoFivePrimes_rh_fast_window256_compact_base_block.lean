-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_base_block
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:16:50.400571+00:00
-- url     : https://prove2.me/submissions/f77f9b8d-e659-46da-880d-aa12b7c01b33

import Definitions.Def_TaoFivePrimes_RHFastWindow256Reference
import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_packed_reference_lookup
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_block00
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RHFastCompactBaseBlockProof
lemma references (j:Nat) (hj:j<2048) :
 RHFastWindow256CompactReference.references j=RHFastWindow256Reference.references j := by
 unfold RHFastWindow256CompactReference.references RHFastWindow256Reference.references
 apply List.map_congr_left
 intro k hk
 exact TaoFivePrimes.rh_fast_window256_packed_reference_lookup k j (List.mem_range.mp hk) hj
lemma checked (j:Nat) (hj:j<2048) :
 RHFastWindow256CompactReference.checked j=RHFastWindow256Reference.checked j := by
 simp only [RHFastWindow256CompactReference.checked,RHFastWindow256Reference.checked,references j hj]
end RHFastCompactBaseBlockProof

theorem solution : RHFastWindow256CompactReference.block 0 32=true := by
 have h:=TaoFivePrimes.rh_fast_window256_block00
 simp only [RHFastWindow256Reference.block,List.all_eq_true,List.mem_range] at h
 simp only [RHFastWindow256CompactReference.block,List.all_eq_true,List.mem_range]
 intro i hi
 rw [RHFastCompactBaseBlockProof.checked (0+i) (by omega)]
 exact h i hi
#print axioms solution
