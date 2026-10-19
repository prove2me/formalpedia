-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_all_arithmetic_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:39:16.965189+00:00
-- url     : https://prove2.me/submissions/856852dc-b2db-42b4-9ef4-986955adf543

import Mathlib.Tactic.IntervalCases
import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_base_block
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block01
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block02
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block03
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block04
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block05
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block06
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block07
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block08
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block09
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block10
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block11
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block12
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block13
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block14
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block15
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block16
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block17
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block18
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block19
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block20
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block21
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block22
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block23
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block24
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block25
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block26
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block27
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block28
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block29
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block30
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block31
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block32
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block33
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block34
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block35
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block36
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block37
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block38
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block39
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block40
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block41
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block42
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block43
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block44
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block45
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block46
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block47
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block48
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block49
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block50
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block51
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block52
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block53
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block54
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block55
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block56
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block57
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block58
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block59
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block60
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block61
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RHFastCheckedComposition256Proof
lemma member (a n:Nat) (h:RHFastWindow256CompactReference.block a n=true) (j:Nat) (hlo:a ≤ j) (hhi:j<a+n) :
 RHFastWindow256CompactReference.checked j=true := by
 have hr:j-a<n:=by omega
 have he:a+(j-a)=j:=by omega
 have hm:=List.all_eq_true.mp h (j-a) (List.mem_range.mpr hr)
 change RHFastWindow256CompactReference.checked (a+(j-a))=true at hm
 rwa [he] at hm
end RHFastCheckedComposition256Proof

theorem solution (j:Nat) (hj:j<1954) : RHFastWindow256CompactReference.checked j=true := by
 have hb:j/32<62:=by omega
 generalize he:j/32=b at hb
 interval_cases b
 · exact RHFastCheckedComposition256Proof.member 0 32 TaoFivePrimes.rh_fast_window256_compact_base_block j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 32 32 TaoFivePrimes.rh_fast_window256_compact_block01 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 64 32 TaoFivePrimes.rh_fast_window256_compact_block02 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 96 32 TaoFivePrimes.rh_fast_window256_compact_block03 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 128 32 TaoFivePrimes.rh_fast_window256_compact_block04 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 160 32 TaoFivePrimes.rh_fast_window256_compact_block05 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 192 32 TaoFivePrimes.rh_fast_window256_compact_block06 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 224 32 TaoFivePrimes.rh_fast_window256_compact_block07 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 256 32 TaoFivePrimes.rh_fast_window256_compact_block08 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 288 32 TaoFivePrimes.rh_fast_window256_compact_block09 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 320 32 TaoFivePrimes.rh_fast_window256_compact_block10 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 352 32 TaoFivePrimes.rh_fast_window256_compact_block11 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 384 32 TaoFivePrimes.rh_fast_window256_compact_block12 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 416 32 TaoFivePrimes.rh_fast_window256_compact_block13 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 448 32 TaoFivePrimes.rh_fast_window256_compact_block14 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 480 32 TaoFivePrimes.rh_fast_window256_compact_block15 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 512 32 TaoFivePrimes.rh_fast_window256_compact_block16 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 544 32 TaoFivePrimes.rh_fast_window256_compact_block17 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 576 32 TaoFivePrimes.rh_fast_window256_compact_block18 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 608 32 TaoFivePrimes.rh_fast_window256_compact_block19 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 640 32 TaoFivePrimes.rh_fast_window256_compact_block20 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 672 32 TaoFivePrimes.rh_fast_window256_compact_block21 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 704 32 TaoFivePrimes.rh_fast_window256_compact_block22 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 736 32 TaoFivePrimes.rh_fast_window256_compact_block23 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 768 32 TaoFivePrimes.rh_fast_window256_compact_block24 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 800 32 TaoFivePrimes.rh_fast_window256_compact_block25 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 832 32 TaoFivePrimes.rh_fast_window256_compact_block26 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 864 32 TaoFivePrimes.rh_fast_window256_compact_block27 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 896 32 TaoFivePrimes.rh_fast_window256_compact_block28 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 928 32 TaoFivePrimes.rh_fast_window256_compact_block29 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 960 32 TaoFivePrimes.rh_fast_window256_compact_block30 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 992 32 TaoFivePrimes.rh_fast_window256_compact_block31 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1024 32 TaoFivePrimes.rh_fast_window256_compact_block32 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1056 32 TaoFivePrimes.rh_fast_window256_compact_block33 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1088 32 TaoFivePrimes.rh_fast_window256_compact_block34 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1120 32 TaoFivePrimes.rh_fast_window256_compact_block35 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1152 32 TaoFivePrimes.rh_fast_window256_compact_block36 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1184 32 TaoFivePrimes.rh_fast_window256_compact_block37 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1216 32 TaoFivePrimes.rh_fast_window256_compact_block38 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1248 32 TaoFivePrimes.rh_fast_window256_compact_block39 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1280 32 TaoFivePrimes.rh_fast_window256_compact_block40 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1312 32 TaoFivePrimes.rh_fast_window256_compact_block41 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1344 32 TaoFivePrimes.rh_fast_window256_compact_block42 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1376 32 TaoFivePrimes.rh_fast_window256_compact_block43 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1408 32 TaoFivePrimes.rh_fast_window256_compact_block44 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1440 32 TaoFivePrimes.rh_fast_window256_compact_block45 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1472 32 TaoFivePrimes.rh_fast_window256_compact_block46 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1504 32 TaoFivePrimes.rh_fast_window256_compact_block47 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1536 32 TaoFivePrimes.rh_fast_window256_compact_block48 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1568 32 TaoFivePrimes.rh_fast_window256_compact_block49 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1600 32 TaoFivePrimes.rh_fast_window256_compact_block50 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1632 32 TaoFivePrimes.rh_fast_window256_compact_block51 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1664 32 TaoFivePrimes.rh_fast_window256_compact_block52 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1696 32 TaoFivePrimes.rh_fast_window256_compact_block53 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1728 32 TaoFivePrimes.rh_fast_window256_compact_block54 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1760 32 TaoFivePrimes.rh_fast_window256_compact_block55 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1792 32 TaoFivePrimes.rh_fast_window256_compact_block56 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1824 32 TaoFivePrimes.rh_fast_window256_compact_block57 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1856 32 TaoFivePrimes.rh_fast_window256_compact_block58 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1888 32 TaoFivePrimes.rh_fast_window256_compact_block59 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1920 32 TaoFivePrimes.rh_fast_window256_compact_block60 j (by omega) (by omega)
 · exact RHFastCheckedComposition256Proof.member 1952 2 TaoFivePrimes.rh_fast_window256_compact_block61 j (by omega) (by omega)
#print axioms solution
