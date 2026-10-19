-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_all_zeta_correlations
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T16:10:13.603966+00:00
-- url     : https://prove2.me/submissions/54bf575d-ee99-44d3-b757-6c40ebf727bc

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCoefficientAssembly
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation08
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation09
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation10
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation11
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation12
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation13
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation14
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation15
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation16
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation17
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation18
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation19
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation20
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation21
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation22
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation23
theorem solution (k : Nat) (hk:k<24) :
 RHBatch01ZetaCorrelation.output k (RHBatch01GammaFourierTable.values k)=
  RHBatch01ZetaCorrelation.decode ((RHBatch01ZetaCoefficientAssembly.packets[k]?).getD []) ∧
 ∀j:Nat,j<1954 → |(RHBatch01ZetaCorrelation.sample (RHBatch01GammaFourierTable.values k) j).1|≤(2:Int)^100 ∧
  |(RHBatch01ZetaCorrelation.sample (RHBatch01GammaFourierTable.values k) j).2|≤(2:Int)^100 := by
 interval_cases k
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation00
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation01
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation02
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation03
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation04
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation05
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation06
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation07
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation08
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation09
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation10
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation11
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation12
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation13
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation14
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation15
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation16
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation17
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation18
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation19
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation20
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation21
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation22
 · simpa only[RHBatch01GammaFourierTable.values,RHBatch01GammaFourierTable.packets,RHBatch01ZetaCoefficientAssembly.packets,
   List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using TaoFivePrimes.rh_batch01_height_zeta_correlation23
#print axioms solution
