-- Prove2me | solution 1 for TunnellMap.intIcc_sort_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:52:59.722982+00:00
-- url     : https://prove2.me/submissions/d7c47490-865e-4b83-a899-1659b1a640f1

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_mem_intIccL
import Theorems.Thm_TunnellMap_intIccL_pairwise_lt
import Theorems.Thm_TunnellMap_Finset_sort_eq_of_sorted_lt


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution (lo hi : ℤ) : (intIcc lo hi).sort (· ≤ ·) = intIccL lo hi :=
  Finset.sort_eq_of_sorted_lt _ _ (intIccL_pairwise_lt lo hi) fun x => by
    rw [mem_intIccL, mem_intIcc]
end TunnellMap
