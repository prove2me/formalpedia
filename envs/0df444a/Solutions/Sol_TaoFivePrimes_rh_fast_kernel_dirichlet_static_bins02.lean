-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:54:39.074642+00:00
-- url     : https://prove2.me/submissions/af203f2a-d09c-40b5-91c7-704aa40bf576

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirichletStaticChunk02
open RHFastKernelDirichletArithmetic RHFastKernelLogData
lemma checked : (List.range 10000).all (fun j => decide
    (2*(delta (j+20001)).natAbs+2^100≤D ∧ bin (j+20001)≤928))=true := by
  decide +kernel
end RHFastDirichletStaticChunk02
open RHFastKernelDirichletArithmetic RHFastKernelLogData
theorem solution (n : Nat) (hn : 20001≤n) (hN : n≤30000) :
    2*(delta n).natAbs+2^100≤D ∧ bin n≤928 := by
  have h := List.all_eq_true.mp RHFastDirichletStaticChunk02.checked (n-20001)
    (List.mem_range.mpr (show n-20001<10000 by omega))
  simpa only [Nat.sub_add_cancel hn,decide_eq_true_eq] using h
#print axioms solution
