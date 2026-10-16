-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:44:53.232865+00:00
-- url     : https://prove2.me/submissions/2cc6086a-3095-4755-b187-d9f1b1933c5b

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirichletStaticChunk03
open RHFastKernelDirichletArithmetic RHFastKernelLogData
lemma checked : (List.range 10000).all (fun j => decide
    (2*(delta (j+30001)).natAbs+2^100≤D ∧ bin (j+30001)≤928))=true := by
  decide +kernel
end RHFastDirichletStaticChunk03
open RHFastKernelDirichletArithmetic RHFastKernelLogData
theorem solution (n : Nat) (hn : 30001≤n) (hN : n≤40000) :
    2*(delta n).natAbs+2^100≤D ∧ bin n≤928 := by
  have h := List.all_eq_true.mp RHFastDirichletStaticChunk03.checked (n-30001)
    (List.mem_range.mpr (show n-30001<10000 by omega))
  simpa only [Nat.sub_add_cancel hn,decide_eq_true_eq] using h
#print axioms solution
