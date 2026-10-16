-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:14:51.565611+00:00
-- url     : https://prove2.me/submissions/f2dc5818-fe90-41ed-a595-32ef59c1ea5d

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirichletStaticChunk01
open RHFastKernelDirichletArithmetic RHFastKernelLogData
lemma checked : (List.range 10000).all (fun j => decide
    (2*(delta (j+10001)).natAbs+2^100≤D ∧ bin (j+10001)≤928))=true := by
  decide +kernel
end RHFastDirichletStaticChunk01
open RHFastKernelDirichletArithmetic RHFastKernelLogData
theorem solution (n : Nat) (hn : 10001≤n) (hN : n≤20000) :
    2*(delta n).natAbs+2^100≤D ∧ bin n≤928 := by
  have h := List.all_eq_true.mp RHFastDirichletStaticChunk01.checked (n-10001)
    (List.mem_range.mpr (show n-10001<10000 by omega))
  simpa only [Nat.sub_add_cancel hn,decide_eq_true_eq] using h
#print axioms solution
