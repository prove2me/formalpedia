-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:28:11.481137+00:00
-- url     : https://prove2.me/submissions/01d4b681-ec62-4a88-aeca-2f3fd8b6ff07

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirichletStaticChunk00
open RHFastKernelDirichletArithmetic RHFastKernelLogData
lemma checked : (List.range 10000).all (fun j => decide
    (2*(delta (j+1)).natAbs+2^100≤D ∧ bin (j+1)≤928))=true := by
  decide +kernel
end RHFastDirichletStaticChunk00
open RHFastKernelDirichletArithmetic RHFastKernelLogData
theorem solution (n : Nat) (hn : 1≤n) (hN : n≤10000) :
    2*(delta n).natAbs+2^100≤D ∧ bin n≤928 := by
  have h := List.all_eq_true.mp RHFastDirichletStaticChunk00.checked (n-1)
    (List.mem_range.mpr (show n-1<10000 by omega))
  simpa only [Nat.sub_add_cancel hn,decide_eq_true_eq] using h
#print axioms solution
