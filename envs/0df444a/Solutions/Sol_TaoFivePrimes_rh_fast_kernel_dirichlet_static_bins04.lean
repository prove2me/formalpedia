-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:38:47.583864+00:00
-- url     : https://prove2.me/submissions/32d5fd62-0407-489b-b11c-ca3cdec263a4

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirichletStaticChunk04
open RHFastKernelDirichletArithmetic RHFastKernelLogData
lemma checked : (List.range 10000).all (fun j => decide
    (2*(delta (j+40001)).natAbs+2^100≤D ∧ bin (j+40001)≤928))=true := by
  decide +kernel
end RHFastDirichletStaticChunk04
open RHFastKernelDirichletArithmetic RHFastKernelLogData
theorem solution (n : Nat) (hn : 40001≤n) (hN : n≤50000) :
    2*(delta n).natAbs+2^100≤D ∧ bin n≤928 := by
  have h := List.all_eq_true.mp RHFastDirichletStaticChunk04.checked (n-40001)
    (List.mem_range.mpr (show n-40001<10000 by omega))
  simpa only [Nat.sub_add_cancel hn,decide_eq_true_eq] using h
#print axioms solution
