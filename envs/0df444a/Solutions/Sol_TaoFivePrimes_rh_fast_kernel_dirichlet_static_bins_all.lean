-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:40:31.676925+00:00
-- url     : https://prove2.me/submissions/54434bbf-afd9-4a86-8a33-f35c86f49875

import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins00
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins01
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins02
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins03
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins04
set_option autoImplicit false
theorem solution (n : Nat) (hn : 1≤n ∧ n≤50000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by
  by_cases h0 : n≤10000
  · exact TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins00 n (by omega) h0
  by_cases h1 : n≤20000
  · exact TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins01 n (by omega) h1
  by_cases h2 : n≤30000
  · exact TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins02 n (by omega) h2
  by_cases h3 : n≤40000
  · exact TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins03 n (by omega) h3
  exact TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins04 n (by omega) hn.2
#print axioms solution
