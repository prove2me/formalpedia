-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:48:37.536581+00:00
-- url     : https://prove2.me/submissions/abdecc3a-4ef8-4d34-8764-67e7ecfe6819

import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins_all
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_uniform_analytic_conditional
set_option autoImplicit false
theorem solution (T n k : Nat) (hT : T≤4000000000) (hn : 1≤n ∧ n≤50000) (hk : k<24) :
  let L : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
  let d : ℝ := 512*L/(2*Real.pi)-(RHFastKernelDirichletArithmetic.bin n:ℝ)
  let c := RHFastKernelDirichletArithmetic.coefficient T n k
  ‖((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128-
    Complex.exp (-(1/2+Complex.I*(T:ℂ))*(L:ℂ))*(d:ℂ)^k‖≤1/10^24 ∧
  |d|≤1/2 ∧ RHFastKernelDirichletArithmetic.bin n≤928 := by
  have hs := TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all n hn
  have ha := TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic_conditional T n k hT hn hk hs.1
  exact ⟨ha.1,ha.2,hs.2⟩
#print axioms solution
