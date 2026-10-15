-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_zeta_coefficient_assembly
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:54:51.281789+00:00
-- url     : https://prove2.me/submissions/455fda40-5471-4219-9194-dcbafe41786a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaCoefficientAssembly
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHHighZetaCoefficientAssemblyCheck
theorem length_checked : RHHighZetaCoefficientAssembly.total.length=1025 := by decide +kernel
theorem values_checked : RHHighZetaCoefficientAssembly.rounded=RHHighZetaCoefficientAssembly.expected := by decide +kernel
theorem constant_checked : (((RHHighZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)= -1 := by decide +kernel
end RHHighZetaCoefficientAssemblyCheck
theorem solution :
  RHHighZetaCoefficientAssembly.total.length=1025 ∧
  RHHighZetaCoefficientAssembly.rounded=RHHighZetaCoefficientAssembly.expected ∧
  (((RHHighZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)= -1 := by
  exact ⟨RHHighZetaCoefficientAssemblyCheck.length_checked,RHHighZetaCoefficientAssemblyCheck.values_checked,RHHighZetaCoefficientAssemblyCheck.constant_checked⟩
