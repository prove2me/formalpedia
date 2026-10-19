-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:55:28.374269+00:00
-- url     : https://prove2.me/submissions/551e9b4c-a8cf-455c-9970-9932eec8e8bf

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCoefficientAssembly
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01ZetaCoefficientAssemblyCheck
theorem length_checked : RHBatch01ZetaCoefficientAssembly.total.length=1025 := by decide +kernel
theorem values_checked : RHBatch01ZetaCoefficientAssembly.rounded=RHBatch01ZetaCoefficientAssembly.expected := by decide +kernel
theorem constant_checked : |(((RHBatch01ZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)|≤1 := by decide +kernel
end RHBatch01ZetaCoefficientAssemblyCheck
theorem solution :
  RHBatch01ZetaCoefficientAssembly.total.length=1025 ∧
  RHBatch01ZetaCoefficientAssembly.rounded=RHBatch01ZetaCoefficientAssembly.expected ∧
  |(((RHBatch01ZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)|≤1 := by
  exact ⟨RHBatch01ZetaCoefficientAssemblyCheck.length_checked,RHBatch01ZetaCoefficientAssemblyCheck.values_checked,RHBatch01ZetaCoefficientAssemblyCheck.constant_checked⟩
#print axioms solution
