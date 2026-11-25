-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_den_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:38.636528+00:00
-- url     : https://prove2.me/submissions/ec1ef30d-a6ca-4d7c-9b10-bd29852e3bc7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
theorem _root_.solution (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  first
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by rw [mul_comm]; exact hyb⟩)
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (K := K) v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by
        rw [mul_comm, IsScalarTower.algebraMap_apply R K (v.adicCompletion K)] at *; exact hyb⟩)
  | (obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by
        simpa [mul_comm, IsScalarTower.algebraMap_apply R K (v.adicCompletion K)] using hyb⟩)
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
