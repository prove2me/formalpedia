-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_continuous_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:05.323817+00:00
-- url     : https://prove2.me/submissions/d76c1797-5fc9-4187-a7cc-6bb4346fe330

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (a b : Fin N → ℕ) :
    Continuous fun z : Fin N → ℂ => starRingEnd ℂ (monoC a z) * monoC b z := by
  have hm : ∀ c : Fin N → ℕ, Continuous fun z : Fin N → ℂ => monoC c z := fun c =>
    continuous_finset_prod _ fun i _ => (continuous_apply i).pow _
  exact (Complex.continuous_conj.comp (hm a)).mul (hm b)
end ReciprocityTheory.GeometryOfNumbersTheory
