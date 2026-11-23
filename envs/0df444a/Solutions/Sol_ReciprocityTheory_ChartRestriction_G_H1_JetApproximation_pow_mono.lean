-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:11.184345+00:00
-- url     : https://prove2.me/submissions/4460889e-b4c7-4a9b-8e69-adc57a63006b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_one_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]
namespace ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
theorem _root_.solution {V : Submodule F R} (h1 : 1 ≤ V) {a b : ℕ} (hab : a ≤ b) : V ^ a ≤ V ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc V ^ a = V ^ a * 1 := (mul_one _).symm
    _ ≤ V ^ a * V ^ c := mul_le_mul' le_rfl (one_le_pow h1 c)
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
