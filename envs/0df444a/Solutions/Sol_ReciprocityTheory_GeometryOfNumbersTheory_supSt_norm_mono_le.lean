-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_norm_mono_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:38.616338+00:00
-- url     : https://prove2.me/submissions/a5e39411-fd55-4553-9ee6-aa1f7fc7e11f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) (z : Fin (D + 1) → ℂ) (h : sqN z = 1) :
    ‖monoC a z‖ ≤ 1 := by
  simp only [monoC, norm_prod, norm_pow]
  apply Finset.prod_le_one (fun i _ => by positivity)
  intro i _
  have h1 : ‖z i‖ ^ 2 ≤ sqN z := by
    unfold sqN
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  rw [h] at h1
  have h2 : ‖z i‖ ≤ 1 := by nlinarith [norm_nonneg (z i)]
  exact pow_le_one₀ (norm_nonneg _) h2
end ReciprocityTheory.GeometryOfNumbersTheory
