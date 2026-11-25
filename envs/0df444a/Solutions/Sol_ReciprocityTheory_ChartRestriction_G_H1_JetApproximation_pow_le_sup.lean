-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:22.696561+00:00
-- url     : https://prove2.me/submissions/46931009-47b5-4942-8ea9-e5e44ff1040d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_le_pow_of_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_le_ideal_pow

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
theorem _root_.solution {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R}
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m) (D : ℕ) (n : ℕ) :
    V ^ n ≤ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
  set W : Submodule F R := V ⊓ m.restrictScalars F
  have hVW : V ≤ 1 ⊔ W := by
    intro v hv
    obtain ⟨c, hc⟩ := hres v
    refine Submodule.mem_sup.2 ⟨algebraMap F R c, Submodule.algebraMap_mem c, v - algebraMap F R c,
      ⟨V.sub_mem hv (h1 (Submodule.algebraMap_mem c)), hc⟩, add_sub_cancel _ _⟩
  have hWm : W ≤ m.restrictScalars F := inf_le_right
  have key : ∀ n k : ℕ, W ^ k * V ^ n ≤ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero, mul_one]
      rcases le_or_gt k D with hk | hk
      · exact le_sup_of_le_left ((pow_le_pow_of_le inf_le_left k).trans (pow_mono h1 hk))
      · refine le_sup_of_le_right ((pow_le_ideal_pow hWm k).trans ?_)
        intro x hx
        exact Ideal.pow_le_pow_right hk hx
    | succ n ih =>
      intro k
      calc W ^ k * V ^ (n + 1) = W ^ k * (V ^ n * V) := by rw [pow_succ]
        _ ≤ W ^ k * (V ^ n * (1 ⊔ W)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hVW)
        _ = W ^ k * V ^ n ⊔ W ^ (k + 1) * V ^ n := by
          rw [Submodule.mul_sup, mul_one, Submodule.mul_sup, ← mul_assoc, pow_succ, mul_right_comm (W ^ k) W]
        _ ≤ _ := sup_le (ih k) (ih (k + 1))
  simpa using key n 0
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
