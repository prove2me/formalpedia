-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotential_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:46.085593+00:00
-- url     : https://prove2.me/submissions/6324e323-562c-4a88-9d44-a63f9b592649

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (c : ℝ)
    (Q : LocPot X) (hU : Q.U = P.U) (hφ : ∀ x y, Q.φ x y = c * P.φ x y) : IsPotential A Q := by
  have hQφ : ∀ x, Q.φ x = fun y => c * P.φ x y := fun x => funext (hφ x)
  refine ⟨fun x => ?_, fun x x' y hy => ?_⟩
  · rw [hQφ x, hU]
    exact fun j => contDiffOn_const.mul (hP.1 x j)
  · rw [hU] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, fun z => (c : ℂ) * G z, holoOn_mul A hG c, fun z hz => ?_⟩
    rw [hU] at hz
    rw [hφ, hφ, ← mul_sub, hGe z hz, Complex.re_ofReal_mul]
end ReciprocityTheory.AnForm.M
