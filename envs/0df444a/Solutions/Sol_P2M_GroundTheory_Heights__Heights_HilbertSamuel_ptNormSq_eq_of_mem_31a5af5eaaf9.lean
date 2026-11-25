-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:45.555802+00:00
-- url     : https://prove2.me/submissions/8e4265e9-d27d-43fd-a6a0-df499e93146c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
  have hk : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hkj : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hk, hx⟩
  have hg : 0 < ‖L.g (chartIdx A x) j x‖ ^ 2 := by
    have := L.ne_zero _ _ x hkj
    positivity
  have he : Real.exp ((n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hg n)]
  rw [ptNormSq, hs.2.1 _ j x hkj, W.compat _ j x hkj, norm_mul, norm_pow,
    show -(n : ℝ) * (W.φ j x + Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2) by ring,
    Real.exp_sub, he]
  have hp : 0 < (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := pow_pos hg n
  field_simp
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
