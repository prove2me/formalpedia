-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_comp_le_of_isOpen_6d6ecdc7201c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:33.116702+00:00
-- url     : https://prove2.me/submissions/b1a95f8c-df24-4bbd-bd20-4170a579f096

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
