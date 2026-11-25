-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.map_mul_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:19.192006+00:00
-- url     : https://prove2.me/submissions/e50fa1d0-b5c4-4c8b-bbe6-72546b752680

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) :
    Measure.map (fun c : ι → ℂ => s * c) volume = ENNReal.ofReal (∏ w, ‖s w‖ ^ 2)⁻¹ • volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun i => (LinearMap.mul ℝ ℂ (s i)).comp (LinearMap.proj i)
  have hd : LinearMap.det f = ∏ w, ‖s w‖ ^ 2 := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := Algebra.norm_apply ℝ (s i)
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq] at this
    exact this.symm
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := f) (by rw [hd]; exact hp.ne')
  rw [hd, abs_of_pos (inv_pos.2 hp)] at this
  exact this
end PositivityTheory.ThKG.Loc.Bump
