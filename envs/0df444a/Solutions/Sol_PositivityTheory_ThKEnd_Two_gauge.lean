-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.gauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:40.825965+00:00
-- url     : https://prove2.me/submissions/5f5a2d63-22c8-424b-92ed-ba79d0ddb2d1

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q) {L : AddSubgroup Λ} (Lo : IsOpen (L : Set Λ)) :
    ∃ d : R → ℝ, Continuous d ∧ d 0 = 0 ∧ (∀ x, 0 ≤ d x) ∧ (∀ x y, q (x - y) ∈ L → |d x - d y| ≤ ‖p (x - y)‖) ∧
      ∀ x, ∀ ε ≤ 1 / 2, d x ≤ ε → ‖p x‖ ≤ ε ∧ q x ∈ L := by
  classical
  let d : R → ℝ := fun x => ‖p x‖ + if q x ∈ L then 0 else 1
  have d0 : ∀ x, 0 ≤ d x := fun x => add_nonneg (norm_nonneg _) (by split_ifs <;> simp)
  have dc : Continuous d := hp.norm.add ((IsLocallyConstant.continuous (f := fun z : Λ => if z ∈ L then (0 : ℝ) else 1)
    ((IsLocallyConstant.iff_eventually_eq _).2 fun z => by
      by_cases hz : z ∈ L
      · filter_upwards [Lo.mem_nhds hz] with w hw
        simp [hz, show w ∈ L from hw]
      · filter_upwards [(L.isClosed_of_isOpen Lo).isOpen_compl.mem_nhds hz] with w hw
        simp [hz, show w ∉ L from hw])).comp hq)
  have dt : ∀ x y, q (x - y) ∈ L → |d x - d y| ≤ ‖p (x - y)‖ := fun x y h => by
    have : q x ∈ L ↔ q y ∈ L := by
      rw [map_sub] at h
      exact ⟨fun a => by simpa using sub_mem a h, fun a => by simpa using add_mem h a⟩
    simp only [d, this, add_sub_add_right_eq_sub, map_sub]
    exact abs_norm_sub_norm_le _ _
  refine ⟨d, dc, by simp [d], d0, dt, fun x ε h3 h2 => ?_⟩
  have h4 := norm_nonneg (p x)
  simp only [d] at h2
  split_ifs at h2 with h
  · exact ⟨by linarith, h⟩
  · linarith
end PositivityTheory.ThKEnd.Two
