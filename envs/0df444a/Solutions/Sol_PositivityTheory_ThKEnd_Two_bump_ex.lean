-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.bump_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:34.038467+00:00
-- url     : https://prove2.me/submissions/93e3e302-e4a9-4fa9-bedf-44541b5d7fdb

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
import Theorems.Thm_PositivityTheory_ThKEnd_Two_box
import Theorems.Thm_PositivityTheory_ThKEnd_Two_nhds_box
import Theorems.Thm_PositivityTheory_ThKEnd_Two_gauge

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
theorem _root_.solution [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O)
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U)
    {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ η, Bump W η ∧ ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ ∀ (y y' : SL(2, R)) (b : ℝ),
      (∀ i j, q ((y.1 - y'.1) i j) ∈ L ∧ ‖p ((y.1 - y'.1) i j)‖ ≤ b) → |η y' - η y| ≤ 4 * b := by
  classical
  obtain ⟨O, hO, hOW⟩ := nhds_box hW
  obtain ⟨ε₀, h0, U, hU, hO'⟩ := hn O hO
  obtain ⟨L, Lo, Lc, LU⟩ := hL U hU
  obtain ⟨ε, ε0, ε1, ε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ 1 / 2 := ⟨_, lt_min h0 one_half_pos, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨d, dc, d00, d0, dt, dl⟩ := gauge p q hp hq Lo
  obtain ⟨e, he⟩ : ∃ e : SL(2, R) → ℝ, ∀ y, e y = ∑ i, ∑ j, d ((y.1 - 1) i j) := ⟨_, fun _ => rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : SL(2, R) → ℝ, ∀ y, η y = max (ε - e y) 0 := ⟨_, fun _ => rfl⟩
  have ec : Continuous e := by
    rw [funext he]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    dc.comp ((continuous_subtype_val.sub continuous_const).matrix_elem i j)
  have hs : ∀ y ∈ tsupport η, ∀ i j, ‖p ((y.1 - 1) i j)‖ ≤ ε ∧ q ((y.1 - 1) i j) ∈ L := fun y hy i j => by
    have h1 : e y ≤ ε := closure_minimal (s := Function.support η) (t := {y | e y ≤ ε})
      (fun z hz => le_of_not_gt fun h : ε < e z => hz ((hη z).trans (max_eq_right (by linarith))))
      (isClosed_le ec continuous_const) hy
    have h2 : d ((y.1 - 1) i j) ≤ ε :=
      ((Finset.single_le_sum (f := fun j => d ((y.1 - 1) i j)) (fun _ _ => d0 _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, d ((y.1 - 1) i j)) (fun _ _ => Finset.sum_nonneg fun _ _ => d0 _)
          (Finset.mem_univ i))).trans (he y ▸ h1)
    exact dl _ ε ε2 h2
  have hcs : HasCompactSupport η :=
    (box fun i j => (hc ε L Lc).image (continuous_add_const ((1 : Matrix (Fin 2) (Fin 2) R) i j))).of_isClosed_subset
      (isClosed_tsupport _) fun y hy i j => ⟨_, hs y hy i j, by simp⟩
  have ηc : Continuous η := by rw [funext hη]; exact (continuous_const.sub ec).max continuous_const
  refine ⟨η, ⟨ηc, hcs, fun y hy => hOW y fun i j => hO' _ ((hs y hy i j).1.trans ε1) (LU (hs y hy i j).2),
    fun y => (le_max_right _ _).trans_eq (hη y).symm, ?_⟩, L, Lo, fun y y' b hb => ?_⟩
  · have : e 1 = 0 := by simp [he, d00]
    simp only [hη, this, sub_zero, max_eq_left ε0.le]
    exact ε0.ne'
  rw [hη, hη]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [sub_sub_sub_cancel_left]
  simp only [he, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (g := fun _ => b) fun j _ => ?_)).trans_eq (by simp; ring))
  have e2 : (y.1 - 1) i j - (y'.1 - 1) i j = (y.1 - y'.1) i j := by rw [← Matrix.sub_apply, sub_sub_sub_cancel_right]
  exact (dt _ _ (e2 ▸ (hb i j).1)).trans (e2 ▸ (hb i j).2)
end PositivityTheory.ThKEnd.Two
