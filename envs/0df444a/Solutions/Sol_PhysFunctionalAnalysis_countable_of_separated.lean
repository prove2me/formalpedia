-- Prove2me | solution 1 for PhysFunctionalAnalysis.countable_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:43.872988+00:00
-- url     : https://prove2.me/submissions/aecc00d6-d2fb-42ca-9d42-fa431c925726

-- Generated from PhysFunctionalAnalysis.lean — solution of PhysFunctionalAnalysis.countable_of_separated
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_ChapterA4
open PhysFunctionalAnalysis



open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {ι : Type*} (u : ι → X) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (u i) (u j)) : Countable ι := by

  obtain ⟨ D, hD_countable, hD_dense ⟩ := TopologicalSpace.exists_countable_dense X;
  -- For each $i \in \iota$, choose $d_i \in D$ such that $dist (u i) (d_i) < r / 2$.
  obtain ⟨d, hd⟩ : ∃ d : ι → X, (∀ i, d i ∈ D) ∧ (∀ i, dist (u i) (d i) < r / 2) := by
    exact ⟨ fun i => Classical.choose ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ), fun i =>
      Classical.choose_spec ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ) |>.1, fun i =>
      Classical.choose_spec ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ) |>.2 ⟩;
  have h_inj : Function.Injective d := by
    intro i j hij;
    exact Classical.not_not.1 fun h => by
      have := hsep i j h
      linarith [ hd.2 i, hd.2 j, dist_triangle_right ( u i ) ( u j ) ( d i ), dist_triangle_right (
        u j ) ( u i ) ( d j ), hij ▸ hd.2 i, hij ▸ hd.2 j ]
  exact Set.countable_univ_iff.mp ( Set.Countable.mono ( fun x _ => by aesop ) (
                                                                      hD_countable.preimage h_inj )
    )
