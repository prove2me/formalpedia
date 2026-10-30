-- Prove2me | solution 1 for compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:34:11.636647+00:00
-- url     : https://prove2.me/submissions/9f4a7026-e891-4b0a-96f5-ea6041e41895
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_planar_arc_attachment_same_component_count
import Theorems.Thm_planar_arc_attachment_different_components_count

theorem solution
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (a : ℝ → ℝ × ℝ)
    (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (hfinite : Finite (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ})) :
    Finite (ConnectedComponents
      {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) ∧
    (a 1 ∈ connectedComponentIn K (a 0) →
      Nat.card (ConnectedComponents
        {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) =
      Nat.card (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ}) + 1) ∧
    (a 1 ∉ connectedComponentIn K (a 0) →
      Nat.card (ConnectedComponents
        {z : ℝ × ℝ // z ∈ (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ}) =
      Nat.card (ConnectedComponents {z : ℝ × ℝ // z ∈ Kᶜ})) := by
  by_cases hs : a 1 ∈ connectedComponentIn K (a 0)
  · obtain ⟨hf, hc⟩ := planar_arc_attachment_same_component_count
      K a hK hc hinj hzero hone hinterior hs hfinite
    exact ⟨hf, fun _ => hc, fun hn => (hn hs).elim⟩
  · obtain ⟨hf, hd⟩ := planar_arc_attachment_different_components_count
      K a hK hc hinj hzero hone hinterior hs hfinite
    exact ⟨hf, fun hh => (hs hh).elim, fun _ => hd⟩
