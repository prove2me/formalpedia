-- Prove2me | solution 1 for TwoDegenerateGraphs.entropy_potential_layers_impossible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/cde8c021-0dad-484f-829b-27fdfcd5e6f6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (depth : ℕ) (potential : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth,
      certifiedWindowWidth / 2 < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  have htotal :
      ∀ i ≤ depth,
        (i : ℝ) * (certifiedWindowWidth / 2) ≤
          potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiprev : i ≤ depth := by omega
        have histep : i < depth := by omega
        have hprevious := ih hiprev
        have hnext := (hincrement i histep).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith
end TwoDegenerateGraphs
