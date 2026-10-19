-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryPinskerGapDerivTwo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/44342703-efee-4aec-87af-d1929cf5af41

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {q : ℝ}
    (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ binaryPinskerGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      binaryPinskerGapDerivTwo q =
        (2 * q - 1) ^ 2 / (q * (1 - q)) := by
    unfold binaryPinskerGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (sq_nonneg _) (mul_pos hqzero hcomplement).le
end TwoDegenerateGraphs
