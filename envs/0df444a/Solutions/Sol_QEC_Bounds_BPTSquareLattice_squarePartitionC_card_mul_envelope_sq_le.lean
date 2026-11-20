-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.squarePartitionC_card_mul_envelope_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:18.524973+00:00
-- url     : https://prove2.me/submissions/792f0c0a-0f63-4582-9c26-b88ad37724a5

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionC_card_le_grid_four_mul_sq
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_siteCount_eq_rows_mul_columns

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution
    (L : BPTSquareLattice) {blockWidth margin envelopeWidth tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth) (hseparationWidth : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
      16 * margin * margin * L.siteCount := by
  have hcount := L.squarePartitionC_card_le_grid_four_mul_sq (margin := margin) hblockWidth
    (by omega) hrows hcolumns
  have henvelopeLe : envelopeWidth ≤ 2 * blockWidth := by omega
  have henvelopeSq : envelopeWidth * envelopeWidth ≤
      (2 * blockWidth) * (2 * blockWidth) :=
    Nat.mul_le_mul henvelopeLe henvelopeLe
  have hsites : L.siteCount = tileRows * tileColumns * blockWidth * blockWidth := by
    rw [siteCount_eq_rows_mul_columns L, hrows, hcolumns]
    ring
  calc
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
        (tileRows * tileColumns * (4 * margin * margin)) *
          (envelopeWidth * envelopeWidth) :=
      Nat.mul_le_mul_right _ hcount
    _ ≤ (tileRows * tileColumns * (4 * margin * margin)) *
          ((2 * blockWidth) * (2 * blockWidth)) :=
      Nat.mul_le_mul_left _ henvelopeSq
    _ = 16 * margin * margin * (tileRows * tileColumns * blockWidth * blockWidth) := by
      ring
    _ = 16 * margin * margin * L.siteCount := by rw [hsites]
end QEC.Bounds.BPTSquareLattice
