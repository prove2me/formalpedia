-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:28.119097+00:00
-- url     : https://prove2.me/submissions/38c22e82-63f1-4d34-b1a4-e06623939447

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D : ℕ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {g h : MvPowerSeries (Fin D) ℂ} (hlt : lexOrder g < lexOrder h) :
    lexOrder (g + h) = lexOrder g := by
  apply le_antisymm
  · have hg : g ≠ 0 := by rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero]; exact ne_top_of_lt hlt
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hg
    rw [hd]
    apply lexOrder_le_of_coeff_ne_zero
    rw [map_add, coeff_eq_zero_of_lt_lexOrder (φ := h) (d := d) (by rw [← hd]; exact hlt), add_zero]
    exact coeff_ne_zero_of_lexOrder hd.symm
  · calc lexOrder g = min (lexOrder g) (lexOrder h) := (min_eq_left hlt.le).symm
      _ ≤ _ := min_lexOrder_le
end GlobalTheory.HilbertSamuelPS
