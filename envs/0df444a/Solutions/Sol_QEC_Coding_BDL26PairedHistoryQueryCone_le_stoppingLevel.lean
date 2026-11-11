-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.le_stoppingLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:31:29.327239+00:00
-- url     : https://prove2.me/submissions/735541e2-eb2a-4a12-8f21-f4f10263ff0f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n)
    (ha : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a) :
    a ≤ stoppingLevel S n s e := by
  have hm : a ∈ coalescentLevels S n s e := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  rw [stoppingLevel,dif_pos ⟨a,hm⟩]
  exact Finset.le_max' _ a hm
end QEC.Coding.BDL26PairedHistoryQueryCone
