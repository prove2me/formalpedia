-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.queries_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:01:51.57041+00:00
-- url     : https://prove2.me/submissions/ba02a867-b8cc-41ca-8dec-dce443e28dca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
section
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
private theorem queryPrefix_succ_eq (e : TopWord S n) (a : LevelIndex n)
    (b : Nat) (hb : b+1 ≤ n) :
    queryPrefix S n e a (b+1) hb =
      if h : a.val = b+1 then
        (show a = ⟨b+1,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else if ha : a.val ≤ b then
        correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
          (potential S n e ⟨b+1,Nat.lt_succ_of_le hb⟩) ∪
          liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (queryPrefix S n e a b (by omega))
      else ∅ := by
  rw [queryPrefix] <;> rfl
end QEC.Coding.BDL26PairedHistoryQueryCone
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) :
    queries S n e a i.succ =
      correctionQueries S (n+2) (LevelTwoHistory.physicalStep i) (potential S n e i.succ) ∪
        liftQueries S (n+2) (LevelTwoHistory.physicalStep i) (queries S n e a i.castSucc) := by
  rcases i with ⟨b,hb⟩
  change a.val ≤ b at ha
  change queryPrefix S n e a (b+1) _ =
    correctionQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,hb⟩)
      (potential S n e ⟨b+1,by omega⟩) ∪
      liftQueries S (n+2) (LevelTwoHistory.physicalStep ⟨b,hb⟩) (queryPrefix S n e a b _)
  rw [queryPrefix_succ_eq,dif_neg (by omega),dif_pos ha]
end QEC.Coding.BDL26PairedHistoryQueryCone
