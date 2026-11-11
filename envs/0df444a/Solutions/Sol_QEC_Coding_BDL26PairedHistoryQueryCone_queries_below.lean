-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.queries_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:17:29.701602+00:00
-- url     : https://prove2.me/submissions/60a13a48-5341-4232-94e7-472a91d080c4

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
private theorem queryPrefix_zero_eq (e : TopWord S n) (a : LevelIndex n) (hb : 0 ≤ n) :
    queryPrefix S n e a 0 hb =
      if h : a.val = 0 then
        (show a = ⟨0,Nat.lt_succ_of_le hb⟩ from Fin.ext h) ▸ querySeed S n e a
      else ∅ := by
  rw [queryPrefix] <;> rfl
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
theorem _root_.solution (e : TopWord S n) (a b : LevelIndex n) (h : b.val < a.val) :
    queries S n e a b = ∅ := by
  rcases b with ⟨b,hb⟩
  cases b with
  | zero =>
      change 0 < a.val at h
      change queryPrefix S n e a 0 _ = ∅
      rw [queryPrefix_zero_eq]
      exact dif_neg (by omega)
  | succ b =>
      change b+1 < a.val at h
      change queryPrefix S n e a (b+1) _ = ∅
      rw [queryPrefix_succ_eq,dif_neg (by omega),dif_neg (by omega)]
end QEC.Coding.BDL26PairedHistoryQueryCone
