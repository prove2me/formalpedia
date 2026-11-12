-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:34:59.290782+00:00
-- url     : https://prove2.me/submissions/6b9345bb-087b-4cd9-a006-83ab274c7d06

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a c : LevelIndex n)
    (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 c
      ((SuffixData S n).family.coboundary0 c (accumulatedPotential S n b u a c.val hcb hac)) = 0 := by
  have h := LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 c)
    (accumulatedPotential S n b u a c.val hcb hac)
  exact h
end QEC.Coding.BDL26HistoryErrorTelescoping
