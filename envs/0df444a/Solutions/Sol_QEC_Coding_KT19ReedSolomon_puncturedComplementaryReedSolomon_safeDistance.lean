-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_safeDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:15.63727+00:00
-- url     : https://prove2.me/submissions/e0a44c3f-7614-4650-811a-8b2127822cc7

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedComplementaryReedSolomon_minimumDistance

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistanceAtLeast (puncturedReedSolomonCode p (p - l) k) (l - k) := by
  rcases puncturedComplementaryReedSolomon_minimumDistance p l k h with
    ⟨witness, hwitness, hwitnessNe, hwitnessWeight, hleast⟩
  intro word hword hwordNe
  exact (by omega : l - k ≤ l + 1 - k).trans (hleast word hword hwordNe)
end QEC.Coding.KT19ReedSolomon
