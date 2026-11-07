-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_le_puncturedReedSolomonCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:59.115203+00:00
-- url     : https://prove2.me/submissions/353c41a5-25d0-4428-af56-ed99dda192b7

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution
    (p l k : Nat) [Fact p.Prime] :
    (shortenedReedSolomonCode p l k).carrier ≤
      (puncturedReedSolomonCode p l k).carrier := by
  intro word hword
  rcases (mem_shortenedReedSolomonCode word).1 hword with
    ⟨full, hfull, _hselected, rfl⟩
  exact (mem_puncturedReedSolomonCode _).2 ⟨full, hfull, rfl⟩
end QEC.Coding.KT19ReedSolomon
