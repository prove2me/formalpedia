-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_le_puncturedReedMullerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:13:48.178622+00:00
-- url     : https://prove2.me/submissions/e094962d-484f-406e-84d0-abc4655eaf64

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    (r m w : Nat) :
    (shortenedReedMullerCode r m w).carrier ≤
      (puncturedReedMullerCode r m w).carrier := by
  intro word hword
  rcases (mem_shortenedReedMullerCode word).1 hword with
    ⟨full, hfull, _hlow, rfl⟩
  exact (mem_puncturedReedMullerCode _).2 ⟨full, hfull, rfl⟩
end QEC.Coding.PuncturedReedMuller
