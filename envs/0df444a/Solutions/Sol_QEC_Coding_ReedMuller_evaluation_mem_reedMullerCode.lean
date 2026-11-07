-- Prove2me | solution 1 for QEC.Coding.ReedMuller.evaluation_mem_reedMullerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:21:02.79005+00:00
-- url     : https://prove2.me/submissions/0341b3e6-2329-4896-be2a-d0215122f240

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution {r m : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial ∈ (reedMullerCode r m).carrier :=
  (mem_reedMullerCode _).2 ⟨polynomial, rfl⟩
end QEC.Coding.ReedMuller
