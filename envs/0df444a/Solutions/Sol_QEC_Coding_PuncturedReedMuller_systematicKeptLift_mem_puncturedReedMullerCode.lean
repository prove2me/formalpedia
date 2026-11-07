-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_puncturedReedMullerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:13:54.008876+00:00
-- url     : https://prove2.me/submissions/69fe642f-0c78-4761-ac6a-1816837be10e

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (puncturedReedMullerCode r m w).carrier := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  apply (mem_puncturedReedMullerCode _).2
  exact ⟨lowCoordinateExtension hwr logical,
    lowCoordinateExtension_mem_reedMullerCode hwr logical, rfl⟩
end QEC.Coding.PuncturedReedMuller
