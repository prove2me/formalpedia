-- Prove2me | solution 1 for QEC.QLDPC.generatedStabilizer_of_generators_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:27:49.666977+00:00
-- url     : https://prove2.me/submissions/18588b95-9835-4caf-912f-024e5c7651fa

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : Type v} {mu : Type w} [Fintype κ] [Fintype mu]
    {source : κ → Coding.PauliSymplectic.Binary ι}
    {target : mu → Coding.PauliSymplectic.Binary ι}
    (hgenerator : ∀ j, Coding.PauliSymplectic.GeneratedStabilizer target (source j))
    {P : Coding.PauliSymplectic.Binary ι}
    (hP : Coding.PauliSymplectic.GeneratedStabilizer source P) :
    Coding.PauliSymplectic.GeneratedStabilizer target P := by
  induction hP with
  | one => exact Coding.PauliSymplectic.GeneratedStabilizer.one
  | generator j => exact hgenerator j
  | mul _ _ ihP ihQ => exact Coding.PauliSymplectic.GeneratedStabilizer.mul ihP ihQ
  | dagger _ ihP => exact Coding.PauliSymplectic.GeneratedStabilizer.dagger ihP
end QEC.QLDPC
