-- Prove2me | solution 2 for QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_blockLength
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:08.342321+00:00
-- url     : https://prove2.me/submissions/83f63489-9f97-4d28-86fb-581d2a6f6139

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeParameters

theorem solution {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).blockLength = (p.length : ℝ) := by
  rfl
