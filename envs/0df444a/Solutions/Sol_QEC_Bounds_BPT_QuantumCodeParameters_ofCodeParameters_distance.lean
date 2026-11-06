-- Prove2me | solution 1 for QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:53.912676+00:00
-- url     : https://prove2.me/submissions/0e5936f7-0967-4d55-a241-e7475a083734

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound

set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeParameters
namespace QEC.Bounds.BPT.QuantumCodeParameters
theorem _root_.solution {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).distance = (p.minimumDistance : ℝ) :=
  rfl
end QEC.Bounds.BPT.QuantumCodeParameters
