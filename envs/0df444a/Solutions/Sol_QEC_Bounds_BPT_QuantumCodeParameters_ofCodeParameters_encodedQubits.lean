-- Prove2me | solution 1 for QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_encodedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:50.45099+00:00
-- url     : https://prove2.me/submissions/6af013ab-eec3-4cf6-9db3-0deb4f933c20

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
    (ofCodeParameters p).encodedQubits = (p.dimension : ℝ) :=
  rfl
end QEC.Bounds.BPT.QuantumCodeParameters
