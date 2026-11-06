-- Prove2me | solution 1 for QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_blockLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:39.20084+00:00
-- url     : https://prove2.me/submissions/b8df47eb-ba03-4643-98c4-99ab9890e22e

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
    (ofCodeParameters p).blockLength = (p.length : ℝ) :=
  rfl
end QEC.Bounds.BPT.QuantumCodeParameters
