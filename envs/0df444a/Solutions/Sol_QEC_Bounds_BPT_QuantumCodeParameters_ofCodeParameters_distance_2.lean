-- Prove2me | solution 2 for QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_distance
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:09.502363+00:00
-- url     : https://prove2.me/submissions/b4db3d00-bdca-4cee-ab0d-61b23c233aa5

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
    (ofCodeParameters p).distance = (p.minimumDistance : ℝ) := by
  rfl
