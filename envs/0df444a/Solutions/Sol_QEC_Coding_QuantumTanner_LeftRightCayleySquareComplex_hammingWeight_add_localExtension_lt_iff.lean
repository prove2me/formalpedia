-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_add_localExtension_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:29:30.371737+00:00
-- url     : https://prove2.me/submissions/85178c35-0fea-4686-9c89-cbabc6806056

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_hammingWeight_add_localExtension

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    HammingWeight (x + X.localExtension vertex c) < HammingWeight x ↔
      HammingWeight (X.localRestriction vertex x + c) <
        HammingWeight (X.localRestriction vertex x) := by
  have h := X.hammingWeight_add_localExtension vertex x c
  omega
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
