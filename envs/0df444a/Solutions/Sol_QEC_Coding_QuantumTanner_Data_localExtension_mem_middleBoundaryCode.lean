-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localExtension_mem_middleBoundaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:03:44.655221+00:00
-- url     : https://prove2.me/submissions/4e691a13-22dd-4dd1-b96b-c5ff87dc8589

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_localExtension_mem_range_zGeneratorMap

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA D.codeB).carrier) :
    D.complex.localExtension (g, false) c ∈ D.chainComplex.middleBoundaryCode.carrier := by
  exact D.toRawData.localExtension_mem_range_zGeneratorMap g c hc
end QEC.Coding.QuantumTanner.Data
