-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localExtension_mem_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:03:41.13076+00:00
-- url     : https://prove2.me/submissions/a135e77b-d6c5-4f51-a4f8-2c90ab34ee5e

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_localExtension_mem_range_xGeneratorMap
import Theorems.Thm_QEC_Coding_wordLinearMapTranspose_transpose


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
    (hc : c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier) :
    D.complex.localExtension (g, true) c ∈ D.chainComplex.firstCoboundaryCheckCode.carrier := by
  change D.complex.localExtension (g, true) c ∈
    LinearMap.range (wordLinearMapTranspose (wordLinearMapTranspose D.toRawData.xGeneratorMap))
  rw [wordLinearMapTranspose_transpose]
  exact D.toRawData.localExtension_mem_range_xGeneratorMap g c hc
end QEC.Coding.QuantumTanner.Data
