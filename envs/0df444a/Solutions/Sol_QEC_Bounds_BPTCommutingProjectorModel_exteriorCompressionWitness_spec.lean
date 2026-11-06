-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exteriorCompressionWitness_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:36.571064+00:00
-- url     : https://prove2.me/submissions/19ce963a-0358-4742-944c-630316b2bba7

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorWitness
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionFactorization_conj_exteriorLocal


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 500000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let S := M.regionSubsystem region
    S.registerFactorization.conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
        (M.exteriorCompressionComplementAction region P) := by
  exact Classical.choose_spec (M.regionFactorization_conj_exteriorLocal region P)
end QEC.Bounds.BPTCommutingProjectorModel
