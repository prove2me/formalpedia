-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_sdiff_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:15.115638+00:00
-- url     : https://prove2.me/submissions/e32285b3-d9d2-42fe-a191-7695dbf3a5c8

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.ActualProjectorSeparated (left \ right) right := by
  intro check hboth
  apply hseparated check
  refine ⟨?_, hboth.2⟩
  rcases hboth.1 with ⟨site, hsite⟩
  rcases Finset.mem_inter.mp hsite with ⟨hsupport, hleftMinus⟩
  exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_sdiff.mp hleftMinus).1⟩⟩
end QEC.Bounds.BPTCommutingProjectorModel
