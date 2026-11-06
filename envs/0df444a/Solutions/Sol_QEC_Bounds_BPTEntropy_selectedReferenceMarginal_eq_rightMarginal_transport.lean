-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.selectedReferenceMarginal_eq_rightMarginal_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:10:42.750656+00:00
-- url     : https://prove2.me/submissions/f52e99c0-e21d-45ff-8e06-81cafa2d0593

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    S.selectedReferenceMarginal Ref omega =
      rightMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) :=
  rfl
end QEC.Bounds.BPTEntropy
