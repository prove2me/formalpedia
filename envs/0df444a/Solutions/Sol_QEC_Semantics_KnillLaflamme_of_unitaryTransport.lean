-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.of_unitaryTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:52.747952+00:00
-- url     : https://prove2.me/submissions/a8a0dff9-ad01-4172-b7d7-ec18b6440773

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
open QEC.Semantics.KnillLaflamme
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.KnillLaflamme
theorem _root_.solution
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors)) :
    KnillLaflammeCriterion H C errors := by
  rcases hKL with ⟨scalar, hscalar⟩
  refine ⟨fun E F => scalar (U.conjOperator E) (U.conjOperator F), ?_⟩
  intro E hE F hF x hx y hy
  have hxD : U.toLinearEquiv x ∈ D.carrier := (hCD x).1 hx
  have hyD : U.toLinearEquiv y ∈ D.carrier := (hCD y).1 hy
  have hmatrix :=
    hscalar (E := U.conjOperator E)
      (Set.mem_image_of_mem (UnitaryTransport.conjOperator U) hE)
      (F := U.conjOperator F)
      (Set.mem_image_of_mem (UnitaryTransport.conjOperator U) hF)
      (U.toLinearEquiv x) hxD (U.toLinearEquiv y) hyD
  calc
    inner Complex (E x) (F y)
        = inner Complex (U.toLinearEquiv (E x)) (U.toLinearEquiv (F y)) := by
          simpa using (U.map_inner (E x) (F y)).symm
    _ = scalar (U.conjOperator E) (U.conjOperator F) * inner Complex x y := by
          simpa [UnitaryTransport.conjOperator, U.map_inner x y] using hmatrix
end QEC.Semantics.KnillLaflamme
