-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then_union
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:12.806479+00:00
-- url     : https://prove2.me/submissions/abe29e12-010c-43c2-a8ef-819ea4bcb79d

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

namespace QBAux

theorem extendLocalToRegister_mul {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : Semantics.QuditSubsystem q) (A B : Semantics.Operator S.selectedSystem) :
    S.extendLocalToRegister (A * B) = S.extendLocalToRegister A * S.extendLocalToRegister B := by
  have h : S.extendLocal (A * B) = S.extendLocal A * S.extendLocal B := by
    apply TensorProduct.ext'
    intro x y
    simp [Semantics.QuditSubsystem.extendLocal]
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [h, Semantics.UnitaryTransport.conjOperator_mul]

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn left U) (hV : M.UnitarySupportedOn right V) :
    M.UnitarySupportedOn (left ∪ right) (thenUnitary U V) := by
  have hU' : M.UnitarySupportedOn (left ∪ right) U :=
    operatorSupportedOnRegister_of_subset (M.regionSubsystem left)
      (M.regionSubsystem (left ∪ right)) (fun x hx => Finset.mem_union_left _ hx) hU
  have hV' : M.UnitarySupportedOn (left ∪ right) V :=
    operatorSupportedOnRegister_of_subset (M.regionSubsystem right)
      (M.regionSubsystem (left ∪ right)) (fun x hx => Finset.mem_union_right _ hx) hV
  obtain ⟨a, ha⟩ := hU'
  obtain ⟨b, hb⟩ := hV'
  refine ⟨b * a, ?_⟩
  rw [QBAux.extendLocalToRegister_mul, ha, hb]
  apply LinearMap.ext
  intro x
  rfl
