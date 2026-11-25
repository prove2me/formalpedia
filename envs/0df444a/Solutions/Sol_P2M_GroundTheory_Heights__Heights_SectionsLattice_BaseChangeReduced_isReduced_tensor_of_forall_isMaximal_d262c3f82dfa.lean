-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:12.811116+00:00
-- url     : https://prove2.me/submissions/227ce130-e19a-483e-bdb3-965aff5c81b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_PBaseChangeReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open TensorProduct
open GroundTheory.Heights₂.Heights.SectionsLattice
open GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
namespace GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
theorem _root_.solution {k R B : Type} [Field k] [CommRing R] [Algebra k R]
    [IsJacobsonRing R] [IsReduced R] [CommRing B] [Algebra k B]
    (h : ∀ m : Ideal R, m.IsMaximal → IsReduced ((R ⧸ m) ⊗[k] B)) : IsReduced (R ⊗[k] B) := by
  let b := Module.Free.chooseBasis k B
  have key : ∀ (m : Ideal R) (i) (y : R ⊗[k] B),
      Ideal.Quotient.mk m ((Algebra.TensorProduct.basis R b).repr y i) =
        (Algebra.TensorProduct.basis (R ⧸ m) b).repr
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k m) (AlgHom.id k B) y) i := by
    intro m i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add y z hy hz => simp [map_add, hy, hz]
  constructor
  intro x hx
  apply (Algebra.TensorProduct.basis R b).repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hmem : (Algebra.TensorProduct.basis R b).repr x i ∈ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, key m i x]
    have hz : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k m) (AlgHom.id k B) x = 0 :=
      (h m hm).eq_zero _ (hx.map _)
    rw [hz]
    simp
  rwa [IsJacobsonRing.out inferInstance Ideal.isRadical_bot] at hmem
end GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
