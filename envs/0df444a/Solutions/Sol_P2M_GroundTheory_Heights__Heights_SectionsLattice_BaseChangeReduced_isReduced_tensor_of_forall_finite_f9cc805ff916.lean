-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:35.076955+00:00
-- url     : https://prove2.me/submissions/fae8b51c-d0f3-4bf1-8b3e-bbf807a1c731

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_PBaseChangeReduced
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa

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
theorem _root_.solution {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (hB : ∀ (E : Type) [Field E] [Algebra k E] [FiniteDimensional k E], IsReduced (E ⊗[k] B))
    (A : Type) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (B ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro A₀ hfg
  have : Algebra.FiniteType k A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsJacobsonRing A₀ := isJacobsonRing_of_finiteType (A := k)
  have : IsReduced A₀ := isReduced_of_injective A₀.val Subtype.val_injective
  have hA₀ : IsReduced (A₀ ⊗[k] B) := isReduced_tensor_of_forall_isMaximal fun m hm => by
    let := Ideal.Quotient.field m
    have := finite_of_finite_type_of_isJacobsonRing k (A₀ ⧸ m)
    exact hB (A₀ ⧸ m)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k B A₀).toAlgHom
    (Algebra.TensorProduct.comm k B A₀).injective
end GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
