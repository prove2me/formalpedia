-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:59.540964+00:00
-- url     : https://prove2.me/submissions/efce4490-7ace-4a76-9275-7c2b86f480e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    FiniteDimensional k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)) := by
  set E := (affRing k y j).toIntermediateField' (isField_affRing hy hj)
  let g : Poly k N →ₐ[k] E :=
    AlgHom.codRestrict (aeval (aff y j) : Poly k N →ₐ[k] Ω) E.toSubalgebra
      (fun f => show _ ∈ affRing k y j from ⟨f, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨z, f, rfl⟩
    exact ⟨f, rfl⟩
  have : Algebra.FiniteType k E := Algebra.FiniteType.of_surjective g hg
  exact finite_of_finite_type_of_isJacobsonRing k E
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
